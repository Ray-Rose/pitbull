//! External SMT solver invocation.
//!
//! Today: just Z3, via `Command::new("z3")` reading SMT-LIB from
//! stdin. Z3 is the most widely deployed SMT solver and is
//! available pre-packaged on every platform Pitbull targets, so
//! it's the natural first integration.
//!
//! Future:
//! - CVC5 adapter, same shape.
//! - Alt-Ergo adapter (Why3's native solver).
//! - Multi-solver agreement gate: run all three, require 2-of-3
//!   `unsat` agreement before reporting an obligation discharged.
//!   See Safety Manual §3.3 for the soundness rationale (1,500+
//!   known solver bugs as of 2026-05).
//! - Per-solver version pinning (already in pitbull.toml's
//!   `[verification.solver_versions]` map); the solver adapter
//!   should refuse to run a version not on that list.
//! - Configurable per-VC timeout (today: hardcoded 10s).
//!
//! ## Graceful degradation
//!
//! Z3 might not be installed on a developer's machine. The
//! invocation distinguishes "solver missing" from "solver returned
//! error" so the calling code can fall back to "VC unsolved" rather
//! than crashing. CI installs Z3 explicitly when verification
//! coverage is part of the gate.
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
/// Outcome of an SMT solver invocation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverResult {
    /// `(check-sat)` returned `sat` — a counterexample exists. For
    /// safety obligations (where we ask the solver to disprove the
    /// negation), this means the obligation does NOT discharge.
    Sat,
    /// `(check-sat)` returned `unsat` — no counterexample. The
    /// obligation is discharged; the property holds.
    Unsat,
    /// `(check-sat)` returned `unknown` — solver couldn't decide
    /// within its limits. Conservative posture: treat as
    /// undischarged.
    Unknown,
    /// Solver binary not installed on this machine. The verifier
    /// reports this distinctly so the user can install Z3 rather
    /// than wondering why every VC is "unknown".
    NotInstalled,
    /// Solver invocation hit the timeout we set.
    Timeout,
    /// Anything else: spawn failure, malformed output, etc.
    /// The `String` is a short human-readable diagnostic.
    Error(String),
}
/// Default per-VC timeout. Generous for the v0.2 scaffold; tighten
/// once we have CI baseline data.
const DEFAULT_TIMEOUT: Duration = Duration::from_secs(10);
/// Maximum bytes captured from a child solver's stdout. A
/// pathological SMT problem can drive Z3 to emit unbounded output
/// (e.g. via `(get-model)` on a problem with millions of free
/// constants) and OOM the wrapper. Cap defends against that.
///
/// 16 MiB is far more than any well-formed v0.2 problem produces
/// (verdicts are ~10 bytes; models are at most a few KiB) while
/// still leaving headroom for legitimate debug output.
///
/// Audit-cleanup (audit finding N3, 2026-05-26).
const STDOUT_CAP_BYTES: u64 = 16 * 1024 * 1024;
/// Same cap on stderr. Z3's error messages are at most a few KiB
/// in normal operation; an unbounded stderr usually indicates a
/// runaway internal panic loop.
const STDERR_CAP_BYTES: u64 = 1024 * 1024;
/// Maximum SMT-LIB input length (bytes) the wrapper will accept
/// from a single obligation. A malicious upstream maintainer who
/// can write `pitbull.toml` could otherwise add a multi-GB
/// precondition that — even though F2-validated — would OOM the
/// wrapper as the writer thread holds the full string until Z3
/// consumes it.
///
/// 64 MiB is far larger than any plausible legitimate SMT
/// problem (Pitbull's own emission for a single obligation is
/// under 4 KiB) while still bounding the per-VC memory footprint.
///
/// Audit-cleanup (audit finding H-RT3, 2026-05-26).
const SMT_INPUT_CAP_BYTES: usize = 64 * 1024 * 1024;
/// OS-level supervisory timeout cushion. The wrapper sets Z3's
/// internal `:timeout` via SMT-LIB (which only applies during
/// `(check-sat)`); we add a process-level kill some multiple
/// later to catch the case where Z3 hangs DURING PARSING (before
/// the internal timeout becomes effective).
///
/// 2.5× the requested timeout gives Z3 plenty of grace for slow
/// parsing of large problems while still bounding hang risk.
/// Audit-cleanup (audit finding N3, 2026-05-26 + N3-red-team-followup
/// finding H5): the absolute ceiling stops misconfigured callers
/// from producing multi-hour deadlines from misconfigured very-long
/// SMT timeouts.
const PROCESS_KILL_DEADLINE_CEILING: Duration = Duration::from_secs(2 * 60 * 60);
fn process_kill_deadline(smt_timeout: Duration) -> Duration {
    // 2.5× truncated (integer division), then add 2s for
    // short-timeout cases; clamp to a 2h absolute ceiling.
    let scaled = smt_timeout.saturating_mul(5) / 2;
    let with_grace = scaled.saturating_add(Duration::from_secs(2));
    with_grace.min(PROCESS_KILL_DEADLINE_CEILING)
}
/// Poll interval for `try_wait` while waiting on the child.
/// 50ms balances responsiveness against CPU burn.
const POLL_INTERVAL: Duration = Duration::from_millis(50);
/// How a solver expresses a per-check timeout. The OS-level kill
/// deadline (`process_kill_deadline`) bounds every solver regardless;
/// this is the solver-NATIVE limit that lets a well-behaved solver
/// return `unknown` gracefully instead of being killed.
///
/// Task S (2026-05-28).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum TimeoutConvention {
    /// Z3: prepend `(set-option :timeout <ms>)` to the SMT text.
    Z3SmtOption,
    /// CVC5: pass `--tlimit-per=<ms>` (per-check millisecond limit).
    Cvc5TlimitMillis,
    /// Alt-Ergo: pass `--timelimit=<secs>` (whole-run second limit).
    /// Note: Alt-Ergo ≤ 2.4.0 has NO bit-vector support, so it
    /// cannot vote on Pitbull's QF_BV problems — it returns an
    /// error and is structurally a non-voter. The descriptor exists
    /// for completeness / future BV-capable builds.
    AltErgoTimelimitSecs,
}
/// A descriptor for an external SMT solver that reads SMT-LIB 2 from
/// stdin and emits `sat` / `unsat` / `unknown`. Task S multi-solver
/// agreement (2026-05-28).
#[derive(Clone, Debug)]
pub struct Solver {
    /// Display name used in verdict lines and config (`"z3"`,
    /// `"cvc5"`, `"alt-ergo"`).
    pub name: &'static str,
    /// Executable to spawn (looked up on `PATH`).
    program: &'static str,
    /// Fixed CLI args that put the solver in SMT-LIB2/stdin mode.
    base_args: &'static [&'static str],
    /// How this solver expresses a per-check timeout.
    timeout: TimeoutConvention,
}
/// Z3: `z3 -in` reads SMT-LIB2 from stdin; timeout via SMT option.
pub const Z3: Solver = Solver {
    name: "z3",
    program: "z3",
    base_args: &["-in"],
    timeout: TimeoutConvention::Z3SmtOption,
};
/// CVC5: `cvc5 --lang=smt2` reads SMT-LIB2 from stdin. Modern CVC5
/// supports the bit-vector overflow predicates (`bvuaddo`, …) that
/// Pitbull emits, so it is a full peer to Z3 for QF_BV.
pub const CVC5: Solver = Solver {
    name: "cvc5",
    program: "cvc5",
    base_args: &["--lang=smt2"],
    timeout: TimeoutConvention::Cvc5TlimitMillis,
};
/// Alt-Ergo: `alt-ergo -i smtlib2 -o smtlib2` reads SMT-LIB2 from
/// stdin. WARNING: Alt-Ergo ≤ 2.4.0 lacks bit-vector support and
/// will return an error (non-vote) on Pitbull's QF_BV problems.
/// Recognized for config completeness; not in the default pool.
pub const ALT_ERGO: Solver = Solver {
    name: "alt-ergo",
    program: "alt-ergo",
    base_args: &["-i", "smtlib2", "-o", "smtlib2"],
    timeout: TimeoutConvention::AltErgoTimelimitSecs,
};
/// Resolve a config solver name to its descriptor. Unknown names
/// return `None` so the caller can surface a clear error rather
/// than silently dropping a solver from the agreement pool.
#[must_use]
pub fn known_solver(name: &str) -> Option<Solver> {
    match name {
        "z3" => Some(Z3),
        "cvc5" => Some(CVC5),
        "alt-ergo" => Some(ALT_ERGO),
        _ => None,
    }
}
/// The verdict of a multi-solver agreement vote over one obligation.
///
/// Soundness rationale (Safety Manual §3.3): the whole point of the
/// gate is to defend against a single buggy/hostile solver that
/// wrongly reports `unsat` (claims an unsafe operation safe). So:
/// `Discharged` requires `threshold` independent `unsat` votes AND
/// zero `sat` votes; any `sat` is a counterexample that blocks
/// discharge; a `sat`+`unsat` split is a `Disagreement` (a red
/// flag — a solver bug or a missed counterexample — that must fail
/// closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgreementVerdict {
    /// `threshold`+ solvers returned `unsat` and none returned
    /// `sat`. The obligation is proven safe.
    Discharged {
        /// How many solvers confirmed `unsat`.
        unsat_votes: usize,
    },
    /// At least one solver returned `sat` (a counterexample) and
    /// none returned `unsat`. The obligation is genuinely refuted.
    Refuted,
    /// Solvers DISAGREED: at least one `sat` and at least one
    /// `unsat`. Never discharge — one of them is wrong, and we
    /// cannot tell which. Fail closed and shout.
    Disagreement {
        /// Solvers that said `unsat`.
        unsat: Vec<String>,
        /// Solvers that said `sat`.
        sat: Vec<String>,
    },
    /// Not enough `unsat` votes to reach `threshold` (and no `sat`).
    /// E.g. only one solver could decide, or solvers returned
    /// unknown/timeout/error/not-installed. Undischarged —
    /// insufficient independent confirmation.
    Inconclusive {
        /// How many `unsat` votes were obtained.
        unsat_votes: usize,
        /// The threshold that was required.
        threshold: usize,
    },
}
/// Apply the agreement policy to a set of per-solver results.
///
/// PURE function (no I/O) so the soundness-critical voting logic is
/// exhaustively unit-testable without any solver installed.
///
/// `threshold` is the minimum number of independent `unsat` votes
/// required to discharge. It is a FIXED floor — it does NOT adapt
/// down to the number of solvers that happened to answer, because
/// adapting would reintroduce the single-solver-trust hole the gate
/// exists to close.
#[must_use]
pub fn vote(results: &[(String, SolverResult)], threshold: usize) -> AgreementVerdict {
    // Count DISTINCT solver names per verdict, NOT raw result entries.
    // Soundness (audit 2026-05-29, Critical): if the pool ever contains
    // the same solver twice (e.g. `solvers = ["z3", "z3"]`), one binary's
    // single `unsat` must NOT count as two independent votes — that would
    // let a duplicate config entry defeat the agreement threshold and
    // collapse the gate back to single-solver trust (the exact hole this
    // gate exists to close). Deduping by name here makes the policy immune
    // to upstream duplication no matter how the pool was assembled.
    let mut unsat: Vec<String> = results
        .iter()
        .filter(|(_, r)| *r == SolverResult::Unsat)
        .map(|(n, _)| n.clone())
        .collect();
    unsat.sort();
    unsat.dedup();
    let mut sat: Vec<String> = results
        .iter()
        .filter(|(_, r)| *r == SolverResult::Sat)
        .map(|(n, _)| n.clone())
        .collect();
    sat.sort();
    sat.dedup();
    if !sat.is_empty() && !unsat.is_empty() {
        return AgreementVerdict::Disagreement { unsat, sat };
    }
    if !sat.is_empty() {
        return AgreementVerdict::Refuted;
    }
    if unsat.len() >= threshold {
        AgreementVerdict::Discharged { unsat_votes: unsat.len() }
    } else {
        AgreementVerdict::Inconclusive { unsat_votes: unsat.len(), threshold }
    }
}
/// Run every solver in `solvers` on the same SMT problem, in
/// parallel, and collect `(name, result)` pairs. Each solver runs
/// in its own thread (they are independent processes); the wall
/// clock is the slowest solver, not the sum. Task S.
#[must_use]
pub fn run_solvers(
    solvers: &[Solver],
    smt: &str,
    timeout: Duration,
) -> Vec<(String, SolverResult)> {
    let handles: Vec<_> = solvers
        .iter()
        .map(|solver| {
            // Each solver runs in its own spawned (`'static`) thread,
            // so it needs an OWNED copy rather than a borrow of
            // `solvers`. Clone inside the closure (not via a
            // `.cloned()` adapter) to satisfy clippy::redundant_iter_cloned.
            let solver = solver.clone();
            let smt = smt.to_string();
            std::thread::spawn(move || {
                let r = invoke_solver_with_timeout(&solver, &smt, timeout);
                (solver.name.to_string(), r)
            })
        })
        .collect();
    handles
        .into_iter()
        .map(|h| {
            h.join().unwrap_or_else(|_| {
                // A coordinator thread panicking is itself a fault;
                // surface it as an Error result (non-vote) rather
                // than crashing the whole dispatch.
                (
                    "<panicked>".to_string(),
                    SolverResult::Error("solver coordinator thread panicked".into()),
                )
            })
        })
        .collect()
}
/// Invoke Z3 with an SMT-LIB problem string on stdin. Returns the
/// solver's verdict. Back-compat wrapper over `invoke_solver`.
///
/// If Z3 isn't on PATH, returns `SolverResult::NotInstalled` —
/// caller decides whether that's fatal.
#[must_use]
pub fn invoke_z3(smt: &str) -> SolverResult {
    invoke_z3_with_timeout(smt, DEFAULT_TIMEOUT)
}
/// `invoke_z3` with a custom timeout. Mostly for tests that need
/// a shorter cap.
///
/// Timeout semantics (post-audit N3):
/// - The SMT-LIB `:timeout` option caps the time spent inside
///   `(check-sat)`. Z3 returns `unknown` when this fires.
/// - The OS-level kill cushion (`process_kill_deadline`) catches
///   the case where Z3 hangs BEFORE reaching `(check-sat)` — e.g.
///   pathologically large SMT problems whose PARSING alone is
///   unbounded. When this fires the wrapper kills the child and
///   returns `SolverResult::Timeout`.
/// - stdout / stderr are captured with hard byte caps. A solver
///   that emits unbounded output (e.g. `(get-model)` on a
///   thousand-free-variable problem) cannot OOM the wrapper.
///   When the cap fires, we return `SolverResult::Error` with a
///   description rather than risk picking a verdict from
///   truncated output.
#[must_use]
pub fn invoke_z3_with_timeout(smt: &str, timeout: Duration) -> SolverResult {
    invoke_solver_with_timeout(&Z3, smt, timeout)
}
/// Invoke an arbitrary `Solver` with an SMT-LIB problem on stdin,
/// applying the same N3 hardening as the original Z3 path: a
/// dedicated stdin writer thread, capped stdout/stderr reader
/// threads, an OS-level kill deadline, and strict single-verdict
/// parsing. The only per-solver differences are the program/args
/// and how the timeout is expressed. Task S (2026-05-28).
#[must_use]
pub fn invoke_solver_with_timeout(
    solver: &Solver,
    smt: &str,
    timeout: Duration,
) -> SolverResult {
    let name = solver.name;
    let timeout_ms = timeout.as_millis().min(u64::MAX as u128) as u64;
    // Build the SMT text. Z3 takes its timeout as an SMT option
    // prepended to the problem; other solvers take it as a CLI arg
    // (added below), so their text is the problem verbatim.
    let mut full = String::with_capacity(smt.len() + 64);
    if solver.timeout == TimeoutConvention::Z3SmtOption {
        // Prepend so a caller-supplied `:timeout` wins
        // (last-write-wins in Z3).
        full.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
    }
    full.push_str(smt);
    // Audit finding H-RT3 (2026-05-26): refuse oversized SMT input.
    // A malicious pitbull.toml precondition can ship a multi-GB
    // assertion that F2 validates but would OOM the wrapper as the
    // writer thread holds it in memory. Cap at 64 MiB — legitimate
    // Pitbull problems are <4 KiB.
    if full.len() > SMT_INPUT_CAP_BYTES {
        return SolverResult::Error(format!(
            "smt input exceeded {} MiB cap (got {} bytes); refusing \
             to invoke {name}. Pitbull's own emitted problems are \
             under 4 KiB; an input this large indicates a pathological \
             precondition (see pitbull.toml `[verification.preconditions]`).",
            SMT_INPUT_CAP_BYTES / (1024 * 1024),
            full.len(),
        ));
    }
    // Assemble CLI args: the solver's base args plus any
    // timeout-expressing arg.
    let mut args: Vec<String> = solver.base_args.iter().map(|s| (*s).to_string()).collect();
    match solver.timeout {
        TimeoutConvention::Z3SmtOption => {}
        TimeoutConvention::Cvc5TlimitMillis => {
            args.push(format!("--tlimit-per={timeout_ms}"));
        }
        TimeoutConvention::AltErgoTimelimitSecs => {
            // Whole seconds, rounded up, minimum 1.
            let secs = timeout.as_secs().max(1);
            args.push(format!("--timelimit={secs}"));
        }
    }
    let mut child = match Command::new(solver.program)
        .args(&args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return SolverResult::NotInstalled;
        }
        Err(e) => return SolverResult::Error(format!("spawn {name}: {e}")),
    };
    // Move stdin into a dedicated writer thread.
    //
    // N3 red-team finding H1: in the previous design, `write_all`
    // ran on the main thread BEFORE the deadline regime started.
    // If Z3 hung during parsing (reading stdin slowly or not at
    // all), `write_all` blocked on a full pipe buffer indefinitely
    // — defeating the entire point of an OS-level timeout for
    // pathological large inputs. Spawning the writer means the
    // poll loop covers it: when the deadline fires and we kill
    // the child, the writer's pipe-write returns an error and
    // the writer thread exits.
    //
    // We take stdout/stderr handles BEFORE spawning the writer
    // (so the readers can capture from the start), then move stdin
    // into the writer. All three handles live on dedicated threads;
    // the main thread only polls and joins.
    let stdout = child.stdout.take();
    let stderr = child.stderr.take();
    let stdin = child.stdin.take();
    let stdout_handle = stdout.map(|s| {
        std::thread::spawn(move || read_capped(s, STDOUT_CAP_BYTES))
    });
    let stderr_handle = stderr.map(|s| {
        std::thread::spawn(move || read_capped(s, STDERR_CAP_BYTES))
    });
    let writer_handle = stdin.map(|mut s| {
        std::thread::spawn(move || {
            // `write_all` may fail with BrokenPipe if Z3 exits
            // before we finish writing (e.g. it parsed a malformed
            // problem and exited early). That's not a wrapper bug
            // — just convert the io::Error to a string for the
            // join-side. Successful write returns Ok(()).
            s.write_all(full.as_bytes())
            // stdin is dropped here, sending EOF to the child.
        })
    });
    // OS-level kill deadline. Polls `try_wait` until the child
    // exits or the deadline passes; on deadline, kill the child
    // and return Timeout. The poll interval (50ms) is short
    // enough to bound the worst-case overshoot but long enough
    // to keep CPU burn negligible.
    let deadline = Instant::now() + process_kill_deadline(timeout);
    let (exit_status, hit_deadline) = loop {
        match child.try_wait() {
            Ok(Some(status)) => break (Some(status), false),
            Ok(None) => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let status = child.wait().ok();
                    break (status, true);
                }
                std::thread::sleep(POLL_INTERVAL);
            }
            Err(e) => {
                // N3 red-team finding H2: cleanup before early
                // return. Kill the child (defensively — try_wait
                // failed but the child may still be running),
                // then drain the reader/writer threads so we
                // don't leak descriptors or detached threads.
                let _ = child.kill();
                let _ = child.wait();
                let _ = stdout_handle.map(std::thread::JoinHandle::join);
                let _ = stderr_handle.map(std::thread::JoinHandle::join);
                let _ = writer_handle.map(std::thread::JoinHandle::join);
                return SolverResult::Error(format!("try_wait {name}: {e}"));
            }
        }
    };
    // N3 red-team finding M1: a panicked reader thread used to
    // be coerced to `Ok((Vec::new(), false))` — the downstream
    // verdict parser then saw no verdict line and emitted
    // "no verdict from z3" with no clue that the OUR thread
    // crashed. For a soundness-critical verifier, opacity is
    // bad audit posture. Now we propagate the panic as a
    // distinguishable Error message.
    let stdout_result = match stdout_handle {
        Some(h) => h.join().unwrap_or_else(|_| {
            Err(std::io::Error::other("stdout reader thread panicked"))
        }),
        None => Ok((Vec::new(), false)),
    };
    let stderr_result = match stderr_handle {
        Some(h) => h.join().unwrap_or_else(|_| {
            Err(std::io::Error::other("stderr reader thread panicked"))
        }),
        None => Ok((Vec::new(), false)),
    };
    // The writer thread's result is consulted only on the
    // non-deadline path. On deadline, the writer almost
    // certainly hit BrokenPipe when we killed the child — that's
    // expected, not a failure. We still join to reap the thread.
    //
    // Audit finding M-RT3 (2026-05-26): mirror M1's reader-thread
    // panic handling. A writer-thread panic (e.g. OOM mid-write)
    // is now distinguishable from a clean exit; previously, both
    // collapsed to `None`.
    let writer_result = writer_handle.map(|h| {
        h.join().unwrap_or_else(|_| {
            Err(std::io::Error::other("stdin writer thread panicked"))
        })
    });
    let (stdout_bytes, stdout_capped) = match stdout_result {
        Ok(v) => v,
        Err(e) => return SolverResult::Error(format!("read {name} stdout: {e}")),
    };
    let (stderr_bytes, _stderr_capped) = match stderr_result {
        Ok(v) => v,
        Err(e) => return SolverResult::Error(format!("read {name} stderr: {e}")),
    };
    // N3 red-team finding H3 (carried through to the threaded
    // design): if the writer failed for a reason OTHER than
    // BrokenPipe (the expected outcome when Z3 closes its stdin
    // early or when we kill it), surface as Error. BrokenPipe
    // is normal — Z3 may finish parsing before we finish writing.
    if !hit_deadline {
        if let Some(Err(e)) = &writer_result {
            if e.kind() != std::io::ErrorKind::BrokenPipe {
                return SolverResult::Error(format!("write {name} stdin: {e}"));
            }
        }
    }
    if hit_deadline {
        return SolverResult::Timeout;
    }
    if stdout_capped {
        return SolverResult::Error(format!(
            "{name} stdout exceeded {} MiB cap; refusing to interpret \
             possibly-truncated verdict. This usually indicates a \
             pathological SMT problem (e.g. unbounded model output).",
            STDOUT_CAP_BYTES / (1024 * 1024),
        ));
    }
    let stdout = String::from_utf8_lossy(&stdout_bytes);
    // Audit hardening (red-team finding F9): a well-formed problem
    // produces EXACTLY ONE verdict line. Multiple verdicts mean
    // either (a) an injected `(check-sat)` directive snuck through
    // (predicate.rs::validate_assertion_form should block this) or
    // (b) the problem text has multiple check-sat directives by
    // design (which we don't emit). In either case, we refuse to
    // pick a verdict — surface the issue as an Error so the wrapper
    // reports the obligation as undischarged.
    let verdict_lines: Vec<&str> = stdout
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown" | "timeout"))
        .collect();
    match verdict_lines.as_slice() {
        ["sat"] => SolverResult::Sat,
        ["unsat"] => SolverResult::Unsat,
        ["unknown"] => SolverResult::Unknown,
        ["timeout"] => SolverResult::Timeout,
        [] => {
            // No verdict line at all. Inspect the rest of the
            // output to characterize the failure for the auditor.
            let stderr_str = String::from_utf8_lossy(&stderr_bytes);
            let status_success = exit_status.is_some_and(|s| s.success());
            let status_code = exit_status.and_then(|s| s.code());
            if stdout.contains("error") || stderr_str.contains("error") {
                SolverResult::Error(format!(
                    "{name} emitted no verdict; output contained errors. \
                     stdout: {stdout:?}, stderr: {stderr_str:?}",
                ))
            } else if status_success {
                SolverResult::Error(format!(
                    "no verdict from {name} (stdout: {stdout:?}, stderr: {stderr_str:?})",
                ))
            } else {
                SolverResult::Error(format!(
                    "{name} exited {status_code:?} with no verdict in output: {stdout}",
                ))
            }
        }
        many => {
            // Multiple verdicts — refuse to interpret. This is the
            // F9 defense: an attacker who plants a pre-emit
            // `(check-sat)` directive intends to confuse our parser
            // into picking the WRONG verdict.
            SolverResult::Error(format!(
                "{name} emitted {} verdict lines (expected exactly 1); \
                 refusing to interpret. Verdicts: {many:?}",
                many.len(),
            ))
        }
    }
}
/// Read from `reader` into a Vec, capping at `cap_bytes`. Returns
/// `Ok((bytes, was_capped))` where `was_capped == true` if the
/// reader produced AT LEAST `cap_bytes` of output (the function
/// stops reading at that point).
///
/// Implementation note: we read in 8 KiB chunks rather than using
/// `Read::take` + `read_to_end` so we can distinguish "exactly
/// cap_bytes" (reader had more) from "less than cap_bytes" (reader
/// reached EOF on its own). The `Take` adapter doesn't expose that
/// distinction directly.
///
/// Audit-cleanup (audit finding N3, 2026-05-26): used by
/// `invoke_z3_with_timeout` to defend against pathological SMT
/// problems that drive Z3 to unbounded output.
fn read_capped<R: Read>(mut reader: R, cap_bytes: u64) -> std::io::Result<(Vec<u8>, bool)> {
    // Cap the underlying reader at cap_bytes + 1: the extra byte
    // lets us detect "reader had more than cap" by checking
    // bytes.len() > cap_bytes after the read.
    let read_limit = cap_bytes.saturating_add(1);
    let mut limited = reader.by_ref().take(read_limit);
    let mut buf = Vec::with_capacity(8 * 1024);
    let mut chunk = [0u8; 8 * 1024];
    loop {
        match limited.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => buf.extend_from_slice(&chunk[..n]),
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
    let was_capped = buf.len() as u64 > cap_bytes;
    if was_capped {
        // Trim the tell-tale extra byte so the returned buffer
        // matches the documented cap. The caller uses
        // `was_capped` to decide whether to interpret the output.
        buf.truncate(cap_bytes as usize);
    }
    Ok((buf, was_capped))
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt;
    use pitbull_subset::ArithOp;
    /// `NotInstalled` is observably distinct from `Error(...)`.
    /// Calling code uses this to decide whether to retry, fall back,
    /// or surface a "please install Z3" message to the user.
    #[test]
    fn not_installed_is_distinct_from_error() {
        let ni = SolverResult::NotInstalled;
        let er = SolverResult::Error("anything".into());
        assert_ne!(ni, er);
    }
    /// Sanity: the four primary verdicts and the operational
    /// outcomes (NotInstalled, Timeout, Error) are all distinct.
    #[test]
    fn solver_result_variants_are_distinct() {
        let variants = [
            SolverResult::Sat,
            SolverResult::Unsat,
            SolverResult::Unknown,
            SolverResult::NotInstalled,
            SolverResult::Timeout,
            SolverResult::Error("x".into()),
        ];
        for (i, a) in variants.iter().enumerate() {
            for (j, b) in variants.iter().enumerate() {
                if i == j {
                    assert_eq!(a, b);
                } else {
                    assert_ne!(a, b);
                }
            }
        }
    }
    /// End-to-end: emit an overflow problem and dispatch to Z3.
    /// Skips gracefully if Z3 isn't installed. Pinning the expected
    /// verdicts here is the v0.2 scaffold's "the pipeline works" test.
    ///
    /// For `u32 + u32` with no constraints, overflow IS possible
    /// (witness: `0xFFFFFFFF + 1`). Z3 should return `sat`.
    ///
    /// For `u32 * 0` with the multiplicand pinned to 0 (we hand-
    /// edit the problem here), overflow is impossible. Z3 should
    /// return `unsat`.
    #[test]
    fn end_to_end_overflow_check_via_z3() {
        let problem = smt::emit_overflow_problem("u32", ArithOp::Add)
            .expect("u32 + supported");
        match invoke_z3_with_timeout(&problem, Duration::from_secs(5)) {
            SolverResult::Sat => {
                // Expected verdict — overflow is possible for
                // unconstrained u32 + u32.
            }
            SolverResult::NotInstalled => {
                eprintln!(
                    "end_to_end_overflow_check_via_z3: SKIPPED — z3 not installed.",
                );
            }
            other => panic!(
                "expected Sat (overflow witness exists) or NotInstalled; got {other:?}",
            ),
        }
    }
    /// Audit hardening (red-team F9): a problem with TWO check-sat
    /// directives (which can happen if a multi-directive injection
    /// somehow slipped through pitbull-subset's validator) must be
    /// REFUSED as Error, not silently interpreted as the first or
    /// last verdict.
    ///
    /// pitbull-subset's `validate_assertion_form` should normally
    /// block this upstream; this test pins the defense-in-depth
    /// behavior at the solver layer.
    #[test]
    fn multiple_verdict_lines_refused() {
        let problem = "(set-logic QF_BV)\n\
                       (declare-const x (_ BitVec 32))\n\
                       (assert (= x #x00000001))\n\
                       (check-sat)\n\
                       (assert (= x #x00000002))\n\
                       (check-sat)\n";
        match invoke_z3_with_timeout(problem, Duration::from_secs(5)) {
            SolverResult::Error(msg) => {
                assert!(
                    msg.contains("verdict lines") || msg.contains("expected exactly 1"),
                    "Error should explain the verdict-count problem; got {msg}",
                );
            }
            SolverResult::NotInstalled => {
                eprintln!("multiple_verdict_lines_refused: SKIPPED — z3 not installed.");
            }
            other => panic!(
                "expected Error (refuse multi-verdict) or NotInstalled; got {other:?}",
            ),
        }
    }
    // ----- audit finding N3: timeout + output cap tests -----------------
    /// `read_capped` returns the full reader contents when they fit
    /// under the cap. `was_capped` is false in that case.
    #[test]
    fn read_capped_under_cap_returns_full_bytes() {
        let data = b"hello world".to_vec();
        let (out, capped) = read_capped(data.as_slice(), 1024).expect("read");
        assert_eq!(out, data);
        assert!(!capped);
    }
    /// `read_capped` stops at the cap and reports it. The returned
    /// buffer is exactly `cap_bytes` long; the source-reader bytes
    /// beyond that are NOT returned.
    #[test]
    fn read_capped_at_cap_truncates_and_reports() {
        // 100 KiB source, 10 KiB cap.
        let data = vec![b'A'; 100 * 1024];
        let cap = 10 * 1024;
        let (out, capped) = read_capped(data.as_slice(), cap).expect("read");
        assert!(capped, "should report capped when source exceeds cap");
        assert_eq!(out.len() as u64, cap, "buffer should be exactly cap bytes");
        assert!(out.iter().all(|&b| b == b'A'));
    }
    /// `read_capped` on an empty reader returns an empty buffer and
    /// reports not-capped.
    #[test]
    fn read_capped_empty_reader() {
        let data: &[u8] = b"";
        let (out, capped) = read_capped(data, 1024).expect("read");
        assert!(out.is_empty());
        assert!(!capped);
    }
    /// `read_capped` with EXACTLY `cap_bytes` available reports
    /// not-capped (the boundary is `> cap_bytes`, not `>=`).
    #[test]
    fn read_capped_exactly_at_cap_not_reported_as_capped() {
        let data = vec![b'X'; 100];
        let (out, capped) = read_capped(data.as_slice(), 100).expect("read");
        assert_eq!(out.len(), 100);
        assert!(
            !capped,
            "exactly-cap reader should NOT report capped — only OVER-cap does",
        );
    }
    /// Process-kill deadline grows with the SMT-LIB timeout: a 1s
    /// SMT timeout gives the process 2 + 2.5 = 4.5s before OS-level
    /// kill; a 10s SMT timeout gives 27s. The scaling factor is part
    /// of the audit-cleanup N3 contract.
    #[test]
    fn process_kill_deadline_scales_with_timeout() {
        let d = process_kill_deadline(Duration::from_secs(1));
        assert!(d >= Duration::from_secs(4), "1s timeout → ≥4s deadline; got {d:?}");
        assert!(d <= Duration::from_secs(5), "1s timeout → ≤5s deadline; got {d:?}");
        let d = process_kill_deadline(Duration::from_secs(10));
        assert!(d >= Duration::from_secs(27), "10s timeout → ≥27s deadline; got {d:?}");
        assert!(d <= Duration::from_secs(28), "10s timeout → ≤28s deadline; got {d:?}");
    }
    /// Unsat path: constrain the inputs so overflow is impossible
    /// and confirm Z3 returns unsat.
    #[test]
    fn pinned_inputs_proves_no_overflow() {
        let problem = "(set-logic QF_BV)\n\
                       (declare-const lhs (_ BitVec 32))\n\
                       (declare-const rhs (_ BitVec 32))\n\
                       (assert (= lhs #x00000001))\n\
                       (assert (= rhs #x00000001))\n\
                       (assert (bvuaddo lhs rhs))\n\
                       (check-sat)\n";
        match invoke_z3_with_timeout(problem, Duration::from_secs(5)) {
            SolverResult::Unsat => {
                // 1 + 1 cannot overflow u32 — expected.
            }
            SolverResult::NotInstalled => {
                eprintln!(
                    "pinned_inputs_proves_no_overflow: SKIPPED — z3 not installed.",
                );
            }
            other => panic!("expected Unsat or NotInstalled; got {other:?}"),
        }
    }
    // ===== Task S: multi-solver agreement voting (pure logic) =========
    // These exercise the soundness-critical voting policy WITHOUT any
    // solver installed — `vote` is a pure function over results.
    fn r(name: &str, res: SolverResult) -> (String, SolverResult) {
        (name.to_string(), res)
    }
    /// Two independent `unsat` votes meet threshold 2 → Discharged.
    #[test]
    fn vote_two_unsat_meets_threshold_2() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        assert_eq!(
            vote(&results, 2),
            AgreementVerdict::Discharged { unsat_votes: 2 },
        );
    }
    /// ONE `unsat` vote does NOT meet threshold 2 → Inconclusive.
    /// This is the core defense: a single solver (even an honest one)
    /// cannot discharge under a 2-of-N policy.
    #[test]
    fn vote_single_unsat_below_threshold_is_inconclusive() {
        let results = [
            r("z3", SolverResult::Unsat),
            r("cvc5", SolverResult::Error("no bv".into())),
        ];
        assert_eq!(
            vote(&results, 2),
            AgreementVerdict::Inconclusive { unsat_votes: 1, threshold: 2 },
        );
    }
    /// A hostile/buggy solver saying `unsat` while another finds a
    /// `sat` counterexample is a DISAGREEMENT — never discharge.
    /// This is exactly the scenario the gate exists to catch.
    #[test]
    fn vote_unsat_plus_sat_is_disagreement() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Sat)];
        match vote(&results, 2) {
            AgreementVerdict::Disagreement { unsat, sat } => {
                assert_eq!(unsat, vec!["z3"]);
                assert_eq!(sat, vec!["cvc5"]);
            }
            other => panic!("expected Disagreement, got {other:?}"),
        }
    }
    /// All-`sat` (no unsat) is a genuine refutation, not a
    /// disagreement.
    #[test]
    fn vote_all_sat_is_refuted() {
        let results = [r("z3", SolverResult::Sat), r("cvc5", SolverResult::Sat)];
        assert_eq!(vote(&results, 2), AgreementVerdict::Refuted);
    }
    /// One `sat` + one no-opinion (unknown) is still Refuted — a
    /// counterexample from any solver blocks discharge, and there's
    /// no competing `unsat` to make it a disagreement.
    #[test]
    fn vote_sat_plus_unknown_is_refuted() {
        let results = [r("z3", SolverResult::Sat), r("cvc5", SolverResult::Unknown)];
        assert_eq!(vote(&results, 2), AgreementVerdict::Refuted);
    }
    /// Threshold 1 (single-solver back-compat mode): one `unsat`
    /// discharges.
    #[test]
    fn vote_threshold_one_single_unsat_discharges() {
        let results = [r("z3", SolverResult::Unsat)];
        assert_eq!(
            vote(&results, 1),
            AgreementVerdict::Discharged { unsat_votes: 1 },
        );
    }
    /// All non-deciding (unknown/timeout/error/not-installed) →
    /// Inconclusive with zero unsat votes.
    #[test]
    fn vote_no_decisions_is_inconclusive_zero() {
        let results = [
            r("z3", SolverResult::Unknown),
            r("cvc5", SolverResult::NotInstalled),
            r("alt-ergo", SolverResult::Error("no bv".into())),
        ];
        assert_eq!(
            vote(&results, 2),
            AgreementVerdict::Inconclusive { unsat_votes: 0, threshold: 2 },
        );
    }
    /// `known_solver` resolves the three built-ins and rejects
    /// unknown names (so the wrapper surfaces a clear config error
    /// rather than silently dropping a solver).
    #[test]
    fn known_solver_resolves_builtins() {
        assert_eq!(known_solver("z3").unwrap().name, "z3");
        assert_eq!(known_solver("cvc5").unwrap().name, "cvc5");
        assert_eq!(known_solver("alt-ergo").unwrap().name, "alt-ergo");
        assert!(known_solver("bogus-solver").is_none());
        assert!(known_solver("Z3").is_none(), "name match is case-sensitive");
    }
    /// SOUNDNESS REGRESSION GUARD (audit 2026-05-29, Critical):
    /// the SAME solver appearing twice (`solvers = ["z3", "z3"]`)
    /// must count as ONE distinct vote, never two. Otherwise a
    /// duplicate config entry would let a single binary's `unsat`
    /// reach a threshold-2 gate and rubber-stamp unsafe code —
    /// exactly the single-solver-trust hole the gate closes.
    #[test]
    fn vote_duplicate_solver_name_counts_once() {
        let results = [r("z3", SolverResult::Unsat), r("z3", SolverResult::Unsat)];
        assert_eq!(
            vote(&results, 2),
            AgreementVerdict::Inconclusive { unsat_votes: 1, threshold: 2 },
            "two entries for the same solver must count as one distinct vote",
        );
        // And under threshold 1 the single distinct vote still discharges.
        assert_eq!(
            vote(&results, 1),
            AgreementVerdict::Discharged { unsat_votes: 1 },
        );
    }
    /// Empty result set (e.g. an empty solver pool) is Inconclusive
    /// with zero votes — fail-closed, never a vacuous discharge.
    /// (A threshold of 0 is impossible at the call site, which
    /// applies `.max(1)`; this pins the empty-input behavior.)
    #[test]
    fn vote_empty_results_is_inconclusive() {
        let results: [(String, SolverResult); 0] = [];
        assert_eq!(
            vote(&results, 2),
            AgreementVerdict::Inconclusive { unsat_votes: 0, threshold: 2 },
        );
        assert_eq!(
            vote(&results, 1),
            AgreementVerdict::Inconclusive { unsat_votes: 0, threshold: 1 },
        );
    }
}
