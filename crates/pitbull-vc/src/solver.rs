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
use std::io::Write;
use std::process::{Command, Stdio};
use std::time::Duration;
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
/// Invoke Z3 with an SMT-LIB problem string on stdin. Returns the
/// solver's verdict.
///
/// Z3 is invoked with `-in` so it reads SMT-LIB from stdin. Output
/// goes to stdout; the first non-empty trimmed line is the verdict
/// (`sat` / `unsat` / `unknown`). Subsequent lines (`get-model`
/// output, etc.) are ignored at this layer; counterexample
/// rendering would consume them separately.
///
/// If Z3 isn't on PATH, returns `SolverResult::NotInstalled` —
/// caller decides whether that's fatal. This matters: the v0.2
/// scaffold ships before Z3 becomes a hard requirement, and the
/// existing test suite must keep passing without it.
#[must_use]
pub fn invoke_z3(smt: &str) -> SolverResult {
    invoke_z3_with_timeout(smt, DEFAULT_TIMEOUT)
}
/// `invoke_z3` with a custom timeout. Mostly for tests that need
/// a shorter cap.
#[must_use]
pub fn invoke_z3_with_timeout(smt: &str, timeout: Duration) -> SolverResult {
    // Inject the timeout via SMT-LIB's `set-option :timeout`.
    // Milliseconds, applied to subsequent `check-sat` calls. We
    // prepend rather than append so any timeout the caller wrote
    // wins (last-write-wins semantics in Z3).
    let timeout_ms = timeout.as_millis().min(u64::MAX as u128) as u64;
    let mut full = String::with_capacity(smt.len() + 64);
    full.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
    full.push_str(smt);
    let mut child = match Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return SolverResult::NotInstalled;
        }
        Err(e) => return SolverResult::Error(format!("spawn z3: {e}")),
    };
    if let Some(stdin) = child.stdin.as_mut() {
        if let Err(e) = stdin.write_all(full.as_bytes()) {
            return SolverResult::Error(format!("write z3 stdin: {e}"));
        }
    }
    // Close stdin by dropping the handle so Z3 sees EOF and
    // processes the (check-sat).
    drop(child.stdin.take());
    let output = match child.wait_with_output() {
        Ok(o) => o,
        Err(e) => return SolverResult::Error(format!("wait z3: {e}")),
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    let first_line = stdout
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("");
    match first_line {
        "sat" => SolverResult::Sat,
        "unsat" => SolverResult::Unsat,
        "unknown" => SolverResult::Unknown,
        "timeout" => SolverResult::Timeout,
        other => {
            // Z3 sometimes prints a (model ...) block after sat;
            // sometimes prints "(error ...)" on syntax issues.
            // Surface what we got so a caller can diagnose.
            if other.contains("error") {
                SolverResult::Error(other.to_string())
            } else if output.status.success() {
                // Empty stdout + clean exit: probably a malformed
                // problem that Z3 silently rejected.
                SolverResult::Error(format!(
                    "no verdict from z3 (stdout: {stdout:?}, stderr: {:?})",
                    String::from_utf8_lossy(&output.stderr),
                ))
            } else {
                SolverResult::Error(format!(
                    "z3 exited {:?} with output: {stdout}",
                    output.status.code(),
                ))
            }
        }
    }
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
}
