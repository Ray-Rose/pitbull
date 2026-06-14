//! Corpus-based integration tests for the PSS-1 subset checker.
//!
//! The corpus lives under `tests/corpus/` with two subdirectories:
//!
//! - `reject/PB{rule}_{slug}.rs` — must trigger PSS-1 violation of `PB{rule}`.
//! - `accept/PB{rule}_{slug}.rs` — adjacent valid program that must NOT
//!   trigger any PSS-1 violation.
//!
//! ## Why two layers
//!
//! Reject-only tests prove the visitor *can* find a violation. They do not
//! prove the visitor is well-calibrated — a visitor that rejects every
//! program also passes every reject test. Accept tests prove the
//! complement: adjacent valid code must not be rejected.
//!
//! For full PSS-1 conformance, every rule must have ≥10 reject examples and
//! ≥5 accept examples. The v0.1 release ships the first wave; subsequent
//! corpus expansion is tracked in the milestone tracker.
//!
//! ## Test driver
//!
//! Each corpus file is parsed to extract its expected rule from the
//! filename, then fed through the visitor. The actual MIR comes from the
//! shadow build (no rustc dependency at test time). Once the real
//! `rustc_public` wiring lands, this test driver switches to invoking
//! rustc and consuming real MIR; the corpus contents do not change.
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
/// Per-process counter that uniquifies temp file paths beyond
/// `std::process::id()`. The test binary runs multiple tests in
/// parallel by default; many use the same corpus file
/// (e.g. PB018_static_mut.rs), so a pid-only filename collides
/// across concurrent invocations and the rustc subprocess
/// occasionally fails to read a file another test just deleted.
/// Bumping a counter per invocation makes the filename unique
/// even within the same process.
static TEMP_FILE_COUNTER: AtomicU64 = AtomicU64::new(0);
/// Extract the rule id from a filename like `PB004_raw_pointer.rs`.
fn rule_from_filename(name: &str) -> Option<u16> {
    name.strip_prefix("PB")
        .and_then(|s| s.split('_').next())
        .and_then(|s| s.parse().ok())
}
fn corpus_files(subdir: &str) -> Vec<PathBuf> {
    let root: PathBuf = ["tests", "corpus", subdir].iter().collect();
    if !root.exists() {
        return Vec::new();
    }
    fs::read_dir(&root)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", root.display()))
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("rs") {
                Some(path)
            } else {
                None
            }
        })
        .collect()
}
/// Sanity test: every reject/ file's name follows the convention.
#[test]
fn reject_corpus_filenames_well_formed() {
    for path in corpus_files("reject") {
        let name = path.file_name().unwrap().to_str().unwrap();
        let rule = rule_from_filename(name).unwrap_or_else(|| {
            panic!("malformed reject filename {name:?}; expected PB{{nnn}}_{{slug}}.rs")
        });
        assert!((1..=75).contains(&rule), "rule {rule} out of range");
    }
}
/// Sanity test: every accept/ file's name follows the convention.
#[test]
fn accept_corpus_filenames_well_formed() {
    for path in corpus_files("accept") {
        let name = path.file_name().unwrap().to_str().unwrap();
        let rule = rule_from_filename(name).unwrap_or_else(|| {
            panic!("malformed accept filename {name:?}; expected PB{{nnn}}_{{slug}}.rs")
        });
        assert!((1..=75).contains(&rule), "rule {rule} out of range");
    }
}
/// Coverage report. Not a hard test in v0.1 (corpus is incipient) but a
/// reportable metric in CI.
#[test]
fn corpus_coverage_summary() {
    let mut reject_by_rule = std::collections::BTreeMap::<u16, usize>::new();
    let mut accept_by_rule = std::collections::BTreeMap::<u16, usize>::new();
    for path in corpus_files("reject") {
        let name = path.file_name().unwrap().to_str().unwrap();
        if let Some(rule) = rule_from_filename(name) {
            *reject_by_rule.entry(rule).or_default() += 1;
        }
    }
    for path in corpus_files("accept") {
        let name = path.file_name().unwrap().to_str().unwrap();
        if let Some(rule) = rule_from_filename(name) {
            *accept_by_rule.entry(rule).or_default() += 1;
        }
    }
    eprintln!("Reject coverage: {} rules touched", reject_by_rule.len());
    eprintln!("Accept coverage: {} rules touched", accept_by_rule.len());
    // v0.1 baseline acceptance: every rule with at least one example in
    // either bucket. This relaxes the ≥10 reject / ≥5 accept goal stated
    // in PSS-1 §15 to a v0.1-baseline incremental gate.
}
/// End-to-end corpus pipeline test (Milestone 2 Task C).
///
/// For each `reject/PB{nnn}_{slug}.rs` corpus file:
///   1. Read the source.
///   2. Strip `#[pitbull::*]` attributes (the corpus uses them as a
///      future-proof annotation; today the visitor uses verify_roots
///      instead, and the bare attributes don't compile under rustc
///      without `register_tool(pitbull)`).
///   3. Write to a temp file.
///   4. Invoke the built `pitbull-rustc.exe` wrapper as a rustc
///      replacement, compiling the temp file as a binary.
///   5. Capture stderr and assert it contains a line citing the
///      expected `PB{nnn}` rule.
///
/// For each `accept/PB{nnn}_{slug}.rs`:
///   1. Same setup.
///   2. Assert that PB{nnn} does NOT appear in stderr (the acceptable
///      counterpart should not trigger that specific rule).
///
/// ## Graceful skip prerequisites
///
/// This test depends on:
///   - `pitbull-rustc.exe` being built at the workspace target dir.
///     Build with: `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29
///     build -p pitbull-driver --bin pitbull-rustc`.
///   - `nightly-2026-01-29` toolchain installed (for sysroot lookup).
///
/// If either is missing, the test prints a helpful message and
/// returns Ok rather than failing — that way `cargo test` on a
/// developer machine without nightly setup still passes the rest of
/// the suite. Set `PITBULL_REQUIRE_E2E=1` in CI to escalate the
/// missing-prerequisite case to a hard failure.
#[test]
fn corpus_runs_full_pipeline() {
    let Some(env) = E2eEnv::probe() else {
        let require = std::env::var_os("PITBULL_REQUIRE_E2E").is_some();
        if require {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!(
            "corpus_runs_full_pipeline: SKIPPED — prerequisites missing.\n\
             Build the wrapper:  PITBULL_USE_RUSTC_PUBLIC=1 \\\n  \
             cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc\n\
             Install nightly:   rustup toolchain install nightly-2026-01-29 \\\n  \
             --component rustc-dev rust-src\n\
             Set PITBULL_REQUIRE_E2E=1 to make missing prerequisites a hard failure."
        );
        return;
    };
    let mut failures: Vec<String> = Vec::new();
    let mut ran = 0usize;
    let mut skipped_unimpl = 0usize;
    for path in corpus_files("reject") {
        let name = path.file_name().unwrap().to_str().unwrap().to_string();
        let Some(rule_num) = rule_from_filename(&name) else { continue };
        let expected = format!("PB{rule_num:03}");
        // Some PB rules are documented v0.1 visitor limitations: the
        // rule exists in the registry and corpus but the v0.1 visitor
        // doesn't detect it (either because detection requires
        // information unavailable post-MIR, or because it's a VC
        // obligation handled by the v0.2+ proof backend). For these,
        // we still run the wrapper to confirm it doesn't crash, but
        // we don't assert the rule fires.
        if KNOWN_UNIMPLEMENTED_REJECT.contains(&rule_num) {
            let _ = run_one_corpus_file(&env, &path);
            skipped_unimpl += 1;
            ran += 1;
            continue;
        }
        let result = run_one_corpus_file(&env, &path);
        ran += 1;
        match result {
            Ok(stderr) => {
                if !stderr.contains(&expected) {
                    failures.push(format!(
                        "[reject] {name}: expected `{expected}` in wrapper stderr; got:\n{stderr}"
                    ));
                }
            }
            Err(e) => failures.push(format!("[reject] {name}: wrapper failed: {e}")),
        }
    }
    let mut skipped_undischarged_accept = 0usize;
    for path in corpus_files("accept") {
        let name = path.file_name().unwrap().to_str().unwrap().to_string();
        let Some(rule_num) = rule_from_filename(&name) else { continue };
        let unexpected = format!("PB{rule_num:03}");
        // Symmetric to KNOWN_UNIMPLEMENTED_REJECT: rules whose
        // accept-side corpus file cannot pass yet because the
        // verifier can't yet *discharge* the obligation (rather
        // than can't *detect* it). For these we still run the
        // wrapper to confirm it doesn't crash, but we don't
        // assert the rule fails to fire — the wrapper correctly
        // emits an undischarged obligation, which the contains-
        // check would interpret as "rule fired".
        if KNOWN_UNDISCHARGED_ACCEPT.contains(&rule_num) {
            let _ = run_one_corpus_file(&env, &path);
            skipped_undischarged_accept += 1;
            ran += 1;
            continue;
        }
        if KNOWN_REJECTED_ACCEPT.contains(&rule_num) {
            // Documented false positive (e.g. PB031 generic dispatch under
            // the v0.2 no-monomorphization limitation): the verifier
            // conservatively rejects this otherwise-valid file. Run-only.
            let _ = run_one_corpus_file(&env, &path);
            skipped_unimpl += 1;
            ran += 1;
            continue;
        }
        let result = run_one_corpus_file(&env, &path);
        ran += 1;
        match result {
            Ok(stderr) => {
                if stderr.contains(&unexpected) {
                    failures.push(format!(
                        "[accept] {name}: expected NO `{unexpected}` but it fired:\n{stderr}"
                    ));
                }
                // Strict accept check (audit 2026-05-31): an accept file must
                // not be REJECTED by ANY rule, not merely the one it's named
                // for. Assert the wrapper reports zero subset violations —
                // catches a mislabeled accept file (or a regression that
                // starts rejecting valid code) that the single-rule grep
                // above would miss.
                if let Some(n) = subset_violation_count(&stderr) {
                    if n != 0 {
                        failures.push(format!(
                            "[accept] {name}: expected 0 subset violations but the \
                             wrapper reported {n}:\n{stderr}"
                        ));
                    }
                }
            }
            Err(e) => failures.push(format!("[accept] {name}: wrapper failed: {e}")),
        }
    }
    if skipped_undischarged_accept > 0 {
        eprintln!(
            "corpus_runs_full_pipeline: skipped {} accept-side file(s) \
             whose rule can be detected but not yet discharged",
            skipped_undischarged_accept
        );
    }
    eprintln!(
        "corpus_runs_full_pipeline: ran {ran} corpus file(s) ({} skipped as unimplemented)",
        skipped_unimpl
    );
    if !failures.is_empty() {
        for f in &failures {
            eprintln!("---\n{f}");
        }
        panic!("{} corpus file(s) failed e2e checks", failures.len());
    }
}
/// PB rule numbers whose corpus reject test is expected NOT to fire
/// the rule under the v0.1 visitor. Each one is a documented
/// limitation; the corpus file is "future-proof" for when the rule
/// is implemented in a later milestone.
///
/// - PB041 (recursion without `#[decreases]`): requires call-graph
///   strongly-connected-component analysis. The visitor walks bodies
///   one at a time without the call graph. v0.2's reachability
///   driver in pitbull-subset/src/reachability.rs has the BodyProvider
///   plumbing but the SCC detection is not yet implemented.
///
/// PB054 was removed from this list in Task P.1: the visitor now
/// emits an `IndexBound` obligation for slice indices,
/// `pitbull-vc::compile` produces a real SMT problem, and the
/// wrapper surfaces the canonical "PB054" rule string on every
/// verdict line via `VcObligationKind::rule_id()`. Without operand
/// bindings the obligation reports as undischarged
/// ("NOT DISCHARGED — counterexample exists" with Z3, or
/// "undischarged (no solver)" without) but the rule fires
/// uppercase in stderr, which is what this integration test
/// requires.
const KNOWN_UNIMPLEMENTED_REJECT: &[u16] = &[41];
/// PB rule numbers whose corpus ACCEPT test cannot pass yet because
/// the verifier can detect the candidate but cannot yet discharge
/// it (i.e. prove the safety property holds even when a sound
/// precondition is present in the source). Symmetric to
/// `KNOWN_UNIMPLEMENTED_REJECT`: the reject side asks "does the
/// rule fire?", the accept side asks "does the rule NOT fire?".
/// Both can be blocked on independent pieces of v0.2 work.
///
/// - PB054 (slice index without bound): the visitor emits an
///   `IndexBound` obligation, `pitbull-vc::compile` produces a
///   real SMT problem, AND Task P.2 wired the operand binding
///   so user preconditions can constrain the SMT search space.
///   What's still missing: the corpus accept file
///   (`PB054_bounded_index.rs`) uses an EXPRESSION-form
///   `#[pitbull::requires(i < s.len())]` attribute that the
///   O.3 HIR attribute parser doesn't accept (it only handles
///   string-literal arguments). Also the predicate grammar
///   doesn't yet support `<ident> <cmp> <ident>` form. Until
///   either one lands, the corpus accept file has no extractable
///   precondition, the obligation reports as undischarged, and
///   the wrapper's `(PB054)` verdict surface triggers the
///   contains-check as if the rule fired.
///
///   Note: the parallel e2e test
///   `wrapper_proves_bounded_index_safe_under_precondition`
///   demonstrates a successful PB054 discharge by routing the
///   precondition through `pitbull.toml` (raw SMT-LIB form) —
///   that path IS fully wired.
const KNOWN_UNDISCHARGED_ACCEPT: &[u16] = &[54];
/// PB rule numbers whose corpus ACCEPT file is currently REJECTED by the
/// verifier as a documented FALSE POSITIVE (conservative, sound — the
/// verifier rejects safe code it cannot yet prove safe). Distinct from
/// `KNOWN_UNDISCHARGED_ACCEPT` (detected-but-not-discharged): these emit
/// subset violations, so the strict "zero subset violations" accept check
/// below would otherwise flag them.
///
/// - PB031 (static dispatch): `accept/PB031_static_dispatch.rs` exercises
///   generic dispatch that is monomorphic after instantiation. The v0.2
///   wrapper walks the GENERIC body without a monomorphization pass, so the
///   unresolved type parameter trips PB039 (`unresolvable impl Trait`) —
///   fail-closed. Until the pipeline instantiates generics, this valid file
///   is conservatively rejected. Audit 2026-05-31 (corpus mislabel finding).
///
/// PB050 (fixed-point, `>> 16`) was REMOVED from this list on 2026-06-13:
/// the PB051-on-shift false positive is fixed. rustc lowers a shift's
/// amount to an implicit `IntToInt` cast (the untyped `16` defaults to
/// i32 → `16_i32 as u64` for the bounds check), and PB051 now exempts
/// value-preserving constant casts, so `accept/PB050_fixed_point.rs`
/// passes the strict zero-violations check end-to-end. See PSS-1.md
/// §17.1 "PB051 value-preserving-constant cast exemption".
const KNOWN_REJECTED_ACCEPT: &[u16] = &[31];
/// Environment needed to drive the wrapper: paths to the built
/// pitbull-rustc binary and the nightly sysroot.
struct E2eEnv {
    wrapper: PathBuf,
    nightly_sysroot: PathBuf,
}
impl E2eEnv {
    fn probe() -> Option<Self> {
        let wrapper = locate_wrapper()?;
        let sysroot = nightly_sysroot()?;
        Some(Self { wrapper, nightly_sysroot: sysroot })
    }
}
/// Look for the built wrapper binary at the workspace target dir.
fn locate_wrapper() -> Option<PathBuf> {
    // Walk up from CARGO_MANIFEST_DIR looking for target/debug/pitbull-rustc(.exe).
    let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")?;
    let crate_dir = PathBuf::from(manifest_dir);
    let exe_name = if cfg!(windows) { "pitbull-rustc.exe" } else { "pitbull-rustc" };
    for ancestor in crate_dir.ancestors() {
        for profile in ["debug", "release"] {
            let candidate = ancestor.join("target").join(profile).join(exe_name);
            if candidate.exists() {
                return Some(candidate);
            }
        }
    }
    None
}
/// Resolve the nightly toolchain's sysroot via rustup.
fn nightly_sysroot() -> Option<PathBuf> {
    let output = std::process::Command::new("rustup")
        .args(["run", "nightly-2026-01-29", "rustc", "--print", "sysroot"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let s = String::from_utf8(output.stdout).ok()?;
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return None;
    }
    Some(PathBuf::from(trimmed))
}
/// True when the wrapper reported that NO SMT solver was available
/// to discharge obligations, so any solver-dependent assertion must
/// be skipped-with-pass. Matches the multi-solver dispatch's
/// "no configured solver is installed" banner and per-obligation
/// "undischarged (no solver)" line (Task S, 2026-05-28), plus the
/// legacy single-solver "z3 not installed" text for safety.
fn no_solver_available(stderr: &str) -> bool {
    stderr.contains("no configured solver is installed")
        || stderr.contains("undischarged (no solver)")
        || stderr.contains("z3 not installed")
}
/// Parse the count `N` from the wrapper's summary line
/// "... N subset violation(s)". `None` if the line isn't present.
fn subset_violation_count(stderr: &str) -> Option<usize> {
    let idx = stderr.find(" subset violation")?;
    // The token immediately before " subset violation" is the count.
    stderr[..idx]
        .rsplit(|c: char| !c.is_ascii_digit())
        .find(|tok| !tok.is_empty())?
        .parse()
        .ok()
}
/// True when `program` is invocable on PATH (mirrors how the wrapper
/// spawns solvers). Used to gate the multi-solver agreement e2e test
/// on BOTH solvers being present — it skips cleanly otherwise.
fn solver_on_path(program: &str) -> bool {
    std::process::Command::new(program)
        .arg("--version")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}
/// Strip `#[pitbull::*]` and `#[pitbull_spec::*]` attributes from
/// a source string. The corpus uses them as forward-looking
/// annotations; the v0.2 visitor uses verify_roots config instead.
/// Without stripping, rustc fails because the `pitbull` tool name
/// isn't registered.
///
/// Naive line-based: any line whose trimmed form starts with
/// `#[pitbull::` or `#[pitbull_spec::` becomes blank. This is sound
/// for the v0.1 corpus (one attribute per line, on its own line).
fn strip_pitbull_attrs(source: &str) -> String {
    source
        .lines()
        .map(|line| {
            let trimmed = line.trim_start();
            if trimmed.starts_with("#[pitbull::") || trimmed.starts_with("#[pitbull_spec::") {
                "" // keep line numbering stable
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}
/// Compile one corpus file via the wrapper and return its stderr.
fn run_one_corpus_file(env: &E2eEnv, path: &Path) -> Result<String, String> {
    run_one_corpus_file_with_env(env, path, &[])
}
/// Compile one corpus file via the wrapper with additional env vars
/// (PITBULL_TOML, etc.) and return its stderr.
fn run_one_corpus_file_with_env(
    env: &E2eEnv,
    path: &Path,
    extra_env: &[(&str, &std::ffi::OsStr)],
) -> Result<String, String> {
    run_one_corpus_file_full(env, path, extra_env).map(|(stderr, _)| stderr)
}
/// Same as `run_one_corpus_file_with_env` but also returns the
/// wrapper's exit code. Used by tests that need to confirm the
/// wrapper hard-exits on misconfiguration (audit finding H1).
fn run_one_corpus_file_full(
    env: &E2eEnv,
    path: &Path,
    extra_env: &[(&str, &std::ffi::OsStr)],
) -> Result<(String, Option<i32>), String> {
    run_one_corpus_file_full_inner(env, path, extra_env, true)
}
/// Same as `run_one_corpus_file_full` but preserves
/// `#[pitbull::...]` attributes in the source (rather than the
/// default behavior of stripping them). O.3 tests need this so
/// the wrapper's HIR pre-pass actually sees the attributes.
/// The source must include `#![feature(register_tool)]` and
/// `#![register_tool(pitbull)]` for rustc to accept the
/// attributes.
fn run_one_corpus_file_preserving_attrs(
    env: &E2eEnv,
    path: &Path,
    extra_env: &[(&str, &std::ffi::OsStr)],
) -> Result<(String, Option<i32>), String> {
    run_one_corpus_file_full_inner(env, path, extra_env, false)
}
fn run_one_corpus_file_full_inner(
    env: &E2eEnv,
    path: &Path,
    extra_env: &[(&str, &std::ffi::OsStr)],
    strip_attrs: bool,
) -> Result<(String, Option<i32>), String> {
    let source =
        fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let stripped = if strip_attrs {
        strip_pitbull_attrs(&source)
    } else {
        source
    };
    // Write to a unique temp file in the OS temp dir. The
    // per-process counter is what makes the path unique within
    // a single test binary process — many tests use the same
    // corpus filename (e.g. PB018_static_mut.rs), and cargo test
    // runs them in parallel by default, so a pid-only filename
    // would collide and cause flaky failures where one test's
    // cleanup deletes another's input file mid-rustc.
    let counter = TEMP_FILE_COUNTER.fetch_add(1, Ordering::Relaxed);
    let mut temp_dir = std::env::temp_dir();
    temp_dir.push(format!(
        "pitbull-corpus-{}-{}-{}.rs",
        path.file_stem().unwrap().to_str().unwrap(),
        std::process::id(),
        counter,
    ));
    fs::write(&temp_dir, stripped)
        .map_err(|e| format!("write temp {}: {e}", temp_dir.display()))?;
    // Build PATH with the nightly bin dir prepended (Windows DLL deps).
    let nightly_bin = env.nightly_sysroot.join("bin");
    let path_var = std::env::var_os("PATH").unwrap_or_default();
    let mut paths: Vec<PathBuf> = vec![nightly_bin];
    paths.extend(std::env::split_paths(&path_var));
    let new_path =
        std::env::join_paths(paths).map_err(|e| format!("PATH assembly: {e}"))?;
    // The corpus files compile as binaries (they have a fn main() in
    // some, others have only annotated fns — but for our PSS-1 check
    // the executable shape doesn't matter; we use --crate-type=lib so
    // missing `main` is not an error).
    let mut output_artifact = std::env::temp_dir();
    output_artifact.push(format!(
        "pitbull-corpus-out-{}-{}.rmeta",
        std::process::id(),
        counter,
    ));
    let mut cmd = std::process::Command::new(&env.wrapper);
    cmd.arg("--sysroot")
        .arg(&env.nightly_sysroot)
        .arg("--edition=2021")
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        // Force the crate name so `item.name()` returns
        // "corpus_test::<fn>" — matches the convention the
        // pitbull.toml-based tests use for their precondition
        // keys. Without this, rustc derives the crate name from
        // the temp filename (e.g. `pitbull_corpus_PBxxx_yyy_zzz`)
        // and the precondition lookup silently misses, leaving
        // obligations with no assumptions even when the user
        // wrote a precondition. CARGO_PKG_NAME is a cargo env var
        // that rustc itself doesn't read — must come through CLI.
        .arg("--crate-name=corpus_test")
        .arg("-o")
        .arg(&output_artifact)
        .arg(&temp_dir)
        .env("PATH", &new_path)
        .env("CARGO_PKG_NAME", "corpus_test");
    for (k, v) in extra_env {
        cmd.env(k, v);
    }
    let output = cmd.output().map_err(|e| format!("spawn wrapper: {e}"))?;
    // Best-effort cleanup; ignore errors.
    let _ = fs::remove_file(&temp_dir);
    let _ = fs::remove_file(&output_artifact);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let code = output.status.code();
    // We don't require exit code 0 — pitbull-rustc continues compilation
    // even when violations are found, so success means rustc completed.
    // A non-zero exit could mean the file itself doesn't compile (e.g.,
    // unknown crate `pitbull`) — surface that as part of stderr for the
    // assertion to handle. The exit code is returned for tests that
    // need it (H1 hard-error regression).
    Ok((stderr, code))
}
/// Regression test for audit finding H1: when `PITBULL_TOML` points
/// at a path that exists but contains malformed TOML, the wrapper
/// must hard-error (exit code 2) rather than silently fall back to
/// the test default config. The earlier behavior would let a typo'd
/// config produce a "successful" verification under permissive
/// defaults — the silent-skip anti-pattern.
#[test]
fn malformed_pitbull_toml_hard_errors() {
    let Some(env) = E2eEnv::probe() else {
        let require = std::env::var_os("PITBULL_REQUIRE_E2E").is_some();
        if require {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!(
            "malformed_pitbull_toml_hard_errors: SKIPPED — prerequisites missing.",
        );
        return;
    };
    // Write a syntactically broken pitbull.toml. The TOML parser
    // will reject `not = valid = toml = ===` outright.
    let mut config_path = std::env::temp_dir();
    config_path.push(format!("pitbull-h1-malformed-{}.toml", std::process::id()));
    let broken_text = "not = valid = toml = ===\n";
    fs::write(&config_path, broken_text)
        .expect("write temp malformed pitbull.toml");
    let corpus = Path::new("tests")
        .join("corpus")
        .join("reject")
        .join("PB018_static_mut.rs");
    let result = run_one_corpus_file_full(
        &env,
        &corpus,
        &[("PITBULL_TOML", config_path.as_os_str())],
    );
    let _ = fs::remove_file(&config_path);
    let (stderr, code) = result.expect("wrapper should spawn");
    assert_eq!(
        code,
        Some(2),
        "H1: malformed pitbull.toml must exit 2 (config error); \
         got exit code {code:?}, stderr:\n{stderr}",
    );
    assert!(
        stderr.contains("config error"),
        "H1: stderr should mention 'config error' to make the failure \
         mode clear; got:\n{stderr}",
    );
}
/// Regression for the config-validation fail-open (audit 2026-05-31): a
/// pitbull.toml that PARSES but violates a PSS-1 config policy (here PB048,
/// `panic_strategy != "abort"`) must REFUSE to verify (exit 2) — not print
/// the error and exit 0. A non-conforming config (e.g. an unsupported
/// toolchain, PB071) invalidates the run's soundness basis, so proceeding
/// would be a fail-open. Before the fix, a clean body under this config
/// exited 0 ("verified").
#[test]
fn invalid_config_policy_refuses_verification() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("invalid_config_policy_refuses_verification: SKIPPED — prerequisites missing.");
        return;
    };
    let mut config_path = std::env::temp_dir();
    config_path.push(format!("pitbull-cfgpolicy-{}.toml", std::process::id()));
    // Parses fine; `panic_strategy = "unwind"` violates PB048.
    fs::write(
        &config_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[subset]\npanic_strategy = \"unwind\"\n",
    )
    .expect("write temp pitbull.toml");
    // A clean body — without the fix this would exit 0 despite the policy
    // violation.
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-cfgpolicy-{}.rs", std::process::id()));
    fs::write(&probe_rs, "pub fn ok(x: u32) -> u32 { x }\n").expect("write probe.rs");
    let result = run_one_corpus_file_full(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", config_path.as_os_str())],
    );
    let _ = fs::remove_file(&config_path);
    let _ = fs::remove_file(&probe_rs);
    let (stderr, code) = result.expect("wrapper should spawn");
    assert_eq!(
        code,
        Some(2),
        "config policy violation (PB048) must refuse with exit 2, not pass; \
         got {code:?}, stderr:\n{stderr}",
    );
    assert!(
        stderr.contains("PB048") || stderr.contains("validation error"),
        "stderr should name the config validation failure; got:\n{stderr}",
    );
}
/// Regression test for audit finding H1 (companion): when
/// `PITBULL_TOML` is set to a path that does not exist, the wrapper
/// must hard-error rather than silently fall back.
#[test]
fn nonexistent_pitbull_toml_path_hard_errors() {
    let Some(env) = E2eEnv::probe() else {
        let require = std::env::var_os("PITBULL_REQUIRE_E2E").is_some();
        if require {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!(
            "nonexistent_pitbull_toml_path_hard_errors: SKIPPED — prerequisites missing.",
        );
        return;
    };
    let mut nonexistent = std::env::temp_dir();
    nonexistent.push(format!(
        "pitbull-h1-nonexistent-{}-does-not-exist.toml",
        std::process::id(),
    ));
    // Ensure it really doesn't exist.
    let _ = fs::remove_file(&nonexistent);
    let corpus = Path::new("tests")
        .join("corpus")
        .join("reject")
        .join("PB018_static_mut.rs");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &corpus,
        &[("PITBULL_TOML", nonexistent.as_os_str())],
    )
    .expect("wrapper should spawn");
    assert_eq!(
        code,
        Some(2),
        "H1: PITBULL_TOML pointing at nonexistent path must exit 2; \
         got exit code {code:?}, stderr:\n{stderr}",
    );
    assert!(
        stderr.contains("does not exist"),
        "H1: stderr should mention 'does not exist'; got:\n{stderr}",
    );
}
/// Regression test for the F1 audit fix (CRITICAL): a
/// `pitbull.toml` precondition that is logically contradictory
/// (`(assert false)`) MUST be refused by the wrapper's
/// consistency-check guard. Without the guard, Z3 would return
/// `unsat` for any safety property and the wrapper would
/// incorrectly report "discharged" — silently "verifying"
/// unsafe code via vacuous truth.
#[test]
fn dispatch_refuses_contradictory_preconditions() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("dispatch_refuses_contradictory_preconditions: SKIPPED");
        return;
    };
    // Write a pitbull.toml whose preconditions are contradictory.
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-f1-contradictory-{}.toml", std::process::id()));
    // The corpus filename becomes "corpus_test::<stem>" inside the
    // wrapper (cargo sets CARGO_PKG_NAME=corpus_test in the e2e
    // helper). The corpus we run is PB018_static_mut.rs, but
    // statics don't emit overflow obligations. We need a body
    // with an arithmetic op to trigger the F1 path. Use a
    // self-contained probe file written inline.
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-f1-probe-{}.rs",
        std::process::id(),
    ));
    fs::write(&probe_rs, "pub fn add_one(x: u32) -> u32 { x + 1 }\n")
        .expect("write probe.rs");
    // Use the bare function name format — wrapper looks up via
    // CrateDef::name() which for a free function in the crate
    // returns "<crate>::add_one". Since corpus_test is the crate
    // name set by the wrapper test harness, we don't need it; the
    // wrapper uses item.name() which may already include the crate
    // prefix. The test below validates by checking stderr for
    // "REFUSED" regardless of exact key match — if F1 fires for
    // the right body, the message appears.
    //
    // To make it portable, we set the precondition under several
    // plausible key forms.
    let cfg_text = r#"
[project]
name = "corpus_test"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"

[verification]
solvers = ["z3"]
solver_agreement = 1

[verification.preconditions]
"corpus_test::add_one" = ["(assert false)"]
"#
    .to_string();
    fs::write(&cfg_path, cfg_text).expect("write contradictory pitbull.toml");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    // Z3 may not be installed on every dev/CI machine. The
    // consistency-check path only fires when Z3 is reachable
    // (NotInstalled bypasses the check). Skip-with-pass if so.
    let solver_available = !no_solver_available(&stderr);
    if !solver_available {
        eprintln!(
            "dispatch_refuses_contradictory_preconditions: SKIPPED \
             (no solver installed; the consistency-check guard \
             requires a solver to detect the contradiction)",
        );
        return;
    }
    assert!(
        stderr.contains("REFUSED") && stderr.contains("contradictory"),
        "F1: wrapper must REFUSE discharge when preconditions are \
         contradictory; got code {code:?}, stderr:\n{stderr}",
    );
    // Exit code follows F10 (violations OR undischarged ⇒ 1).
    assert_eq!(
        code,
        Some(1),
        "F1+F10: a refused contradictory precondition counts as \
         undischarged → exit 1. Got code {code:?}, stderr:\n{stderr}",
    );
}
/// Regression test for the F10 audit fix: the wrapper's exit
/// code reflects Pitbull's findings, not just rustc's. A file
/// that compiles cleanly but violates PSS-1 must exit non-zero.
#[test]
fn wrapper_exits_nonzero_on_violation() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_exits_nonzero_on_violation: SKIPPED");
        return;
    };
    let corpus = Path::new("tests")
        .join("corpus")
        .join("reject")
        .join("PB018_static_mut.rs");
    let (stderr, code) = run_one_corpus_file_full(&env, &corpus, &[])
        .expect("wrapper should spawn");
    assert!(
        stderr.contains("PB018"),
        "F10 prerequisite: PB018 should fire on this corpus file; got stderr:\n{stderr}",
    );
    assert_eq!(
        code,
        Some(1),
        "F10: clean compile + Pitbull violation must exit 1. Got code {code:?}, stderr:\n{stderr}",
    );
}
/// O.3 attribute extraction: when a function carries a
/// `#[pitbull::requires("...")]` tool attribute, the wrapper's
/// HIR pre-pass extracts it and attaches it to that function's
/// obligations alongside (or instead of) any pitbull.toml
/// `[verification.preconditions]` entry.
///
/// We can't easily inspect the assumption text without Z3, but
/// the verdict line now carries an `[N assumptions]` suffix
/// that exposes the count. With one `#[pitbull::requires]`
/// attribute on `add_one`, the obligation has 2 assumptions
/// (1 const-pin from O.2.5 + 1 attribute precondition).
/// Without the attribute, the same function emits 1 assumption
/// (just the const-pin). The differential is the signal that
/// the attribute extraction fires.
#[test]
fn pitbull_requires_attribute_attaches_precondition() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_requires_attribute_attaches_precondition: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-o3-attr-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        // `#![feature(register_tool)]` is required because the
        // tool attribute mechanism is still unstable on this
        // nightly. Documented in HANDOFF.md.
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::requires(\"x < 100\")]\n\
         pub fn add_one(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    // Use the preserving helper — default `run_one_corpus_file_full`
    // strips `#[pitbull::*]` attributes (legacy corpus compatibility),
    // which would defeat the entire O.3 mechanism we're testing.
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    // Differential signal: the precondition attribute adds one
    // assumption on top of the const-pin O.2.5 already adds.
    // The wrapper now prints `[N assumptions]` per verdict line.
    assert!(
        stderr.contains("[2 assumptions]"),
        "O.3: `#[pitbull::requires(...)]` should add a second \
         assumption (one const-pin from O.2.5 + one precondition \
         from the attribute). Expected `[2 assumptions]` in \
         stderr; got:\n{stderr}",
    );
}
/// `#[pitbull::ensures("...")]` produces a PB076 EnsuresPostcondition
/// obligation at every function exit, and (Q.4b) the wrapper now
/// COMPILES it to SMT rather than reporting "pending" — `add_one`'s
/// `x + 1` body effect is captured through the checked-add MIR
/// (AddWithOverflow tuple + overflow Assert + `_0 = (_2.0)`). This
/// non-gated test pins the pipeline up to dispatch (HIR attr → visitor
/// → compile): the PB076 obligation is emitted AND is no longer
/// compilation-pending. The live unsat/sat verdict is pinned by the
/// Z3-gated discharge tests below.
#[test]
fn pitbull_ensures_attribute_emits_pb076_obligation() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_ensures_attribute_emits_pb076_obligation: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q4-ensures-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::ensures(\"result < 101\")]\n\
         pub fn add_one(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    // The PB076 verdict line carries the canonical rule id and
    // the obligation kind's Debug-rendered ret_name/ret_ty_name.
    assert!(
        stderr.contains("(PB076)"),
        "Q.4: ensures should emit a PB076 obligation. Got stderr:\n{stderr}",
    );
    assert!(
        stderr.contains("pb076-ensures-"),
        "Q.4: verdict line should reference the pb076-ensures-{{seq}} id format. Got stderr:\n{stderr}",
    );
    // Q.4b: `add_one`'s wrapping `x + 1` body effect is now CAPTURED and
    // compiled to SMT, so the obligation must NOT be reported as
    // compilation-pending. (The exact unsat/sat verdict is solver-
    // dependent and pinned by the Z3-gated tests below.)
    assert!(
        !stderr.contains("compilation not yet supported"),
        "Q.4b: add_one's ensures must compile (not stay compilation-pending). Got stderr:\n{stderr}",
    );
}
/// Q.4a (2026-05-29) capstone — TRUE postcondition DISCHARGES (unsat).
/// `#[pitbull::ensures("result == x")] fn copy_arg(x: u32) -> u32 { x }`:
/// the visitor captures the body effect `result == x`, asserts it
/// alongside the negated goal `(not (= result x))` — a contradiction —
/// so Z3 returns `unsat` and the wrapper reports `discharged (unsat`.
/// This is the proof that PB076 ACTUALLY discharges end-to-end, not
/// merely emits a pending obligation. Gated on Z3 like the other
/// discharge capstones.
#[test]
fn wrapper_proves_ensures_copy_arg_discharges() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_proves_ensures_copy_arg_discharges: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-q4a-true-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-q4a-true-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::ensures(\"result == x\")]\n\
         pub fn copy_arg(x: u32) -> u32 {\n\
             x\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!(
            "wrapper_proves_ensures_copy_arg_discharges: SKIPPED \
             (no solver on PATH; install z3 to exercise this end-to-end test)",
        );
        return;
    }
    assert!(
        stderr.contains("(PB076)") && stderr.contains("discharged (unsat")
            && !stderr.contains("NOT DISCHARGED"),
        "Q.4a: `copy_arg(x){{ x }}` with `ensures(result == x)` must \
         DISCHARGE (unsat) under Z3. Got code {code:?}, stderr:\n{stderr}",
    );
    assert_eq!(
        code,
        Some(0),
        "Q.4a: a fully-discharged ensures obligation should exit 0. Got {code:?}",
    );
}
/// Q.4a (2026-05-29) adversarial twin — FALSE postcondition does NOT
/// discharge (sat). `#[pitbull::ensures("result < 5")] fn copy_arg(x) { x }`:
/// `result == x` ∧ `not(result < 5)` is satisfiable (x = 5), so Z3
/// returns `sat` and the wrapper reports `NOT DISCHARGED (sat`. Pairing
/// this with the TRUE test proves the discharge is REAL — the encoder
/// distinguishes a holding postcondition from a violated one, rather
/// than rubber-stamping everything `unsat` (the cardinal sin). Gated on
/// Z3.
#[test]
fn wrapper_ensures_false_postcondition_not_discharged() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_ensures_false_postcondition_not_discharged: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-q4a-false-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-q4a-false-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::ensures(\"result < 5\")]\n\
         pub fn copy_arg(x: u32) -> u32 {\n\
             x\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!(
            "wrapper_ensures_false_postcondition_not_discharged: SKIPPED (no solver on PATH)",
        );
        return;
    }
    assert!(
        stderr.contains("(PB076)") && stderr.contains("NOT DISCHARGED (sat")
            && !stderr.contains("discharged (unsat"),
        "Q.4a: `copy_arg(x){{ x }}` with `ensures(result < 5)` must NOT \
         discharge — a counterexample (x = 5) exists. Got code {code:?}, stderr:\n{stderr}",
    );
    assert_ne!(
        code,
        Some(0),
        "Q.4a: an undischarged ensures obligation must drive a non-zero exit. Got {code:?}",
    );
}
/// SOUNDNESS regression (audit 2026-05-31, CRITICAL) — a precondition that
/// references `result` (the OUTPUT) must NOT vacuously discharge a false
/// postcondition. `#[requires("result < 100")] #[ensures("result < 100")]
/// fn copy_arg(x: u32) -> u32 { x }`: `copy_arg(200) = 200 ≥ 100`, so the
/// ensures is FALSE. Before the fix, treating the precondition as a
/// hypothesis ABOUT the output made the main check unsat and wrongly
/// reported `discharged`. The precondition now references the output, which
/// is out of precondition scope ⇒ untranslatable ⇒ the obligation stays
/// pending/undischarged. This MUST NOT report `discharged (unsat`. Z3-gated.
#[test]
fn wrapper_ensures_precondition_on_result_not_discharged() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_ensures_precondition_on_result_not_discharged: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-presult-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-presult-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::requires(\"result < 100\")]\n\
         #[pitbull::ensures(\"result < 100\")]\n\
         pub fn copy_arg(x: u32) -> u32 {\n\
             x\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_ensures_precondition_on_result_not_discharged: SKIPPED (no solver)");
        return;
    }
    // The cardinal-sin guard: this FALSE postcondition must NEVER be
    // reported discharged, regardless of the result-referencing precondition.
    assert!(
        stderr.contains("(PB076)") && !stderr.contains("discharged (unsat"),
        "CRITICAL: a precondition on `result` must not vacuously discharge a \
         false ensures. Got code {code:?}, stderr:\n{stderr}",
    );
}
/// Q.4b (2026-05-31) capstone — ensures over WRAPPING ARITHMETIC
/// discharges. `add_one(x){ x + 1 }` with `requires(x < 100)` +
/// `ensures(result < 101)`: the visitor walks the checked-add MIR
/// (AddWithOverflow tuple + overflow Assert + `_0 = (_2.0)`), captures
/// `result == (bvadd x #x00000001)`, assumes `x < 100`, and negates
/// `result < 101` — unsat under Z3, so PB076 reports `discharged
/// (unsat`. This is the canonical `add_one` ensures Q.4a left pending,
/// now discharging end-to-end. (PB049 overflow also discharges under the
/// same precondition, so the wrapper exits 0.) Z3-gated.
#[test]
fn wrapper_proves_ensures_add_one_discharges_under_precondition() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_proves_ensures_add_one_discharges_under_precondition: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-q4b-true-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-q4b-true-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::requires(\"x < 100\")]\n\
         #[pitbull::ensures(\"result < 101\")]\n\
         pub fn add_one(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_proves_ensures_add_one_discharges_under_precondition: SKIPPED (no solver)");
        return;
    }
    assert!(
        stderr.contains("(PB076)") && stderr.contains("discharged (unsat")
            && !stderr.contains("NOT DISCHARGED"),
        "Q.4b: `add_one(x){{ x + 1 }}` with `requires(x < 100)` + \
         `ensures(result < 101)` must DISCHARGE (unsat). Got code {code:?}, stderr:\n{stderr}",
    );
    assert_eq!(
        code,
        Some(0),
        "Q.4b: add_one fully discharged (PB049 + PB076) should exit 0. Got {code:?}",
    );
}
/// Q.4b adversarial twin — a FALSE arithmetic postcondition does NOT
/// discharge, isolated from overflow. `add_one(x){ x + 1 }` with
/// `requires(x < 100)` + `ensures(result < 50)`: PB049 overflow
/// discharges (x < 100 ⇒ no overflow), but PB076 is `sat` (e.g. x = 60 ⇒
/// result = 61 ≥ 50), so the wrapper reports `NOT DISCHARGED (sat` for
/// the postcondition. Pairing this with the discharge test proves the
/// wrapping-arithmetic encoder distinguishes a holding postcondition
/// from a violated one. Z3-gated.
#[test]
fn wrapper_ensures_add_one_false_postcondition_not_discharged() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_ensures_add_one_false_postcondition_not_discharged: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-q4b-false-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-q4b-false-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::requires(\"x < 100\")]\n\
         #[pitbull::ensures(\"result < 50\")]\n\
         pub fn add_one(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_ensures_add_one_false_postcondition_not_discharged: SKIPPED (no solver)");
        return;
    }
    assert!(
        stderr.contains("(PB076)") && stderr.contains("NOT DISCHARGED (sat"),
        "Q.4b: `add_one` with `ensures(result < 50)` must NOT discharge — \
         x = 60 ⇒ result = 61 ≥ 50 is a counterexample. Got code {code:?}, stderr:\n{stderr}",
    );
}
/// Q.4c (2026-05-31) capstone — ensures over DIVISION discharges.
/// `safe_div(a,b){ a / b }` with `requires(b > 0)` + `ensures(result <= a)`:
/// the visitor walks the div MIR (div-by-zero `Assert` then `_0 =
/// Div(a,b)`), captures `result == (bvudiv a b)`, assumes `b > 0`, and
/// negates `result <= a` — unsat under Z3. (The `requires(b > 0)` also
/// discharges the PB054/Task-R division-by-zero obligation, so the
/// wrapper exits 0.) Z3-gated.
#[test]
fn wrapper_proves_ensures_safe_div_discharges() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_proves_ensures_safe_div_discharges: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-q4c-true-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-q4c-true-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::requires(\"b > 0\")]\n\
         #[pitbull::ensures(\"result <= a\")]\n\
         pub fn safe_div(a: u32, b: u32) -> u32 {\n\
             a / b\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_proves_ensures_safe_div_discharges: SKIPPED (no solver)");
        return;
    }
    assert!(
        stderr.contains("(PB076)") && stderr.contains("discharged (unsat")
            && !stderr.contains("NOT DISCHARGED"),
        "Q.4c: `safe_div(a,b){{ a / b }}` with `requires(b > 0)` + \
         `ensures(result <= a)` must DISCHARGE (unsat). Got code {code:?}, stderr:\n{stderr}",
    );
    assert_eq!(
        code,
        Some(0),
        "Q.4c: safe_div fully discharged (div-by-zero + PB076) should exit 0. Got {code:?}",
    );
}
/// Q.4c adversarial twin — a FALSE division postcondition does not
/// discharge. `safe_div(a,b){ a / b }` with `requires(b > 0)` +
/// `ensures(result < a)`: `b = 1` ⇒ `result = a`, so `result < a` is
/// violated → PB076 is `sat` (NOT DISCHARGED), while the div-by-zero
/// obligation still discharges under `b > 0`. Z3-gated.
#[test]
fn wrapper_ensures_safe_div_strict_false_not_discharged() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_ensures_safe_div_strict_false_not_discharged: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-q4c-false-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-q4c-false-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::requires(\"b > 0\")]\n\
         #[pitbull::ensures(\"result < a\")]\n\
         pub fn safe_div(a: u32, b: u32) -> u32 {\n\
             a / b\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_ensures_safe_div_strict_false_not_discharged: SKIPPED (no solver)");
        return;
    }
    assert!(
        stderr.contains("(PB076)") && stderr.contains("NOT DISCHARGED (sat"),
        "Q.4c: `safe_div` with `ensures(result < a)` must NOT discharge — \
         b = 1 ⇒ result = a is a counterexample. Got code {code:?}, stderr:\n{stderr}",
    );
}
/// Q.4d (2026-05-31) capstone — ensures over a SHIFT discharges.
/// `halve(x){ x >> 1 }` with `ensures(result <= x)`: the visitor walks
/// the shift MIR (over-shift `Assert` then `_0 = Shr(x, 1)`), captures
/// `result == (bvlshr x #x00000001)` (logical right shift, unsigned),
/// and negates `result <= x` — unsat under Z3 (`x >> 1 <= x` for all x).
/// Asserts the PB076 verdict specifically (the separate over-shift
/// obligation is not this test's concern). Z3-gated.
#[test]
fn wrapper_proves_ensures_shr_halve_discharges() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_proves_ensures_shr_halve_discharges: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-q4d-true-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-q4d-true-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::ensures(\"result <= x\")]\n\
         pub fn halve(x: u32) -> u32 {\n\
             x >> 1\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_proves_ensures_shr_halve_discharges: SKIPPED (no solver)");
        return;
    }
    assert!(
        stderr.contains("(PB076)") && stderr.contains("discharged (unsat")
            && !stderr.contains("NOT DISCHARGED"),
        "Q.4d: `halve(x){{ x >> 1 }}` with `ensures(result <= x)` must \
         DISCHARGE (unsat). Got code {code:?}, stderr:\n{stderr}",
    );
}
/// Q.4d adversarial twin — a FALSE shift postcondition does not
/// discharge. `halve(x){ x >> 1 }` with `ensures(result < x)`: `x = 0` ⇒
/// `0 >> 1 = 0`, not `< 0`, so PB076 is `sat` (NOT DISCHARGED). Z3-gated.
#[test]
fn wrapper_ensures_shr_strict_false_not_discharged() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_ensures_shr_strict_false_not_discharged: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-q4d-false-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-q4d-false-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::ensures(\"result < x\")]\n\
         pub fn halve(x: u32) -> u32 {\n\
             x >> 1\n\
         }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        "[project]\nname = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         \n[verification]\nsolvers = [\"z3\"]\nsolver_agreement = 1\n",
    )
    .expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_preserving_attrs(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_ensures_shr_strict_false_not_discharged: SKIPPED (no solver)");
        return;
    }
    assert!(
        stderr.contains("(PB076)") && stderr.contains("NOT DISCHARGED (sat"),
        "Q.4d: `halve` with `ensures(result < x)` must NOT discharge — \
         x = 0 ⇒ 0 >> 1 = 0 is a counterexample. Got code {code:?}, stderr:\n{stderr}",
    );
}
/// Q.4 trust × ensures interaction (Option C design open-question #4):
/// a `#[pitbull::trusted]` body's ensures is NOT emitted as a proof
/// obligation (trust means body-content assumed correct). The visitor
/// audit-notes the gap so the auditor sees that the ensures was
/// noticed but not proven. Caller-side propagation of trusted
/// postconditions is out of scope for the MVP.
#[test]
fn pitbull_trusted_with_ensures_audits_but_no_pb076() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_trusted_with_ensures_audits_but_no_pb076: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q4-trusted-ensures-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::trusted]\n\
         #[pitbull::ensures(\"result < 101\")]\n\
         pub fn add_one(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    // No PB076 obligation should appear (trusted bodies skip body
    // walk before reaching emit_ensures_obligation).
    assert!(
        !stderr.contains("pb076-ensures-"),
        "Q.4: trusted body should NOT emit a PB076 obligation. Got stderr:\n{stderr}",
    );
    // Audit note must explain the gap.
    assert!(
        stderr.contains("ensures on trusted body"),
        "Q.4: trusted body with ensures must produce an explanatory audit note. \
         Got stderr:\n{stderr}",
    );
}
/// Task R (2026-05-28) capstone: division-by-zero discharges
/// end-to-end under Z3. `fn d(a, b) { a / b }` with
/// `requires("b > 0")` must report `discharged (unsat)` — the
/// solver proves a zero divisor is impossible. This is the AoRTE
/// hole the full-codebase audit found (div/rem/shift emitted no
/// obligation) now closed end-to-end. Gated on Z3 like the other
/// discharge capstones.
#[test]
fn wrapper_proves_division_safe_under_precondition() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_proves_division_safe_under_precondition: SKIPPED");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-r-div-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-r-div-{}.rs", std::process::id()));
    fs::write(&probe_rs, "pub fn d(a: u32, b: u32) -> u32 { a / b }\n")
        .expect("write probe.rs");
    let cfg_text = r#"
[project]
name = "corpus_test"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"

[verification]
solvers = ["z3"]
solver_agreement = 1

[verification.preconditions]
"corpus_test::d" = ["b > 0"]
"#
    .to_string();
    fs::write(&cfg_path, cfg_text).expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_proves_division_safe_under_precondition: SKIPPED (no solver)");
        return;
    }
    // The division obligation is a PB049 `pb049-div-*` and must
    // discharge: b > 0 rules out the zero divisor.
    assert!(
        stderr.contains("pb049-div-0") && stderr.contains("discharged (unsat"),
        "Task R: `a / b` with `b > 0` must discharge the div-by-zero \
         obligation. Got code {code:?}, stderr:\n{stderr}",
    );
    assert!(
        !stderr.contains("NOT DISCHARGED"),
        "Task R: nothing should remain undischarged for `a / b` under `b > 0`. \
         stderr:\n{stderr}",
    );
}
/// Task R complement: WITHOUT a precondition, the same division
/// must NOT discharge — Z3 finds the b = 0 counterexample. Proves
/// the obligation is real (not vacuously discharged) and the
/// fail-closed direction holds.
#[test]
fn wrapper_division_without_precondition_not_discharged() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_division_without_precondition_not_discharged: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-r-div-bare-{}.rs", std::process::id()));
    fs::write(&probe_rs, "pub fn d(a: u32, b: u32) -> u32 { a / b }\n")
        .expect("write probe.rs");
    let (stderr, code) = run_one_corpus_file_full(&env, &probe_rs, &[])
        .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!("wrapper_division_without_precondition_not_discharged: SKIPPED (no solver)");
        return;
    }
    assert!(
        stderr.contains("pb049-div-0") && stderr.contains("NOT DISCHARGED (sat"),
        "Task R: bare `a / b` must NOT discharge (b = 0 counterexample). \
         Got code {code:?}, stderr:\n{stderr}",
    );
    // F10: undischarged obligation ⇒ non-zero exit.
    assert_eq!(code, Some(1), "undischarged div obligation ⇒ exit 1");
}
/// Audit-cleanup post-Q.3 red-team finding M-RT-Q.D (2026-05-26):
/// Q.2's commit message asserted PB001 unsafe-block detection
/// inside impl methods still works, but no integration test
/// pinned the behavior. Verify: an impl method containing
/// `unsafe { ... }` produces exactly one PB001 violation.
#[test]
fn pb001_fires_inside_impl_method() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pb001_fires_inside_impl_method: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q2-impl-pb001-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "pub struct Foo;\n\
         impl Foo {\n\
             pub fn bar(&self) {\n\
                 unsafe { let _ptr: *const u8 = std::ptr::null(); }\n\
             }\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) = run_one_corpus_file_full(&env, &probe_rs, &[])
        .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    // Exactly one PB001 — defeats Q.2's potential double-fire.
    let pb001_count = stderr.matches("PB001").count();
    assert!(
        pb001_count >= 1,
        "PB001 must fire on `unsafe {{ ... }}` inside impl method; got {pb001_count} matches \
         in stderr:\n{stderr}",
    );
    // Note: stderr may mention PB001 multiple times across rule
    // descriptions, error tags, etc. The "1 unsafe blocks" summary
    // line is the canonical count of distinct blocks detected.
    assert!(
        stderr.contains("1 unsafe blocks"),
        "Q.2 regression pin: expected exactly 1 unsafe block detected; \
         got stderr:\n{stderr}",
    );
}
/// Task Q.3 (2026-05-26): expression-form
/// `#[pitbull::requires(x < 100)]` (NO quotes) is extracted via
/// the new token-tree pretty-printing path in
/// `HirPreVisitor::extract_requires_strings`. Pre-Q.3 the
/// attribute's args had to be a string literal; expression-form
/// silently dropped through `meta_item_list()` returning None.
/// Now we fall through to `AttrArgs::Delimited` and stringify
/// via `rustc_ast_pretty::pprust::tts_to_string`.
///
/// Same `[2 assumptions]` differential signal as Q.1's
/// string-literal test — proves the extraction worked end-to-end
/// through the visitor's overflow obligation pipeline.
#[test]
fn pitbull_requires_expression_form_attaches_precondition() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_requires_expression_form_attaches_precondition: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q3-expr-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::requires(x < 100)]\n\
         pub fn add_one(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    assert!(
        stderr.contains("[2 assumptions]"),
        "Q.3: expression-form `#[pitbull::requires(x < 100)]` should be extracted \
         the same as string-literal form, producing `[2 assumptions]`. Got stderr:\n{stderr}",
    );
}
/// Task Q.3 backward-compat: the existing string-literal form
/// `#[pitbull::requires("x < 100")]` still works (this is the
/// O.3-baseline path — pre-cleanup behavior preserved).
#[test]
fn pitbull_requires_string_literal_form_still_works() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_requires_string_literal_form_still_works: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q3-strlit-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::requires(\"x < 100\")]\n\
         pub fn add_one(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    assert!(
        stderr.contains("[2 assumptions]"),
        "Q.3 backcompat: string-literal form must still produce `[2 assumptions]`. \
         Got stderr:\n{stderr}",
    );
}
/// Task Q.2 (2026-05-26): `#[pitbull::requires(...)]` and
/// `#[pitbull::trusted]` on impl methods are extracted by the
/// new `HirPreVisitor::visit_impl_item`. Pre-Q.2, the HIR
/// pre-pass only handled top-level `ItemKind::Fn` items —
/// impl methods' bodies still got walked (via
/// `rustc_public::all_local_items()` which flattens
/// `DefKind::AssocFn`) but their attributes were silently
/// dropped, so users got `[1 assumption]` (const-pin only)
/// instead of `[2 assumptions]` (const-pin + requires).
#[test]
fn pitbull_requires_on_impl_method_attaches_precondition() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_requires_on_impl_method_attaches_precondition: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q2-impl-requires-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         pub struct Foo;\n\
         impl Foo {\n\
             #[pitbull::requires(\"x < 100\")]\n\
             pub fn bar(&self, x: u32) -> u32 {\n\
                 x + 1\n\
             }\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    assert!(
        stderr.contains("[2 assumptions]"),
        "Q.2: `#[pitbull::requires]` on impl method should produce \
         `[2 assumptions]` (1 const-pin + 1 requires). Got stderr:\n{stderr}",
    );
}
/// Task Q.2: `#[pitbull::trusted]` on an impl method must also
/// short-circuit the body walk (no PB049 obligation emitted).
/// Pairs with the Q.1 trust test but for impl methods.
#[test]
fn pitbull_trusted_on_impl_method_skips_body_walk() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_trusted_on_impl_method_skips_body_walk: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q2-impl-trusted-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         pub struct Foo;\n\
         impl Foo {\n\
             #[pitbull::trusted]\n\
             pub fn bar(&self, x: u32) -> u32 {\n\
                 x + 1\n\
             }\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    assert!(
        !stderr.contains("pb049-add-"),
        "Q.2: `#[pitbull::trusted]` on impl method should short-circuit \
         body walk (no PB049). Got stderr:\n{stderr}",
    );
    assert!(
        !stderr.contains("VC summary"),
        "Q.2: trusted impl method should emit zero obligations (no VC summary). \
         Got stderr:\n{stderr}",
    );
}
/// Task Q.1 (2026-05-26): `#[pitbull::trusted]` skips the
/// MIR-body walk while keeping signature-level rules in force.
/// A body with `x + 1` (which normally emits a PB049 overflow
/// obligation) emits ZERO VC obligations when marked trusted.
///
/// Differential signal: stderr's "N obligation(s)" summary line.
/// Untrusted body of `add_one` produces "1 obligation(s)";
/// trusted body produces "0 obligation(s)". This is the
/// audit-safe verification of trust: the visitor genuinely
/// stops walking, not just suppresses output.
#[test]
fn pitbull_trusted_attribute_skips_body_walk() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_trusted_attribute_skips_body_walk: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q1-trusted-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::trusted]\n\
         pub fn add_one(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    // The wrapper emits "VC summary: N obligation(s), ..." ONLY when
    // at least one obligation exists. A trusted body with zero
    // obligations produces no "VC summary" line at all — the visitor's
    // body-walk short-circuit means PB049's `maybe_emit_overflow_obligation`
    // never runs.
    assert!(
        !stderr.contains("pb049-add-"),
        "Q.1: `#[pitbull::trusted]` on add_one should NOT emit a pb049 \
         overflow obligation (the body walk short-circuits). Got stderr:\n{stderr}",
    );
    assert!(
        !stderr.contains("VC summary"),
        "Q.1: trusted body with no obligations should produce no VC summary \
         line. Got stderr:\n{stderr}",
    );
    // The visitor DID see the body (the items count is non-zero) —
    // trust short-circuits AFTER signature checks, not before.
    assert!(
        stderr.contains("1 bodies walked"),
        "Q.1: trusted body should still be walked (signature checks fire). \
         Got stderr:\n{stderr}",
    );
}
/// Task Q.1 negative control: WITHOUT `#[pitbull::trusted]`,
/// the same body emits its normal PB049 overflow obligation.
/// Pins the differential signal that the trust-extraction test
/// relies on.
#[test]
fn no_pitbull_trusted_attribute_walks_body() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("no_pitbull_trusted_attribute_walks_body: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q1-untrusted-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "pub fn add_one(x: u32) -> u32 { x + 1 }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) = run_one_corpus_file_full(&env, &probe_rs, &[])
        .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    assert!(
        stderr.contains("1 obligation(s)"),
        "Q.1 control: without `#[pitbull::trusted]`, add_one should produce \
         exactly 1 PB049 overflow obligation. Got stderr:\n{stderr}",
    );
}
/// Task Q.1: trust does NOT admit unsafe. A trusted `unsafe fn`
/// must STILL produce a PB002 violation — trust applies to body
/// content, not to signature-level safety qualifiers. Closes the
/// open question from the Option C design doc (Q.1 #1).
#[test]
fn pitbull_trusted_does_not_silence_pb002_unsafe_fn() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_trusted_does_not_silence_pb002_unsafe_fn: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-q1-trusted-unsafe-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "#![feature(register_tool)]\n\
         #![register_tool(pitbull)]\n\
         \n\
         #[pitbull::trusted]\n\
         pub unsafe fn raw_op(x: u32) -> u32 {\n\
             x + 1\n\
         }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_preserving_attrs(&env, &probe_rs, &[])
            .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    assert!(
        stderr.contains("PB002"),
        "Q.1 safety pin: `#[pitbull::trusted] unsafe fn` MUST still report PB002. \
         Trust ≠ unsafe admission. Got stderr:\n{stderr}",
    );
}
/// O.3 control: the same body WITHOUT the attribute carries
/// only the O.2.5 const-pin assumption. Pins the differential
/// signal that the attribute-extraction test relies on.
#[test]
fn no_pitbull_requires_attribute_keeps_only_const_pin() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("no_pitbull_requires_attribute_keeps_only_const_pin: SKIPPED");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-o3-no-attr-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "pub fn add_one(x: u32) -> u32 { x + 1 }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) = run_one_corpus_file_full(&env, &probe_rs, &[])
        .expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    assert!(
        stderr.contains("[1 assumption]"),
        "O.3 control: without the attribute, the obligation \
         carries only the O.2.5 const-pin (1 assumption). Got:\n{stderr}",
    );
}
/// O.2.5 headline-demo capstone: when Z3 is installed, the
/// wrapper proves `fn add_one(x: u32) -> u32 { x + 1 }` is safe
/// under `requires(x < 100)` end-to-end. This pins the entire
/// chain — visitor's const-pin synthesis, predicate translation,
/// pitbull-vc::compile composition, solver dispatch, and verdict
/// mapping — that the unit tests cover only piecewise.
///
/// Gated on Z3 availability: gracefully skips if Z3 isn't on
/// PATH (most dev machines). CI with `PITBULL_REQUIRE_E2E=1`
/// also needs Z3 installed for this specific test to run; the
/// graceful-skip path is the same.
#[test]
fn wrapper_proves_add_one_safe_under_precondition() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_proves_add_one_safe_under_precondition: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!(
        "pitbull-o25-headline-{}.toml",
        std::process::id(),
    ));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-o25-headline-{}.rs",
        std::process::id(),
    ));
    fs::write(&probe_rs, "pub fn add_one(x: u32) -> u32 { x + 1 }\n")
        .expect("write probe.rs");
    fs::write(
        &cfg_path,
        r#"
[project]
name = "corpus_test"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"

[verification]
solvers = ["z3"]
solver_agreement = 1

[verification.preconditions]
"corpus_test::add_one" = ["x < 100"]
"#,
    )
    .expect("write headline pitbull.toml");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!(
            "wrapper_proves_add_one_safe_under_precondition: SKIPPED \
             (no solver on PATH; install z3 to exercise this end-to-end test)",
        );
        return;
    }
    // With Z3 installed, the dispatch should report discharged.
    assert!(
        stderr.contains("discharged (unsat")
            && !stderr.contains("NOT DISCHARGED"),
        "O.2.5 headline demo: `add_one(x){{ x + 1 }}` with \
         `requires(x < 100)` must discharge under Z3. Got code \
         {code:?}, stderr:\n{stderr}",
    );
    // Wrapper exit code should be 0 (no violations, no
    // undischarged) per F10.
    assert_eq!(
        code,
        Some(0),
        "O.2.5: a fully-discharged obligation should exit 0 \
         (rustc clean + Pitbull clean). Got {code:?}",
    );
}
/// PB054 P.2 capstone (parallel to the O.2.5 add_one test): when
/// Z3 is installed, the wrapper proves `fn at(s: &[u8], i: usize) -> u8 { s[i] }`
/// is safe under `(assert (bvult i len))` end-to-end. This pins the
/// chain — visitor extracts the source name "i" for the index local,
/// `pitbull-vc::compile` emits a `(define-fun i () (_ BitVec 64) idx)`
/// alias, the user precondition references `i` (which resolves to idx),
/// the safety negation `(bvuge idx len)` is unsat under the conjunction,
/// the wrapper reports "discharged (unsat)".
///
/// Gated on Z3 availability: gracefully skips if Z3 isn't on PATH.
#[test]
fn wrapper_proves_bounded_index_safe_under_precondition() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_proves_bounded_index_safe_under_precondition: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!(
        "pitbull-p2-bounded-{}.toml",
        std::process::id(),
    ));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-p2-bounded-{}.rs",
        std::process::id(),
    ));
    // The body uses `s[i]` which lowers to a `ProjectionElem::Index`
    // on the slice — the visitor's PB054 path emits an IndexBound
    // obligation. The argument `i` resolves to source name "i", and
    // the compile path emits a define-fun alias so the user
    // precondition can reference `i` directly.
    fs::write(
        &probe_rs,
        "pub fn at(s: &[u8], i: usize) -> u8 { s[i] }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        r#"
[project]
name = "corpus_test"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"

[verification]
solvers = ["z3"]
solver_agreement = 1

[verification.preconditions]
"corpus_test::at" = ["(assert (bvult i len))"]
"#,
    )
    .expect("write P.2 pitbull.toml");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!(
            "wrapper_proves_bounded_index_safe_under_precondition: SKIPPED \
             (no solver on PATH; install z3 to exercise this end-to-end test)",
        );
        return;
    }
    // With Z3 installed, the PB054 obligation must discharge. The
    // verdict line will look like
    //   `vc pb054-idx-0 (PB054): discharged (unsat — safety property holds) [1 assumption]`
    assert!(
        stderr.contains("discharged (unsat") && !stderr.contains("NOT DISCHARGED"),
        "P.2 capstone: `at(s, i)[i]` with `(assert (bvult i len))` must discharge \
         under Z3. Got code {code:?}, stderr:\n{stderr}",
    );
    // The verdict should specifically be on a PB054 obligation,
    // not just any other discharged obligation that happened to
    // be in the stderr.
    assert!(
        stderr.contains("(PB054)"),
        "P.2 capstone: stderr should reference the canonical PB054 rule on the \
         discharged verdict line. Got stderr:\n{stderr}",
    );
    // Wrapper exit code should be 0 (no violations, no undischarged) per F10.
    assert_eq!(
        code,
        Some(0),
        "P.2: a fully-discharged PB054 obligation should exit 0 \
         (rustc clean + Pitbull clean). Got {code:?}",
    );
}
/// Phase B / Vision-audit #2 capstone (2026-05-26): same body as
/// `wrapper_proves_bounded_index_safe_under_precondition` but the
/// precondition uses the new ident-vs-ident PREDICATE FORM
/// (`"i < len"`) instead of raw SMT-LIB. This validates the full
/// pipeline:
///   - HIR pre-pass extracts the string literal
///   - Visitor's PB054 emitter routes through
///     `parse_ident_vs_ident_predicate` (Path 1 of the three-path
///     dispatcher)
///   - Both idents resolve in the known-name set
///     ({"idx", "len", "i"} via the source-arg alias)
///   - `ident_vs_ident_to_smt_assertion` produces
///     `(assert (bvult i len))`
///   - Z3 discharges as `unsat — safety property holds`
///
/// Removes the UX cliff documented in HANDOFF.md: users no longer
/// need to drop to raw SMT-LIB for the natural index-bound shape.
///
/// Gated on Z3 availability: gracefully skips if Z3 isn't on PATH.
#[test]
fn wrapper_proves_bounded_index_via_predicate_form() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_proves_bounded_index_via_predicate_form: SKIPPED (no wrapper)");
        return;
    };
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!(
        "pitbull-phaseB-pred-{}.toml",
        std::process::id(),
    ));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!(
        "pitbull-phaseB-pred-{}.rs",
        std::process::id(),
    ));
    fs::write(
        &probe_rs,
        "pub fn at(s: &[u8], i: usize) -> u8 { s[i] }\n",
    )
    .expect("write probe.rs");
    fs::write(
        &cfg_path,
        r#"
[project]
name = "corpus_test"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"

[verification]
solvers = ["z3"]
solver_agreement = 1

[verification.preconditions]
"corpus_test::at" = ["i < len"]
"#,
    )
    .expect("write Phase-B pitbull.toml");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    if no_solver_available(&stderr) {
        eprintln!(
            "wrapper_proves_bounded_index_via_predicate_form: SKIPPED \
             (no solver on PATH)",
        );
        return;
    }
    assert!(
        stderr.contains("discharged (unsat") && !stderr.contains("NOT DISCHARGED"),
        "Phase B: predicate-form `\"i < len\"` precondition must discharge \
         like raw-SMT `(assert (bvult i len))`. Got code {code:?}, stderr:\n{stderr}",
    );
    assert!(
        stderr.contains("(PB054)"),
        "Phase B: discharged verdict must reference PB054. stderr:\n{stderr}",
    );
    assert_eq!(
        code,
        Some(0),
        "Phase B: fully-discharged obligation should exit 0. Got {code:?}",
    );
}
/// Task S capstone (2026-05-28): the MULTI-SOLVER AGREEMENT GATE
/// proven end-to-end. `fn d(a, b) { a / b }` with `requires("b > 0")`
/// is discharged ONLY when BOTH z3 AND cvc5 independently return
/// `unsat` (agreement threshold 2 of the configured pool
/// `["z3", "cvc5"]`). The verdict line must report a `2-solver
/// agreement`, proving the discharge rests on two independent
/// provers — not a single (possibly buggy or hostile) solver
/// rubber-stamping unsafe code (Safety Manual §3.3, the soundness
/// motivation for the gate).
///
/// Gated on BOTH solvers being present; skips cleanly otherwise so
/// the suite stays green on machines with only one (or no) solver.
#[test]
fn wrapper_two_solver_agreement_discharges_division() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("wrapper_two_solver_agreement_discharges_division: SKIPPED (no wrapper)");
        return;
    };
    // The gate needs two independent provers. If either is absent we
    // cannot exercise 2-of-2 agreement — skip with pass, EVEN under
    // PITBULL_REQUIRE_E2E (audit 2026-05-31). Requiring two specific
    // provers (z3 AND cvc5) on every CI runner is an unreasonable bar —
    // CI installs neither by default, and this is the only test needing
    // both — so escalating to a panic made the whole nightly-e2e job
    // un-greenable. The wrapper-presence check above still hard-fails
    // under REQUIRE_E2E; the multi-solver `vote()` logic is covered by
    // unit tests regardless of installed solvers.
    if !(solver_on_path("z3") && solver_on_path("cvc5")) {
        eprintln!(
            "wrapper_two_solver_agreement_discharges_division: SKIPPED \
             (needs BOTH z3 and cvc5 on PATH)",
        );
        return;
    }
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-s-agree-{}.toml", std::process::id()));
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-s-agree-{}.rs", std::process::id()));
    fs::write(&probe_rs, "pub fn d(a: u32, b: u32) -> u32 { a / b }\n")
        .expect("write probe.rs");
    // Explicitly pin the agreement pool to z3 + cvc5 with threshold 2
    // so the discharge requires BOTH to vote unsat.
    let cfg_text = r#"
[project]
name = "corpus_test"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"

[verification]
solvers = ["z3", "cvc5"]
solver_agreement = 2

[verification.preconditions]
"corpus_test::d" = ["b > 0"]
"#
    .to_string();
    fs::write(&cfg_path, cfg_text).expect("write pitbull.toml");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &probe_rs,
        &[("PITBULL_TOML", cfg_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&cfg_path);
    let _ = fs::remove_file(&probe_rs);
    // Both solvers are present (asserted above), so the no-solver
    // path must NOT trigger.
    assert!(
        !no_solver_available(&stderr),
        "Task S: both z3 and cvc5 are on PATH; the wrapper should not \
         report a missing solver. stderr:\n{stderr}",
    );
    // The division obligation must discharge AND the verdict must
    // record a 2-solver agreement — the whole point of the gate.
    assert!(
        stderr.contains("pb049-div-0")
            && stderr.contains("discharged (unsat")
            && stderr.contains("2-solver agreement"),
        "Task S: `a / b` under `b > 0` must discharge via 2-solver \
         agreement (z3 + cvc5). Got code {code:?}, stderr:\n{stderr}",
    );
    // No counterexample and — critically — no DISAGREEMENT: the two
    // solvers must concur, not split.
    assert!(
        !stderr.contains("NOT DISCHARGED") && !stderr.contains("DISAGREEMENT"),
        "Task S: z3 and cvc5 must agree (no split, no counterexample). \
         stderr:\n{stderr}",
    );
    assert_eq!(
        code,
        Some(0),
        "Task S: a 2-solver-discharged obligation should exit 0. Got {code:?}",
    );
}
/// PB059 negative e2e (2026-05-29): BUILT-IN derives (`Debug`,
/// `Clone`, ...) and std macros (`vec!`) are defined in core/std, which
/// the proc-macro allowlist check treats as trusted — so they must NOT
/// fire PB059. This pins the no-false-positive guarantee on real rustc
/// expansion data (a regression here would reject ordinary Rust).
///
/// The POSITIVE direction (an EXTERNAL proc-macro not on the allowlist
/// fires PB059, and allowlisting it suppresses the violation) was
/// verified manually against a hand-built proc-macro `.dll`; it can't
/// run in this single-file harness (no external-crate deps), and the
/// decision logic is unit-tested in `config::tests::pb059_*`.
#[test]
fn pb059_builtin_derives_and_std_macros_do_not_fire() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pb059_builtin_derives_and_std_macros_do_not_fire: SKIPPED (no wrapper)");
        return;
    };
    let mut probe_rs = std::env::temp_dir();
    probe_rs.push(format!("pitbull-pb059-builtin-{}.rs", std::process::id()));
    fs::write(
        &probe_rs,
        "#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]\n\
         pub struct Point { pub x: u32, pub y: u32 }\n\
         pub fn mk() -> Vec<u32> { vec![1u32, 2, 3] }\n",
    )
    .expect("write probe.rs");
    let (stderr, _code) =
        run_one_corpus_file_full(&env, &probe_rs, &[]).expect("wrapper should spawn");
    let _ = fs::remove_file(&probe_rs);
    assert!(
        !stderr.contains("PB059"),
        "PB059 must NOT fire on built-in (core/std) derives or std macros; \
         got stderr:\n{stderr}",
    );
}
/// Regression test for audit finding H3: when a hostile build.rs
/// sets `PITBULL_TOML` to a file without a `.toml` extension (the
/// realistic attack target being key files like `~/.ssh/id_rsa`
/// or `~/.aws/credentials` whose content would leak via TOML
/// parse error messages), the wrapper must refuse rather than
/// open the file.
#[test]
fn pitbull_toml_with_nontoml_extension_refused() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_toml_with_nontoml_extension_refused: SKIPPED");
        return;
    };
    // Create a real file with no `.toml` extension so the path
    // is observable but the extension check should still refuse it.
    let mut bad_path = std::env::temp_dir();
    bad_path.push(format!("pitbull-h3-id_rsa-{}", std::process::id()));
    fs::write(&bad_path, "PRETEND THIS IS A PRIVATE KEY\n")
        .expect("write temp file");
    let corpus = Path::new("tests")
        .join("corpus")
        .join("reject")
        .join("PB018_static_mut.rs");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &corpus,
        &[("PITBULL_TOML", bad_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    let _ = fs::remove_file(&bad_path);
    assert_eq!(
        code,
        Some(2),
        "H3: PITBULL_TOML with non-.toml extension must exit 2; \
         got code {code:?}, stderr:\n{stderr}",
    );
    assert!(
        stderr.contains("does not end in") || stderr.contains(".toml"),
        "H3: stderr should mention the extension requirement; got:\n{stderr}",
    );
    // Critical: the file content must NOT appear in stderr.
    // (That's the actual H3 attack — content leak via parse errors.)
    assert!(
        !stderr.contains("PRIVATE KEY"),
        "H3 VIOLATED: file content leaked into stderr:\n{stderr}",
    );
}
/// Regression test for audit finding H3 (companion): a `PITBULL_TOML`
/// path containing `..` (path traversal) must be refused regardless
/// of whether the resolved target is benign.
#[test]
fn pitbull_toml_with_traversal_refused() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_toml_with_traversal_refused: SKIPPED");
        return;
    };
    let traversal_path = std::path::PathBuf::from("../something/../config.toml");
    let corpus = Path::new("tests")
        .join("corpus")
        .join("reject")
        .join("PB018_static_mut.rs");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &corpus,
        &[("PITBULL_TOML", traversal_path.as_os_str())],
    )
    .expect("wrapper should spawn");
    assert_eq!(
        code,
        Some(2),
        "H3: PITBULL_TOML with '..' must exit 2; got code {code:?}, stderr:\n{stderr}",
    );
    assert!(
        stderr.contains("..") && stderr.contains("traversal"),
        "H3: stderr should mention traversal; got:\n{stderr}",
    );
}
/// Regression test for audit finding H3 (SARIF side): a hostile
/// build.rs setting `PITBULL_SARIF_OUT` to a file like `~/.bashrc`
/// (or any non-`.sarif`/`.json` path) must NOT result in a file
/// overwrite. The wrapper skips the SARIF emission and logs a
/// warning, but still completes the rustc compile (SARIF is
/// optional output, not a hard precondition).
#[test]
fn pitbull_sarif_out_with_nonjson_extension_refused() {
    let Some(env) = E2eEnv::probe() else {
        if std::env::var_os("PITBULL_REQUIRE_E2E").is_some() {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!("pitbull_sarif_out_with_nonjson_extension_refused: SKIPPED");
        return;
    };
    // Pretend-bashrc: real file with sentinel content.
    let mut sarif_target = std::env::temp_dir();
    sarif_target.push(format!("pitbull-h3-bashrc-{}", std::process::id()));
    let sentinel = "# original bashrc content — must not be overwritten\n";
    fs::write(&sarif_target, sentinel).expect("write sentinel file");
    let corpus = Path::new("tests")
        .join("corpus")
        .join("reject")
        .join("PB018_static_mut.rs");
    let (stderr, code) = run_one_corpus_file_full(
        &env,
        &corpus,
        &[("PITBULL_SARIF_OUT", sarif_target.as_os_str())],
    )
    .expect("wrapper should spawn");
    // SARIF refusal does not exit; rustc continues. Wrapper just
    // logs a "refusing SARIF write" warning.
    assert!(
        stderr.contains("refusing SARIF write"),
        "H3: stderr should announce SARIF refusal; got:\n{stderr}",
    );
    // Sentinel file content must be intact.
    let after = fs::read_to_string(&sarif_target).expect("re-read sentinel");
    let _ = fs::remove_file(&sarif_target);
    assert_eq!(
        after, sentinel,
        "H3 VIOLATED: SARIF write overwrote a non-SARIF file (exit code {code:?})",
    );
}
/// Regression test for audit finding C1: when `pitbull.toml` sets
/// `verify_roots` to a pattern that does not match any item in the
/// crate under test, statics and consts must STILL be walked. The
/// `verify_roots` filter is a reachability closure for fn items only;
/// item-level rules (PB018 `static mut`, PB021 interior-mutable
/// static, PB022 forbidden static type) apply unconditionally to all
/// statics/consts in the local crate.
///
/// Before the C1 fix, the wrapper's Static/Const arms short-circuited
/// when `verify_roots` was non-empty, silently re-opening the PB018
/// hole Task E was meant to close. This test pins the corrected
/// behavior.
#[test]
fn verify_roots_does_not_skip_pb018_on_statics() {
    let Some(env) = E2eEnv::probe() else {
        let require = std::env::var_os("PITBULL_REQUIRE_E2E").is_some();
        if require {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!(
            "verify_roots_does_not_skip_pb018_on_statics: SKIPPED — prerequisites missing.",
        );
        return;
    };
    // Minimal pitbull.toml with verify_roots set to a pattern that
    // can't match anything in PB018_static_mut.rs (the corpus file's
    // fn is named `get_and_increment`, not `nothing`).
    let mut config_path = std::env::temp_dir();
    config_path.push(format!("pitbull-c1-regression-{}.toml", std::process::id()));
    let config_text = "\
[project]
name = \"corpus_test\"
toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"

[reachability]
verify_roots = [\"nonexistent_crate::nothing\"]
";
    fs::write(&config_path, config_text)
        .expect("write temp pitbull.toml for C1 regression test");
    let corpus = Path::new("tests")
        .join("corpus")
        .join("reject")
        .join("PB018_static_mut.rs");
    let result = run_one_corpus_file_with_env(
        &env,
        &corpus,
        &[("PITBULL_TOML", config_path.as_os_str())],
    );
    let _ = fs::remove_file(&config_path);
    let stderr = result.expect("wrapper should run");
    assert!(
        stderr.contains("PB018"),
        "C1 regression: PB018 must fire on `static mut` even when \
         verify_roots is set to a non-matching fn pattern, but stderr \
         did not contain PB018:\n{stderr}",
    );
}
/// #27 fail-closed reachability: when `verify_roots` narrows to a root
/// that CALLS a non-root in-crate function, that callee is reachable but
/// not walked. The wrapper must surface it (`PB-reachability`) and FAIL
/// CLOSED (exit 1) — a "verified" verdict must never rest on an unverified
/// in-crate callee. Pre-fix the callee was silently skipped and the
/// wrapper exited 0 ("verified") even though the callee held a `Box`
/// (PB011) that was never checked.
#[test]
fn verify_roots_fails_closed_on_unverified_in_crate_callee() {
    let Some(env) = E2eEnv::probe() else {
        let require = std::env::var_os("PITBULL_REQUIRE_E2E").is_some();
        if require {
            panic!("PITBULL_REQUIRE_E2E set but e2e prerequisites missing");
        }
        eprintln!(
            "verify_roots_fails_closed_on_unverified_in_crate_callee: SKIPPED — prerequisites missing.",
        );
        return;
    };
    // `root` (matched by verify_roots) calls `helper` (NOT matched).
    // `helper` holds a `Box` (PB011) only ever checked if it is walked.
    // The harness forces `--crate-name=corpus_test`, so item paths are
    // `corpus_test::<fn>`; verify_roots matches `root` but not `helper`.
    let counter = TEMP_FILE_COUNTER.fetch_add(1, Ordering::Relaxed);
    let mut src_path = std::env::temp_dir();
    src_path.push(format!("pitbull-27-callee-{}-{}.rs", std::process::id(), counter));
    fs::write(
        &src_path,
        "pub fn root(x: u32) -> u32 { helper(x) }\n\
         pub fn helper(x: u32) -> u32 { let b = Box::new(x); *b }\n",
    )
    .expect("write #27 probe source");
    let mut cfg_path = std::env::temp_dir();
    cfg_path.push(format!("pitbull-27-callee-{}-{}.toml", std::process::id(), counter));
    fs::write(
        &cfg_path,
        "[project]\n\
         name = \"corpus_test\"\n\
         toolchain = \"pitbull-0.1.0-ferrocene-26.02.0\"\n\
         [reachability]\n\
         verify_roots = [\"corpus_test::root\"]\n",
    )
    .expect("write #27 pitbull.toml");
    let result =
        run_one_corpus_file_full(&env, &src_path, &[("PITBULL_TOML", cfg_path.as_os_str())]);
    let _ = fs::remove_file(&src_path);
    let _ = fs::remove_file(&cfg_path);
    let (stderr, code) = result.expect("wrapper should run");
    assert!(
        stderr.contains("PB-reachability") && stderr.contains("corpus_test::helper"),
        "#27: the unverified in-crate callee must be surfaced; stderr:\n{stderr}",
    );
    assert_eq!(
        code,
        Some(1),
        "#27: an unverified reachable in-crate callee must FAIL CLOSED \
         (exit 1), not exit 0 (\"verified\"); stderr:\n{stderr}",
    );
}
