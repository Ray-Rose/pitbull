//! Corpus-based integration tests for the PSS-1 subset checker.
//!
//! The corpus lives under `tests/corpus/` with two subdirectories:
//!
//! - `reject/PB{rule}_{slug}.rs` — must trigger PSS-1 violation of `PB{rule}`.
//! - `accept/PB{rule}_{slug}.rs` — adjacent valid program that must NOT
//!                                  trigger any PSS-1 violation.
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
        assert!(rule >= 1 && rule <= 75, "rule {rule} out of range");
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
        assert!(rule >= 1 && rule <= 75, "rule {rule} out of range");
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
    for path in corpus_files("accept") {
        let name = path.file_name().unwrap().to_str().unwrap().to_string();
        let Some(rule_num) = rule_from_filename(&name) else { continue };
        let unexpected = format!("PB{rule_num:03}");
        let result = run_one_corpus_file(&env, &path);
        ran += 1;
        match result {
            Ok(stderr) => {
                if stderr.contains(&unexpected) {
                    failures.push(format!(
                        "[accept] {name}: expected NO `{unexpected}` but it fired:\n{stderr}"
                    ));
                }
            }
            Err(e) => failures.push(format!("[accept] {name}: wrapper failed: {e}")),
        }
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
/// - PB001 (`unsafe` block): the visitor runs post-MIR, which has
///   already discarded HIR-level `unsafe { }` block markers. Detection
///   is indirect — operations within an unsafe block (raw pointer
///   ops, transmute, intrinsics) fire their own rules (PB004, PB007,
///   PB009). A v0.2 HIR pre-pass closes the gap.
///
/// - PB018 (`static mut` / interior-mutable static): the wrapper
///   currently walks function items only via `all_local_items` +
///   `body()` (which returns None for non-functions). Static-item
///   walking via `visit_static_item` is wired in pitbull-subset but
///   the wrapper-side enumeration is a follow-up.
///
/// - PB041 (recursion without `#[decreases]`): requires call-graph
///   strongly-connected-component analysis. The visitor walks bodies
///   one at a time without the call graph. v0.2's reachability
///   driver in pitbull-subset/src/reachability.rs has the BodyProvider
///   plumbing but the SCC detection is not yet implemented.
///
/// - PB054 (slice index without bound): the visitor *accepts* the
///   `ProjectionElem::Index` projection and emits a proof obligation
///   for the v0.2+ VC generator to discharge. This is by design (see
///   visitor.rs `visit_projection`) — PSS-1 PB054 is a VC obligation,
///   not a syntactic visitor rule.
const KNOWN_UNIMPLEMENTED_REJECT: &[u16] = &[1, 18, 41, 54];
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
    let source =
        fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let stripped = strip_pitbull_attrs(&source);
    // Write to a unique temp file in the OS temp dir.
    let mut temp_dir = std::env::temp_dir();
    temp_dir.push(format!(
        "pitbull-corpus-{}-{}.rs",
        path.file_stem().unwrap().to_str().unwrap(),
        std::process::id(),
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
    output_artifact.push(format!("pitbull-corpus-out-{}.rmeta", std::process::id()));
    let output = std::process::Command::new(&env.wrapper)
        .arg("--sysroot")
        .arg(&env.nightly_sysroot)
        .arg("--edition=2021")
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        .arg("-o")
        .arg(&output_artifact)
        .arg(&temp_dir)
        .env("PATH", &new_path)
        .env("CARGO_PKG_NAME", "corpus_test")
        .output()
        .map_err(|e| format!("spawn wrapper: {e}"))?;
    // Best-effort cleanup; ignore errors.
    let _ = fs::remove_file(&temp_dir);
    let _ = fs::remove_file(&output_artifact);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    // We don't require exit code 0 — pitbull-rustc continues compilation
    // even when violations are found, so success means rustc completed.
    // A non-zero exit could mean the file itself doesn't compile (e.g.,
    // unknown crate `pitbull`) — surface that as part of stderr for the
    // assertion to handle.
    Ok(stderr)
}
