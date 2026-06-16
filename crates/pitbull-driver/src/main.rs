//! # `cargo pitbull`
//!
//! The Pitbull verifier's user-facing entry point.
//!
//! ## Subcommand structure
//!
//! - `cargo pitbull check`   — run subset checking only (fast, the
//!   v0.1 demo path).
//! - `cargo pitbull verify`  — run subset + translation + SMT
//!   (full pipeline, lands in subsequent milestones).
//! - `cargo pitbull replay`  — re-execute committed proof certificates
//!   against current solver binaries.
//! - `cargo pitbull rules`   — print the rule registry as JSON, for
//!   tooling and audit scripts.
//!
//! v0.1 ships `check`, `rules`, and a stub `verify` that delegates to
//! `check` plus a warning that translation is still in development.
//! `replay` is functional (Task T.2): it re-executes a proof
//! certificate produced by `check` (with `PITBULL_CERT_OUT` set) and
//! confirms each recorded agreement verdict reproduces — on stable
//! Rust, no nightly toolchain required.
//!
//! ## Exit codes
//!
//! - `0`  — clean verification.
//! - `1`  — PSS-1 subset violations found.
//! - `2`  — verification could not run (config invalid, MIR unavailable,
//!   solver unreachable).
//! - `3`  — internal error (panic, ICE).
//!
//! These map to the SARIF-consumer conventions used by GitHub
//! code-scanning and similar tools.
// Defense-in-depth (red-team F8): no unsafe in the cargo
// subcommand. It only orchestrates rustc, parses configs, and
// renders reports — all of which is safe Rust. Forbidding here
// makes a future refactor that adds unsafe a hard compile error.
#![forbid(unsafe_code)]
use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
#[derive(Parser, Debug)]
#[command(
    name = "cargo-pitbull",
    bin_name = "cargo pitbull",
    version,
    about = "Deductive verifier for Rust (SPARK-style)",
    long_about = None,
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
    /// Path to `pitbull.toml`. Defaults to crate-root-relative discovery.
    #[arg(long, global = true)]
    config: Option<PathBuf>,
    /// Emit machine-readable JSON instead of human-formatted output.
    #[arg(long, global = true)]
    json: bool,
}
#[derive(Subcommand, Debug)]
enum Cmd {
    /// Run PSS-1 subset enforcement.
    Check {
        /// Fail closed if any workspace crate was served from a warm cargo
        /// cache and not re-analyzed this run (its cross-crate coverage would
        /// otherwise be reported INDETERMINATE rather than failing). Use in
        /// CI / qualification — after `cargo clean` — for a complete
        /// whole-workspace verdict (2026-06-15 deep audit, F4).
        #[arg(long)]
        strict: bool,
    },
    /// Run the full pipeline (subset + translation + SMT). Stub in v0.1.
    Verify,
    /// Re-execute a committed proof certificate: re-run each recorded
    /// SMT problem through the solver pool and confirm the agreement
    /// verdict reproduces. Exits 1 if any obligation fails to reproduce.
    Replay {
        /// Path to the proof-certificate JSON (produced by
        /// `cargo pitbull check` with `PITBULL_CERT_OUT` set).
        cert: PathBuf,
    },
    /// Print the rule registry.
    Rules,
}
fn main() -> ExitCode {
    let cli = Cli::parse();
    match dispatch(cli) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("pitbull: {e:#}");
            ExitCode::from(2)
        }
    }
}
fn dispatch(cli: Cli) -> Result<ExitCode> {
    // Match by reference so the `Replay { cert }` arm can borrow the
    // path without partially moving `cli` (the run_* helpers take
    // `&cli`).
    match &cli.cmd {
        Cmd::Check { strict } => run_check(&cli, *strict),
        Cmd::Verify => run_verify_stub(&cli),
        Cmd::Replay { cert } => run_replay(&cli, cert),
        Cmd::Rules => run_rules(&cli),
    }
}
fn run_check(cli: &Cli, strict: bool) -> Result<ExitCode> {
    let cfg_path = cli.config.clone().unwrap_or_else(|| PathBuf::from("pitbull.toml"));
    let outcome = pitbull_subset::SubsetConfig::load_and_validate(&cfg_path)
        .with_context(|| format!("loading {}", cfg_path.display()))?;
    // Config-level errors are reported and then we proceed to the MIR walk;
    // we want users to see all problems in one shot.
    if !outcome.errors.is_empty() {
        for err in &outcome.errors {
            eprintln!("pitbull: {err}");
        }
    }
    if !outcome.errors.is_empty() {
        eprintln!("pitbull check: {} configuration violation(s)", outcome.errors.len());
        return Ok(ExitCode::from(1));
    }
    // Hand off to the rustc wrapper for the actual MIR walk. We invoke
    // cargo with `RUSTC_WORKSPACE_WRAPPER` set to our wrapper binary's
    // absolute path; cargo then calls the wrapper instead of `rustc`
    // for every compile unit in the target workspace, and the wrapper
    // injects the Pitbull subset-check pass after MIR generation via
    // `rustc_driver::Callbacks`.
    //
    // The wrapper itself only does meaningful work on a nightly build
    // with PITBULL_USE_RUSTC_PUBLIC=1 set. On stable, the wrapper is a
    // stub that exits 1 with a diagnostic — which causes cargo's compile
    // to fail on the first crate, and the user sees the wrapper's
    // explanation. That is a calibrated UX choice: rather than silently
    // skipping the analysis, we make the missing capability obvious.
    let wrapper = locate_wrapper()
        .context("locating pitbull-rustc wrapper binary")?;
    // Resolve pitbull.toml to an absolute path and pass it via env var
    // so the wrapper sees the user's config no matter which package
    // cargo is currently compiling. Cargo runs each rustc invocation
    // with CWD set to the package being compiled — for dependencies
    // that's the registry cache, not the user's project root. Without
    // an absolute PITBULL_TOML the wrapper would only see the user's
    // config on the user's own crate compile.
    let pitbull_toml_abs = std::fs::canonicalize(&cfg_path)
        .with_context(|| format!("canonicalizing {}", cfg_path.display()))?;
    // Cross-crate reachability aggregation. Each per-crate wrapper run only
    // sees its own crate (the #27 gate's universe is local), so a verified
    // root that calls into another WORKSPACE crate whose own verify_roots
    // narrowing skipped that entry slips past both crates' local gates. We
    // have every wrapper run emit a reachability manifest into a fresh dir,
    // then verify the WHOLE-workspace closure here (SAFETY-MANUAL §3.6).
    let manifest_dir = std::env::temp_dir().join(format!("pitbull-reach-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&manifest_dir); // clear any stale run
    std::fs::create_dir_all(&manifest_dir)
        .with_context(|| format!("creating reachability manifest dir {}", manifest_dir.display()))?;
    eprintln!("pitbull check: invoking cargo check with RUSTC_WORKSPACE_WRAPPER={}", wrapper.display());
    eprintln!("pitbull check: PITBULL_TOML={}", pitbull_toml_abs.display());
    let status = std::process::Command::new("cargo")
        .arg("check")
        .arg("--all-targets")
        .env("RUSTC_WORKSPACE_WRAPPER", &wrapper)
        .env("PITBULL_TOML", &pitbull_toml_abs)
        .env("PITBULL_REACH_DIR", &manifest_dir)
        .status()
        .context("spawning `cargo check` with pitbull-rustc as the rustc wrapper")?;
    // Aggregate the per-crate manifests into the whole-workspace gate. This
    // is best-effort: if cargo metadata or the manifests can't be read we
    // warn and fall back to the per-crate verdict (cargo's exit status),
    // never silently claiming a stronger guarantee than we verified.
    // Read the manifests ONCE (before the dir is removed): their presence is
    // also the signal for "did analysis actually run this invocation?" (F5).
    let manifests = read_manifests(&manifest_dir);
    let manifests_present = !manifests.is_empty();
    let cross_crate_failed = run_cross_crate_gate(&manifests, strict);
    let _ = std::fs::remove_dir_all(&manifest_dir);
    // Exit-code fidelity (2026-06-15 deep audit, F5): distinguish
    // "could-not-run" (exit 2) from "found problems" (exit 1). The historic
    // code collapsed every non-success to 1, so a stable build with no
    // nightly wrapper (analysis never ran) looked identical to "violations
    // found". If cargo failed AND no crate emitted a reachability manifest,
    // the analysis pass did not run — surface that as exit 2.
    let code = check_exit_code(status.success(), cross_crate_failed, manifests_present);
    match code {
        0 => eprintln!("pitbull check: configuration OK; analysis pass exited cleanly"),
        2 => eprintln!(
            "pitbull check: COULD NOT RUN (exit 2) — cargo failed and no crate emitted a \
             reachability manifest, so the Pitbull analysis pass did not run. The nightly \
             `pitbull-rustc` wrapper is probably not active (stable build = stub) or it \
             failed before analysis. This is NOT a clean verification; see HANDOFF §3-4 to \
             enable the wrapper.",
        ),
        _ => eprintln!(
            "pitbull check: NOT VERIFIED (exit 1) — subset violations, undischarged \
             obligations, or a cross-crate reachability gap.",
        ),
    }
    Ok(ExitCode::from(code))
}
/// Pure exit decision for `cargo pitbull check` (2026-06-15 deep audit, F5).
/// Distinguishes the three CI-relevant outcomes instead of collapsing every
/// non-success to 1: `0` clean, `2` could-not-run (cargo failed AND no
/// manifest was emitted — the analysis pass never ran), else `1` not-verified
/// (violations / undischarged / a cross-crate gap, incl. `--strict`'s
/// cache-incomplete coverage). Pure so the decision is unit-testable.
fn check_exit_code(cargo_success: bool, cross_crate_failed: bool, manifests_present: bool) -> u8 {
    if cargo_success && !cross_crate_failed {
        0
    } else if !cargo_success && !manifests_present {
        2
    } else {
        1
    }
}
/// Read every per-crate reachability manifest, resolve the workspace member
/// crate names, and run the whole-workspace cross-crate gate. Returns
/// `true` iff a workspace-member callee reachable from a verified root was
/// left unverified by EVERY crate's run (a fail-closed cross-crate gap).
///
/// Best-effort and fail-SAFE in the reporting direction: any failure to
/// gather inputs (cargo metadata error, unreadable manifests) is a warning
/// and returns `false` — the per-crate gates already ran inside the wrapper
/// and contribute to cargo's exit status; this layer only ADDS the
/// cross-crate check on top.
fn run_cross_crate_gate(
    manifests: &[pitbull_subset::reachability::ReachManifest],
    strict: bool,
) -> bool {
    let workspace = match workspace_crate_names() {
        Ok(w) => w,
        Err(e) => {
            eprintln!(
                "pitbull check: WARNING: `cargo metadata` failed ({e:#}); skipping the \
                 cross-crate reachability gate (per-crate gates still applied).",
            );
            return false;
        }
    };
    if manifests.is_empty() {
        // No manifests: the nightly wrapper isn't active (stable stub), or
        // cargo served everything from cache. Nothing to aggregate.
        return false;
    }
    let unverified = pitbull_subset::reachability::cross_crate_unverified(manifests, &workspace);
    let indeterminate =
        pitbull_subset::reachability::cross_crate_indeterminate(manifests, &workspace);
    for callee in &unverified {
        eprintln!(
            "pitbull check: CROSS-CRATE: workspace function `{callee}` is reachable from a \
             verified root but was NOT verified by any crate's run (skipped by some crate's \
             `verify_roots` narrowing). Add it to that crate's [reachability] verify_roots, \
             leave verify_roots empty for full-crate coverage, or mark it \
             #[pitbull::trusted]. Treating as unverified (fail-closed).",
        );
    }
    if !indeterminate.is_empty() {
        if strict {
            // F4: --strict turns warm-cache incompleteness into a hard failure.
            // cargo's freshness fingerprint does NOT include pitbull.toml or the
            // solver set, so a cached crate is silently NOT re-analyzed; a
            // qualification run must reject that rather than note it.
            eprintln!(
                "pitbull check: STRICT FAIL: {} cross-crate callee(s) had INDETERMINATE \
                 coverage — their crate was served from a warm cargo cache and not \
                 re-analyzed this run, so the whole-workspace verdict is incomplete. \
                 `--strict` requires a complete run: `cargo clean` then re-run. \
                 Failing closed.",
                indeterminate.len(),
            );
        } else {
            eprintln!(
                "pitbull check: note: {} cross-crate callee(s) had INDETERMINATE coverage — \
                 their crate was served from a warm cargo cache and not re-analyzed this \
                 run, so the cross-crate verdict is incomplete. Run a clean build (e.g. \
                 `cargo clean`), or use `--strict` to fail closed on this.",
                indeterminate.len(),
            );
        }
    }
    !unverified.is_empty() || (strict && !indeterminate.is_empty())
}
/// Resolve the set of workspace-member crate names (as they appear in
/// fully-qualified item paths: the package/target name with `-` normalized
/// to `_`). Used by the cross-crate gate to tell a workspace-member callee
/// (which MUST be verified by some crate's run) from an external one
/// (std/registry dep — the trusted boundary).
fn workspace_crate_names() -> Result<HashSet<String>> {
    let out = std::process::Command::new("cargo")
        .args(["metadata", "--no-deps", "--format-version", "1"])
        .output()
        .context("spawning `cargo metadata`")?;
    if !out.status.success() {
        anyhow::bail!("`cargo metadata` exited with status {}", out.status);
    }
    let json: serde_json::Value =
        serde_json::from_slice(&out.stdout).context("parsing `cargo metadata` JSON")?;
    let mut names = HashSet::new();
    if let Some(packages) = json["packages"].as_array() {
        for pkg in packages {
            if let Some(n) = pkg["name"].as_str() {
                names.insert(n.replace('-', "_"));
            }
            // Target names are the actual crate names (a package may set a
            // `[lib] name` different from the package name); collect those too.
            if let Some(targets) = pkg["targets"].as_array() {
                for t in targets {
                    if let Some(tn) = t["name"].as_str() {
                        names.insert(tn.replace('-', "_"));
                    }
                }
            }
        }
    }
    Ok(names)
}
/// Read every `*.json` reachability manifest in `dir`. Unreadable or
/// malformed files are skipped with a warning (a partial set only weakens
/// the gate toward more INDETERMINATE entries, never a false discharge).
fn read_manifests(dir: &Path) -> Vec<pitbull_subset::reachability::ReachManifest> {
    let mut manifests = Vec::new();
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return manifests,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("json") {
            continue;
        }
        match std::fs::read_to_string(&path) {
            Ok(text) => {
                match serde_json::from_str::<pitbull_subset::reachability::ReachManifest>(&text) {
                    Ok(m) => manifests.push(m),
                    Err(e) => eprintln!(
                        "pitbull check: WARNING: skipping malformed reachability manifest {}: {e}",
                        path.display(),
                    ),
                }
            }
            Err(e) => eprintln!(
                "pitbull check: WARNING: could not read reachability manifest {}: {e}",
                path.display(),
            ),
        }
    }
    manifests
}
/// Find the pitbull-rustc wrapper binary path.
///
/// Search order: (1) explicit `PITBULL_RUSTC_WRAPPER` env var, (2)
/// sibling of the running cargo-pitbull executable. The sibling search
/// covers the most common case (built/installed as a workspace member);
/// the env var is the escape hatch for non-standard installs.
fn locate_wrapper() -> Result<PathBuf> {
    if let Ok(p) = std::env::var("PITBULL_RUSTC_WRAPPER") {
        return Ok(PathBuf::from(p));
    }
    let me = std::env::current_exe().context("std::env::current_exe()")?;
    let dir = me
        .parent()
        .context("cargo-pitbull binary has no parent directory?!")?;
    let candidate = if cfg!(windows) {
        dir.join("pitbull-rustc.exe")
    } else {
        dir.join("pitbull-rustc")
    };
    if !candidate.exists() {
        anyhow::bail!(
            "pitbull-rustc wrapper not found at {}; \
             set PITBULL_RUSTC_WRAPPER or build with `cargo build -p pitbull-driver`",
            candidate.display()
        );
    }
    Ok(candidate)
}
fn run_verify_stub(cli: &Cli) -> Result<ExitCode> {
    eprintln!("pitbull verify: v0.1 ships subset checking only; running `check` instead.");
    eprintln!("pitbull verify: translation + SMT dispatch land in v0.2.");
    run_check(cli, false)
}
/// Re-execute a proof certificate. Reads the bundle, rebuilds the
/// solver pool from the bundle's recorded solver names, re-runs each
/// recorded SMT problem, and confirms the agreement verdict
/// reproduces. Exits 0 if every obligation reproduces, 1 if any does
/// not (solver drift, a missing solver, or a tampered certificate).
///
/// Replay runs entirely on STABLE Rust — it needs only the solvers and
/// the recorded SMT, never the nightly `rustc_public` lane — so a
/// certificate produced on one machine can be independently re-checked
/// anywhere the solvers are installed.
fn run_replay(_cli: &Cli, cert_path: &std::path::Path) -> Result<ExitCode> {
    // Bound the certificate file before slurping it: a multi-GB file
    // would otherwise be read fully into memory (local DoS). 16 MiB is
    // far above any realistic certificate (audit 2026-05-29).
    const CERT_FILE_CAP_BYTES: u64 = 16 * 1024 * 1024;
    if let Ok(meta) = std::fs::metadata(cert_path) {
        if meta.len() > CERT_FILE_CAP_BYTES {
            anyhow::bail!(
                "certificate {} is {} bytes, over the {CERT_FILE_CAP_BYTES}-byte replay cap",
                cert_path.display(),
                meta.len(),
            );
        }
    }
    let text = std::fs::read_to_string(cert_path)
        .with_context(|| format!("reading certificate {}", cert_path.display()))?;
    let bundle = pitbull_vc::cert::CertificateBundle::from_json(&text)
        .map_err(|e| anyhow::anyhow!("{e}"))?;
    eprintln!(
        "pitbull replay: {} — crate `{}`, {} obligation(s), agreement threshold {}, \
         recorded solver pool {:?}, recorded timeout {}s",
        cert_path.display(),
        bundle.crate_name,
        bundle.obligations.len(),
        bundle.threshold,
        bundle.solvers,
        bundle.timeout_seconds,
    );
    // An empty bundle is NOT a verification success — nothing was
    // re-verified. Fail closed (exit 2) so a CI gate keyed on the exit
    // code cannot be fooled by a swapped-in empty (but well-formed)
    // certificate, or by a producer that emitted zero obligations
    // (audit 2026-05-29).
    if bundle.obligations.is_empty() && bundle.uncertified.is_empty() {
        anyhow::bail!(
            "certificate contains 0 obligations — nothing to replay; refusing to report \
             success for an empty certificate",
        );
    }
    // Coverage ledger (2026-06-15 deep audit, F3): make partial coverage
    // VISIBLE so a consumer can't mistake "the listed certs reproduced" for
    // "the crate verified". `total_obligations` is the denominator;
    // `uncertified` are obligations that never reached the gate (pending /
    // consistency-refused / consistency-unconfirmed).
    let certified_discharged = bundle
        .obligations
        .iter()
        .filter(|o| o.is_discharged())
        .count();
    let certified_other = bundle.obligations.len() - certified_discharged;
    eprintln!(
        "pitbull replay: coverage — {} total obligation(s): {} discharged, {} \
         certified-but-undischarged, {} uncertified.",
        bundle.total_obligations,
        certified_discharged,
        certified_other,
        bundle.uncertified.len(),
    );
    for u in &bundle.uncertified {
        eprintln!("  UNCERTIFIED {} ({}): {}", u.id, u.rule, u.status);
    }
    // Integrity check (Task T.3) + strict-signing policy (2026-06-15 deep
    // audit, F1/F2). If PITBULL_CERT_KEY is set, verify the HMAC-SHA256
    // signature; an INVALID signature always fails closed (exit 2) before any
    // solver runs. PITBULL_REQUIRE_SIGNED additionally makes a *verified*
    // signature MANDATORY: an unsigned bundle, or a missing key, also fails
    // closed — so a CI `replay` step that forgets the key cannot silently
    // downgrade to unauthenticated replay. Without the strict flag the
    // historic warn-and-continue behavior holds for the unsigned/no-key cases.
    let require_signed = std::env::var_os("PITBULL_REQUIRE_SIGNED").is_some();
    let sig_status: Option<pitbull_vc::cert::SignatureStatus> =
        match std::env::var_os("PITBULL_CERT_KEY") {
            Some(keypath) => {
                let key = pitbull_vc::cert::read_key_file(std::path::Path::new(&keypath))
                    .map_err(|e| anyhow::anyhow!("{e}"))?;
                if key.len() < pitbull_vc::cert::MIN_RECOMMENDED_KEY_BYTES {
                    eprintln!(
                        "pitbull replay: WARNING: PITBULL_CERT_KEY is short ({} bytes); a weak \
                         key provides little tamper-resistance.",
                        key.len(),
                    );
                }
                Some(bundle.verify_signature(&key))
            }
            None => None,
        };
    match sig_status {
        Some(pitbull_vc::cert::SignatureStatus::Valid) => {
            eprintln!("pitbull replay: signature OK (HMAC-SHA256 verified).");
        }
        Some(pitbull_vc::cert::SignatureStatus::Unsigned) => {
            eprintln!(
                "pitbull replay: WARNING: certificate is UNSIGNED; re-run confirms \
                 reproduction but tampering is not detectable.",
            );
        }
        Some(pitbull_vc::cert::SignatureStatus::Invalid) => {
            // A present-but-bad signature always fails closed, strict or not.
            anyhow::bail!(
                "certificate signature is INVALID (tampered, or signed with a \
                 different key) — refusing to replay",
            );
        }
        None => {
            if bundle.is_signed() {
                eprintln!(
                    "pitbull replay: WARNING: certificate is SIGNED but no PITBULL_CERT_KEY \
                     was provided — cannot verify integrity{}.",
                    if require_signed { "" } else { "; re-running anyway" },
                );
            } else {
                eprintln!(
                    "pitbull replay: note: certificate is UNSIGNED and no key provided; \
                     integrity not checked (set PITBULL_CERT_KEY on both `check` and \
                     `replay` to enable tamper detection).",
                );
            }
        }
    }
    if !signing_policy_ok(require_signed, sig_status) {
        anyhow::bail!(
            "PITBULL_REQUIRE_SIGNED is set but this certificate is not backed by a \
             verified signature (it needs PITBULL_CERT_KEY set AND a signature that \
             verifies under it) — refusing to replay",
        );
    }
    // Rebuild the solver pool from the bundle's recorded names. Replay
    // reproduces the ORIGINAL decision, so we use the recorded pool and
    // each certificate's own recorded threshold (via `replay_bundle`).
    let mut solvers = Vec::new();
    for name in &bundle.solvers {
        match pitbull_vc::solver::known_solver(name) {
            Some(s) => solvers.push(s),
            None => eprintln!(
                "pitbull replay: WARNING: bundle references unknown solver `{name}` — \
                 it cannot be re-run, which may turn a recorded discharge into a MISMATCH.",
            ),
        }
    }
    if solvers.is_empty() {
        anyhow::bail!(
            "no usable solver from the recorded pool {:?}; install at least one of them \
             (e.g. z3, cvc5) to replay this certificate",
            bundle.solvers,
        );
    }
    // Replay under the RECORDED timeout (clamped to a sane range) so a
    // non-default original budget can't cause a spurious MISMATCH
    // (audit 2026-05-29).
    let timeout = std::time::Duration::from_secs(bundle.timeout_seconds.clamp(1, 3600));
    let outcomes = pitbull_vc::cert::replay_bundle(&bundle, &solvers, timeout);
    let mut mismatches = 0usize;
    let mut discharges_reproduced = 0usize;
    for (id, outcome) in &outcomes {
        match outcome {
            pitbull_vc::cert::ReplayOutcome::Match { verdict } => {
                if verdict == "discharged" {
                    discharges_reproduced += 1;
                }
                println!("  MATCH     {id}: reproduced `{verdict}`");
            }
            pitbull_vc::cert::ReplayOutcome::Mismatch { recorded, replayed } => {
                mismatches += 1;
                println!(
                    "  MISMATCH  {id}: recorded `{recorded}`, replayed `{replayed}`",
                );
            }
        }
    }
    let reproduced = outcomes.len() - mismatches;
    eprintln!(
        "pitbull replay: {reproduced} reproduced ({discharges_reproduced} discharge(s)), \
         {mismatches} mismatch(es), of {} obligation(s).",
        outcomes.len(),
    );
    // Scope caveat (audit 2026-05-29): replay confirms each recorded SMT
    // still reproduces its recorded verdict under the recorded pool and
    // threshold. It does NOT (yet) prove the recorded SMT corresponds to
    // the source obligation it names — binding SMT to obligation is
    // cryptographic signing (Task T.3). A clean replay (exit 0) means
    // "recorded verdicts reproduced", NOT "the code is safe".
    eprintln!(
        "pitbull replay: note — confirms recorded SMT->verdict reproduction, not that each \
         SMT matches its named obligation (that binding is signing, Task T.3); a clean \
         replay is not itself a safety claim.",
    );
    // Completeness gate (2026-06-15 deep audit, F3): a clean replay (exit 0)
    // must imply the CRATE verified, not merely that the listed certs
    // reproduce. So exit 0 requires BOTH zero mismatches AND that the bundle
    // attests full verification — its ledger adds up, nothing was left
    // uncertified, and every certificate discharged. A bundle that records
    // pending / refused / non-discharged obligations represents a crate that
    // did NOT fully verify; replay reports that and fails closed, even when
    // every recorded verdict reproduced.
    let fully = bundle.attests_full_verification();
    let code = replay_exit_code(mismatches, fully);
    if code == 0 {
        eprintln!(
            "pitbull replay: OK — all {} obligation(s) reproduced their recorded verdict \
             AND the bundle attests full verification ({} obligation(s), all discharged).",
            outcomes.len(),
            bundle.total_obligations,
        );
    } else if mismatches > 0 {
        eprintln!(
            "pitbull replay: FAILED — {mismatches} of {} obligation(s) did NOT reproduce \
             (solver drift/version skew, a missing solver, a timeout-budget change, or a \
             tampered certificate). Treat the affected proofs as UNVERIFIED.",
            outcomes.len(),
        );
    } else {
        // Every recorded verdict reproduced, but the bundle does NOT attest a
        // fully-verified crate. Fail closed: reproduction is not a safety claim.
        eprintln!(
            "pitbull replay: INCOMPLETE — every recorded verdict reproduced, but this \
             certificate does NOT attest a fully-verified crate: {certified_discharged} \
             discharged, {certified_other} certified-but-undischarged, {} uncertified, of \
             {} total obligation(s){}. A clean replay here is reproduction, not a safety \
             claim — failing closed.",
            bundle.uncertified.len(),
            bundle.total_obligations,
            if bundle.total_obligations == 0 {
                " (legacy v1 certificate without a coverage ledger; re-run `cargo pitbull \
                 check` with the current tool for a complete certificate)"
            } else {
                ""
            },
        );
    }
    Ok(ExitCode::from(code))
}
/// Pure replay exit decision (2026-06-15 deep audit, F3). A clean replay
/// (exit 0) requires BOTH that every recorded verdict reproduced
/// (`mismatches == 0`) AND that the bundle attests full verification
/// (`attests_full`: ledger consistent, nothing uncertified, all discharged).
/// Otherwise fail closed (exit 1): reproduction alone is not a safety claim,
/// and a bundle with uncertified/undischarged obligations represents a crate
/// that did not fully verify. Pure so the soundness-relevant decision is
/// unit-testable, mirroring the wrapper's `decide_pitbull_exit_code`.
/// (Load failures, an empty bundle, and an invalid signature fail closed
/// earlier with exit 2, before replay reaches this decision.)
fn replay_exit_code(mismatches: usize, attests_full: bool) -> u8 {
    if mismatches == 0 && attests_full {
        0
    } else {
        1
    }
}
/// Whether replay may proceed under the strict-signing policy (2026-06-15
/// deep audit, F1/F2). `status` is the signature verification result when a
/// key was provided, or `None` when no key was available to verify with.
/// Under `require_signed`, only a verified (`Valid`) signature proceeds —
/// unsigned, unverifiable (no key), or invalid all fail closed. Without it,
/// everything proceeds EXCEPT a present-but-`Invalid` signature, which always
/// fails closed. Pure for unit-testing.
fn signing_policy_ok(
    require_signed: bool,
    status: Option<pitbull_vc::cert::SignatureStatus>,
) -> bool {
    use pitbull_vc::cert::SignatureStatus;
    match (require_signed, status) {
        (true, Some(SignatureStatus::Valid)) => true,
        (true, _) => false, // strict: a verified signature is mandatory
        (false, Some(SignatureStatus::Invalid)) => false, // a bad sig never passes
        (false, _) => true, // lax: unsigned / unverified / valid all proceed
    }
}
fn run_rules(cli: &Cli) -> Result<ExitCode> {
    if cli.json {
        let json = serde_json::to_string_pretty(pitbull_subset::RULES)
            .context("serializing rule registry")?;
        println!("{json}");
    } else {
        println!("Pitbull {} ({} rules)\n", pitbull_subset::PSS_VERSION, pitbull_subset::RULE_COUNT);
        for rule in pitbull_subset::RULES {
            println!("{:<6} {:<20} {}", format!("{}", rule.id), format!("{:?}", rule.category), rule.title);
        }
    }
    Ok(ExitCode::from(0))
}
#[cfg(test)]
mod tests {
    // Most driver behavior is integration-tested via the
    // `tests/integration.rs` corpus. Unit tests here cover the
    // arg-parsing surface.
    use super::*;
    use clap::CommandFactory;
    #[test]
    fn cli_parses() {
        Cli::command().debug_assert();
    }
    /// F3 completeness gate: a clean replay (exit 0) requires BOTH no
    /// mismatches AND full-verification attestation. Reproduction alone, or
    /// full coverage with a mismatch, must fail closed (exit 1).
    #[test]
    fn replay_exit_code_requires_reproduction_and_completeness() {
        assert_eq!(replay_exit_code(0, true), 0, "reproduced + complete → ok");
        assert_eq!(replay_exit_code(1, true), 1, "a mismatch fails even if complete");
        assert_eq!(
            replay_exit_code(0, false), 1,
            "reproduced but INCOMPLETE coverage must fail closed (the F3 fix)",
        );
        assert_eq!(replay_exit_code(3, false), 1);
    }
    /// F1/F2 strict signing: under `PITBULL_REQUIRE_SIGNED` only a verified
    /// signature proceeds; without it, everything proceeds except a
    /// present-but-invalid signature.
    #[test]
    fn signing_policy_strict_requires_valid_signature() {
        use pitbull_vc::cert::SignatureStatus::{Invalid, Unsigned, Valid};
        // Strict: only a verified signature passes.
        assert!(signing_policy_ok(true, Some(Valid)));
        assert!(!signing_policy_ok(true, Some(Unsigned)));
        assert!(!signing_policy_ok(true, Some(Invalid)));
        assert!(!signing_policy_ok(true, None), "strict + no key must fail closed");
        // Lax: proceed unless the signature is present-but-invalid.
        assert!(signing_policy_ok(false, Some(Valid)));
        assert!(signing_policy_ok(false, Some(Unsigned)));
        assert!(signing_policy_ok(false, None));
        assert!(!signing_policy_ok(false, Some(Invalid)), "a bad sig always fails");
    }
    /// F5 exit fidelity: `check` distinguishes could-not-run (2) from
    /// not-verified (1) and clean (0), instead of collapsing all non-success
    /// to 1.
    #[test]
    fn check_exit_code_distinguishes_couldnt_run_from_violations() {
        // Clean: cargo ok, no cross-crate failure (manifest presence moot).
        assert_eq!(check_exit_code(true, false, true), 0);
        assert_eq!(check_exit_code(true, false, false), 0);
        // A cross-crate gap even on a clean cargo build → not verified.
        assert_eq!(check_exit_code(true, true, true), 1);
        // cargo failed but analysis ran (manifests present) → violations.
        assert_eq!(check_exit_code(false, false, true), 1);
        // cargo failed AND no manifest emitted → analysis could not run.
        assert_eq!(check_exit_code(false, false, false), 2);
    }
}
