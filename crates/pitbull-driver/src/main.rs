//! # `cargo pitbull`
//!
//! The Pitbull verifier's user-facing entry point.
//!
//! ## Subcommand structure
//!
//! - `cargo pitbull check`   — run subset checking only (fast, the
//!                              v0.1 demo path).
//! - `cargo pitbull verify`  — run subset + translation + SMT
//!                              (full pipeline, lands in subsequent
//!                              milestones).
//! - `cargo pitbull replay`  — re-execute committed proof certificates
//!                              against current solver binaries.
//! - `cargo pitbull rules`   — print the rule registry as JSON, for
//!                              tooling and audit scripts.
//!
//! v0.1 ships `check`, `rules`, and a stub `verify` that delegates to
//! `check` plus a warning that translation is still in development.
//!
//! ## Exit codes
//!
//! - `0`  — clean verification.
//! - `1`  — PSS-1 subset violations found.
//! - `2`  — verification could not run (config invalid, MIR unavailable,
//!          solver unreachable).
//! - `3`  — internal error (panic, ICE).
//!
//! These map to the SARIF-consumer conventions used by GitHub
//! code-scanning and similar tools.
use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use std::path::PathBuf;
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
    Check,
    /// Run the full pipeline (subset + translation + SMT). Stub in v0.1.
    Verify,
    /// Re-execute committed proof certificates.
    Replay,
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
    match cli.cmd {
        Cmd::Check => run_check(&cli),
        Cmd::Verify => run_verify_stub(&cli),
        Cmd::Replay => run_replay_stub(&cli),
        Cmd::Rules => run_rules(&cli),
    }
}
fn run_check(cli: &Cli) -> Result<ExitCode> {
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
    eprintln!("pitbull check: invoking cargo check with RUSTC_WORKSPACE_WRAPPER={}", wrapper.display());
    let status = std::process::Command::new("cargo")
        .arg("check")
        .arg("--all-targets")
        .env("RUSTC_WORKSPACE_WRAPPER", &wrapper)
        .status()
        .context("spawning `cargo check` with pitbull-rustc as the rustc wrapper")?;
    if status.success() {
        eprintln!("pitbull check: configuration OK; analysis pass exited cleanly");
        Ok(ExitCode::from(0))
    } else {
        // Exit code 1 = subset violations / analysis failures.
        // Exit code 2+ = wrapper not yet active (stub mode), or compile
        // failure unrelated to Pitbull. We don't currently distinguish
        // these — that's part of the next driver-wiring chunk.
        Ok(ExitCode::from(1))
    }
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
    run_check(cli)
}
fn run_replay_stub(_cli: &Cli) -> Result<ExitCode> {
    eprintln!("pitbull replay: certificate replay arrives with v0.2 translation backend.");
    Ok(ExitCode::from(0))
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
}
