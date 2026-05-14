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
    // Real MIR ingestion would happen here, behind `rustc_public`. The v0.1
    // skeleton's `check` command exits with the config validation result
    // alone; the body walk lands when the driver wires up rustc as a
    // library.
    let exit = if outcome.errors.is_empty() {
        eprintln!("pitbull check: configuration OK; MIR-level checks pending wiring");
        ExitCode::from(0)
    } else {
        eprintln!("pitbull check: {} configuration violation(s)", outcome.errors.len());
        ExitCode::from(1)
    };
    Ok(exit)
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
