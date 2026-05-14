//! `pitbull-subset` build script.
//!
//! ## What this does
//!
//! Sets the `--cfg rustc_public_real` rustc flag *only* when the developer
//! explicitly opts in via the `PITBULL_USE_RUSTC_PUBLIC=1` environment
//! variable AND the active rustc is a nightly toolchain. By default, this
//! script does nothing and the crate compiles with the shadow MIR types
//! defined in `src/mir_api.rs` — preserving the v0.1 stable-Rust build.
//!
//! ## Why opt-in via env var rather than auto-detect
//!
//! - The shadow build is the default everyone gets, including stable Rust
//!   users running `cargo check`. Auto-detecting nightly would silently
//!   change behavior depending on the developer's toolchain — surprising
//!   and audit-hostile.
//! - Cargo features can't gate `extern crate rustc_public;` because that
//!   crate is only available via the `rustc_private` mechanism on nightly,
//!   which means a feature requiring it would break `cargo check
//!   --all-features` on stable. (See the `Cargo.toml` comment block.)
//! - Env-var opt-in is reversible per-build with no source changes:
//!   `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 check`.
//!
//! ## Cfg declaration
//!
//! The custom cfg name `rustc_public_real` is declared in the workspace
//! `Cargo.toml` under `[workspace.lints.rust]` so rustc's `--check-cfg`
//! warning system knows it's intentional. We re-declare it here as a
//! defense-in-depth measure for one-shot builds that don't pick up the
//! workspace lints.
//!
//! ## What's NOT done here
//!
//! This script only sets the cfg flag. It does not arrange for
//! `extern crate rustc_public` to be findable — that requires the consuming
//! crate to declare `#![feature(rustc_private)]` and depend on the rustc
//! sysroot's libraries, which is a per-source-file concern handled in
//! `src/mir_api.rs` under `#[cfg(rustc_public_real)]`.
fn main() {
    // Always re-run if the env var or this script changes.
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=PITBULL_USE_RUSTC_PUBLIC");
    // Declare the custom cfg so rustc doesn't emit `unexpected_cfgs`.
    // Defense in depth — the workspace `Cargo.toml` already declares this
    // in `[workspace.lints.rust]`, but build scripts can't always rely on
    // that being applied (e.g., `cargo build -p pitbull-subset` from
    // outside the workspace root).
    println!("cargo:rustc-check-cfg=cfg(rustc_public_real)");
    // Default path: emit nothing. The shadow MIR types in `src/mir_api.rs`
    // carry the build, the workspace tests pass on stable Rust, the v0.1
    // baseline is unchanged.
    let opted_in = std::env::var_os("PITBULL_USE_RUSTC_PUBLIC").is_some();
    if !opted_in {
        return;
    }
    // Opt-in path: verify we're on a nightly toolchain. `rustc_public` is
    // exposed only via the `rustc_private` mechanism, which requires a
    // nightly compiler (or a stable compiler with `RUSTC_BOOTSTRAP=1`,
    // which we deliberately do not support — bootstrap mode is for
    // compiler developers, not Pitbull users).
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let output = std::process::Command::new(&rustc)
        .arg("--version")
        .arg("--verbose")
        .output()
        .expect("running `rustc --version --verbose` for nightly check");
    let version_text = String::from_utf8_lossy(&output.stdout);
    let is_nightly = version_text.contains("nightly")
        || version_text.contains("dev")
        || version_text.contains("-pre");
    if !is_nightly {
        // Hard error: the developer asked for the rustc_public lane, and
        // they're not on a nightly toolchain. Failing loudly here is far
        // better than silently falling back to the shadow build, which
        // would defeat the point of the opt-in.
        panic!(
            "PITBULL_USE_RUSTC_PUBLIC=1 requires a nightly Rust toolchain.\n\
             Active rustc: {}\n\
             Install nightly with:\n  \
             rustup toolchain install nightly-2026-01-29\n\
             Then re-run with:\n  \
             PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build",
            version_text.trim()
        );
    }
    // All checks passed. Set the cfg.
    println!("cargo:rustc-cfg=rustc_public_real");
    // Tell the consumer (mir_api.rs) about the active toolchain so it can
    // log it in the resulting binary if desired.
    println!("cargo:rustc-env=PITBULL_RUSTC_PUBLIC_TOOLCHAIN={}", version_text.trim());
}
