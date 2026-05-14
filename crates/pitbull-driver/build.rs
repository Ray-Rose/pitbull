//! `pitbull-driver` build script.
//!
//! Mirrors `crates/pitbull-subset/build.rs`: emits `--cfg rustc_public_real`
//! when the developer opts in via `PITBULL_USE_RUSTC_PUBLIC=1` AND the
//! active rustc is a nightly toolchain. By default this script is inert
//! and the driver compiles its `pitbull-rustc` wrapper binary as a
//! placeholder that informs the user the rustc-internal lane is
//! disabled.
//!
//! See `crates/pitbull-subset/build.rs` for the full design rationale —
//! this is the same opt-in mechanism applied to the driver crate so
//! the wrapper binary's `rustc_driver` / `rustc_interface` dependencies
//! are only loaded when actually needed.
fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=PITBULL_USE_RUSTC_PUBLIC");
    println!("cargo:rustc-check-cfg=cfg(rustc_public_real)");
    let opted_in = std::env::var_os("PITBULL_USE_RUSTC_PUBLIC").is_some();
    if !opted_in {
        return;
    }
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
    println!("cargo:rustc-cfg=rustc_public_real");
}
