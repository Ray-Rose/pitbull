//! `pitbull-rustc` — rustc-replacement wrapper.
//!
//! ## Role in the pipeline
//!
//! When the user runs `cargo pitbull check <target>`, the cargo subcommand
//! sets the environment variable `RUSTC_WORKSPACE_WRAPPER` to the absolute
//! path of this binary, then invokes `cargo check`. Cargo then calls this
//! binary in place of `rustc` for every compile unit in the target
//! workspace, with cargo's standard rustc CLI: argv\[0\] is this binary,
//! argv\[1\] is the path to the real `rustc` (which we can use or ignore),
//! and argv\[2..\] is the rustc invocation cargo intended.
//!
//! ## Two-mode design
//!
//! - **Stable Rust (default):** this binary compiles to a stub that
//!   prints a clear diagnostic and exits with code 1. The cargo
//!   subcommand `cargo pitbull check` is therefore non-functional on
//!   stable; only `cargo pitbull rules` and `cargo pitbull verify`
//!   (which delegates to `check` with a stub message) work without the
//!   nightly + opt-in lane.
//!
//! - **Nightly + opt-in (`PITBULL_USE_RUSTC_PUBLIC=1`):** this binary
//!   uses `rustc_driver` to run the standard compile pipeline AND inject
//!   the Pitbull subset-checking pass after MIR generation via a custom
//!   `Callbacks` implementation. This is the real Pitbull v0.2 compile.
//!
//! ## Status
//!
//! Milestone 2 scaffold. The nightly path currently runs `rustc_driver`
//! with no-op callbacks (a passthrough rustc). The actual subset-check
//! callback that walks reachable MIR through
//! `pitbull_subset::mir_api::adapter` is the next chunk of Milestone 2
//! implementation work.
#![cfg_attr(rustc_public_real, feature(rustc_private))]
// Stable / no-opt-in path: print a diagnostic and exit. Reached when the
// wrapper is somehow invoked despite not being on a nightly build with
// the opt-in env var set. We do not silently passthrough to rustc here
// because that would let the user think they had `cargo pitbull check`
// working when in fact no analysis happened.
#[cfg(not(rustc_public_real))]
fn main() {
    eprintln!("pitbull-rustc: this binary is the rustc-replacement wrapper that");
    eprintln!("              `cargo pitbull check` invokes for each compile");
    eprintln!("              unit. It requires a nightly toolchain and the");
    eprintln!("              PITBULL_USE_RUSTC_PUBLIC=1 opt-in to do useful");
    eprintln!("              work. Built without those, this is a stub.");
    eprintln!();
    eprintln!("              To enable the real wrapper:");
    eprintln!("                rustup toolchain install nightly-2026-01-29");
    eprintln!("                PITBULL_USE_RUSTC_PUBLIC=1 \\");
    eprintln!("                  cargo +nightly-2026-01-29 build -p pitbull-driver");
    eprintln!();
    eprintln!("              See PSS-1 §17.1 for the milestone-2 status.");
    std::process::exit(1);
}
// Nightly + opt-in path: rustc_driver passthrough.
//
// The current implementation is intentionally minimal: it forwards every
// CLI argument to rustc_driver and uses the no-op default Callbacks.
// This proves the wrapper binary mechanism works (can be built, can be
// pointed to via RUSTC_WORKSPACE_WRAPPER, can compile a target crate).
// The next step is replacing the no-op callbacks with a PitbullCallbacks
// impl whose `after_analysis` hook walks reachable MIR via the adapter.
#[cfg(rustc_public_real)]
extern crate rustc_driver;
#[cfg(rustc_public_real)]
fn main() {
    // Cargo invokes a `RUSTC_WORKSPACE_WRAPPER` binary as
    //   <wrapper> <real-rustc-path> <rustc-args...>
    // We don't need the real-rustc path (we use rustc_driver directly),
    // but we must strip it before passing to rustc_driver; otherwise
    // rustc treats it as a positional input filename and the compile
    // fails with "multiple input filenames".
    //
    // For DIRECT invocation (e.g. `./pitbull-rustc --version` for
    // smoke-testing), there is no leading rustc path — argv\[0\] is
    // our binary, argv\[1..\] is the rustc CLI as the user typed it.
    // We must NOT strip argv\[1\] in that case.
    //
    // Heuristic (matches Clippy and Kani): if argv\[1\] file-stem is
    // exactly "rustc", assume cargo-wrapper mode and remove it. The
    // wrapper's own argv\[0\] stays in place — rustc_driver expects
    // a program name there.
    let mut args: Vec<String> = std::env::args().collect();
    if args
        .get(1)
        .and_then(|a| std::path::Path::new(a).file_stem())
        .and_then(|s| s.to_str())
        == Some("rustc")
    {
        args.remove(1);
    }
    // No-op callbacks for the scaffold checkpoint. `rustc_driver::Callbacks`
    // has four methods (`config`, `after_crate_root_parsing`,
    // `after_expansion`, `after_analysis`) all with default empty bodies,
    // so an empty impl is a valid passthrough.
    //
    // API note (May 2026): the current rustc_driver exposes a free
    // function `run_compiler(at_args, callbacks)` returning `()`, not
    // the older `RunCompiler::new(...).run() -> Result` builder. The
    // companion `catch_with_exit_code` now takes `impl FnOnce()` (not
    // `impl FnOnce() -> Result`) and translates panics/ICEs into a
    // process exit code. Earlier rustc versions had `impl Callbacks for ()`
    // for convenience but the current trait requires an explicit type.
    struct NoopCallbacks;
    impl rustc_driver::Callbacks for NoopCallbacks {}
    let mut callbacks = NoopCallbacks;
    let exit_code = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut callbacks);
    });
    std::process::exit(exit_code);
}
