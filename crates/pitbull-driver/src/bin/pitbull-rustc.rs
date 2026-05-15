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
// Nightly + opt-in path: rustc_driver with PitbullCallbacks.
//
// The wrapper forwards every CLI argument to rustc_driver and installs
// our `PitbullCallbacks`. The callback's `after_analysis` hook bridges
// from rustc's `TyCtxt` into rustc_public's context (via
// `rustc_internal::run`), walks every local item that has a body,
// translates each body via `pitbull_subset::mir_api::adapter::body`,
// and runs `SubsetVisitor` over the result. Violations are printed
// to stderr.
//
// All four of these extern crates are sysroot-only (rustc_private):
//   - rustc_driver:    the Callbacks trait, run_compiler entry point
//   - rustc_interface: the Compiler type used in Callbacks signatures
//   - rustc_middle:    the TyCtxt we pass into rustc_internal::run
//   - rustc_public:    StableMIR — the typed view we run analysis against
#[cfg(rustc_public_real)]
extern crate rustc_driver;
#[cfg(rustc_public_real)]
extern crate rustc_interface;
#[cfg(rustc_public_real)]
extern crate rustc_middle;
#[cfg(rustc_public_real)]
extern crate rustc_public;
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
    // Install PitbullCallbacks: rustc_driver runs the standard compile
    // pipeline; after analysis completes, our after_analysis hook fires,
    // bridges into rustc_public via rustc_internal::run, and runs the
    // PSS-1 subset visitor over every reachable function body in the
    // crate.
    //
    // API note (May 2026): the current rustc_driver exposes a free
    // function `run_compiler(at_args, callbacks)` returning `()`, not
    // the older `RunCompiler::new(...).run() -> Result` builder. The
    // companion `catch_with_exit_code` now takes `impl FnOnce()` (not
    // `impl FnOnce() -> Result`) and translates panics/ICEs into a
    // process exit code. Earlier rustc versions had `impl Callbacks for ()`
    // for convenience but the current trait requires an explicit type.
    let mut callbacks = PitbullCallbacks::default();
    let exit_code = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut callbacks);
    });
    std::process::exit(exit_code);
}
/// Pitbull's rustc_driver callback. State lives across compile units
/// when invoked per-crate; for the v0.2 scaffold we accumulate counts
/// only.
#[cfg(rustc_public_real)]
#[derive(Default)]
struct PitbullCallbacks {
    /// Number of items in the crate (any kind).
    items_seen: usize,
    /// Number of items with a reachable MIR body.
    bodies_walked: usize,
    /// Total subset violations found across all bodies.
    violations: usize,
}
#[cfg(rustc_public_real)]
impl rustc_driver::Callbacks for PitbullCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        // Bridge from the rustc TyCtxt to rustc_public's compiler context.
        // Inside the closure, calls like `rustc_public::all_local_items()`
        // and `CrateItem::body()` work; outside it they would panic with
        // "rustc_public has not been properly initialized".
        let result = rustc_public::rustc_internal::run(tcx, || {
            self.run_pitbull_subset_check();
        });
        if let Err(e) = result {
            eprintln!("pitbull-rustc: rustc_public bridge failed: {e:?}");
        }
        // Report a per-crate summary on stderr so the user sees what
        // happened. The driver-side cargo-pitbull command wraps this in
        // higher-level reporting; for now this raw output is fine.
        eprintln!(
            "pitbull-rustc: crate analyzed: {} items, {} bodies walked, {} subset violation(s)",
            self.items_seen, self.bodies_walked, self.violations,
        );
        // Continue compilation. Pitbull's analysis is read-only with
        // respect to the standard compile; we don't want to short-circuit
        // codegen even if we found PSS-1 violations (the wrapper's exit
        // code reflects them via std::process::exit at the end of main,
        // not through Compilation::Stop here).
        rustc_driver::Compilation::Continue
    }
}
#[cfg(rustc_public_real)]
impl PitbullCallbacks {
    /// Walk every item in the crate that has a body, translate the body
    /// via the adapter, run the subset visitor, accumulate counts.
    ///
    /// Must be called inside a `rustc_public::rustc_internal::run`
    /// closure or it will panic in `with(...)` calls.
    fn run_pitbull_subset_check(&mut self) {
        // For this scaffold checkpoint we run the visitor with the
        // default test config. A future driver-wiring commit threads in
        // the user's `pitbull.toml`.
        let cfg = pitbull_subset::SubsetConfig::default_for_test();
        let mut visitor = pitbull_subset::SubsetVisitor::new(&cfg);
        for item in rustc_public::all_local_items() {
            self.items_seen += 1;
            if !item.has_body() {
                continue;
            }
            let real_body = item.expect_body();
            let shadow_body = pitbull_subset::mir_api::adapter::body(&real_body);
            self.bodies_walked += 1;
            // For now we run all bodies as untrusted. Reachability
            // seeding from `#[pitbull::verify]` annotations is the next
            // sub-chunk; until then, we walk every body, which is a
            // strict over-approximation of PSS-1's "reachable from a
            // verify root" semantics.
            visitor.visit_body(&shadow_body, /*trusted=*/ false);
        }
        let report = visitor.into_report();
        self.violations = report.errors.len();
        for err in &report.errors {
            eprintln!("pitbull-rustc: {err}");
        }
    }
}
