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
    /// Number of non-body items (statics, consts) dispatched to
    /// `visit_static_item` / `visit_const_item`.
    non_body_items_walked: usize,
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
        // `TyCtxt` is `Copy`, so we can move it into the FnOnce closure
        // and still use it (or its copy) inside. The subset check needs
        // tcx to resolve static mutability via the rustc_internal bridge
        // (rustc_public's `ItemKind::Static` is a payload-less variant
        // and exposes no `mutability()` accessor).
        let result = rustc_public::rustc_internal::run(tcx, || {
            self.run_pitbull_subset_check(tcx);
        });
        if let Err(e) = result {
            eprintln!("pitbull-rustc: rustc_public bridge failed: {e:?}");
        }
        // Report a per-crate summary on stderr so the user sees what
        // happened. The driver-side cargo-pitbull command wraps this in
        // higher-level reporting; for now this raw output is fine.
        eprintln!(
            "pitbull-rustc: crate analyzed: {} items, {} bodies walked, {} non-fn items, {} subset violation(s)",
            self.items_seen,
            self.bodies_walked,
            self.non_body_items_walked,
            self.violations,
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
    /// Walk items via configured `verify_roots`, translate each body via
    /// the adapter, run the subset visitor, accumulate counts.
    ///
    /// Filtering policy:
    ///   - If `pitbull.toml` is loadable and its `[reachability]
    ///     verify_roots` is non-empty, walk ONLY items whose
    ///     fully-qualified name matches at least one root pattern AND
    ///     does not match any `exclude` pattern.
    ///   - If `verify_roots` is empty (or no `pitbull.toml`), walk
    ///     every item with a body. This preserves the over-approximating
    ///     fail-safe behavior of earlier checkpoints — useful for
    ///     ad-hoc demos against unconfigured crates.
    ///
    /// Why path-based and not `#[pitbull::verify]` attribute-based:
    /// rustc tool attributes (`#[pitbull::verify]`) require the user's
    /// crate to declare `#![register_tool(pitbull)]` AND require the
    /// pitbull-spec proc-macros to re-emit them on the item (currently
    /// they consume the attribute and return the bare item). Path-based
    /// filtering via `pitbull.toml` sidesteps both UX hurdles and uses
    /// the existing `SubsetConfig.reachability.verify_roots` field
    /// from v0.1. Attribute-based seeding remains a future option once
    /// the proc-macros and register_tool plumbing land.
    ///
    /// Must be called inside a `rustc_public::rustc_internal::run`
    /// closure or it will panic in `with(...)` calls.
    ///
    /// `tcx` is threaded in so that non-function items (statics) can
    /// resolve mutability via `TyCtxt::is_mutable_static` through the
    /// rustc_internal bridge — `rustc_public::ItemKind::Static` is a
    /// plain enum variant with no mutability payload.
    fn run_pitbull_subset_check<'tcx>(
        &mut self,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) {
        let cfg = load_config();
        let verify_roots = cfg.reachability.verify_roots.clone();
        let exclude = cfg.reachability.exclude.clone();
        let mut visitor = pitbull_subset::SubsetVisitor::new(&cfg);
        let mut walked = 0usize;
        let mut filtered_out = 0usize;
        // CrateDef gives `name()`, `span()`, `def_id()` as trait methods.
        // `ty()` is exposed as an inherent method on CrateItem (via the
        // `crate_def_with_ty!` macro), so no separate trait import needed.
        use rustc_public::CrateDef;
        for item in rustc_public::all_local_items() {
            self.items_seen += 1;
            let item_path = item.name();
            if exclude.iter().any(|p| pattern_matches(p, &item_path)) {
                filtered_out += 1;
                continue;
            }
            match item.kind() {
                rustc_public::ItemKind::Fn => {
                    let matches_root = verify_roots.is_empty()
                        || verify_roots
                            .iter()
                            .any(|p| pattern_matches(p, &item_path));
                    if !matches_root {
                        filtered_out += 1;
                        continue;
                    }
                    if !item.has_body() {
                        // Some Fn items have no MIR body (extern fn
                        // declarations, intrinsics without a provided
                        // body). Nothing to walk — skip silently.
                        continue;
                    }
                    let real_body = item.expect_body();
                    let shadow_body =
                        pitbull_subset::mir_api::adapter::body(&real_body);
                    self.bodies_walked += 1;
                    walked += 1;
                    // All bodies are walked as untrusted in v0.2. Trust
                    // marking requires the proc-macro / attribute plumbing
                    // described in the doc comment above.
                    visitor.visit_body(&shadow_body, /*trusted=*/ false);
                }
                rustc_public::ItemKind::Static => {
                    // verify_roots patterns are authored for callable
                    // function paths (e.g. `mycrate::foo::*`). Matching
                    // them against a `static FOO` path is semantically
                    // odd and would silently drop most users' statics.
                    // Walk statics only in the open-walk fallback
                    // (verify_roots empty).
                    if !verify_roots.is_empty() {
                        filtered_out += 1;
                        continue;
                    }
                    let internal_id = rustc_public::rustc_internal::internal(
                        tcx,
                        item.def_id(),
                    );
                    let mutable = tcx.is_mutable_static(internal_id);
                    let shadow_ty =
                        pitbull_subset::mir_api::adapter::ty(item.ty());
                    let shadow_span =
                        pitbull_subset::mir_api::adapter::span(item.span());
                    self.non_body_items_walked += 1;
                    visitor.visit_static_item(
                        mutable,
                        Some(&shadow_ty),
                        shadow_span,
                    );
                }
                rustc_public::ItemKind::Const => {
                    if !verify_roots.is_empty() {
                        filtered_out += 1;
                        continue;
                    }
                    let shadow_ty =
                        pitbull_subset::mir_api::adapter::ty(item.ty());
                    let shadow_span =
                        pitbull_subset::mir_api::adapter::span(item.span());
                    self.non_body_items_walked += 1;
                    visitor.visit_const_item(Some(&shadow_ty), shadow_span);
                }
                rustc_public::ItemKind::Ctor(rustc_public::CtorKind::Const)
                | rustc_public::ItemKind::Ctor(rustc_public::CtorKind::Fn) => {
                    // Tuple/unit-struct constructors are auto-synthesized
                    // by rustc; no user-authored content for any PSS-1
                    // rule to fire on in v0.2.
                }
            }
        }
        if !verify_roots.is_empty() {
            eprintln!(
                "pitbull-rustc: verify-roots mode: {} root pattern(s), walked {} item(s), filtered {}",
                verify_roots.len(),
                walked,
                filtered_out,
            );
        }
        let mut report = visitor.into_report();
        // Drain the per-thread filename table the adapter accumulated
        // while building shadow Spans; attach it to the report so SARIF
        // emission can surface `artifactLocation.uri` strings (the span
        // file IDs alone are opaque hashes). Empty table → leave the
        // optional field at None (shadow-test parity).
        let filename_table =
            pitbull_subset::mir_api::adapter::take_filename_table();
        if !filename_table.is_empty() {
            report.filenames = Some(filename_table);
        }
        self.violations = report.errors.len();
        for err in &report.errors {
            eprintln!("pitbull-rustc: {err}");
        }
        // Optional SARIF emission. When `PITBULL_SARIF_OUT` is set,
        // write the (minimal) SARIF report to that path. Each wrapper
        // invocation overwrites the file — fine for single-crate
        // smoke tests; multi-crate aggregation is a job for the
        // `cargo pitbull check` subcommand (it can set a per-invocation
        // unique path or merge later).
        if let Some(out) = std::env::var_os("PITBULL_SARIF_OUT") {
            let sarif = report.to_sarif_minimal();
            match serde_json::to_string_pretty(&sarif) {
                Ok(text) => match std::fs::write(&out, text) {
                    Ok(()) => eprintln!(
                        "pitbull-rustc: SARIF written to {}",
                        std::path::Path::new(&out).display(),
                    ),
                    Err(e) => eprintln!(
                        "pitbull-rustc: failed to write SARIF to {}: {e}",
                        std::path::Path::new(&out).display(),
                    ),
                },
                Err(e) => eprintln!("pitbull-rustc: SARIF serialize failed: {e}"),
            }
        }
    }
}
/// Load pitbull.toml from `$PITBULL_TOML` (if set) or from `./pitbull.toml`
/// in the current working directory. Falls back to the default test
/// config if neither is present or loadable. Validation errors are
/// reported on stderr but do not abort.
///
/// The env-var lookup is the preferred path because cargo invokes the
/// wrapper with CWD set to whichever package is being compiled — for
/// dependencies that's `~/.cargo/registry/...`, not the user's project.
/// `cargo-pitbull check` sets `$PITBULL_TOML` to the absolute path of
/// the user's pitbull.toml so dependency compiles see the same config.
#[cfg(rustc_public_real)]
fn load_config() -> pitbull_subset::SubsetConfig {
    let path = std::env::var_os("PITBULL_TOML")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::PathBuf::from("pitbull.toml"));
    if !path.exists() {
        return pitbull_subset::SubsetConfig::default_for_test();
    }
    match pitbull_subset::SubsetConfig::load_and_validate(&path) {
        Ok(outcome) => {
            if !outcome.errors.is_empty() {
                eprintln!(
                    "pitbull-rustc: {} pitbull.toml validation error(s):",
                    outcome.errors.len()
                );
                for err in &outcome.errors {
                    eprintln!("pitbull-rustc:   {err}");
                }
            }
            outcome.config
        }
        Err(e) => {
            eprintln!(
                "pitbull-rustc: could not load {}: {e}; using default config",
                path.display()
            );
            pitbull_subset::SubsetConfig::default_for_test()
        }
    }
}
/// Pattern matcher mirroring `pitbull_subset::reachability::pattern_matches`.
/// Patterns ending with `::*` match any item whose path starts with
/// the prefix; other patterns match exactly. v0.1 deliberately keeps
/// the matching simple — see `reachability.rs` for the rationale.
#[cfg(rustc_public_real)]
fn pattern_matches(pattern: &str, path: &str) -> bool {
    if let Some(prefix) = pattern.strip_suffix("::*") {
        path == prefix || path.starts_with(&format!("{prefix}::"))
    } else {
        pattern == path
    }
}
