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
extern crate rustc_hir;
#[cfg(rustc_public_real)]
extern crate rustc_interface;
#[cfg(rustc_public_real)]
extern crate rustc_middle;
#[cfg(rustc_public_real)]
extern crate rustc_public;
#[cfg(rustc_public_real)]
extern crate rustc_span;
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
    /// Number of HIR-level `unsafe { ... }` blocks PB001 fired on
    /// during the pre-pass. Reported separately from MIR-derived
    /// violations because the detection mechanism differs.
    hir_unsafe_blocks: usize,
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
            "pitbull-rustc: crate analyzed: {} items, {} bodies walked, {} non-fn items, {} unsafe blocks, {} subset violation(s)",
            self.items_seen,
            self.bodies_walked,
            self.non_body_items_walked,
            self.hir_unsafe_blocks,
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
        // HIR pre-pass: rustc_public's MIR has already discarded
        // HIR-level `unsafe { ... }` block markers (operations inside
        // an unsafe block fire their own rules — PB004/PB007/PB009 —
        // but PB001 on the bare block needs HIR). We walk HIR once
        // before the MIR pass and emit PB001 violations directly into
        // the report. tcx.hir_visit_all_item_likes_in_crate is callable
        // here because tcx remains valid inside rustc_internal::run.
        let (hir_pb001_errors, hir_filename_partials) =
            collect_hir_unsafe_blocks(tcx);
        self.hir_unsafe_blocks = hir_pb001_errors.len();
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
                    // O.1: install spec-derived preconditions for
                    // this body so VC obligations emitted from its
                    // walk carry the assumptions. The lookup uses
                    // the item's full path (via CrateDef::name)
                    // against `[verification.preconditions]` in
                    // pitbull.toml. Bodies not in the map get an
                    // empty list — explicit "clear" so prior body's
                    // preconditions don't leak across the loop.
                    let preconditions = cfg
                        .verification
                        .preconditions
                        .get(&item_path)
                        .cloned()
                        .unwrap_or_default();
                    visitor.set_current_preconditions(preconditions);
                    // All bodies are walked as untrusted in v0.2. Trust
                    // marking requires the proc-macro / attribute plumbing
                    // described in the doc comment above.
                    visitor.visit_body(&shadow_body, /*trusted=*/ false);
                }
                rustc_public::ItemKind::Static => {
                    // `verify_roots` is a reachability-closure filter
                    // for fn items — it picks the set of bodies whose
                    // *call closure* gets walked. It does NOT apply to
                    // project-level items like statics: PB018 (`static
                    // mut`), PB021 (interior-mutable static),
                    // PB022 (forbidden static types) all reject ANY
                    // such item in the local crate regardless of which
                    // fn (if any) reads it. Earlier (Task E) this arm
                    // skipped statics when verify_roots was non-empty,
                    // which silently reintroduced the very PB018 hole
                    // Task E was meant to close (audit finding C1).
                    // The `exclude` filter at the top of the loop
                    // still applies for users who want to skip
                    // specific item paths by name.
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
                    // Same rationale as Static above — consts are
                    // project-level items; verify_roots doesn't apply.
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
        // Append HIR-derived PB001 violations to the MIR-derived
        // violations. The two walks see distinct constructs (HIR
        // unsafe-blocks vs MIR statements/types), so there's no
        // duplication concern.
        report.errors.extend(hir_pb001_errors);
        // Drain the per-thread filename table the adapter accumulated
        // while building shadow Spans, then merge in the HIR-side
        // filename map. Both paths use DefaultHasher on the filename
        // string; if the string format differs between paths the same
        // file may appear under two hashes (visible only as duplicate
        // URI entries in SARIF — soft degradation, not incorrect).
        let mut filename_table =
            pitbull_subset::mir_api::adapter::take_filename_table();
        for (hash, name) in hir_filename_partials {
            filename_table.entry(hash).or_insert(name);
        }
        if !filename_table.is_empty() {
            report.filenames = Some(filename_table);
        }
        self.violations = report.errors.len();
        for err in &report.errors {
            eprintln!("pitbull-rustc: {err}");
        }
        // Audit notes are non-violations the visitor flagged for
        // auditor review (e.g. an unclassifiable callee at a Call
        // terminator — see classify_called_function in visitor.rs).
        // They never block verification but surface here so the gap
        // is visible.
        for note in &report.audit_notes {
            eprintln!("pitbull-rustc: {note}");
        }
        // VC obligations: discharge each through pitbull-vc and
        // surface the verdict on stderr. This is the v0.2 deductive
        // step — the visitor identified what needs proving; here
        // an SMT solver answers. Per-obligation breakdown:
        //   - `unsat` ⇒ proven safe ⇒ no PSS-1 violation
        //   - `sat`   ⇒ counterexample exists ⇒ obligation NOT
        //               discharged ⇒ this becomes a (future) PB049
        //               violation tied to the call site
        //   - `unknown` / `timeout` / `error` ⇒ inconclusive ⇒
        //               obligation reported as undischarged
        //   - `not installed` ⇒ Z3 missing on PATH ⇒ surface once,
        //               then list each obligation as undischarged
        //               so the user knows the gap exists
        //
        // Compilation failure (kind not yet supported, e.g.
        // PanicReachability) surfaces as "pending" — the obligation
        // is recorded but no SMT was generated.
        if !report.vc_obligations.is_empty() {
            dispatch_vc_obligations(&report);
        }
        // Optional SARIF emission. When `PITBULL_SARIF_OUT` is set,
        // write the (minimal) SARIF report to that path. Each wrapper
        // invocation overwrites the file — fine for single-crate
        // smoke tests; multi-crate aggregation is a job for the
        // `cargo pitbull check` subcommand (it can set a per-invocation
        // unique path or merge later).
        //
        // H3: the env-var is adversarially controllable via build.rs
        // (`cargo:rustc-env=PITBULL_SARIF_OUT=$HOME/.bashrc` would
        // otherwise overwrite that file with JSON). Refuse paths
        // that don't end in .sarif / .json or that contain `..`.
        // Skip emission and warn rather than exit, since SARIF output
        // is optional in the first place.
        if let Some(out) = std::env::var_os("PITBULL_SARIF_OUT") {
            let out_path = std::path::PathBuf::from(&out);
            if let Err(e) =
                check_env_path("PITBULL_SARIF_OUT", &out_path, &["sarif", "json"])
            {
                eprintln!("pitbull-rustc: refusing SARIF write: {e}");
            } else {
                let sarif = report.to_sarif_minimal();
                match serde_json::to_string_pretty(&sarif) {
                    Ok(text) => match std::fs::write(&out_path, text) {
                        Ok(()) => eprintln!(
                            "pitbull-rustc: SARIF written to {}",
                            out_path.display(),
                        ),
                        Err(e) => eprintln!(
                            "pitbull-rustc: failed to write SARIF to {}: {e}",
                            out_path.display(),
                        ),
                    },
                    Err(e) => eprintln!("pitbull-rustc: SARIF serialize failed: {e}"),
                }
            }
        }
    }
}
/// Compile each `VcObligation` in the report into SMT-LIB via
/// `pitbull-vc::compile`, dispatch to Z3 via
/// `pitbull-vc::solver::invoke_z3`, and surface the verdict on
/// stderr. Logs a summary line at the end.
///
/// Free function (not a method on `PitbullCallbacks`) because it
/// only reads the report — no callback state mutation needed.
#[cfg(rustc_public_real)]
fn dispatch_vc_obligations(report: &pitbull_subset::SubsetReport) {
    let mut solver_missing_announced = false;
    let mut discharged = 0usize;
    let mut undischarged = 0usize;
    for obligation in &report.vc_obligations {
        let Some(goal) = pitbull_vc::compile(obligation) else {
            eprintln!(
                "pitbull-rustc: vc {}: pending (compilation not yet supported for {:?})",
                obligation.id, obligation.kind,
            );
            undischarged += 1;
            continue;
        };
        match pitbull_vc::solver::invoke_z3(&goal.smt) {
            pitbull_vc::SolverResult::Unsat => {
                eprintln!(
                    "pitbull-rustc: vc {}: discharged (unsat — safety property holds)",
                    obligation.id,
                );
                discharged += 1;
            }
            pitbull_vc::SolverResult::Sat => {
                eprintln!(
                    "pitbull-rustc: vc {}: NOT DISCHARGED (sat — counterexample exists)",
                    obligation.id,
                );
                undischarged += 1;
            }
            pitbull_vc::SolverResult::NotInstalled => {
                if !solver_missing_announced {
                    eprintln!(
                        "pitbull-rustc: z3 not installed; VC obligations cannot \
                         be discharged. Install z3 (https://github.com/Z3Prover/z3) \
                         and add it to PATH.",
                    );
                    solver_missing_announced = true;
                }
                eprintln!(
                    "pitbull-rustc: vc {}: undischarged (no solver)",
                    obligation.id,
                );
                undischarged += 1;
            }
            pitbull_vc::SolverResult::Unknown => {
                eprintln!(
                    "pitbull-rustc: vc {}: undischarged (solver returned unknown)",
                    obligation.id,
                );
                undischarged += 1;
            }
            pitbull_vc::SolverResult::Timeout => {
                eprintln!(
                    "pitbull-rustc: vc {}: undischarged (timeout)",
                    obligation.id,
                );
                undischarged += 1;
            }
            pitbull_vc::SolverResult::Error(e) => {
                eprintln!(
                    "pitbull-rustc: vc {}: undischarged (solver error: {e})",
                    obligation.id,
                );
                undischarged += 1;
            }
        }
    }
    eprintln!(
        "pitbull-rustc: VC summary: {} obligation(s), {} discharged, {} undischarged",
        report.vc_obligations.len(),
        discharged,
        undischarged,
    );
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
/// Defense-in-depth path validator for env-supplied file paths
/// (PITBULL_TOML, PITBULL_SARIF_OUT). Audit finding H3.
///
/// Threat model
/// ------------
/// A hostile transitive dependency's `build.rs` can emit
/// `cargo:rustc-env=PITBULL_TOML=...` or `PITBULL_SARIF_OUT=...`
/// which becomes the wrapper's env when cargo invokes us for that
/// crate's rustc step. Without checks:
///
/// - `PITBULL_TOML=$HOME/.ssh/id_rsa` → wrapper opens the file,
///   `toml::from_str` fails with a parse error that embeds the
///   first failing characters → secret leak via stderr.
/// - `PITBULL_SARIF_OUT=$HOME/.bashrc` → wrapper overwrites the
///   file with SARIF JSON → data destruction (and on some
///   platforms, lateral movement via config-file execution).
///
/// What this catches
/// -----------------
/// - Path components containing `..` (traversal).
/// - Wrong file extension for the env-var's purpose. The realistic
///   attack targets are dotfiles and key files that don't end in
///   `.toml` / `.sarif` / `.json`.
///
/// What it doesn't catch
/// ---------------------
/// - A path with the right extension that points somewhere it
///   shouldn't (e.g. `~/.config/sneaky.toml`).
/// - A symlink whose target is sensitive (the wrapper doesn't yet
///   refuse symlinks; that's a follow-up if real-world abuse appears).
///
/// Escape hatch
/// ------------
/// `PITBULL_ALLOW_UNSAFE_PATHS=1` disables both checks for the
/// rare user whose legitimate config path doesn't match the
/// extension whitelist. Production should leave this unset.
#[cfg(rustc_public_real)]
fn check_env_path(
    var_name: &str,
    path: &std::path::Path,
    allowed_extensions: &[&str],
) -> Result<(), String> {
    if std::env::var_os("PITBULL_ALLOW_UNSAFE_PATHS").is_some() {
        return Ok(());
    }
    let s = path.to_string_lossy();
    if s.contains("..") {
        return Err(format!(
            "{var_name}={} contains '..' (path traversal); refusing. \
             Set PITBULL_ALLOW_UNSAFE_PATHS=1 to override.",
            path.display(),
        ));
    }
    let ext_ok = path
        .extension()
        .and_then(|e| e.to_str())
        .map(|e| allowed_extensions.iter().any(|a| e.eq_ignore_ascii_case(a)))
        .unwrap_or(false);
    if !ext_ok {
        return Err(format!(
            "{var_name}={} does not end in one of {:?}; refusing as \
             defense against build-script env injection. Set \
             PITBULL_ALLOW_UNSAFE_PATHS=1 to override.",
            path.display(),
            allowed_extensions,
        ));
    }
    Ok(())
}
#[cfg(rustc_public_real)]
fn load_config() -> pitbull_subset::SubsetConfig {
    // Two sources, both optional:
    //   1. `PITBULL_TOML` env var (preferred — `cargo-pitbull check`
    //      sets it to the absolute path of the user's config so
    //      dependency compiles, which run with a different cwd, see
    //      the same configuration).
    //   2. `./pitbull.toml` in the wrapper's cwd.
    //
    // Hard-error posture (audit finding H1): the wrapper REFUSES to
    // proceed when a config was named but cannot be loaded, rather
    // than silently substituting `default_for_test()`. Earlier behavior
    // would let a typo'd path or a malformed file produce a
    // "successful" verification under test defaults — exactly the
    // silent-skip anti-pattern PSS-1 §17 says to avoid.
    //
    // The one permissive path that remains: PITBULL_TOML unset AND
    // ./pitbull.toml absent → fall back to `default_for_test()` so
    // ad-hoc smoke tests against an unconfigured crate still work
    // (documented v0.1 demo posture). Set PITBULL_TOML to a real path
    // for production use.
    let (path, source_was_env) = match std::env::var_os("PITBULL_TOML") {
        Some(p) => (std::path::PathBuf::from(p), true),
        None => (std::path::PathBuf::from("pitbull.toml"), false),
    };
    // H3: validate env-supplied paths to defend against build-script
    // env injection (PITBULL_TOML=$HOME/.ssh/id_rsa → file leak via
    // parse error). The check only applies to the env-var source;
    // the implicit `./pitbull.toml` fallback is trusted because it's
    // not adversarially controllable.
    if source_was_env {
        if let Err(e) = check_env_path("PITBULL_TOML", &path, &["toml"]) {
            eprintln!("pitbull-rustc: config error: {e}");
            std::process::exit(2);
        }
    }
    if !path.exists() {
        if source_was_env {
            eprintln!(
                "pitbull-rustc: config error: PITBULL_TOML={} does not exist",
                path.display(),
            );
            std::process::exit(2);
        }
        // No config file and no env var — open-walk fallback for
        // ad-hoc smoke tests. Production should set PITBULL_TOML.
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
                "pitbull-rustc: config error: could not load {}: {e}",
                path.display(),
            );
            std::process::exit(2);
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
/// HIR pre-pass that emits PB001 for every user-authored
/// `unsafe { ... }` block in the crate.
///
/// ## Why HIR and not MIR
///
/// rustc's MIR construction discards HIR-level block scopes — by the
/// time the visitor sees a body, the `unsafe` keyword that wrapped a
/// raw-pointer deref is gone. The deref itself fires PB004 from MIR,
/// but PSS-1 also rejects the bare `unsafe` block (even if its body
/// happens to be empty or trivially safe). So this is a separate
/// HIR-only signal.
///
/// ## How
///
/// `tcx.hir_visit_all_item_likes_in_crate` enters every free item,
/// trait item, impl item, and foreign item. With
/// `NestedFilter = nested_filter::All`, the visitor recurses into
/// nested items (including bodies). `visit_block` fires on every
/// `hir::Block`, and we match its `rules` field for
/// `BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided)` —
/// `CompilerGenerated` covers e.g. `unsafe trait` method bodies that
/// the compiler adds wrapping unsafety, which is not a user-written
/// `unsafe { ... }` and not the PSS-1 PB001 target.
///
/// Returns the violations and a partial filename table — the wrapper
/// merges this with `adapter::take_filename_table()` so the SARIF
/// emission's `artifactLocation.uri` resolves for HIR spans too.
#[cfg(rustc_public_real)]
fn collect_hir_unsafe_blocks<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> (
    Vec<pitbull_subset::SubsetError>,
    std::collections::HashMap<u32, String>,
) {
    let mut visitor = UnsafeBlockVisitor {
        tcx,
        violations: Vec::new(),
        filename_table: std::collections::HashMap::new(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
    (visitor.violations, visitor.filename_table)
}
#[cfg(rustc_public_real)]
struct UnsafeBlockVisitor<'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    violations: Vec<pitbull_subset::SubsetError>,
    filename_table: std::collections::HashMap<u32, String>,
}
#[cfg(rustc_public_real)]
impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for UnsafeBlockVisitor<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;
    fn maybe_tcx(&mut self) -> rustc_middle::ty::TyCtxt<'tcx> {
        self.tcx
    }
    fn visit_block(&mut self, b: &'tcx rustc_hir::Block<'tcx>) {
        if matches!(
            b.rules,
            rustc_hir::BlockCheckMode::UnsafeBlock(
                rustc_hir::UnsafeSource::UserProvided,
            )
        ) {
            let span =
                rustc_span_to_shadow(self.tcx, b.span, &mut self.filename_table);
            self.violations.push(pitbull_subset::SubsetError {
                rule: pitbull_subset::rules::PB001,
                span,
                detail: "`unsafe { ... }` block".to_string(),
                in_spec: false,
            });
        }
        rustc_hir::intravisit::walk_block(self, b);
    }
}
/// Convert a `rustc_span::Span` to the shadow `Span` (line/col packed
/// into u32 halves; filename hashed to a u32 file ID). Populates the
/// caller's filename table with the (hash, filename) mapping so that
/// SARIF emission can later resolve the URI.
///
/// Dummy spans (post-macro-expansion synthetic spans without a source
/// location) collapse to `Span::default()`.
///
/// Column conversion: rustc's `Loc.col` is a 0-indexed `CharPos`; SARIF
/// wants 1-indexed. We add 1 to match the rustc_public side
/// (`adapter::span`, which passes through 1-indexed columns directly).
#[cfg(rustc_public_real)]
fn rustc_span_to_shadow(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    span: rustc_span::Span,
    table: &mut std::collections::HashMap<u32, String>,
) -> pitbull_subset::mir_api::Span {
    use pitbull_subset::mir_api::Span as ShadowSpan;
    if span.is_dummy() {
        return ShadowSpan::default();
    }
    let sm = tcx.sess.source_map();
    let lo = sm.lookup_char_pos(span.lo());
    let hi = sm.lookup_char_pos(span.hi());
    let filename = lo.file.name.prefer_local_unconditionally().to_string();
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    filename.hash(&mut hasher);
    let file_hash = (hasher.finish() & 0xFFFF_FFFF) as u32;
    table.entry(file_hash).or_insert_with(|| filename.clone());
    ShadowSpan {
        lo: ShadowSpan::pack(lo.line, lo.col.0 + 1),
        hi: ShadowSpan::pack(hi.line, hi.col.0 + 1),
        file: file_hash,
    }
}
