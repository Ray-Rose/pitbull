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
// Defense-in-depth (red-team F8): the wrapper is part of the
// Pitbull TCB. No unsafe is needed at the Rust language level —
// every API we use (rustc_driver, rustc_public, rustc_middle,
// rustc_hir, rustc_span) is safe Rust. Forbidding `unsafe_code`
// here makes a future refactor that adds `unsafe { ... }` for a
// "tiny optimization" a hard compile error instead of a silent
// soundness-relevant addition.
#![forbid(unsafe_code)]
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
extern crate rustc_ast;
// Task Q.3 (2026-05-26): expression-form attribute argument
// stringification — `#[pitbull::requires(x < 100)]` (no quotes)
// requires us to pretty-print the attribute's token stream back
// into a string we can hand to the predicate parser.
#[cfg(rustc_public_real)]
extern crate rustc_ast_pretty;
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
/// Decide the wrapper's process exit code from rustc's own exit code and
/// Pitbull's findings. Pure + lane-agnostic so it is unit-testable on
/// stable (the rest of the wrapper is nightly-only behind
/// `rustc_public_real`).
///
/// Fail-closed policy (red-team F10 + bridge-failure audit 2026-06-14):
///   - rustc's own failure always propagates — compiler errors win.
///   - a bridge/analysis failure (the subset check could not run at all)
///     yields exit 2: we must NEVER report "verified" when no analysis
///     happened, even off a clean rustc compile with zero findings.
///   - subset violations OR undischarged obligations OR in-crate callees
///     that a `verify_roots`-narrowed walk left unverified (#27) yield
///     exit 1.
///   - otherwise exit 0 (clean verification).
#[cfg(any(rustc_public_real, test))]
fn decide_pitbull_exit_code(
    rustc_exit_code: i32,
    violations: usize,
    undischarged_obligations: usize,
    unverified_reachable_callees: usize,
    coverage_gaps: usize,
    fail_on_coverage_gaps: bool,
    bridge_failed: bool,
) -> i32 {
    // A coverage gap (a safety check that could not run, with no
    // compensating obligation) drives the exit code only when the user
    // hasn't opted out via `verification.fail_on_coverage_gaps = false`.
    // Default is to fail closed: exit 0 must not mean "verified except the
    // parts I could not model" (the "no silent skips" posture).
    let coverage_gap_fail = fail_on_coverage_gaps && coverage_gaps > 0;
    let pitbull_exit_code = if bridge_failed {
        2
    } else if violations > 0
        || undischarged_obligations > 0
        || unverified_reachable_callees > 0
        || coverage_gap_fail
    {
        1
    } else {
        0
    };
    rustc_exit_code.max(pitbull_exit_code)
}
#[cfg(test)]
mod exit_code_tests {
    use super::decide_pitbull_exit_code;
    // Args: (rustc_exit, violations, undischarged, unverified_callees,
    //        coverage_gaps, fail_on_coverage_gaps, bridge_failed).
    #[test]
    fn clean_verification_is_zero() {
        assert_eq!(decide_pitbull_exit_code(0, 0, 0, 0, 0, true, false), 0);
    }
    #[test]
    fn violations_or_undischarged_is_one() {
        assert_eq!(decide_pitbull_exit_code(0, 1, 0, 0, 0, true, false), 1);
        assert_eq!(decide_pitbull_exit_code(0, 0, 1, 0, 0, true, false), 1);
        assert_eq!(decide_pitbull_exit_code(0, 7, 3, 0, 0, true, false), 1);
    }
    /// CRITICAL fail-open regression (audit 2026-06-14): if the
    /// rustc_public bridge fails, the subset check never runs and the
    /// finding counters stay 0 — but the wrapper must STILL fail closed,
    /// never exit 0 ("verified") off a clean rustc compile.
    #[test]
    fn bridge_failure_never_reports_verified() {
        assert_eq!(decide_pitbull_exit_code(0, 0, 0, 0, 0, true, true), 2);
        assert_ne!(decide_pitbull_exit_code(0, 0, 0, 0, 0, true, true), 0);
    }
    /// #27 fail-closed: an in-crate callee reachable from a verified root
    /// but skipped by verify_roots narrowing forces exit 1, never 0.
    #[test]
    fn unverified_reachable_callee_fails_closed() {
        assert_eq!(decide_pitbull_exit_code(0, 0, 0, 1, 0, true, false), 1);
        assert_ne!(decide_pitbull_exit_code(0, 0, 0, 2, 0, true, false), 0);
    }
    /// M1 (audit 2026-06-14): a COVERAGE GAP (a safety check that could not
    /// run, with no compensating obligation) fails closed by default — exit
    /// 0 must not mean "verified except the parts I couldn't model".
    #[test]
    fn coverage_gap_fails_closed_by_default() {
        assert_eq!(decide_pitbull_exit_code(0, 0, 0, 0, 1, true, false), 1);
        assert_ne!(decide_pitbull_exit_code(0, 0, 0, 0, 3, true, false), 0);
    }
    /// ...but the user can opt out (`fail_on_coverage_gaps = false`): the
    /// gap is then a stderr-only note and does not change the verdict.
    #[test]
    fn coverage_gap_opt_out_does_not_fail() {
        assert_eq!(decide_pitbull_exit_code(0, 0, 0, 0, 5, false, false), 0);
        // ...but a real violation alongside still fails regardless of opt-out.
        assert_eq!(decide_pitbull_exit_code(0, 1, 0, 0, 5, false, false), 1);
    }
    #[test]
    fn rustc_failure_takes_precedence() {
        assert_eq!(decide_pitbull_exit_code(101, 0, 0, 0, 0, true, false), 101);
        assert_eq!(decide_pitbull_exit_code(101, 5, 5, 9, 9, true, true), 101);
    }
}
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
    let rustc_exit_code = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut callbacks);
    });
    // Audit-cleanup #5 / red-team F10: the wrapper's exit code
    // now reflects Pitbull's findings, not just rustc's. Earlier
    // behavior: rustc compiled cleanly ⇒ exit 0 even with 47
    // subset violations and undischarged VC obligations. A
    // direct-invocation user (or `cargo pitbull check` once
    // wired) couldn't tell verification failed from the exit
    // status alone.
    //
    // Policy:
    //   - If rustc itself failed (non-zero) ⇒ propagate that
    //     code — rustc errors take precedence.
    //   - Else if Pitbull found subset violations ⇒ exit 1.
    //   - Else if there are undischarged VC obligations ⇒ exit 1.
    //   - Else ⇒ exit 0 (clean verification).
    //
    // Why a single non-zero code regardless of cause: per the
    // cargo-pitbull `--exit-codes` doc, exit 1 means
    // "verification did not pass." Distinguishing
    // "subset-violation vs. undischarged-obligation" lives in
    // the cargo subcommand's report rendering, not the wrapper's
    // exit status.
    // Fail-closed exit code (F10 + bridge-failure audit 2026-06-14):
    // a bridge failure (analysis could not run) must never be reportable
    // as "verified". See `decide_pitbull_exit_code`.
    std::process::exit(decide_pitbull_exit_code(
        rustc_exit_code,
        callbacks.violations,
        callbacks.undischarged_obligations,
        callbacks.unverified_reachable_callees,
        callbacks.coverage_gap_notes,
        callbacks.fail_on_coverage_gaps,
        callbacks.bridge_failed,
    ));
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
    /// VC obligations that the dispatcher could NOT discharge
    /// (sat, unknown, timeout, error, not-installed, contradictory
    /// preconditions, pending compilation, etc.). Combined with
    /// `violations` to determine the wrapper's exit code per the
    /// F10 audit fix.
    undischarged_obligations: usize,
    /// Set when the rustc_public bridge (`rustc_internal::run`) returns
    /// `Err` — i.e. the subset check could not run at all. Forces a
    /// fail-closed nonzero exit so a clean rustc compile is NEVER
    /// reported as "verified" when no analysis actually happened
    /// (audit 2026-06-14, CRITICAL fail-open: bridge failure → exit 0).
    bridge_failed: bool,
    /// Count of in-crate functions reachable from a verified root that
    /// were NOT themselves verified because `verify_roots` narrowing
    /// skipped them (issue #27). Nonzero forces a fail-closed exit 1: a
    /// "verified" verdict must never rest on an unverified in-crate callee.
    unverified_reachable_callees: usize,
    /// Number of COVERAGE-GAP audit notes — safety checks the visitor could
    /// not run, with no compensating VC obligation (M1, audit 2026-06-14).
    /// When `fail_on_coverage_gaps` is set, a nonzero count forces exit 1
    /// so a CI gate cannot mistake a coverage gap for a clean verification.
    coverage_gap_notes: usize,
    /// Mirror of `verification.fail_on_coverage_gaps` (default true). Gates
    /// whether `coverage_gap_notes` affects the exit code.
    fail_on_coverage_gaps: bool,
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
            // Fail closed: the bridge into rustc_public never ran the
            // subset check, so the finding counters are meaningless
            // (still 0). Mark the failure so the exit code can never
            // report "verified" off a clean rustc compile (audit
            // 2026-06-14, CRITICAL fail-open).
            eprintln!("pitbull-rustc: rustc_public bridge failed: {e:?}");
            self.bridge_failed = true;
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
        // M1: mirror the coverage-gap exit-code policy onto the callbacks so
        // `main` can apply it after `rustc_internal::run` returns.
        self.fail_on_coverage_gaps = cfg.verification.fail_on_coverage_gaps;
        let verify_roots = cfg.reachability.verify_roots.clone();
        let exclude = cfg.reachability.exclude.clone();
        let mut visitor = pitbull_subset::SubsetVisitor::new(&cfg);
        let mut walked = 0usize;
        let mut filtered_out = 0usize;
        // Track which function paths were actually walked, so we can warn
        // about `[verification.preconditions]` keys that matched nothing
        // (a typo, or a function filtered out by verify_roots) — those
        // preconditions silently never applied, which the project's
        // "no silent skips" posture forbids (audit 2026-05-29).
        let mut walked_fn_paths: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        // #27 fail-closed reachability check. `local_fn_universe` is every
        // non-excluded in-crate fn-with-body; `referenced_callees` is the
        // union of the direct callees of every walked (non-trusted) body.
        // After the walk, an entry in (referenced ∩ universe) that is
        // neither walked nor trusted is an in-crate callee a
        // verify_roots-narrowed walk skipped — surfaced fail-closed below.
        let mut local_fn_universe: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut referenced_callees: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        // HIR pre-pass: rustc_public's MIR has already discarded
        // HIR-level `unsafe { ... }` block markers (operations inside
        // an unsafe block fire their own rules — PB004/PB007/PB009 —
        // but PB001 on the bare block needs HIR). We walk HIR once
        // before the MIR pass and emit PB001 violations directly into
        // the report. tcx.hir_visit_all_item_likes_in_crate is callable
        // here because tcx remains valid inside rustc_internal::run.
        let HirPrePass {
            violations: hir_violations,
            filename_table: hir_filename_partials,
            preconditions: hir_preconditions,
            trusted: hir_trusted,
            ensures: hir_ensures,
        } = collect_hir_pre_pass(tcx, &cfg.subset.allowed_proc_macros);
        // The HIR pre-pass finds BOTH PB001 (unsafe blocks) and PB003
        // (unsafe impl/trait). Count only PB001 for the "unsafe blocks"
        // summary line so the diagnostic stays accurate; PB003 still flows
        // into `report.errors` below and the total violation count.
        self.hir_unsafe_blocks = hir_violations
            .iter()
            .filter(|e| e.rule == pitbull_subset::rules::PB001)
            .count();
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
                    // #27: record EVERY in-crate fn-with-body in the universe
                    // BEFORE the verify_roots filter — a callee skipped by
                    // narrowing is exactly "in the universe but not walked".
                    // (Excluded items already `continue`d above, so they are
                    // correctly absent from the universe.)
                    if item.has_body() {
                        local_fn_universe.insert(item_path.clone());
                        // #27 drop-glue (2026-06-14): a `Drop::drop` impl is
                        // invoked via IMPLICIT drop-glue (a `Drop` terminator,
                        // not a `Call`), so the Call-based callee tracking below
                        // never references it — under verify_roots narrowing an
                        // unwalked, panicking drop would slip through. Drop glue
                        // can run wherever a value of the type leaves scope, so
                        // treat every local Drop impl as a reachable callee: add
                        // it to `referenced_callees` so the post-loop #27 check
                        // flags it (fail closed) if narrowing left it unwalked.
                        // Conservative (flags a local Drop impl even if no
                        // walked root provably drops that type) but sound, and
                        // Drop impls are rare. `internal()` is the id conversion
                        // (safe on any def_id); `trait_of_assoc` is safe too.
                        let drop_id = rustc_public::rustc_internal::internal(
                            tcx,
                            item.def_id(),
                        );
                        // A Drop-impl method's PARENT is its `impl` block; if
                        // that impl is a TRAIT impl of `Drop`, this fn is a
                        // `Drop::drop`. (`trait_of_assoc` only resolves trait
                        // DECLARATION items, not impl methods — it returns None
                        // here — so use the impl's trait ref.) The `def_kind`
                        // guard keeps `impl_opt_trait_ref` from panicking on a
                        // non-impl parent (free fns, inherent-impl methods).
                        let parent = tcx.parent(drop_id);
                        let is_drop_impl = matches!(
                            tcx.def_kind(parent),
                            rustc_hir::def::DefKind::Impl { of_trait: true }
                        ) && tcx
                            .impl_opt_trait_ref(parent)
                            .map(|tr| tr.skip_binder().def_id)
                            == tcx.lang_items().drop_trait();
                        if is_drop_impl {
                            referenced_callees.insert(item_path.clone());
                        }
                    }
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
                    let mut shadow_body =
                        pitbull_subset::mir_api::adapter::body(&real_body);
                    // Task Q.1 audit-cleanup (2026-05-26): the
                    // adapter's `body()` hardcodes `is_unsafe: false`
                    // and `is_async: false` because the rustc_public
                    // surface doesn't expose those flags. Extract
                    // them via the rustc_internal bridge (same
                    // pattern as PB018's `is_mutable_static` for
                    // statics). Without this, PB002 (unsafe fn) and
                    // PB026 (async fn) silently don't fire on real
                    // MIR — only on shadow-IR unit tests. The Q.1
                    // trust-test surfaced the gap; closing it here
                    // is in scope because it's adjacent (signature-
                    // level safety rules) to trust semantics.
                    let internal_id = rustc_public::rustc_internal::internal(
                        tcx,
                        item.def_id(),
                    );
                    // PRECONDITION (audit-cleanup L-2, 2026-05-26):
                    // `tcx.fn_sig` ICEs on non-fn DefIds. This is
                    // safe ONLY because we're inside the
                    // `ItemKind::Fn` match arm AND past the
                    // `has_body()` filter above — so `internal_id`
                    // is always a fn-like def with a body. Do NOT
                    // hoist this read above the kind match or the
                    // has_body guard, or a const/static/closure
                    // DefId would crash the compiler.
                    let fn_sig = tcx.fn_sig(internal_id).skip_binder().skip_binder();
                    shadow_body.is_unsafe = matches!(
                        fn_sig.safety,
                        rustc_hir::Safety::Unsafe,
                    );
                    shadow_body.is_async = matches!(
                        tcx.asyncness(internal_id),
                        rustc_middle::ty::Asyncness::Yes,
                    );
                    self.bodies_walked += 1;
                    walked += 1;
                    walked_fn_paths.insert(item_path.clone());
                    // O.1 + O.3: install spec-derived preconditions
                    // for this body so VC obligations emitted from
                    // its walk carry the assumptions. Two sources
                    // merged, with config taking the first slot
                    // (config is more deliberate; attribute is the
                    // common dev path):
                    //
                    //   1. `pitbull.toml`'s `[verification.preconditions]`
                    //      lookup by the item's full path (via
                    //      `CrateDef::name`).
                    //   2. `#[pitbull::requires("...")]` tool
                    //      attributes extracted by the HIR pre-pass
                    //      and keyed by `tcx.def_path_str(def_id)`.
                    //
                    // Bodies not in either map get an empty list
                    // — explicit "clear" so prior body's
                    // preconditions don't leak across the loop.
                    //
                    // Both paths produce the same kind of strings
                    // (predicate-grammar or raw-SMT-LIB); the
                    // visitor's downstream processing
                    // (`maybe_emit_overflow_obligation`) is
                    // source-agnostic.
                    let mut preconditions = cfg
                        .verification
                        .preconditions
                        .get(&item_path)
                        .cloned()
                        .unwrap_or_default();
                    if let Some(attr_preconds) =
                        hir_preconditions.get(&item_path)
                    {
                        preconditions.extend(attr_preconds.iter().cloned());
                    }
                    visitor.set_current_preconditions(preconditions);
                    // Q.4 (2026-05-26): mirror of preconditions
                    // for postconditions. The HIR pre-pass
                    // collects `#[pitbull::ensures("...")]`
                    // strings into hir_ensures; merge with
                    // pitbull.toml-side `[verification.ensures]`
                    // (config field added alongside this
                    // commit's wrapper wiring). For now, only
                    // the attribute-side is wired; toml-side
                    // can land in a follow-up if needed.
                    let ensures = hir_ensures
                        .get(&item_path)
                        .cloned()
                        .unwrap_or_default();
                    visitor.set_current_ensures(ensures);
                    // Task Q.1 (2026-05-26): `#[pitbull::trusted]`
                    // — the HIR pre-pass collects every fn-path with
                    // the attribute; here we look up the current
                    // item's path and pass the bool to visit_body.
                    // Trust short-circuits the MIR walk after
                    // signature checks (visitor.rs's
                    // `current_body_trusted`); PB002/PB026 still
                    // fire because they're signature-level and run
                    // before the short-circuit.
                    let is_trusted = hir_trusted.contains(&item_path);
                    visitor.visit_body(&shadow_body, is_trusted);
                    // #27: record this body's direct in-crate callees so the
                    // post-loop check can flag any that narrowing skipped.
                    // Trusted bodies do NOT propagate — by trusting the spec
                    // the user assumes responsibility for the body AND its
                    // callees (mirrors reachability.rs's trusted-no-propagate).
                    if !is_trusted {
                        for cp in pitbull_subset::reachability::callee_paths(&shadow_body) {
                            referenced_callees.insert(cp);
                        }
                    }
                }
                rustc_public::ItemKind::Static => {
                    // `verify_roots` is a reachability-closure filter
                    // for fn items — it picks the ROOT bodies to walk; the
                    // post-loop #27 check then fails closed on any in-crate
                    // callee of a root that narrowing skipped (so the call
                    // closure is ENFORCED, not silently dropped). It does
                    // NOT apply to project-level items like statics: PB018 (`static
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
            // #27 fail-closed reachability gate. A verify_roots-narrowed walk
            // skips in-crate callees of the roots. Flag any in-crate function
            // reachable from a verified (non-trusted) root that was NOT itself
            // verified, and fail closed on it — a "verified" verdict must
            // never rest on an unverified in-crate callee. Applied every run,
            // this transitively forces the whole reachable in-crate closure to
            // be covered. The user resolves it by widening verify_roots,
            // leaving verify_roots empty (full-crate coverage), or marking the
            // callee #[pitbull::trusted].
            let unverified = pitbull_subset::reachability::unverified_reachable_callees(
                &referenced_callees,
                &local_fn_universe,
                &walked_fn_paths,
                &hir_trusted,
            );
            for callee in &unverified {
                eprintln!(
                    "pitbull-rustc: PB-reachability: in-crate function `{callee}` is \
                     reachable from a verified root but was NOT verified (skipped by \
                     verify_roots narrowing). Add it to [reachability] verify_roots, \
                     leave verify_roots empty for full-crate coverage, or mark it \
                     #[pitbull::trusted]. Treating as unverified (fail-closed).",
                );
            }
            self.unverified_reachable_callees = unverified.len();
        } else if filtered_out > 0 {
            // Audit finding (2026-05-26 full-codebase sweep): when
            // `verify_roots` is empty but `exclude` patterns dropped
            // items, the count was previously NOT surfaced — items
            // vanished from verification silently. The project's
            // posture is "no silent skips": a config that excludes
            // (intentionally or by a too-broad glob like
            // `mycrate::*`) must make the dropped count VISIBLE so an
            // auditor cannot mistake "excluded" for "verified clean".
            eprintln!(
                "pitbull-rustc: {} item(s) excluded by `[reachability] exclude` \
                 patterns and NOT verified — confirm this is intended; an \
                 over-broad exclude glob can silently skip the whole crate.",
                filtered_out,
            );
        }
        // Warn about precondition keys that matched no walked function
        // (a typo, or a function filtered out by verify_roots/exclude):
        // those preconditions silently never applied (audit 2026-05-29,
        // "no silent skips"). The direction is safe — a missing
        // precondition means the obligation is checked with FEWER
        // assumptions (over-approximate / fail-closed) — but the user
        // must learn their key didn't bind rather than see an
        // unexpectedly-undischarged obligation with no explanation.
        for key in pitbull_subset::config::unmatched_precondition_keys(
            &cfg.verification.preconditions,
            &walked_fn_paths,
        ) {
            eprintln!(
                "pitbull-rustc: WARNING: [verification.preconditions] key `{key}` \
                 matched no verified function — its preconditions were NOT applied \
                 (check for a typo, or that the function is reached and not excluded).",
            );
        }
        // Cross-crate reachability manifest. When `PITBULL_REACH_DIR` is
        // set (the `cargo pitbull check` subcommand sets it), write this
        // crate's walked / referenced / trusted sets so the subcommand can
        // verify the WHOLE-workspace reachability closure. The per-crate
        // #27 gate above only sees the local crate (its `local_universe` is
        // this crate's items alone), so a workspace-member callee reached
        // ACROSS a crate boundary and skipped by the callee crate's own
        // `verify_roots` narrowing would otherwise slip past both crates'
        // local gates (SAFETY-MANUAL §3.6). Best-effort + non-fatal: a
        // manifest write failure warns but never changes the verdict.
        if let Some(dir) = std::env::var_os("PITBULL_REACH_DIR") {
            // crate_name is informational (the aggregation keys off the
            // referenced PATHS, not this field), so deriving it from a
            // walked/universe path's leading segment is sufficient — every
            // local item shares the crate prefix.
            let crate_name = local_fn_universe
                .iter()
                .chain(walked_fn_paths.iter())
                .map(|p| pitbull_subset::reachability::crate_of_path(p).to_string())
                .next()
                .unwrap_or_else(|| "unknown".to_string());
            let sorted = |s: &std::collections::HashSet<String>| {
                let mut v: Vec<String> = s.iter().cloned().collect();
                v.sort();
                v
            };
            let manifest = pitbull_subset::reachability::ReachManifest {
                crate_name: crate_name.clone(),
                walked: sorted(&walked_fn_paths),
                referenced: sorted(&referenced_callees),
                trusted: sorted(&hir_trusted),
            };
            match serde_json::to_string(&manifest) {
                Ok(json) => {
                    // One file per compile unit. A content hash keeps the
                    // name unique across crates AND across the multiple
                    // targets `cargo check --all-targets` compiles for one
                    // crate (lib/test/bin), while staying deterministic
                    // (idempotent re-runs overwrite the same file). The
                    // subcommand unions every manifest in the dir, so
                    // capturing all targets only ADDS coverage.
                    use std::hash::{Hash, Hasher};
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    json.hash(&mut h);
                    let fname = format!("{crate_name}-{:016x}.json", h.finish());
                    let path = std::path::Path::new(&dir).join(fname);
                    if let Err(e) = std::fs::write(&path, json) {
                        eprintln!(
                            "pitbull-rustc: WARNING: could not write reachability manifest \
                             to {}: {e}",
                            path.display(),
                        );
                    }
                }
                Err(e) => eprintln!(
                    "pitbull-rustc: WARNING: could not serialize reachability manifest: {e}",
                ),
            }
        }
        let mut report = visitor.into_report();
        // Append HIR-derived violations (PB001 unsafe blocks + PB003
        // unsafe impl/trait) to the MIR-derived violations. The two walks
        // see distinct constructs (HIR unsafe-blocks / unsafe-items vs MIR
        // statements/types), so there's no duplication concern.
        report.errors.extend(hir_violations);
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
        // Audit notes are non-violations the visitor flagged for auditor
        // review. A COVERAGE-GAP note (a safety check that could not run,
        // with no compensating obligation) is folded into the exit code
        // (M1, fail closed) so it is visible to a CI gate, not just on
        // stderr; a TRANSPARENCY note is informational only.
        for note in &report.audit_notes {
            eprintln!("pitbull-rustc: {note}");
        }
        self.coverage_gap_notes = report.coverage_gap_count();
        if self.coverage_gap_notes > 0 {
            if self.fail_on_coverage_gaps {
                eprintln!(
                    "pitbull-rustc: {} coverage-gap audit note(s) — a safety check could \
                     not run with no compensating obligation; failing closed (exit 1). \
                     Set `[verification] fail_on_coverage_gaps = false` to downgrade these \
                     to non-blocking notes.",
                    self.coverage_gap_notes,
                );
            } else {
                eprintln!(
                    "pitbull-rustc: {} coverage-gap audit note(s) present but \
                     `fail_on_coverage_gaps = false` — NOT affecting the exit code (the \
                     verdict does not cover these sites).",
                    self.coverage_gap_notes,
                );
            }
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
            // Build the solver pool from config (Task S). Each
            // configured name maps to a known descriptor; an unknown
            // name is surfaced as a loud WARNING and skipped. DUPLICATE
            // names are deduped (audit 2026-05-29, Critical): without
            // this, `solvers = ["z3","z3"]` would spawn one binary
            // twice and let its single `unsat` count as two independent
            // votes, collapsing the gate back to single-solver trust.
            // `vote` also counts distinct names as a backstop, but we
            // dedup here so we don't run the same binary twice and so
            // the duplicate is reported. If the resulting pool is empty
            // — or smaller than the agreement threshold — every
            // obligation will (soundly) fail to discharge; we say so up
            // front rather than letting it read as a silent
            // "nothing verifies".
            let mut solvers: Vec<pitbull_vc::solver::Solver> = Vec::new();
            for name in &cfg.verification.solvers {
                match pitbull_vc::solver::known_solver(name) {
                    Some(s) => {
                        if solvers.iter().any(|existing| existing.name == s.name) {
                            eprintln!(
                                "pitbull-rustc: WARNING: duplicate solver `{name}` in \
                                 [verification] solvers — counted once (a duplicate \
                                 cannot provide independent agreement).",
                            );
                        } else {
                            solvers.push(s);
                        }
                    }
                    None => eprintln!(
                        "pitbull-rustc: WARNING: unknown solver `{name}` in \
                         [verification] solvers — ignoring. Known: z3, cvc5, alt-ergo.",
                    ),
                }
            }
            // Enforce [verification.solver_versions] pins (hardening
            // 2026-05-29). For each pooled solver with a pinned version,
            // probe `--version`; if the pinned string is not present in
            // the output, the binary is NOT the pinned build, so DROP it
            // from the pool. This is fail-closed: a non-pinned (possibly
            // swapped/buggy) solver's vote is not trusted, and a smaller
            // pool only makes the agreement threshold HARDER to reach
            // (never a false discharge). The dropped solver is surfaced
            // loudly. (No pin for a solver ⇒ it runs unchecked, matching
            // the documented opt-in behavior.)
            if !cfg.verification.solver_versions.is_empty() {
                solvers.retain(|s| match cfg.verification.solver_versions.get(s.name) {
                    None => true,
                    Some(pinned) => match pitbull_vc::solver::probe_version(s) {
                        // Version pin satisfied ⇒ keep the solver. The
                        // token-match rationale (a pin must equal a WHOLE
                        // version token, so `1.0` does not trust a reported
                        // `11.0.5`) lives in `version_matches`, which is
                        // unit-tested on the stable lane (red-team Low,
                        // 2026-05-29).
                        Some(out) if pitbull_vc::solver::version_matches(&out, pinned) => true,
                        Some(out) => {
                            eprintln!(
                                "pitbull-rustc: WARNING: solver `{}` version mismatch — \
                                 pinned `{pinned}`, reported `{out}`; dropping it from the \
                                 agreement pool (its vote will not count).",
                                s.name,
                            );
                            false
                        }
                        None => {
                            eprintln!(
                                "pitbull-rustc: WARNING: solver `{}` is pinned to `{pinned}` \
                                 but its version could not be determined (not installed, or \
                                 `--version` failed); dropping it from the pool.",
                                s.name,
                            );
                            false
                        }
                    },
                });
            }
            if cfg.verification.solver_agreement == 0 {
                eprintln!(
                    "pitbull-rustc: WARNING: [verification] solver_agreement = 0 is \
                     invalid; using 1 (a 0 threshold would vacuously discharge).",
                );
            }
            let threshold = usize::from(cfg.verification.solver_agreement).max(1);
            if solvers.is_empty() {
                eprintln!(
                    "pitbull-rustc: WARNING: no usable solver in [verification] \
                     solvers — every obligation will be undischarged (fail closed).",
                );
            } else if solvers.len() < threshold {
                eprintln!(
                    "pitbull-rustc: WARNING: agreement threshold {threshold} exceeds \
                     the {} usable solver(s) in the pool — NO obligation can \
                     discharge. Install more solvers or lower \
                     [verification] solver_agreement.",
                    solvers.len(),
                );
            }
            let raw_timeout = cfg.verification.vc_timeout_seconds;
            if raw_timeout == 0 {
                eprintln!(
                    "pitbull-rustc: WARNING: [verification] vc_timeout_seconds = 0; \
                     using 1s (0 disables some solvers' check-sat timeout \
                     asymmetrically).",
                );
            }
            let timeout = std::time::Duration::from_secs(raw_timeout.max(1));
            let (undischarged, certs) =
                dispatch_vc_obligations(&report, &solvers, threshold, timeout);
            self.undischarged_obligations += undischarged;
            // Optional proof-certificate emission (Task T.2). When
            // PITBULL_CERT_OUT is set, write the replayable certificate
            // bundle (one entry per main-check obligation) as JSON.
            // Same H3 path-safety guard as PITBULL_SARIF_OUT: the env
            // var is adversarially controllable via build.rs, so refuse
            // paths that don't end in `.json` or that contain `..`.
            // Emission is best-effort (warn, don't abort) — the verdict
            // and exit code do not depend on the certificate file.
            if let Some(out) = std::env::var_os("PITBULL_CERT_OUT") {
                let out_path = std::path::PathBuf::from(&out);
                if let Err(e) = check_env_path("PITBULL_CERT_OUT", &out_path, &["json"]) {
                    eprintln!("pitbull-rustc: refusing certificate write: {e}");
                } else {
                    let crate_name = std::env::var("CARGO_PKG_NAME")
                        .unwrap_or_else(|_| "unknown".to_string());
                    let mut bundle = pitbull_vc::cert::CertificateBundle::new(
                        env!("CARGO_PKG_VERSION"),
                        crate_name,
                        threshold,
                        raw_timeout.max(1),
                        solvers.iter().map(|s| s.name.to_string()).collect(),
                    );
                    bundle.obligations = certs;
                    // Sign the bundle if a key is configured (Task T.3).
                    // PITBULL_CERT_KEY is a path to a key file; an
                    // HMAC-SHA256 over the canonical bundle makes the
                    // certificate tamper-resistant (a swapped SMT or
                    // edited threshold invalidates it). Without a key the
                    // certificate is emitted UNSIGNED (still replayable,
                    // but tampering is not detectable).
                    if let Some(keypath) = std::env::var_os("PITBULL_CERT_KEY") {
                        match pitbull_vc::cert::read_key_file(std::path::Path::new(&keypath)) {
                            Ok(key) => {
                                if key.len() < pitbull_vc::cert::MIN_RECOMMENDED_KEY_BYTES {
                                    eprintln!(
                                        "pitbull-rustc: WARNING: PITBULL_CERT_KEY is short \
                                         ({} bytes); a weak key undermines the \
                                         tamper-resistance signing is meant to provide.",
                                        key.len(),
                                    );
                                }
                                match bundle.sign(&key) {
                                    Ok(()) => eprintln!(
                                        "pitbull-rustc: certificate signed (HMAC-SHA256).",
                                    ),
                                    Err(e) => eprintln!(
                                        "pitbull-rustc: WARNING: certificate signing failed \
                                         ({e}); emitting UNSIGNED certificate.",
                                    ),
                                }
                            }
                            Err(e) => eprintln!(
                                "pitbull-rustc: WARNING: {e}; emitting UNSIGNED certificate.",
                            ),
                        }
                    }
                    match bundle.to_json() {
                        Ok(text) => match std::fs::write(&out_path, text) {
                            Ok(()) => eprintln!(
                                "pitbull-rustc: proof certificate ({} obligation(s)) \
                                 written to {}",
                                bundle.obligations.len(),
                                out_path.display(),
                            ),
                            Err(e) => eprintln!(
                                "pitbull-rustc: failed to write certificate to {}: {e}",
                                out_path.display(),
                            ),
                        },
                        Err(e) => eprintln!("pitbull-rustc: certificate serialize failed: {e}"),
                    }
                }
            }
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
/// Returns the number of undischarged obligations so the caller
/// can fold them into the wrapper's exit-code calculation
/// (audit-cleanup F10).
///
/// Free function (not a method on `PitbullCallbacks`) because it
/// only reads the report and accumulates a result — no callback
/// state mutation needed.
/// Short tag for a `SolverResult`, for the per-solver breakdown line.
#[cfg(rustc_public_real)]
fn solver_result_tag(r: &pitbull_vc::SolverResult) -> &'static str {
    match r {
        pitbull_vc::SolverResult::Sat => "sat",
        pitbull_vc::SolverResult::Unsat => "unsat",
        pitbull_vc::SolverResult::Unknown => "unknown",
        pitbull_vc::SolverResult::NotInstalled => "not-installed",
        pitbull_vc::SolverResult::Timeout => "timeout",
        pitbull_vc::SolverResult::Error(_) => "error",
    }
}
/// Render a per-solver breakdown like `z3=unsat cvc5=unsat alt-ergo=error`.
#[cfg(rustc_public_real)]
fn solver_breakdown(results: &[(String, pitbull_vc::SolverResult)]) -> String {
    results
        .iter()
        .map(|(n, r)| format!("{n}={}", solver_result_tag(r)))
        .collect::<Vec<_>>()
        .join(" ")
}
/// Compile each `VcObligation`, then discharge it through the
/// MULTI-SOLVER AGREEMENT GATE (Task S, 2026-05-28): every
/// configured solver runs the same problem in parallel, and an
/// obligation is reported `discharged` only when at least
/// `threshold` solvers independently return `unsat` AND none
/// returns `sat`. This closes the TCB hole where a single hostile
/// or buggy `z3` on `PATH` could rubber-stamp unsafe code by
/// wrongly returning `unsat` (Safety Manual §3.3).
///
/// Returns the number of undischarged obligations for the
/// wrapper's exit-code calculation (F10).
#[cfg(rustc_public_real)]
fn dispatch_vc_obligations(
    report: &pitbull_subset::SubsetReport,
    solvers: &[pitbull_vc::solver::Solver],
    threshold: usize,
    timeout: std::time::Duration,
) -> (usize, Vec<pitbull_vc::cert::ObligationCertificate>) {
    use pitbull_vc::solver::{run_solvers, vote, AgreementVerdict};
    let mut solver_missing_announced = false;
    let mut discharged = 0usize;
    let mut undischarged = 0usize;
    // Proof certificates (Task T.2): one per obligation that reaches
    // the MAIN agreement check. The early-exit paths above (compilation
    // pending, consistency-refused, consistency-unconfirmed) do not
    // produce a main-check certificate — they have no `goal.smt`
    // decision to replay; their "undischarged" status is recorded on
    // stderr. Certifying those refusal decisions is a future extension.
    let mut certs: Vec<pitbull_vc::cert::ObligationCertificate> = Vec::new();
    for obligation in &report.vc_obligations {
        // Canonical PSS-1 rule ID (uppercase `PBxxx`) on every
        // verdict line, so tests/SARIF consumers and auditors don't
        // have to map `pb054-idx-0` → PB054.
        let rule = obligation.kind.rule_id();
        let Some(goal) = pitbull_vc::compile(obligation) else {
            eprintln!(
                "pitbull-rustc: vc {} ({rule}): pending (compilation not yet supported for {:?})",
                obligation.id, obligation.kind,
            );
            undischarged += 1;
            continue;
        };
        // Soundness guard (red-team F1), now multi-solver: if
        // assumptions are present, FIRST verify they are jointly
        // satisfiable. Contradictory preconditions would make the
        // main check vacuously unsat for EVERY honest solver —
        // silently "verifying" unsafe code via vacuous implication,
        // which the agreement gate alone would NOT catch (all
        // honest solvers agree unsat). So: if ANY configured solver
        // proves the assumptions contradictory (`unsat`), refuse.
        // Erring toward detecting contradictions is the safe
        // direction (a false refusal rejects safe code; a missed
        // contradiction is unsound).
        if let Some(cs_smt) = &goal.consistency_check {
            let cs_results = run_solvers(solvers, cs_smt, timeout);
            // (1) Refuse if ANY solver proves the assumptions
            // contradictory: a vacuously-unsat main check would
            // otherwise silently "verify" unsafe code. Erring toward
            // refusal is the safe direction.
            let any_unsat = cs_results
                .iter()
                .any(|(_, r)| *r == pitbull_vc::SolverResult::Unsat);
            if any_unsat {
                eprintln!(
                    "pitbull-rustc: vc {} ({rule}): REFUSED — preconditions are \
                     contradictory (a solver's consistency check returned unsat: \
                     [{}]); a discharge claim here would be vacuously true",
                    obligation.id,
                    solver_breakdown(&cs_results),
                );
                undischarged += 1;
                continue;
            }
            // (2) To PROCEED soundly we need POSITIVE evidence the
            // assumptions are jointly satisfiable. If they are NOT
            // (contradictory) but no solver managed to return `unsat`
            // — e.g. the consistency check timed out, errored, or
            // returned `unknown` — then the main check
            // `assumptions ∧ ¬safety` could be vacuously `unsat` and
            // we would falsely discharge. So require the SAME
            // `threshold` of independent solvers to agree `sat` that
            // we require for the safety property; one solver's `sat`
            // is not trusted (audit 2026-05-29, Critical regression:
            // Timeout/Error/Unknown on the consistency check used to
            // fall through to the main check and risk a vacuous
            // discharge). The all-not-installed case is exempt: there
            // is no solver at all, so we fall through and let the main
            // check emit the canonical "no solver" verdict (also
            // undischarged — still fail-closed).
            let all_not_installed = !cs_results.is_empty()
                && cs_results
                    .iter()
                    .all(|(_, r)| *r == pitbull_vc::SolverResult::NotInstalled);
            if !all_not_installed {
                let mut sat_voters: Vec<&str> = cs_results
                    .iter()
                    .filter(|(_, r)| *r == pitbull_vc::SolverResult::Sat)
                    .map(|(n, _)| n.as_str())
                    .collect();
                sat_voters.sort_unstable();
                sat_voters.dedup();
                if sat_voters.len() < threshold {
                    eprintln!(
                        "pitbull-rustc: vc {} ({rule}): undischarged — could not \
                         confirm the preconditions are jointly satisfiable \
                         ({}/{threshold} independent solvers returned sat: [{}]); \
                         refusing to risk a vacuous discharge",
                        obligation.id,
                        sat_voters.len(),
                        solver_breakdown(&cs_results),
                    );
                    undischarged += 1;
                    continue;
                }
            }
            // Otherwise: `threshold` solvers confirmed the assumptions
            // satisfiable (or no solver is installed at all). Proceed
            // to the main check.
        }
        // "[N assumption(s)]" suffix surfaces how many hypotheses
        // the solvers received (audit finding L-3 visibility).
        let n_assumptions = obligation.assumptions.len();
        let assumption_suffix = if n_assumptions == 0 {
            String::new()
        } else {
            format!(
                " [{n_assumptions} assumption{}]",
                if n_assumptions == 1 { "" } else { "s" },
            )
        };
        // Main check through the agreement gate.
        let results = run_solvers(solvers, &goal.smt, timeout);
        let breakdown = solver_breakdown(&results);
        // Record a replayable proof certificate for this obligation
        // (Task T.2). Built from the SAME results the verdict below is
        // derived from, so the certificate's recorded decision exactly
        // matches the live one. Emitted to disk by the caller when
        // PITBULL_CERT_OUT is set.
        certs.push(pitbull_vc::cert::ObligationCertificate::from_run(
            obligation.id.as_str(),
            rule,
            goal.smt.as_str(),
            &results,
            threshold,
        ));
        // If the pool is empty, OR every solver is not-installed,
        // that's the "no solver" case — announce the install hint once.
        // (Empty `results` means an empty pool; treating it here as
        // "no solver" — not "insufficient agreement" — keeps the
        // diagnostic accurate; audit 2026-05-29.)
        let all_missing = results.is_empty()
            || results
                .iter()
                .all(|(_, r)| *r == pitbull_vc::SolverResult::NotInstalled);
        match vote(&results, threshold) {
            AgreementVerdict::Discharged { unsat_votes } => {
                // Format note: the verdict keeps the literal substring
                // `discharged (unsat` first so existing integration
                // assertions and SARIF consumers that match on it keep
                // working; the agreement count is appended.
                eprintln!(
                    "pitbull-rustc: vc {} ({rule}): discharged (unsat — safety property \
                     holds; {unsat_votes}-solver agreement){assumption_suffix} [{breakdown}]",
                    obligation.id,
                );
                discharged += 1;
            }
            AgreementVerdict::Refuted => {
                eprintln!(
                    "pitbull-rustc: vc {} ({rule}): NOT DISCHARGED (sat — counterexample \
                     exists){assumption_suffix} [{breakdown}]",
                    obligation.id,
                );
                undischarged += 1;
            }
            AgreementVerdict::Disagreement { unsat, sat } => {
                // The loudest possible diagnostic: solvers split on
                // the same problem. One is wrong; we cannot tell
                // which, so we MUST fail closed. This is precisely
                // the event the gate exists to surface.
                eprintln!(
                    "pitbull-rustc: vc {} ({rule}): DISAGREEMENT — solvers split on the \
                     same problem (unsat: {unsat:?}; sat: {sat:?}). Refusing to trust \
                     either verdict; treat as UNVERIFIED and investigate (likely a \
                     solver bug or a missed counterexample).{assumption_suffix} [{breakdown}]",
                    obligation.id,
                );
                undischarged += 1;
            }
            AgreementVerdict::Inconclusive { unsat_votes, threshold } => {
                if all_missing {
                    if !solver_missing_announced {
                        eprintln!(
                            "pitbull-rustc: no configured solver is installed; VC \
                             obligations cannot be discharged. Install at least \
                             {threshold} of the configured solvers (e.g. z3, cvc5) \
                             and add them to PATH.",
                        );
                        solver_missing_announced = true;
                    }
                    eprintln!(
                        "pitbull-rustc: vc {} ({rule}): undischarged (no solver){assumption_suffix} [{breakdown}]",
                        obligation.id,
                    );
                } else {
                    eprintln!(
                        "pitbull-rustc: vc {} ({rule}): undischarged (insufficient \
                         agreement: {unsat_votes}/{threshold} unsat votes — need \
                         {threshold} independent solvers to agree){assumption_suffix} [{breakdown}]",
                        obligation.id,
                    );
                }
                undischarged += 1;
            }
        }
    }
    eprintln!(
        "pitbull-rustc: VC summary: {} obligation(s), {} discharged, {} undischarged \
         (agreement threshold {threshold} of {} solver(s))",
        report.vc_obligations.len(),
        discharged,
        undischarged,
        solvers.len(),
    );
    (undischarged, certs)
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
/// - Audit-cleanup (audit finding N2, 2026-05-26): symbolic links.
///   A build.rs that creates `/tmp/x.json` → symlink to
///   `~/.config/Code/User/settings.json` and sets
///   `PITBULL_SARIF_OUT=/tmp/x.json` would defeat the extension
///   filter — the path *is* a `.json`, but `std::fs::write` follows
///   the symlink and overwrites the target. We refuse when the
///   leaf-component is a symlink.
///
/// What it doesn't catch
/// ---------------------
/// - A path with the right extension that points somewhere it
///   shouldn't (e.g. `~/.config/sneaky.toml`).
/// - A symlink to a symlink to a sensitive file *via intermediate
///   non-symlink components* — e.g. `/a/b/c.toml` where `b` is a
///   symlink to `~/.ssh/` and `c.toml` exists in the target. We
///   only `symlink_metadata` the leaf path; intermediate-component
///   resolution would require walking `path.canonicalize` and
///   comparing each step, which is more invasive and less
///   immediately useful. The remaining attack surface is narrow:
///   the build.rs would have to create the intermediate symlink
///   itself, which it can also do without the leaf-symlink trick.
///
/// Escape hatch
/// ------------
/// `PITBULL_ALLOW_UNSAFE_PATHS=1` disables all checks for the
/// rare user whose legitimate config path doesn't match the
/// extension whitelist (e.g. a deliberately-symlinked config
/// shared across projects). Production should leave this unset.
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
    // Symlink check (audit finding N2). `symlink_metadata` doesn't
    // follow the link — it returns metadata about the link itself.
    // If the path doesn't exist yet (common for PITBULL_SARIF_OUT
    // — the wrapper creates it), `symlink_metadata` returns Err,
    // which we treat as "no symlink to worry about, the wrapper
    // will create a fresh file".
    if let Ok(meta) = std::fs::symlink_metadata(path) {
        if meta.file_type().is_symlink() {
            return Err(format!(
                "{var_name}={} is a symbolic link; refusing as defense \
                 against build-script symlink-redirect attacks (a path-dep \
                 could create a symlink with a whitelisted extension that \
                 points at a sensitive file). Set \
                 PITBULL_ALLOW_UNSAFE_PATHS=1 to override.",
                path.display(),
            ));
        }
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
                // Fail closed (audit 2026-05-31). A config POLICY violation —
                // unsupported toolchain (PB071), panic_strategy != "abort"
                // (PB048), non-{16,32,64} pointer width (PB052), out-of-range
                // trust budget (PB068), or a malformed trusted-build-script
                // hash (PB060) — invalidates the soundness basis for the
                // entire run (the per-toolchain / per-config trust argument no
                // longer holds). These were previously printed and then
                // IGNORED (exit 0 if the bodies happened to be clean) — a
                // fail-open. Refuse to verify, mirroring the structural
                // load-error path below.
                std::process::exit(2);
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
/// HIR pre-pass: a single walk over the crate's HIR that
/// extracts:
///
/// 1. **PB001 unsafe-block violations** — every user-authored
///    `unsafe { ... }` block (filtered by `Span::from_expansion`
///    so `vec![]`, `format!()`, etc. don't false-positive).
/// 2. **`#[pitbull::requires("...")]` preconditions** — tool
///    attributes on function items, indexed by fully-qualified
///    function path. v0.2 Task O.3.
///
/// ## Why HIR and not MIR
///
/// MIR construction discards HIR-level scope information.
/// PB001's "bare unsafe block" can't be reconstructed from MIR
/// (operations inside fire their own rules — PB004/PB007/PB009 —
/// but the syntactic block itself is gone). And attributes like
/// `#[pitbull::requires(...)]` only exist as HIR `Attribute`s;
/// they don't survive into MIR at all.
///
/// ## How
///
/// `tcx.hir_visit_all_item_likes_in_crate` enters every free
/// item, trait item, impl item, and foreign item. With
/// `NestedFilter = nested_filter::All`, the visitor recurses
/// into nested items (including bodies). Two hooks:
///   - `visit_block` matches `BlockCheckMode::UnsafeBlock(
///     UnsafeSource::UserProvided)` for PB001 emission.
///   - `visit_item` filters for `ItemKind::Fn(...)` and reads
///     `tcx.hir_attrs(item.hir_id())` to find
///     `#[pitbull::requires("...")]`. The attribute path is
///     matched via `attr.path_matches(&[pitbull, requires])`;
///     the string argument is extracted via
///     `meta_item_list().get(0).lit()`.
///
/// Returns the violations, a partial filename table (merged with
/// `adapter::take_filename_table()` for SARIF URIs), and the
/// HIR-derived precondition map (merged with
/// `cfg.verification.preconditions` per call site).
/// Result of the HIR pre-pass. A named struct rather than a bare
/// 5-tuple: two of the fields (`preconditions` and `ensures`) share
/// the identical type `HashMap<String, Vec<String>>`, so a positional
/// tuple invited a silent swap — exactly the kind of mistake a
/// soundness tool must not ship. (Also clears clippy::type_complexity.)
#[cfg(rustc_public_real)]
struct HirPrePass {
    /// HIR-level violations: PB001 (`unsafe {}` block) and PB003
    /// (`unsafe trait` / `unsafe impl`) — both are item/scope constructs
    /// the MIR-body visitor cannot see.
    violations: Vec<pitbull_subset::SubsetError>,
    /// Partial DefId→filename table, merged for SARIF URIs.
    filename_table: std::collections::HashMap<u32, String>,
    /// `#[pitbull::requires(...)]` preconditions by fn path.
    preconditions: std::collections::HashMap<String, Vec<String>>,
    /// `#[pitbull::trusted]` function paths.
    trusted: std::collections::HashSet<String>,
    /// `#[pitbull::ensures(...)]` postconditions by fn path.
    ensures: std::collections::HashMap<String, Vec<String>>,
}
#[cfg(rustc_public_real)]
fn collect_hir_pre_pass(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    allowed_proc_macros: &[String],
) -> HirPrePass {
    let mut visitor = HirPreVisitor {
        tcx,
        violations: Vec::new(),
        filename_table: std::collections::HashMap::new(),
        preconditions: std::collections::HashMap::new(),
        ensures: std::collections::HashMap::new(),
        trusted: std::collections::HashSet::new(),
        allowed_proc_macros: allowed_proc_macros.to_vec(),
        pb059_seen: std::collections::HashSet::new(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
    HirPrePass {
        violations: visitor.violations,
        filename_table: visitor.filename_table,
        preconditions: visitor.preconditions,
        trusted: visitor.trusted,
        ensures: visitor.ensures,
    }
}
#[cfg(rustc_public_real)]
struct HirPreVisitor<'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    violations: Vec<pitbull_subset::SubsetError>,
    filename_table: std::collections::HashMap<u32, String>,
    /// HIR-derived preconditions keyed by fully-qualified function
    /// path (`tcx.def_path_str(def_id)`). The wrapper merges this
    /// with `cfg.verification.preconditions` before each
    /// `visit_body` so users can mix attribute-based and
    /// config-based preconditions on the same function.
    preconditions: std::collections::HashMap<String, Vec<String>>,
    /// HIR-derived POSTCONDITIONS keyed by fully-qualified
    /// function path. Task Q.4 (2026-05-26). Mirror of
    /// `preconditions` for the `#[pitbull::ensures("...")]`
    /// attribute. The wrapper passes the merged list to
    /// `SubsetVisitor::set_current_ensures` before each
    /// `visit_body`. The visitor emits a `PB076 EnsuresPostcondition`
    /// obligation at every `TerminatorKind::Return`.
    ensures: std::collections::HashMap<String, Vec<String>>,
    /// Function paths marked `#[pitbull::trusted]` (Task Q.1,
    /// 2026-05-26). The wrapper looks up each item in this set
    /// and passes `trusted=true` to `SubsetVisitor::visit_body`,
    /// which already short-circuits the MIR walk after signature
    /// checks. PB002 (unsafe fn) and PB026 (async fn) STILL fire
    /// on trusted bodies — trust does NOT admit unsafe; it only
    /// trusts the body's contract (typically used for FFI shims
    /// whose body Pitbull can't reason about but whose
    /// signature is auditable). See visitor.rs's
    /// `current_body_trusted` field for the short-circuit point.
    trusted: std::collections::HashSet<String>,
    /// PB059 proc-macro allowlist (`cfg.subset.allowed_proc_macros`).
    /// Every derive/attribute-macro expansion that produced a reachable
    /// item has its DEFINING crate checked against this list.
    allowed_proc_macros: Vec<String>,
    /// PB059 dedup: one `#[derive(Foo, Bar)]` generates several impl
    /// items, all tracing to the same macro call-site. Key on
    /// `crate:call_site` so we emit at most one PB059 per invocation.
    pb059_seen: std::collections::HashSet<String>,
}
#[cfg(rustc_public_real)]
impl<'tcx> HirPreVisitor<'tcx> {
    /// PB059: flag a reachable item generated by a non-allowlisted
    /// proc-macro. Walk `sp`'s expansion chain (outermost-in); for any
    /// `Derive`/`Attr` macro expansion whose DEFINING crate is not the
    /// local crate, not a trusted toolchain crate, and not on
    /// `allowed_proc_macros`, push a PB059 violation pointing at the
    /// user's macro call-site. Derive/attribute macros cannot be
    /// written with `macro_rules!` and built-in derives live in
    /// core/std, so a Derive/Attr expansion from a non-trusted external
    /// crate is, by construction, an external proc-macro — no
    /// `macro_rules!` false positives. (Function-like `Bang` proc-macros
    /// are a tracked follow-up: distinguishing them from external
    /// `macro_rules!` needs a proc-macro-crate check.)
    fn check_pb059_provenance(&mut self, sp: rustc_span::Span) {
        if !sp.from_expansion() {
            return;
        }
        let mut ctxt = sp.ctxt();
        // Bound the walk against any pathological hygiene chain.
        let mut guard = 0u32;
        while !ctxt.is_root() && guard < 64 {
            guard += 1;
            let data = ctxt.outer_expn_data();
            if let rustc_span::hygiene::ExpnKind::Macro(macro_kind, macro_name) = data.kind {
                if matches!(
                    macro_kind,
                    rustc_span::hygiene::MacroKind::Derive
                        | rustc_span::hygiene::MacroKind::Attr
                ) {
                    if let Some(def_id) = data.macro_def_id {
                        let is_local = def_id.krate == rustc_hir::def_id::LOCAL_CRATE;
                        let macro_crate = self.tcx.crate_name(def_id.krate).to_string();
                        if pitbull_subset::config::pb059_proc_macro_rejected(
                            &macro_crate,
                            is_local,
                            &self.allowed_proc_macros,
                        ) {
                            let key = format!("{macro_crate}:{}", data.call_site.lo().0);
                            if self.pb059_seen.insert(key) {
                                let span = rustc_span_to_shadow(
                                    self.tcx,
                                    data.call_site,
                                    &mut self.filename_table,
                                );
                                self.violations.push(pitbull_subset::SubsetError {
                                    rule: pitbull_subset::rules::PB059,
                                    span,
                                    detail: format!(
                                        "reachable code generated by non-allowlisted \
                                         proc-macro `{macro_name}` from crate \
                                         `{macro_crate}` — add `{macro_crate}` to \
                                         [subset] allowed_proc_macros to permit it",
                                    ),
                                    in_spec: false,
                                });
                            }
                        }
                    }
                }
            }
            ctxt = data.call_site.ctxt();
        }
    }
    /// Extract precondition / postcondition strings from a
    /// `#[pitbull::<name>(...)]` attribute. Two forms accepted:
    ///
    /// 1. **String-literal** (O.3 baseline):
    ///    `#[pitbull::<name>("x < 100")]` — uses `meta_item_list()`
    ///    to extract a `LitKind::Str`. Stable, well-understood.
    /// 2. **Expression-form** (Q.3, 2026-05-26):
    ///    `#[pitbull::<name>(x < 100)]` — when `meta_item_list()`
    ///    returns None or empty (the arg isn't a meta-item), we
    ///    fall through to the raw `AttrArgs::Delimited` path and
    ///    pretty-print the token stream via
    ///    `rustc_ast_pretty::pprust::tts_to_string`.
    ///
    /// Used for both `requires` and `ensures` (Task Q.4,
    /// 2026-05-26); the body is `<name>`-agnostic — the caller
    /// pre-checks the attribute path with `attr.path_matches(...)`.
    /// Renamed from `extract_requires_strings` when Q.4 added
    /// the ensures sibling path; both call sites now route
    /// through this helper.
    fn extract_attr_strings(
        &self,
        attr: &rustc_hir::Attribute,
    ) -> Vec<String> {
        // Path 1: meta-item list (string-literal form).
        if let Some(meta_list) = attr.meta_item_list() {
            let mut out = Vec::new();
            for meta_inner in meta_list {
                if let Some(lit) = meta_inner.lit() {
                    if let rustc_ast::ast::LitKind::Str(symbol, _style) = lit.kind {
                        out.push(symbol.to_string());
                    }
                }
            }
            if !out.is_empty() {
                return out;
            }
        }
        // Path 2: Q.3 expression-form. The attribute's args are a
        // raw token stream (e.g. `(x < 100)`). Pretty-print the
        // inner tokens (without the outer parens). We use rustc's
        // own pretty-printer via `rustc_ast_pretty::pprust::tts_to_string`
        // to maintain consistency with how rustc renders the
        // attribute in diagnostics.
        let normal = attr.get_normal_item();
        if let rustc_hir::AttrArgs::Delimited(delim) = &normal.args {
            let stringified = rustc_ast_pretty::pprust::tts_to_string(&delim.tokens);
            // Defense-in-depth (audit-cleanup L-1, 2026-05-26):
            // the stringified attribute flows into the predicate
            // parser or the F2 raw-SMT validator, both of which
            // scan by `char`. SMT-LIB 2.6 only assigns meaning to
            // ASCII, and the F2 validator already rejects `"`,
            // `;`, and `|`. A non-ASCII byte that Z3's UTF-8 lexer
            // treats as a paren/whitespace while F2's char-scan
            // misses it would be the only residual injection
            // vector — almost certainly empty (no such SMT-LIB
            // grammar char exists), but the assert makes it
            // provably closed in debug builds. Release builds
            // skip the check (the F2 validator is the real guard);
            // a non-ASCII string just fails to parse as a predicate
            // and gets audit-noted by the visitor.
            debug_assert!(
                stringified.is_ascii(),
                "expression-form attribute pretty-printed to non-ASCII: {stringified:?}",
            );
            return vec![stringified.trim().to_string()];
        }
        Vec::new()
    }
}
#[cfg(rustc_public_real)]
impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for HirPreVisitor<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;
    fn maybe_tcx(&mut self) -> rustc_middle::ty::TyCtxt<'tcx> {
        self.tcx
    }
    /// O.3: extract `#[pitbull::requires("...")]` tool
    /// attributes from function items. The user crate must have
    /// `#![register_tool(pitbull)]` for rustc to preserve the
    /// attribute through HIR; without it the parser rejects
    /// `pitbull::*` paths entirely.
    ///
    /// Only string-literal arguments are accepted:
    /// `#[pitbull::requires("x < 100")]`. Non-string arguments
    /// (raw token streams, expressions, etc.) are silently
    /// skipped — the v0.2 attribute extraction stays close to
    /// the on-disk pitbull.toml format (also string-based).
    /// Future work: accept Rust-expression-form arguments
    /// `#[pitbull::requires(x < 100)]` via proper attribute
    /// parsing.
    /// Task Q.2 (2026-05-26): extract `#[pitbull::requires]` and
    /// `#[pitbull::trusted]` from methods on impl blocks. The
    /// item-walk (`rustc_public::all_local_items`) already
    /// flattens impl methods into `ItemKind::Fn` entries (via
    /// `tcx.mir_keys` which includes `DefKind::AssocFn`) — so the
    /// MIR body walk and VC emission already work for impl
    /// methods. What was MISSING was the attribute extraction:
    /// `HirPreVisitor::visit_item` only handles top-level items.
    /// `visit_impl_item` runs alongside `visit_item` and applies
    /// the same `requires`/`trusted` extraction logic to
    /// `ImplItemKind::Fn`.
    ///
    /// Trait items (`visit_trait_item`) are deferred — trait
    /// default methods can have bodies but are a smaller corner
    /// case. Tracked as a follow-up gap.
    /// Task Q.2 fix: `hir_visit_all_item_likes_in_crate` calls
    /// `visit_impl_item` directly for every impl item in the
    /// crate. Separately, when `walk_item` fires on the parent
    /// `ItemKind::Impl`, the `NestedFilter::All` setting causes
    /// `visit_nested_impl_item` to recurse into each item — also
    /// calling `visit_impl_item`. The double-fire was observed
    /// during Q.2 debugging (impl method's `#[pitbull::requires]`
    /// produced TWO precondition entries → 3 assumptions instead
    /// of expected 2). Override `visit_nested_impl_item` to a
    /// no-op so the direct-call path is the only one that
    /// produces attribute extraction. PB001 unsafe-block
    /// detection inside method bodies still works because
    /// `visit_block` runs from the direct visit_impl_item
    /// call's walk_impl_item recursion (which we DON'T skip).
    fn visit_nested_impl_item(&mut self, _id: rustc_hir::ImplItemId) {}
    /// Same rationale as `visit_nested_impl_item` above, applied to
    /// trait items (default methods). `hir_visit_all_item_likes_in_crate`
    /// directly calls `visit_trait_item` for every trait item; the
    /// `walk_item(ItemKind::Trait)` recursion under `NestedFilter::All`
    /// would also call it via `visit_nested_trait_item`. Without this
    /// override, PB001 unsafe-block detection inside trait default
    /// methods would double-fire (audit-cleanup post-Q.3 red-team
    /// finding M-RT-Q.2 / 2026-05-26).
    fn visit_nested_trait_item(&mut self, _id: rustc_hir::TraitItemId) {}
    fn visit_impl_item(&mut self, ii: &'tcx rustc_hir::ImplItem<'tcx>) {
        if let rustc_hir::ImplItemKind::Fn(..) = ii.kind {
            let pitbull = rustc_span::Symbol::intern("pitbull");
            let requires = rustc_span::Symbol::intern("requires");
            let trusted = rustc_span::Symbol::intern("trusted");
            let ensures = rustc_span::Symbol::intern("ensures");
            let attrs = self.tcx.hir_attrs(ii.hir_id());
            let def_id = ii.owner_id.to_def_id();
            let crate_name = self
                .tcx
                .crate_name(rustc_hir::def_id::LOCAL_CRATE)
                .to_string();
            let local_path = self.tcx.def_path_str(def_id);
            let fn_path = format!("{crate_name}::{local_path}");
            for attr in attrs {
                if attr.path_matches(&[pitbull, requires]) {
                    for s in self.extract_attr_strings(attr) {
                        self.preconditions
                            .entry(fn_path.clone())
                            .or_default()
                            .push(s);
                    }
                } else if attr.path_matches(&[pitbull, ensures]) {
                    // Q.4 (2026-05-26): mirror of requires for
                    // postconditions. Same string-literal /
                    // expression-form extraction via the renamed
                    // `extract_attr_strings` helper.
                    for s in self.extract_attr_strings(attr) {
                        self.ensures
                            .entry(fn_path.clone())
                            .or_default()
                            .push(s);
                    }
                } else if attr.path_matches(&[pitbull, trusted]) {
                    self.trusted.insert(fn_path.clone());
                }
            }
        }
        // Recurse into the method body so PB001 unsafe-block
        // detection (in visit_block) fires for `unsafe { ... }`
        // blocks inside impl methods. The double-fire concern
        // is handled by overriding visit_nested_impl_item above —
        // walk_impl_item here is reached only via the DIRECT
        // call from hir_visit_all_item_likes_in_crate, not via
        // the parent impl block's recursive walk.
        rustc_hir::intravisit::walk_impl_item(self, ii);
    }
    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        // PB059: an item produced by macro expansion (e.g. a
        // derive-generated `impl`) is checked against the proc-macro
        // allowlist. Self-filters when the span isn't from expansion.
        self.check_pb059_provenance(item.span);
        if let rustc_hir::ItemKind::Fn { .. } = item.kind {
            // `path_matches` and `meta_item_list` are inherent
            // methods on `rustc_hir::Attribute` on this nightly;
            // no trait import needed (`AttributeExt` from
            // rustc_ast is for `rustc_ast::Attribute`, a
            // different type used pre-HIR).
            let pitbull = rustc_span::Symbol::intern("pitbull");
            let requires = rustc_span::Symbol::intern("requires");
            let trusted = rustc_span::Symbol::intern("trusted");
            let ensures = rustc_span::Symbol::intern("ensures");
            let attrs = self.tcx.hir_attrs(item.hir_id());
            let def_id = item.owner_id.to_def_id();
            // Key the precondition map by the SAME string the
            // wrapper's per-item lookup uses
            // (`rustc_public::CrateDef::name()`), which is
            // `<crate>::<path>`. `tcx.def_path_str` omits the
            // crate name for local items, so prepend it.
            let crate_name = self
                .tcx
                .crate_name(rustc_hir::def_id::LOCAL_CRATE)
                .to_string();
            let local_path = self.tcx.def_path_str(def_id);
            let fn_path = format!("{crate_name}::{local_path}");
            for attr in attrs {
                if attr.path_matches(&[pitbull, requires]) {
                    for s in self.extract_attr_strings(attr) {
                        self.preconditions
                            .entry(fn_path.clone())
                            .or_default()
                            .push(s);
                    }
                } else if attr.path_matches(&[pitbull, ensures]) {
                    // Q.4 (2026-05-26): mirror of requires for
                    // postconditions. Same extraction helper.
                    for s in self.extract_attr_strings(attr) {
                        self.ensures
                            .entry(fn_path.clone())
                            .or_default()
                            .push(s);
                    }
                } else if attr.path_matches(&[pitbull, trusted]) {
                    // Task Q.1 (2026-05-26): `#[pitbull::trusted]`
                    // is a flag attribute — no arguments. Its
                    // presence on a function path means
                    // `SubsetVisitor::visit_body` short-circuits
                    // after signature checks (see visitor.rs's
                    // `current_body_trusted`). PB002 / PB026
                    // (unsafe fn / async fn) STILL fire — trust
                    // does NOT admit unsafe.
                    self.trusted.insert(fn_path.clone());
                }
            }
        }
        // PB003: `unsafe trait` / `unsafe impl`. The README's forbidden
        // list is "unsafe in any form: blocks, fn, trait, impl". Blocks
        // are PB001 (visit_block) and `unsafe fn` is PB002 (signature
        // walk), but `unsafe trait`/`unsafe impl` are ITEM-level with no
        // MIR body of their own, so the MIR-body visitor never sees them —
        // pre-2026-06-14 they were SILENTLY accepted (coverage-gap audit).
        // Detect them here at HIR. Macro-expansion spans are skipped (same
        // F7 posture as PB001: a derive may emit an unsafe impl the user
        // didn't author; a non-allowlisted such macro is caught by PB059).
        let unsafe_item: Option<&str> = match &item.kind {
            rustc_hir::ItemKind::Trait(_, _, safety, ..)
                if matches!(safety, rustc_hir::Safety::Unsafe) =>
            {
                Some("`unsafe trait`")
            }
            rustc_hir::ItemKind::Impl(imp) => match imp.of_trait {
                Some(header) if matches!(header.safety, rustc_hir::Safety::Unsafe) => {
                    Some("`unsafe impl`")
                }
                _ => None,
            },
            _ => None,
        };
        if let Some(kind) = unsafe_item {
            if !item.span.from_expansion() {
                let span =
                    rustc_span_to_shadow(self.tcx, item.span, &mut self.filename_table);
                self.violations.push(pitbull_subset::SubsetError {
                    rule: pitbull_subset::rules::PB003,
                    span,
                    detail: format!("{kind} (unsafe in any form is rejected)"),
                    in_spec: false,
                });
            }
        }
        // PB056 / PB057 / PB058 — FFI surface (coverage-gap audit
        // 2026-06-14). `extern` blocks, non-Rust-ABI fn definitions, and
        // `#[no_mangle]` / `#[export_name]` cross the FFI boundary the v0.2
        // model does not cover (the README lists FFI as out-of-subset).
        // Like PB003 these are item/attr-level — foreign items have no MIR
        // body, and ABI + linkage do not survive into MIR — so detect at
        // HIR. Macro-expansion spans are skipped (same F7 posture as PB001).
        if !item.span.from_expansion() {
            let ffi: Option<(pitbull_subset::rules::RuleId, String)> = match &item.kind
            {
                rustc_hir::ItemKind::ForeignMod { .. } => {
                    Some((pitbull_subset::rules::PB056, "`extern` block (FFI)".to_string()))
                }
                rustc_hir::ItemKind::Fn { sig, .. } if !sig.header.abi.is_rustic_abi() => {
                    Some((
                        pitbull_subset::rules::PB058,
                        format!("non-Rust ABI fn (`extern {:?}`)", sig.header.abi),
                    ))
                }
                _ => None,
            };
            if let Some((rule, detail)) = ffi {
                let span =
                    rustc_span_to_shadow(self.tcx, item.span, &mut self.filename_table);
                self.violations.push(pitbull_subset::SubsetError {
                    rule,
                    span,
                    detail,
                    in_spec: false,
                });
            }
            // PB057: `#[no_mangle]` / `#[export_name]` exports a fn under a
            // fixed symbol callable by external (non-Rust) code whose
            // calling contract is outside our model. `no_mangle`/`export_name`
            // are built-in attributes parsed into codegen attrs (not
            // path-matchable HIR attrs), so read them from `codegen_fn_attrs`.
            if matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
                let cfa = self.tcx.codegen_fn_attrs(item.owner_id.to_def_id());
                let no_mangle = cfa.flags.contains(
                    rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::NO_MANGLE,
                );
                if no_mangle || cfa.symbol_name.is_some() {
                    let span = rustc_span_to_shadow(
                        self.tcx,
                        item.span,
                        &mut self.filename_table,
                    );
                    self.violations.push(pitbull_subset::SubsetError {
                        rule: pitbull_subset::rules::PB057,
                        span,
                        detail: "`#[no_mangle]` / `#[export_name]` (FFI linkage)".to_string(),
                        in_spec: false,
                    });
                }
            }
        }
        rustc_hir::intravisit::walk_item(self, item);
    }
    fn visit_block(&mut self, b: &'tcx rustc_hir::Block<'tcx>) {
        // Audit-cleanup #5 / red-team F7: skip `unsafe { ... }`
        // blocks that came from macro expansion. `vec![1,2,3]`,
        // `format!()`, `println!()`, and many std macros expand
        // to bodies containing `unsafe { ... }`. After expansion
        // those blocks live in the user crate's HIR with
        // `UnsafeSource::UserProvided` (because the macro AUTHOR
        // wrote `unsafe`), but the user of the verified crate
        // didn't author that unsafe — and can't fix it without
        // rewriting their code in ways no Rust programmer would
        // accept.
        //
        // `Span::from_expansion()` returns true if the span was
        // introduced by ANY macro expansion (proc-macro, decl-macro,
        // or `#[derive]`). PB001 fires only on
        // user-source-positioned blocks.
        let is_unsafe_user_block = matches!(
            b.rules,
            rustc_hir::BlockCheckMode::UnsafeBlock(
                rustc_hir::UnsafeSource::UserProvided,
            ),
        );
        if is_unsafe_user_block && !b.span.from_expansion() {
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
