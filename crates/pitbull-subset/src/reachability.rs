//! Call-graph reachability and orchestration of the subset visit.
//!
//! ## Why this is a separate module
//!
//! The visitor checks *one body at a time*. PSS-1 enforcement requires
//! checking every body reachable from a `#[pitbull::verify]` entry point,
//! including transitively through trait dispatch, monomorphized generics,
//! and implicit drop glue. That orchestration logic — root discovery, BFS
//! over call edges, exclude-pattern filtering, deduplication — lives here.
//!
//! ## Algorithm sketch
//!
//! ```text
//!   roots := { item ∈ crate | item has #[pitbull::verify] and matches a config root pattern }
//!   visited := ∅
//!   worklist := roots
//!   while worklist non-empty:
//!       item := worklist.pop()
//!       if item ∈ visited: continue
//!       if item matches a config `exclude` pattern: continue
//!       visited.insert(item)
//!       body := query_monomorphized_body(item)
//!       trusted := has_attr(item, pitbull::trusted)
//!       visitor.visit_body(body, trusted)
//!       if not trusted:
//!           for call_target in callees(body):
//!               worklist.push(call_target)
//!           for drop_target in drop_glue(body):
//!               worklist.push(drop_target)
//! ```
//!
//! Trusted items contribute their *signature* (already checked by
//! `visit_body`) but not their callees — by trusting the spec, the user
//! takes responsibility for the body's PSS-1 conformance. Their callees may
//! escape the subset; that's the user's contract.
//!
//! ## Phase tagging for PB010
//!
//! `StatementKind::Deinit` may be emitted by the drop-elaboration pass *or*
//! by a subset-escaping intrinsic. The visitor can't tell them apart from
//! the statement alone. Reachability annotates each statement with its MIR
//! phase before dispatch; the visitor consults the tag.
//!
//! In the v0.1 skeleton the tagger is stubbed: every Deinit is treated as
//! out-of-phase (worst case for the user, safest for soundness). The real
//! implementation queries `rustc_public::mir::MirPhase`.
//!
//! ## Production status (updated 2026-06-15 deep-audit)
//!
//! `ReachabilityDriver` below is a unit-tested **reference** for the
//! call-closure walk; it is **exercised only by this module's tests, not by
//! production** (nothing in `pitbull-driver` constructs it). The
//! `pitbull-rustc` wrapper does a flat `all_local_items()` walk filtered by
//! `verify_roots`, which on its own would skip in-crate callees of a root (a
//! fail-open under explicit narrowing — issue #27). Instead of the driver,
//! the wrapper closes that hole the fail-CLOSED way: it collects the callees
//! of every walked body (`callee_paths`) and, via
//! `unverified_reachable_callees`, reports any in-crate function reachable
//! from a verified root that was not itself verified — forcing a nonzero
//! exit. Applied every run, this transitively requires the whole reachable
//! in-crate closure to be covered before a "verified" verdict is possible.
//! Those two helpers are pure and live here so they are testable on stable.
//!
//! **Do not wire `ReachabilityDriver` in as the production path without first
//! closing the gaps the wrapper already handles.** The 2026-06-15 audit found
//! it short of production-ready on two counts the prose previously hid by
//! calling it "COMPLETE": it has no drop-glue injection (the wrapper adds
//! every local `Drop::drop` impl to the referenced set, #27 drop-glue) and no
//! cross-crate manifest (`ReachManifest`). Its previously-SILENT
//! unavailable-body skip is now fail-closed — a reachable function whose body
//! the provider can't supply records a `CoverageGap` note (see `run`) rather
//! than being dropped — but the other two gaps are why it stays a reference.
use crate::config::SubsetConfig;
use crate::diagnostic::SubsetReport;
use crate::mir_api::{Body, DefId, Span, Ty};
use crate::visitor::SubsetVisitor;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
/// What kind of item appears in the reachability graph.
///
/// Functions get a MIR body and propagate to callees. Statics and consts
/// do not have call-graph successors of their own — they contribute their
/// *type* to the visit. The mutability of a static is the PB018 signal.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ItemKind {
    /// A regular function, including methods and trait impls.
    Function,
    /// A `static X` or `static mut X` declaration.
    Static {
        /// Whether this is `static mut` (the PB018 trigger).
        mutable: bool,
    },
    /// A `const X` declaration.
    Const,
}
/// A reachable item discovered during call-graph traversal.
#[derive(Clone, Debug)]
pub struct ReachableItem {
    /// The item's def id (monomorphized for functions).
    pub def_id: DefId,
    /// What kind of item this is.
    pub kind: ItemKind,
    /// Whether the item carries `#[pitbull::trusted]`.
    pub trusted: bool,
    /// The item's fully-qualified path, for diagnostic and exclude-matching.
    pub path: String,
}
/// The body-provider interface.
///
/// Decouples the reachability driver from the source of MIR. In production
/// this is backed by `rustc_public`; in unit tests, by an in-memory map.
pub trait BodyProvider {
    /// Return the monomorphized MIR body for a function item, plus its
    /// callee/referenced items (targets of `TerminatorKind::Call`,
    /// `TerminatorKind::Drop`, and any static/const references).
    ///
    /// Returns `None` for non-Function items.
    fn body(&self, item: &ReachableItem) -> Option<(Body, Vec<ReachableItem>)>;
    /// Return the declared type of a static or const item.
    ///
    /// Default implementation returns `None`; only providers that can
    /// answer item-level queries override this. Returning `None` from
    /// this method on a non-Function item means the item is skipped
    /// without type-level checks — which is unsound, so production
    /// providers must implement it.
    fn item_type(&self, _item: &ReachableItem) -> Option<Ty> {
        None
    }
    /// Span of an item declaration, used for diagnostic placement.
    fn item_span(&self, _item: &ReachableItem) -> Span {
        Span::default()
    }
}
/// Driver that orchestrates the subset visit over a reachability closure.
pub struct ReachabilityDriver<'cfg, P: BodyProvider> {
    config: &'cfg SubsetConfig,
    provider: P,
    visited: HashSet<u64>, // DefId.0 only; struct doesn't derive Hash
    /// Patterns that exclude items from reachability, sourced from
    /// `config.reachability.exclude`. Patterns end with `::*` for wildcard.
    exclude_patterns: Vec<String>,
}
impl<'cfg, P: BodyProvider> ReachabilityDriver<'cfg, P> {
    /// Construct a new driver.
    #[must_use]
    pub fn new(config: &'cfg SubsetConfig, provider: P) -> Self {
        Self {
            config,
            provider,
            visited: HashSet::new(),
            exclude_patterns: config.reachability.exclude.clone(),
        }
    }
    /// Run the closure walk and produce the accumulated subset report.
    ///
    /// Fail-closed posture (2026-06-15 deep audit): a reachable, non-trusted,
    /// non-excluded function whose body the provider cannot supply is NOT
    /// silently skipped — it records a `CoverageGap` audit note. A `CoverageGap`
    /// is the fail-closed signal Pitbull's exit code keys on
    /// (`SubsetReport::coverage_gap_count`), so wiring this (currently test-only)
    /// driver into production would surface the unanalyzed body rather than hide
    /// it. A body the verifier could not see is a safety check that could not
    /// run, never an implicit pass. (A genuinely foreign/extern item is the FFI
    /// surface, PB056, and must be excluded or `#[pitbull::trusted]` explicitly.)
    pub fn run(mut self, roots: Vec<ReachableItem>) -> SubsetReport {
        let mut visitor = SubsetVisitor::new(self.config);
        let mut worklist = roots;
        // Reachable functions whose body the provider could not supply.
        // Recorded as coverage gaps after the walk (fail closed) rather than
        // dropped — see the method doc and the module-level production note.
        let mut unavailable_bodies: Vec<(String, Span)> = Vec::new();
        while let Some(item) = worklist.pop() {
            if self.visited.contains(&item.def_id.0) {
                continue;
            }
            if self.is_excluded(&item.path) {
                continue;
            }
            self.visited.insert(item.def_id.0);
            match item.kind {
                ItemKind::Function => {
                    let Some((body, callees)) = self.provider.body(&item) else {
                        // Body unavailable for a reachable function the verifier
                        // was asked to cover. Fail closed: record a coverage gap
                        // so the exit code reflects the un-analyzed body, instead
                        // of the historic silent `continue` (a latent false
                        // discharge if this driver were ever wired into
                        // production).
                        unavailable_bodies
                            .push((item.path.clone(), self.provider.item_span(&item)));
                        continue;
                    };
                    visitor.visit_body(&body, item.trusted);
                    // Trusted bodies do not propagate to callees: the user
                    // has assumed the body's conformance.
                    if !item.trusted {
                        for callee in callees {
                            if !self.visited.contains(&callee.def_id.0) {
                                worklist.push(callee);
                            }
                        }
                    }
                }
                ItemKind::Static { mutable } => {
                    let span = self.provider.item_span(&item);
                    let ty = self.provider.item_type(&item);
                    visitor.visit_static_item(mutable, ty.as_ref(), span);
                }
                ItemKind::Const => {
                    let span = self.provider.item_span(&item);
                    let ty = self.provider.item_type(&item);
                    visitor.visit_const_item(ty.as_ref(), span);
                }
            }
        }
        let mut report = visitor.into_report();
        // Fold unavailable-body coverage gaps into the report (fail closed).
        for (path, span) in unavailable_bodies {
            report.audit_notes.push(crate::diagnostic::AuditNote {
                span,
                message: format!(
                    "reachability: body unavailable for reachable function `{path}`; \
                     it could not be verified — exclude it, mark it \
                     #[pitbull::trusted], or supply its MIR. Reported as a coverage \
                     gap (fail closed)."
                ),
                kind: crate::diagnostic::AuditNoteKind::CoverageGap,
            });
        }
        report
    }
    fn is_excluded(&self, path: &str) -> bool {
        self.exclude_patterns.iter().any(|pat| pattern_matches(pat, path))
    }
}
/// Match a path against a `foo::bar::*` pattern.
///
/// Patterns ending with `::*` match any item whose path starts with the
/// prefix. Patterns without the wildcard match exactly. We deliberately do
/// not support deeper glob semantics in v0.1 — simpler patterns make the
/// audit story for "what got verified" trivial.
fn pattern_matches(pattern: &str, path: &str) -> bool {
    if let Some(prefix) = pattern.strip_suffix("::*") {
        path == prefix || path.starts_with(&format!("{prefix}::"))
    } else {
        pattern == path
    }
}
/// Extract the fully-qualified paths of the functions DIRECTLY called by
/// this body — the targets of `TerminatorKind::Call` whose callee operand
/// is a resolved function constant. Used by the wrapper's fail-closed
/// reachability check to detect in-crate callees a `verify_roots`-narrowed
/// walk would otherwise skip.
///
/// Only direct calls with a statically-known callee path are returned.
/// Indirect calls (fn pointers, `dyn` dispatch, closures) carry no static
/// path, so they are not in this set — yet they still cannot smuggle an
/// unchecked in-crate callee past narrowing. The precise argument (audit
/// 2026-06-14, strengthening the earlier one-line assertion the deep-audit
/// agent flagged as hand-wavy):
///   1. This set forces the DIRECT-call closure of the roots to be walked:
///      `unverified_reachable_callees` fails closed on any walked body's
///      direct callee that wasn't itself walked, so iterating to a fixpoint
///      walks every body reachable from a root by direct calls.
///   2. To PERFORM an indirect call, a body must materialize the callee
///      into a local of `fn`-ptr / `dyn` / closure type (MIR loads the
///      receiver/fn-ptr into a typed temporary before the `Call`). The
///      visitor visits that local's type and fires PB031 (`dyn`) / PB032
///      (fn ptr) / PB033 (closure) — a hard violation.
///   3. By (1) every body that performs an indirect call is itself walked
///      (it is in the direct-call closure, or only reachable via an
///      indirect call from a body already walked); by (2) that walk
///      produces a violation. So a `verified` verdict (exit 0) is
///      impossible whenever an indirect dispatch is reachable — the
///      indirect target need not be in this set for soundness.
///
/// Drop glue (`TerminatorKind::Drop`) is not a `Call`, so it is not here;
/// the wrapper separately injects every LOCAL `Drop::drop` impl into the
/// referenced-callee set (#27 drop-glue, 2026-06-14) to close that path.
///
/// Cross-crate edges are out of this set by construction (callee paths in
/// other crates are not in the local universe). Non-local callees are the
/// TRUSTED stdlib/dependency surface — see `docs/SAFETY-MANUAL.md` §3 for
/// that boundary and the panic-bearing exceptions
/// (`Option`/`Result::unwrap`/`expect`) the visitor catches at the call
/// site rather than trusting.
#[must_use]
pub fn callee_paths(body: &Body) -> Vec<String> {
    use crate::mir_api::{ConstOperand, Operand, TerminatorKind};
    let mut paths = Vec::new();
    for block in &body.blocks {
        // Direct call with a statically-known callee path: the callee
        // operand is a function constant carrying a resolved path.
        if let TerminatorKind::Call {
            func: Operand::Constant(ConstOperand { path: Some(p), .. }),
            ..
        } = &block.terminator.kind
        {
            paths.push(p.clone());
        }
    }
    paths
}
/// Compute the in-crate functions that are REACHABLE from a verified root
/// (directly called by some walked body) yet were NOT themselves verified —
/// the fail-open that `verify_roots` narrowing would otherwise hide
/// (issue #27). A clean (empty) result requires every such callee to be
/// either walked, `#[pitbull::trusted]` (explicit user opt-out), or
/// `exclude`d (already absent from `local_universe`). Applied at every run,
/// this transitively forces the whole reachable in-crate closure to be
/// covered — each newly-walked body re-exposes its own unwalked callees —
/// so a "verified" verdict can never rest on an unverified in-crate callee.
///
/// - `referenced`: paths called by walked bodies (union of `callee_paths`).
/// - `local_universe`: paths of all non-excluded in-crate fns with bodies.
/// - `walked`: paths actually visited.
/// - `trusted`: paths the user marked `#[pitbull::trusted]`.
///
/// Returns the offending paths, sorted, for deterministic diagnostics.
#[must_use]
pub fn unverified_reachable_callees(
    referenced: &HashSet<String>,
    local_universe: &HashSet<String>,
    walked: &HashSet<String>,
    trusted: &HashSet<String>,
) -> Vec<String> {
    let mut out: Vec<String> = referenced
        .iter()
        .filter(|c| {
            local_universe.contains(*c) && !walked.contains(*c) && !trusted.contains(*c)
        })
        .cloned()
        .collect();
    out.sort();
    out
}
/// Per-crate reachability manifest, emitted by the `pitbull-rustc`
/// wrapper (one JSON file per compiled crate, into `PITBULL_REACH_DIR`)
/// and aggregated by `cargo pitbull check` to close the CROSS-crate
/// reachability hole.
///
/// The per-crate `#27` gate ([`unverified_reachable_callees`]) only sees
/// the crate it is compiling — its `local_universe` is that crate's items
/// alone. So a verified root in crate A that calls into workspace crate B
/// is invisible to A's gate (B's path isn't in A's universe), and if B's
/// OWN run narrowed `verify_roots` so as to skip that entry, B's gate
/// doesn't flag it either (nothing B walked referenced it). Neither crate
/// catches it — a cross-crate false-"verified". Aggregating these
/// manifests across the whole `cargo check` lets the subcommand verify the
/// WHOLE-workspace closure (see [`cross_crate_unverified`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReachManifest {
    /// The crate this manifest is for, as it appears in fully-qualified
    /// item paths (the crate name with `-` normalized to `_`, e.g.
    /// `pitbull_subset`).
    pub crate_name: String,
    /// Fully-qualified paths of fns actually walked (verified) this run.
    pub walked: Vec<String>,
    /// Direct callees referenced by walked, non-trusted bodies (union of
    /// [`callee_paths`]) plus the local `Drop::drop` impls.
    pub referenced: Vec<String>,
    /// Paths the user marked `#[pitbull::trusted]` (the user takes
    /// responsibility for these and their callees).
    pub trusted: Vec<String>,
    /// Every in-crate fn-with-body the wrapper enumerated this run (the
    /// `#27` `local_universe`), BEFORE `verify_roots` narrowing. A
    /// referenced callee is only hard-flagged cross-crate if it is a member
    /// of SOME crate's universe — i.e. an actual walkable item — exactly as
    /// the local `#27` gate filters `referenced ∩ local_universe`. This is
    /// what keeps a trait-method CALL from being false-flagged: rustc
    /// renders such a call's callee as the TRAIT path `crate::Tr::m`, which
    /// is never a walkable item (the item is the impl, rendered
    /// `<crate::Type as crate::Tr>::m`), so it is absent from every
    /// universe and correctly ignored (verified empirically 2026-06-14).
    #[serde(default)]
    pub universe: Vec<String>,
}
/// The crate segment of a fully-qualified item path. Handles both the plain
/// form (`crate_b::module::foo` → `crate_b`) and rustc's trait-impl
/// rendering (`<crate_b::Foo as some::Trait>::method` → `crate_b`, the crate
/// of the `Self` type inside the angle brackets); a bare segment (`foo`)
/// returns itself. Used to decide whether a callee belongs to a workspace
/// member (must be covered by some crate's run) vs an external crate
/// (std/registry dep — trusted, SAFETY-MANUAL §3.6).
///
/// The `<.. as ..>` handling is load-bearing: `item.name()` renders
/// trait-impl methods that way (verified empirically 2026-06-14), and a
/// naive split on the first `::` would yield `<crate_b` and mis-classify a
/// member as external — a fail-open.
#[must_use]
pub fn crate_of_path(path: &str) -> &str {
    // Trait-impl rendering `<Type as Trait>::method`: the owning crate is
    // the crate of `Type` (the Self type), inside the angle brackets.
    // `trim_start_matches` (not `strip_prefix`) peels ALL leading `<` so the
    // doubly-qualified `<<A as T1>::Assoc as T2>::m` form also resolves to
    // `A`'s crate rather than the fail-open `<crate` (deep audit 2026-06-14).
    let inner = path.trim_start_matches('<');
    let self_ty = inner.split(" as ").next().unwrap_or(inner);
    match self_ty.split_once("::") {
        Some((krate, _)) => krate,
        None => self_ty,
    }
}
/// Cross-crate reachability gate — [`unverified_reachable_callees`] lifted
/// to the whole workspace.
///
/// Returns the WORKSPACE-MEMBER callees that NO crate's run verified: a
/// path referenced by some manifest whose crate is a workspace member
/// (`workspace_crates`) but which appears in NO manifest's `walked` or
/// `trusted` set. Non-workspace callees (std/core/alloc, registry deps)
/// are the trusted surface and are intentionally excluded — modelling them
/// is the prelude's job (SAFETY-MANUAL §3.4 / §3.6).
///
/// A clean (empty) result means every workspace-member function reachable
/// from a verified root ANYWHERE in the build was itself verified — so a
/// whole-workspace "verified" verdict cannot rest on an unverified member
/// function, even across crate boundaries. With every crate at the default
/// empty `verify_roots` (full walk) this is trivially empty; it only fires
/// when `verify_roots` narrowing in some crate left a cross-crate-reachable
/// member uncovered. Sorted + deduped for deterministic diagnostics.
///
/// ## Warm-cache safety
///
/// A referenced member callee is hard-flagged ONLY when its OWNING crate
/// was actually analyzed this run (it emitted a manifest). On a warm cargo
/// cache, cargo may skip recompiling some crate, so the wrapper never runs
/// for it and it emits no manifest; we must not flag that crate's callees
/// as uncovered just because we have no record of them (a false positive on
/// every incremental build). Those are INDETERMINATE — see
/// [`cross_crate_indeterminate`] — and surfaced as a "run a clean build for
/// complete cross-crate coverage" note rather than a hard failure. On a
/// clean build (CI) every member is analyzed, so the gate is fully
/// fail-closed; this mirrors the tool's existing whole-analysis posture
/// (a warm cache already degrades the per-crate pass — SAFETY-MANUAL §3.6).
#[must_use]
pub fn cross_crate_unverified(
    manifests: &[ReachManifest],
    workspace_crates: &HashSet<String>,
) -> Vec<String> {
    let sets = covered_analyzed_universe(manifests);
    let mut bad: Vec<String> = Vec::new();
    for m in manifests {
        for r in &m.referenced {
            let owner = crate_of_path(r);
            // External crates (std/registry deps) are the trusted boundary.
            if !workspace_crates.contains(owner) {
                continue;
            }
            // Verified (walked/trusted) by some crate's run → fine.
            if sets.covered.contains(r.as_str()) {
                continue;
            }
            // Owner not analyzed this run (warm cache) → indeterminate, not
            // a hard fail (avoids false positives on incremental builds).
            if !sets.analyzed.contains(owner) {
                continue;
            }
            // Only an actual WALKABLE ITEM (a member of some crate's
            // universe) can be a real missed walk — mirrors the `#27` gate's
            // `referenced ∩ local_universe` filter, lifted to the workspace.
            // A referenced path that is NO crate's item (a trait-method
            // call's trait path `crate::Tr::m`, an intrinsic, an unresolved
            // form) is not a missed walk and MUST NOT be flagged, else any
            // crate using trait methods would false-fail. (The corresponding
            // impl, if any, is matched separately as `<.. as ..>::m`.)
            if !sets.universe.contains(r.as_str()) {
                continue;
            }
            bad.push(r.clone());
        }
    }
    bad.sort();
    bad.dedup();
    bad
}
/// Companion to [`cross_crate_unverified`]: the workspace-member callees
/// whose coverage is INDETERMINATE because their owning crate was not
/// analyzed this run (cargo served it from a warm cache, so no manifest, so
/// we don't even have that crate's universe to check). These are not
/// failures — surface them as a "run a clean build" note. Sorted+deduped.
#[must_use]
pub fn cross_crate_indeterminate(
    manifests: &[ReachManifest],
    workspace_crates: &HashSet<String>,
) -> Vec<String> {
    let sets = covered_analyzed_universe(manifests);
    let mut out: Vec<String> = Vec::new();
    for m in manifests {
        for r in &m.referenced {
            let owner = crate_of_path(r);
            if workspace_crates.contains(owner)
                && !sets.covered.contains(r.as_str())
                && !sets.analyzed.contains(owner)
            {
                out.push(r.clone());
            }
        }
    }
    out.sort();
    out.dedup();
    out
}
/// The three sets the cross-crate gate needs, in one pass:
/// - `covered`: every path walked or trusted by any crate's run.
/// - `analyzed`: every crate that produced a manifest this run (by its
///   declared name AND the crate segment of every path it walked or listed
///   in its universe, so a crate counts as analyzed even if it walked zero
///   of its own fns).
/// - `universe`: every in-crate fn-with-body any crate enumerated — the
///   "is this a walkable item?" set that filters out trait-paths / non-items.
struct CrossCrateSets<'a> {
    covered: HashSet<&'a str>,
    analyzed: HashSet<&'a str>,
    universe: HashSet<&'a str>,
}
fn covered_analyzed_universe(manifests: &[ReachManifest]) -> CrossCrateSets<'_> {
    let mut covered: HashSet<&str> = HashSet::new();
    let mut analyzed: HashSet<&str> = HashSet::new();
    let mut universe: HashSet<&str> = HashSet::new();
    for m in manifests {
        analyzed.insert(m.crate_name.as_str());
        for w in &m.walked {
            covered.insert(w.as_str());
            analyzed.insert(crate_of_path(w));
        }
        for t in &m.trusted {
            covered.insert(t.as_str());
        }
        for u in &m.universe {
            universe.insert(u.as_str());
            analyzed.insert(crate_of_path(u));
        }
    }
    CrossCrateSets { covered, analyzed, universe }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir_api::{AdtDef, RigidTy, Span, Ty, TyKind};
    use std::collections::HashMap;
    /// In-memory BodyProvider for tests.
    ///
    /// Stores function bodies keyed by `DefId.0` and item types keyed by
    /// `(DefId.0, "type")`. Static and const items use the type map.
    struct StubProvider {
        bodies: HashMap<u64, (Body, Vec<ReachableItem>)>,
        types: HashMap<u64, Ty>,
    }
    impl BodyProvider for StubProvider {
        fn body(&self, item: &ReachableItem) -> Option<(Body, Vec<ReachableItem>)> {
            self.bodies.get(&item.def_id.0).cloned()
        }
        fn item_type(&self, item: &ReachableItem) -> Option<Ty> {
            self.types.get(&item.def_id.0).cloned()
        }
    }
    fn fn_item(id: u64, path: &str) -> ReachableItem {
        ReachableItem {
            def_id: DefId(id),
            kind: ItemKind::Function,
            trusted: false,
            path: path.into(),
        }
    }
    fn empty_body(def_id: DefId) -> Body {
        Body {
            def_id,
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: Ty { kind: TyKind::RigidTy(RigidTy::Bool) },
            is_unsafe: false,
            is_async: false,
            locals: vec![],
            blocks: vec![],
            span: Span::default(),
        }
    }
    #[test]
    fn walks_call_closure() {
        // Root calls foo, which calls bar. Without exclusions, all three are
        // visited.
        let mut bodies = HashMap::new();
        bodies.insert(1, (empty_body(DefId(1)), vec![fn_item(2, "crate::foo")]));
        bodies.insert(2, (empty_body(DefId(2)), vec![fn_item(3, "crate::bar")]));
        bodies.insert(3, (empty_body(DefId(3)), vec![]));
        let provider = StubProvider { bodies, types: HashMap::new() };
        let cfg = SubsetConfig::default_for_test();
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![fn_item(1, "crate::root")]);
        assert!(report.is_clean(), "report not clean: {:?}", report.errors);
    }
    /// Fail-closed regression (2026-06-15 deep audit): a reachable,
    /// non-trusted, non-excluded function whose body the provider cannot
    /// supply must NOT be a silent pass — the driver records a `CoverageGap`
    /// note (which the wrapper folds into the exit code, fail closed).
    /// Pre-fix this arm did a bare `continue`, dropping the un-analyzed body
    /// silently — a latent false discharge had the driver been wired into
    /// production.
    #[test]
    fn unavailable_body_is_coverage_gap_not_silent_skip() {
        // Root has a body and references `crate::opaque`; the provider has NO
        // body for `opaque` (id 2), simulating a reachable item whose MIR the
        // walk cannot obtain.
        let mut bodies = HashMap::new();
        bodies.insert(1, (empty_body(DefId(1)), vec![fn_item(2, "crate::opaque")]));
        // id 2 is deliberately absent from `bodies`.
        let provider = StubProvider { bodies, types: HashMap::new() };
        let cfg = SubsetConfig::default_for_test();
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![fn_item(1, "crate::root")]);
        assert!(
            report.coverage_gap_count() >= 1,
            "an unavailable reachable body must record a coverage gap (fail \
             closed), not be silently skipped; audit_notes={:?}",
            report.audit_notes,
        );
        assert!(
            report.audit_notes.iter().any(|n| n.message.contains("crate::opaque")),
            "the coverage gap should name the unavailable function; got {:?}",
            report.audit_notes,
        );
    }
    #[test]
    fn trusted_does_not_propagate() {
        // Root is trusted and calls an unsafe fn. Because trusted bodies
        // do not propagate to callees, the unsafe fn is not visited and
        // produces no error.
        let mut callee_body = empty_body(DefId(2));
        callee_body.is_unsafe = true;
        let mut bodies = HashMap::new();
        bodies.insert(1, (empty_body(DefId(1)), vec![fn_item(2, "crate::unsafe_callee")]));
        bodies.insert(2, (callee_body, vec![]));
        let provider = StubProvider { bodies, types: HashMap::new() };
        let cfg = SubsetConfig::default_for_test();
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![ReachableItem {
            def_id: DefId(1),
            kind: ItemKind::Function,
            trusted: true, // <-- trusted root
            path: "crate::trusted_root".into(),
        }]);
        assert!(report.is_clean(), "trusted root should not propagate to unsafe callee");
    }
    #[test]
    fn exclude_pattern_skips_items() {
        let mut bodies = HashMap::new();
        bodies.insert(1, (empty_body(DefId(1)), vec![fn_item(2, "crate::tests::should_skip")]));
        let mut callee_body = empty_body(DefId(2));
        callee_body.is_unsafe = true;
        bodies.insert(2, (callee_body, vec![]));
        let provider = StubProvider { bodies, types: HashMap::new() };
        let mut cfg = SubsetConfig::default_for_test();
        cfg.reachability.exclude.push("crate::tests::*".into());
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![fn_item(1, "crate::root")]);
        assert!(report.is_clean(), "excluded callee should not be visited");
    }
    #[test]
    fn pattern_matching_semantics() {
        assert!(pattern_matches("crate::tests::*", "crate::tests::foo"));
        assert!(pattern_matches("crate::tests::*", "crate::tests::sub::foo"));
        assert!(pattern_matches("crate::tests::*", "crate::tests"));
        assert!(!pattern_matches("crate::tests::*", "crate::testify::foo"));
        assert!(pattern_matches("exact::path", "exact::path"));
        assert!(!pattern_matches("exact::path", "exact::path::child"));
    }
    /// PSS-1 PB018 closure: a `static mut X: u32` declaration reached
    /// through the reachability graph triggers PB018.
    #[test]
    fn static_mut_triggers_pb018() {
        let mut types = HashMap::new();
        types.insert(
            1,
            Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U32)) },
        );
        let provider = StubProvider { bodies: HashMap::new(), types };
        let cfg = SubsetConfig::default_for_test();
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![ReachableItem {
            def_id: DefId(1),
            kind: ItemKind::Static { mutable: true },
            trusted: false,
            path: "crate::COUNTER".into(),
        }]);
        assert!(
            report.errors.iter().any(|e| e.rule == crate::rules::PB018),
            "PB018 must fire on `static mut` declaration; got {:?}",
            report.errors
        );
    }
    /// PSS-1 (complement): an immutable `static X: u32 = 0;` does NOT
    /// trigger PB018. Its type is in-subset (a plain `u32`), so the run
    /// is clean.
    #[test]
    fn immutable_static_does_not_trigger_pb018() {
        let mut types = HashMap::new();
        types.insert(
            1,
            Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U32)) },
        );
        let provider = StubProvider { bodies: HashMap::new(), types };
        let cfg = SubsetConfig::default_for_test();
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![ReachableItem {
            def_id: DefId(1),
            kind: ItemKind::Static { mutable: false },
            trusted: false,
            path: "crate::IMMUTABLE".into(),
        }]);
        assert!(report.is_clean(), "immutable static with primitive type should be clean");
    }
    /// PSS-1 PB021 via static type: even an immutable `static FOO: Cell<u32>`
    /// is rejected because the type carries interior mutability. The
    /// visit_static_item routes through visit_ty which fires PB021.
    #[test]
    fn immutable_static_with_cell_triggers_pb021() {
        let mut types = HashMap::new();
        types.insert(
            1,
            Ty {
                kind: TyKind::RigidTy(RigidTy::Adt(AdtDef {
                    path: "core::cell::Cell".into(),
                    is_union: false,
                })),
            },
        );
        let provider = StubProvider { bodies: HashMap::new(), types };
        let cfg = SubsetConfig::default_for_test();
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![ReachableItem {
            def_id: DefId(1),
            kind: ItemKind::Static { mutable: false },
            trusted: false,
            path: "crate::INTERIOR".into(),
        }]);
        assert!(
            report.errors.iter().any(|e| e.rule == crate::rules::PB021),
            "PB021 must fire on `static FOO: Cell<_>`; got {:?}",
            report.errors
        );
    }
    /// PSS-1 PB018 + interior mutability combined: `static mut FOO: Cell<u32>`
    /// triggers BOTH PB018 (for being `mut`) and PB021 (for the Cell type).
    /// Verifies diagnostic accumulation works at the item level.
    #[test]
    fn static_mut_cell_triggers_both_rules() {
        let mut types = HashMap::new();
        types.insert(
            1,
            Ty {
                kind: TyKind::RigidTy(RigidTy::Adt(AdtDef {
                    path: "core::cell::Cell".into(),
                    is_union: false,
                })),
            },
        );
        let provider = StubProvider { bodies: HashMap::new(), types };
        let cfg = SubsetConfig::default_for_test();
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![ReachableItem {
            def_id: DefId(1),
            kind: ItemKind::Static { mutable: true },
            trusted: false,
            path: "crate::DOUBLE_TROUBLE".into(),
        }]);
        assert!(
            report.errors.iter().any(|e| e.rule == crate::rules::PB018),
            "PB018 must fire"
        );
        assert!(
            report.errors.iter().any(|e| e.rule == crate::rules::PB021),
            "PB021 must also fire for the Cell type"
        );
    }
    /// A const item with a primitive type is clean.
    #[test]
    fn const_item_with_primitive_is_clean() {
        let mut types = HashMap::new();
        types.insert(
            1,
            Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U32)) },
        );
        let provider = StubProvider { bodies: HashMap::new(), types };
        let cfg = SubsetConfig::default_for_test();
        let driver = ReachabilityDriver::new(&cfg, provider);
        let report = driver.run(vec![ReachableItem {
            def_id: DefId(1),
            kind: ItemKind::Const,
            trusted: false,
            path: "crate::SIZE".into(),
        }]);
        assert!(report.is_clean());
    }
    /// `callee_paths` returns the path of each directly-called function and
    /// ignores indirect/path-less calls and non-Call terminators.
    #[test]
    fn callee_paths_extracts_direct_call_targets() {
        use crate::mir_api::{
            BasicBlock, BasicBlockData, ConstOperand, Local, Operand, Place, Terminator,
            TerminatorKind,
        };
        let fn_const = |path: Option<&str>| {
            Operand::Constant(ConstOperand {
                ty: Ty { kind: TyKind::RigidTy(RigidTy::Bool) },
                def_id: None,
                path: path.map(str::to_string),
                value: None,
            })
        };
        let call_block = |func: Operand| BasicBlockData {
            statements: vec![],
            terminator: Terminator {
                kind: TerminatorKind::Call {
                    func,
                    args: vec![],
                    destination: Place { local: Local(0), projection: vec![] },
                    target: Some(BasicBlock(0)),
                },
                span: Span::default(),
            },
        };
        let mut body = empty_body(DefId(1));
        body.blocks = vec![
            call_block(fn_const(Some("crate::helper"))), // direct call -> captured
            call_block(fn_const(None)),                  // path-less (indirect) -> ignored
            BasicBlockData {
                // non-Call terminator -> ignored
                statements: vec![],
                terminator: Terminator { kind: TerminatorKind::Return, span: Span::default() },
            },
        ];
        assert_eq!(callee_paths(&body), vec!["crate::helper".to_string()]);
    }
    /// `unverified_reachable_callees` flags exactly the in-crate callees
    /// reachable from a root but neither walked, trusted, nor out-of-crate.
    /// This is the #27 fail-closed gate.
    #[test]
    fn unverified_reachable_callees_flags_skipped_in_crate_callee() {
        let set = |xs: &[&str]| xs.iter().map(|s| (*s).to_string()).collect::<HashSet<_>>();
        // root (walked) calls helper (in-crate, NOT walked) + an external fn.
        let referenced = set(&["crate::helper", "std::vec::Vec::new"]);
        let universe = set(&["crate::root", "crate::helper", "crate::helper2"]);
        let walked = set(&["crate::root"]);
        assert_eq!(
            unverified_reachable_callees(&referenced, &universe, &walked, &set(&[])),
            vec!["crate::helper".to_string()],
            "an in-crate callee skipped by narrowing must be flagged (external callee is not in the universe, so never flagged)"
        );
        // Marking helper trusted is an explicit opt-out -> not flagged.
        assert!(
            unverified_reachable_callees(&referenced, &universe, &walked, &set(&["crate::helper"]))
                .is_empty(),
            "a trusted callee must not be flagged"
        );
        // Walking helper clears it.
        assert!(
            unverified_reachable_callees(
                &referenced,
                &universe,
                &set(&["crate::root", "crate::helper"]),
                &set(&[]),
            )
            .is_empty(),
            "a walked callee must not be flagged"
        );
    }
    // ----- cross-crate aggregation (whole-workspace gate) --------------
    // Args: (crate_name, walked, referenced, trusted, universe). `universe`
    // is every in-crate fn-with-body (⊇ walked); a narrowed crate has
    // universe ⊋ walked. A callee is only hard-flagged if it is in SOME
    // crate's universe (a real walkable item) — mirroring the #27 gate.
    fn manifest(
        name: &str,
        walked: &[&str],
        referenced: &[&str],
        trusted: &[&str],
        universe: &[&str],
    ) -> ReachManifest {
        let v = |xs: &[&str]| xs.iter().map(|s| (*s).to_string()).collect::<Vec<_>>();
        ReachManifest {
            crate_name: name.into(),
            walked: v(walked),
            referenced: v(referenced),
            trusted: v(trusted),
            universe: v(universe),
        }
    }
    fn ws(names: &[&str]) -> HashSet<String> {
        names.iter().map(|s| (*s).to_string()).collect()
    }
    /// Flags a workspace-member callee that NO crate's run verified — the
    /// cross-crate hole. crate_a's walked root calls crate_b::foo + std;
    /// crate_b narrowed and walked nothing (but foo IS in crate_b's
    /// universe), so neither crate's local gate catches foo.
    #[test]
    fn cross_crate_unverified_flags_member_callee_no_one_walked() {
        let manifests = vec![
            manifest("crate_a", &["crate_a::root"], &["crate_b::foo", "std::vec::Vec::new"], &[], &["crate_a::root"]),
            manifest("crate_b", &[], &[], &[], &["crate_b::foo"]),
        ];
        assert_eq!(
            cross_crate_unverified(&manifests, &ws(&["crate_a", "crate_b"])),
            vec!["crate_b::foo".to_string()],
            "a workspace-member callee no crate walked/trusted must be flagged; \
             the external std callee must NOT (trusted boundary)",
        );
    }
    /// Clean when the member callee WAS walked by its owning crate's run.
    #[test]
    fn cross_crate_unverified_clean_when_member_walked_elsewhere() {
        let manifests = vec![
            manifest("crate_a", &["crate_a::root"], &["crate_b::foo"], &[], &["crate_a::root"]),
            manifest("crate_b", &["crate_b::foo"], &[], &[], &["crate_b::foo"]),
        ];
        assert!(
            cross_crate_unverified(&manifests, &ws(&["crate_a", "crate_b"])).is_empty(),
            "a member callee walked by its owning crate must clear the gate",
        );
    }
    /// Trusting the member callee (in any crate's run) is an explicit opt-out.
    #[test]
    fn cross_crate_unverified_respects_trusted() {
        let manifests = vec![
            manifest("crate_a", &["crate_a::root"], &["crate_b::foo"], &[], &["crate_a::root"]),
            manifest("crate_b", &[], &[], &["crate_b::foo"], &["crate_b::foo"]),
        ];
        assert!(
            cross_crate_unverified(&manifests, &ws(&["crate_a", "crate_b"])).is_empty(),
            "a trusted member callee must not be flagged",
        );
    }
    /// External (non-workspace) callees are the trusted boundary — never
    /// flagged, even though no manifest walks them.
    #[test]
    fn cross_crate_unverified_ignores_external_callees() {
        let manifests = vec![manifest(
            "crate_a",
            &["crate_a::root"],
            &["core::option::Option::<u32>::unwrap", "some_dep::helper", "std::mem::swap"],
            &[],
            &["crate_a::root"],
        )];
        assert!(
            cross_crate_unverified(&manifests, &ws(&["crate_a"])).is_empty(),
            "callees from non-workspace crates (std/deps) are trusted, never flagged",
        );
    }
    /// REGRESSION (deep-audit 2026-06-14): a TRAIT-METHOD call must NOT be
    /// false-flagged. rustc renders the call's callee as the trait path
    /// `crate_a::T::m`, but the walkable item is the impl
    /// `<crate_a::S as crate_a::T>::m` (which IS walked). The trait path is
    /// in no crate's universe, so the gate must ignore it — else every crate
    /// using trait methods would spuriously fail. Verified empirically
    /// against real rustc MIR (the manifest had exactly this shape).
    #[test]
    fn cross_crate_unverified_ignores_trait_method_call_path() {
        let manifests = vec![manifest(
            "crate_a",
            &["<crate_a::S as crate_a::T>::m", "crate_a::root"], // impl IS walked
            &["crate_a::T::m"],                                  // call references the TRAIT path
            &[],
            &["<crate_a::S as crate_a::T>::m", "crate_a::root"],
        )];
        assert!(
            cross_crate_unverified(&manifests, &ws(&["crate_a"])).is_empty(),
            "a trait-method call path (no crate's walkable item) must not be flagged",
        );
        assert!(
            cross_crate_indeterminate(&manifests, &ws(&["crate_a"])).is_empty(),
            "...and it is not indeterminate either (the crate WAS analyzed)",
        );
    }
    /// Warm-cache safety: when the OWNING crate emitted no manifest (cargo
    /// served it from cache), its uncovered callee is INDETERMINATE, not
    /// hard-flagged — no false positive on incremental builds. Only
    /// crate_a's manifest is present; crate_b (owner of foo) was not
    /// analyzed this run.
    #[test]
    fn cross_crate_unverified_indeterminate_when_owner_not_analyzed() {
        let manifests = vec![manifest(
            "crate_a",
            &["crate_a::root"],
            &["crate_b::foo"],
            &[],
            &["crate_a::root"],
        )];
        let workspace = ws(&["crate_a", "crate_b"]);
        assert!(
            cross_crate_unverified(&manifests, &workspace).is_empty(),
            "an uncovered callee whose owner wasn't analyzed must NOT hard-fail",
        );
        assert_eq!(
            cross_crate_indeterminate(&manifests, &workspace),
            vec!["crate_b::foo".to_string()],
            "it must instead be reported as indeterminate (clean build needed)",
        );
    }
    /// `crate_of_path` extracts the crate segment from plain AND trait-impl
    /// `<Type as Trait>::method` renderings (the latter is what `item.name()`
    /// produces — a naive first-`::` split would yield `<crate_b`, a
    /// fail-open in the workspace-membership check).
    #[test]
    fn crate_of_path_extracts_leading_segment() {
        assert_eq!(crate_of_path("crate_b::module::foo"), "crate_b");
        assert_eq!(crate_of_path("crate_b::<impl X>::foo"), "crate_b");
        assert_eq!(crate_of_path("<crate_b::Foo as some::Trait>::method"), "crate_b");
        assert_eq!(crate_of_path("<crate_b::Foo<u32> as core::ops::Add>::add"), "crate_b");
        // Doubly-qualified (associated-type Self) — deep audit 2026-06-14:
        // `trim_start_matches('<')` peels both `<`, so the crate is `crate_b`,
        // not the fail-open `<crate_b`.
        assert_eq!(
            crate_of_path("<<crate_b::A as t1::T1>::Assoc as t2::T2>::m"),
            "crate_b",
        );
        assert_eq!(crate_of_path("bare"), "bare");
        assert_eq!(crate_of_path(""), "");
    }
}
