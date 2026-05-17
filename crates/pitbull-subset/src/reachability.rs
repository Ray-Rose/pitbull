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
use crate::config::SubsetConfig;
use crate::diagnostic::SubsetReport;
use crate::mir_api::{Body, DefId, Span, Ty};
use crate::visitor::SubsetVisitor;
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
    pub fn run(mut self, roots: Vec<ReachableItem>) -> SubsetReport {
        let mut visitor = SubsetVisitor::new(self.config);
        let mut worklist = roots;
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
                        // Body unavailable. In production this means the
                        // item is foreign (PB056 territory) or extern; the
                        // visitor's signature check elsewhere flags it.
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
        visitor.into_report()
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
}
