//! Compiled verification-condition goal.
//!
//! A `VcGoal` is a `pitbull_subset::VcObligation` that has been
//! turned into concrete SMT-LIB by `compile`. The split between
//! "obligation" (typed claim, produced by the visitor) and "goal"
//! (concrete encoding, produced here) lets the visitor evolve
//! independently of the SMT back-end — and lets one obligation
//! be encoded multiple ways (Z3, CVC5, Alt-Ergo) without the
//! visitor knowing.
use pitbull_subset::{VcObligation, VcObligationKind};
use serde::{Deserialize, Serialize};
/// A compiled obligation: the original typed claim plus the
/// SMT-LIB 2 text that asks a solver to discharge it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcGoal {
    /// The typed obligation this goal compiles. Round-trip safe:
    /// auditors can read the obligation alone to understand what's
    /// being claimed, without parsing SMT-LIB.
    pub obligation: VcObligation,
    /// Self-contained SMT-LIB 2.6 problem text. Pipe directly to a
    /// solver's stdin. `(check-sat)` is the last directive; the
    /// solver's first non-empty output line is the verdict.
    pub smt: String,
    /// Optional sat-check-only SMT problem with just the
    /// assumptions, no safety predicate. Audit-cleanup #3 / red-team
    /// finding F1: the dispatch layer runs THIS first when
    /// assumptions are present; if it returns `unsat` the
    /// assumptions are contradictory, so the main check's `unsat`
    /// would be vacuously true. Refusing to claim discharge in
    /// that case prevents `(assert false)`-style precondition
    /// poisoning from silently "verifying" unsafe code.
    ///
    /// For `ArithmeticOverflow` / `IndexBound`: `None` when the obligation has
    /// no assumptions (a zero-assumption set is trivially consistent, no extra
    /// solver call needed). For `EnsuresPostcondition` the keying differs —
    /// `obligation.assumptions` is always empty there (preconditions are baked
    /// into the visitor-built `discharge_smt`), so this field instead carries
    /// the visitor-supplied `consistency_smt`, which is `Some` exactly when the
    /// ensures has preconditions to check for vacuity (see the
    /// `EnsuresPostcondition` arm of `compile`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub consistency_check: Option<String>,
}
/// Compile an obligation into a goal by generating SMT-LIB.
///
/// Returns `None` if the obligation can't be compiled today —
/// either because the kind isn't yet supported (PanicReachability,
/// RecursionDecreases) or because the SMT encoder rejected the
/// specific instance (unsupported type, etc.). The caller treats
/// `None` as "undischarged" — the obligation remains in the report
/// so an auditor sees the gap.
#[must_use]
pub fn compile(obligation: &VcObligation) -> Option<VcGoal> {
    compile_with_index_bits(obligation, crate::smt::DEFAULT_INDEX_BITS)
}
/// Like [`compile`], but models PB054 `IndexBound` problems at `index_bits`
/// (the target `usize` width — 16/32/64) instead of the 64-bit default
/// (frontier #5, 2026-06-16). The wrapper passes
/// `cfg.subset.target_pointer_width`; the visitor sizes the index-precondition
/// literals to the SAME width, so the bit-vectors and literals stay consistent
/// (a mismatch would be an SMT sort error → solver `Error` → undischarged,
/// fail closed — never a false discharge). Other obligation kinds ignore
/// `index_bits` (ArithmeticOverflow uses the operand's own type width;
/// EnsuresPostcondition carries visitor-built SMT).
#[must_use]
pub fn compile_with_index_bits(obligation: &VcObligation, index_bits: u32) -> Option<VcGoal> {
    let (smt, consistency_check) = match &obligation.kind {
        VcObligationKind::ArithmeticOverflow { op, ty_name } => {
            let main = crate::smt::emit_overflow_problem_with_assumptions(
                ty_name,
                *op,
                &obligation.assumptions,
            )?;
            // Only generate a consistency-check problem when there
            // are assumptions to check. Zero assumptions is
            // trivially consistent — no extra solver call needed.
            let consistency = if obligation.assumptions.is_empty() {
                None
            } else {
                crate::smt::emit_consistency_check(ty_name, &obligation.assumptions)
            };
            (main, consistency)
        }
        VcObligationKind::IndexBound { idx_source_name } => {
            // PB054 SMT discharge (Task P.1) + operand binding
            // (Task P.2): declare `idx` and `len` as 64-bit
            // unsigned bit-vectors, optionally alias the
            // source-level identifier (e.g. `i`) to `idx` via
            // define-fun, splice assumptions in, assert the
            // negation of the safety predicate (`bvuge idx
            // len`), check sat.
            //
            // When `idx_source_name` is `Some(name)`, the alias
            // lets a user precondition written using the source
            // name — `(assert (bvult i len))` — constrain the
            // solver. When `None` (intermediate-let, computed
            // index, etc.), the obligation stays unconstrained
            // and the verdict is "sat" (counterexample exists),
            // which is the honest verdict for an unproven claim.
            let alias = idx_source_name.as_deref();
            let main = crate::smt::emit_index_bound_problem_with_assumptions_sized(
                alias,
                &obligation.assumptions,
                index_bits,
            );
            let consistency = if obligation.assumptions.is_empty() {
                None
            } else {
                Some(crate::smt::emit_index_bound_consistency_check_sized(
                    alias,
                    &obligation.assumptions,
                    index_bits,
                ))
            };
            (main, consistency)
        }
        // Task Q.4a (2026-05-29): EnsuresPostcondition (PB076) now
        // discharges when the visitor could SOUNDLY capture the body
        // effect and translate every spec. The visitor owns the
        // encoding (the SMT variable names are the function's dynamic
        // parameter names), so `pitbull-vc` just routes the prebuilt
        // problem through: `discharge_smt` becomes the goal's SMT and
        // `consistency_smt` its F1 vacuous-precondition guard. When the
        // visitor returns `discharge_smt: None` (non-int return, body
        // effect not captured, or an untranslatable spec) we fail closed
        // here exactly like an unsupported kind — the obligation stays
        // pending so the auditor sees the gap.
        VcObligationKind::EnsuresPostcondition { discharge_smt, consistency_smt, .. } => {
            match discharge_smt {
                Some(s) => (s.clone(), consistency_smt.clone()),
                None => return None,
            }
        }
        // These kinds need richer encodings than bit-vector arithmetic
        // alone — path-sensitive symbolic execution for panic
        // reachability and termination measures for recursion. Tracked
        // as v0.2+ follow-up work.
        VcObligationKind::PanicReachability | VcObligationKind::RecursionDecreases => {
            return None;
        }
    };
    Some(VcGoal {
        obligation: obligation.clone(),
        smt,
        consistency_check,
    })
}
#[cfg(test)]
mod tests {
    use super::*;
    use pitbull_subset::{ArithOp, VcObligation, VcObligationKind};
    use pitbull_subset::mir_api::Span;
    #[test]
    fn compile_u32_add_produces_smt() {
        let obligation = VcObligation {
            id: "pb049-add-0".into(),
            span: Span::default(),
            kind: VcObligationKind::ArithmeticOverflow {
                op: ArithOp::Add,
                ty_name: "u32".into(),
            },
            assumptions: Vec::new(),
        };
        let goal = compile(&obligation).expect("u32 + supported");
        assert_eq!(goal.obligation, obligation);
        assert!(goal.smt.contains("(set-logic QF_BV)"));
        assert!(goal.smt.contains("(declare-const lhs (_ BitVec 32))"));
        assert!(goal.smt.contains("(assert (bvuaddo lhs rhs))"));
    }
    #[test]
    fn compile_unsupported_kind_returns_none() {
        let obligation = VcObligation {
            id: "pb043-panic-0".into(),
            span: Span::default(),
            kind: VcObligationKind::PanicReachability,
            assumptions: Vec::new(),
        };
        assert!(
            compile(&obligation).is_none(),
            "PanicReachability isn't compiled in v0.2 scaffold",
        );
    }
    #[test]
    fn compile_round_trips_through_json() {
        let goal = VcGoal {
            obligation: VcObligation {
                id: "pb049-mul-7".into(),
                span: Span::default(),
                kind: VcObligationKind::ArithmeticOverflow {
                    op: ArithOp::Mul,
                    ty_name: "i64".into(),
                },
                assumptions: Vec::new(),
            },
            smt: "(check-sat)".into(),
            consistency_check: None,
        };
        let s = serde_json::to_string(&goal).expect("serialize");
        let back: VcGoal = serde_json::from_str(&s).expect("deserialize");
        assert_eq!(back, goal);
    }
    /// Audit hardening (red-team F1): when an obligation carries
    /// assumptions, `compile` produces both the main SMT problem
    /// AND a consistency-check problem. The consistency check is
    /// just declarations + assumptions + `(check-sat)` — no
    /// safety predicate. The dispatcher runs it first to detect
    /// contradictory hypotheses.
    #[test]
    fn compile_produces_consistency_check_when_assumptions_present() {
        let obligation = VcObligation {
            id: "pb049-add-3".into(),
            span: Span::default(),
            kind: VcObligationKind::ArithmeticOverflow {
                op: ArithOp::Add,
                ty_name: "u32".into(),
            },
            assumptions: vec![
                "(assert (bvult lhs #x00000064))".into(),
            ],
        };
        let goal = compile(&obligation).expect("u32 + supported");
        let cs = goal.consistency_check.as_ref()
            .expect("consistency check should be present when assumptions exist");
        // Consistency check contains the assumption ...
        assert!(cs.contains("(assert (bvult lhs #x00000064))"));
        // ... but does NOT contain the safety predicate.
        assert!(
            !cs.contains("bvuaddo"),
            "consistency check must NOT contain the safety predicate; got:\n{cs}",
        );
        // The main problem still contains the safety predicate.
        assert!(goal.smt.contains("(assert (bvuaddo lhs rhs))"));
    }
    /// O.2.5 headline composition: an obligation with BOTH a
    /// constant-pin assumption (the `1` in `x + 1`) AND a user
    /// precondition (`x < 100`) compiles to an SMT problem
    /// containing both as separate `(assert ...)` directives,
    /// followed by the safety predicate. This is the SMT text
    /// that — when Z3 sees it — returns `unsat` and the wrapper
    /// reports "discharged (unsat)".
    ///
    /// We can't actually run Z3 in unit tests (CI may or may not
    /// have it installed), so this test pins the SMT TEXT
    /// shape. The corresponding integration test
    /// `wrapper_proves_add_one_safe_under_precondition` (gated on
    /// Z3 availability) exercises the actual solver verdict.
    #[test]
    fn compile_with_const_pin_plus_precondition_combines_both() {
        let obligation = VcObligation {
            id: "pb049-add-0".into(),
            span: Span::default(),
            kind: VcObligationKind::ArithmeticOverflow {
                op: ArithOp::Add,
                ty_name: "u32".into(),
            },
            assumptions: vec![
                // Synthesized by the visitor for the `1` in `x + 1`.
                "(assert (= rhs #x00000001))".into(),
                // Synthesized by the visitor from the user
                // precondition `x < 100`.
                "(assert (bvult lhs #x00000064))".into(),
            ],
        };
        let goal = compile(&obligation).expect("u32 + supported");
        // Both assumptions must appear before the safety predicate.
        let smt = &goal.smt;
        let pin_idx = smt.find("(assert (= rhs #x00000001))")
            .expect("rhs pin should be in SMT");
        let pre_idx = smt.find("(assert (bvult lhs #x00000064))")
            .expect("precondition should be in SMT");
        let safe_idx = smt.find("(assert (bvuaddo lhs rhs))")
            .expect("safety predicate should be in SMT");
        assert!(
            pin_idx < safe_idx && pre_idx < safe_idx,
            "assumptions must appear before the safety predicate; \
             pin={pin_idx}, pre={pre_idx}, safe={safe_idx}, smt:\n{smt}",
        );
        // The consistency check should also contain both
        // assumptions but NOT the safety predicate.
        let cs = goal.consistency_check.as_ref()
            .expect("consistency check should be present with assumptions");
        assert!(cs.contains("(assert (= rhs #x00000001))"));
        assert!(cs.contains("(assert (bvult lhs #x00000064))"));
        assert!(
            !cs.contains("bvuaddo"),
            "consistency check must NOT contain the safety predicate; \
             got:\n{cs}",
        );
    }
    /// Task P.1: IndexBound now compiles to an SMT problem (no
    /// longer returns None). Pin the goal shape: 64-bit BV idx /
    /// len, unsigned negation of the safety predicate
    /// (`bvuge idx len`), check-sat.
    #[test]
    fn compile_index_bound_produces_smt() {
        let obligation = VcObligation {
            id: "pb054-idx-0".into(),
            span: Span::default(),
            kind: VcObligationKind::IndexBound { idx_source_name: None },
            assumptions: Vec::new(),
        };
        let goal = compile(&obligation).expect("IndexBound now compiles");
        assert_eq!(goal.obligation, obligation);
        assert!(goal.smt.contains("(set-logic QF_BV)"));
        // Audit-cleanup F3: canonical names are now `__pb_idx` /
        // `__pb_len` with `idx`/`len` as user-facing aliases.
        assert!(goal.smt.contains("(declare-const __pb_idx (_ BitVec 64))"));
        assert!(goal.smt.contains("(declare-const __pb_len (_ BitVec 64))"));
        assert!(goal.smt.contains("(define-fun idx () (_ BitVec 64) __pb_idx)"));
        assert!(goal.smt.contains("(define-fun len () (_ BitVec 64) __pb_len)"));
        assert!(goal.smt.contains("(assert (bvuge __pb_idx __pb_len))"));
        // No idx_source_name → no SOURCE-NAME alias. (The
        // canonical idx/len aliases are always present.)
        // Match "(define-fun |" for the quoted-symbol form
        // emit_index_bound_problem_with_assumptions uses for
        // user-source-name aliases.
        assert!(
            !goal.smt.contains("(define-fun |"),
            "None idx_source_name should produce no source-name alias; got:\n{}",
            goal.smt,
        );
        assert!(
            goal.consistency_check.is_none(),
            "no consistency check expected with zero assumptions; got:\n{:?}",
            goal.consistency_check,
        );
    }
    /// Task P.2 + audit-cleanup F4: IndexBound with
    /// `idx_source_name: Some("i")` produces a SMT problem
    /// containing `(define-fun |i| () (_ BitVec 64) __pb_idx)`
    /// — quoted-symbol syntax so any Rust ident (including raw
    /// idents and SMT reserved words) is well-formed — so user
    /// preconditions referencing `i` constrain the SMT problem.
    /// The consistency check carries the SAME alias so the F1
    /// guard runs against the same model as the main problem.
    #[test]
    fn compile_index_bound_with_source_name_emits_alias() {
        let obligation = VcObligation {
            id: "pb054-idx-0".into(),
            span: Span::default(),
            kind: VcObligationKind::IndexBound {
                idx_source_name: Some("i".into()),
            },
            assumptions: vec!["(assert (bvult i len))".into()],
        };
        let goal = compile(&obligation).expect("IndexBound with alias compiles");
        assert!(
            goal.smt.contains("(define-fun |i| () (_ BitVec 64) __pb_idx)"),
            "main problem must contain the quoted-symbol alias; got:\n{}",
            goal.smt,
        );
        let cs = goal
            .consistency_check
            .as_ref()
            .expect("consistency check should be present when assumptions exist");
        assert!(
            cs.contains("(define-fun |i| () (_ BitVec 64) __pb_idx)"),
            "consistency check must carry the SAME alias as the main problem \
             (the F1 guard runs the same model); got:\n{cs}",
        );
    }
    /// Task P.1: IndexBound with assumptions gets the consistency
    /// check populated, matching the contract that ArithmeticOverflow
    /// already follows. The dispatcher runs the consistency check
    /// first to refuse vacuous discharges from contradictory
    /// preconditions (red-team F1).
    #[test]
    fn compile_index_bound_with_assumptions_includes_consistency_check() {
        let obligation = VcObligation {
            id: "pb054-idx-1".into(),
            span: Span::default(),
            kind: VcObligationKind::IndexBound { idx_source_name: None },
            assumptions: vec![
                "(assert (bvult idx #x0000000000000064))".into(),
            ],
        };
        let goal = compile(&obligation).expect("IndexBound now compiles");
        // Main problem contains the safety predicate. Audit-cleanup
        // F3: uses internal canonical name `__pb_idx`/`__pb_len`.
        assert!(goal.smt.contains("(assert (bvuge __pb_idx __pb_len))"));
        // Assumption appears in the main problem (references the
        // user-facing `idx` alias which forwards to `__pb_idx`).
        assert!(goal.smt.contains("(assert (bvult idx #x0000000000000064))"));
        // Consistency check is populated and contains the
        // assumption but NOT the safety predicate.
        let cs = goal
            .consistency_check
            .as_ref()
            .expect("consistency check should be present");
        assert!(cs.contains("(assert (bvult idx #x0000000000000064))"));
        assert!(
            !cs.contains("bvuge"),
            "consistency check must NOT contain the safety predicate; got:\n{cs}",
        );
    }
    /// PanicReachability, RecursionDecreases, and (Q.4 MVP)
    /// EnsuresPostcondition still return None from compile —
    /// they need richer encodings than QF_BV alone. Pin this so
    /// adding IndexBound to compile didn't accidentally open up
    /// the other kinds, and so Q.4a's body-effect encoder
    /// landing for ensures doesn't silently change what panic /
    /// recursion produce.
    #[test]
    fn compile_pending_kinds_still_return_none() {
        let panic_obl = VcObligation {
            id: "pb043-panic-0".into(),
            span: Span::default(),
            kind: VcObligationKind::PanicReachability,
            assumptions: Vec::new(),
        };
        assert!(compile(&panic_obl).is_none());
        let rec_obl = VcObligation {
            id: "pb041-rec-0".into(),
            span: Span::default(),
            kind: VcObligationKind::RecursionDecreases,
            assumptions: Vec::new(),
        };
        assert!(compile(&rec_obl).is_none());
        // Q.4a: an EnsuresPostcondition whose visitor-side encoding
        // came back empty (`discharge_smt: None` — body effect not
        // captured, non-int return, or an untranslatable spec) still
        // compiles to None, so the wrapper reports "pending". The
        // discharging path (`discharge_smt: Some(..)`) is exercised
        // end-to-end by the wrapper integration tests.
        let ens_obl = VcObligation {
            id: "pb076-ensures-0".into(),
            span: Span::default(),
            kind: VcObligationKind::EnsuresPostcondition {
                ret_name: "result".into(),
                ret_ty_name: Some("u32".into()),
                discharge_smt: None,
                consistency_smt: None,
            },
            assumptions: Vec::new(),
        };
        assert!(compile(&ens_obl).is_none());
    }
    /// No assumptions → no consistency check (the empty hypothesis
    /// set is trivially consistent; skipping the extra solver call
    /// is the right optimization).
    #[test]
    fn compile_omits_consistency_check_when_no_assumptions() {
        let obligation = VcObligation {
            id: "pb049-add-4".into(),
            span: Span::default(),
            kind: VcObligationKind::ArithmeticOverflow {
                op: ArithOp::Add,
                ty_name: "u32".into(),
            },
            assumptions: Vec::new(),
        };
        let goal = compile(&obligation).expect("u32 + supported");
        assert!(
            goal.consistency_check.is_none(),
            "no consistency check expected when no assumptions; got: {:?}",
            goal.consistency_check,
        );
    }
    /// O.1 wiring: when the obligation carries assumptions, the
    /// compiled SMT-LIB includes each one as a separate assertion
    /// inserted BEFORE the safety predicate. Order preserved.
    #[test]
    fn compile_incorporates_assumptions() {
        let obligation = VcObligation {
            id: "pb049-add-2".into(),
            span: Span::default(),
            kind: VcObligationKind::ArithmeticOverflow {
                op: ArithOp::Add,
                ty_name: "u32".into(),
            },
            assumptions: vec![
                "(assert (bvult lhs #x00000064))".into(),
                "(assert (bvult rhs #x00000064))".into(),
            ],
        };
        let goal = compile(&obligation).expect("u32 + supported");
        assert!(
            goal.smt.contains("(assert (bvult lhs #x00000064))"),
            "first assumption should appear verbatim; got:\n{}",
            goal.smt,
        );
        assert!(
            goal.smt.contains("(assert (bvult rhs #x00000064))"),
            "second assumption should appear verbatim; got:\n{}",
            goal.smt,
        );
        // The overflow predicate is the LAST assertion (the
        // negated safety property the solver tries to falsify).
        let safety_idx = goal.smt.find("(assert (bvuaddo lhs rhs))").expect("safety assertion");
        let first_idx = goal.smt.find("(assert (bvult lhs #x00000064))").expect("first assumption");
        assert!(
            first_idx < safety_idx,
            "assumptions must come before the safety predicate so the \
             solver has them as hypotheses; first={first_idx}, safety={safety_idx}",
        );
    }
    /// Frontier #5 (2026-06-16): `compile_with_index_bits` threads the target
    /// `usize` width into the IndexBound goal (32-bit here), while the default
    /// `compile` keeps the 64-bit fallback.
    #[test]
    fn compile_with_index_bits_threads_target_width() {
        let obligation = VcObligation {
            id: "pb054-idx-0".into(),
            span: Span::default(),
            kind: VcObligationKind::IndexBound { idx_source_name: Some("i".into()) },
            assumptions: vec!["(assert (bvult i len))".into()],
        };
        let goal32 = compile_with_index_bits(&obligation, 32).expect("IndexBound compiles");
        assert!(
            goal32.smt.contains("(declare-const __pb_idx (_ BitVec 32))")
                && goal32.smt.contains("(define-fun |i| () (_ BitVec 32) __pb_idx)"),
            "32-bit width must thread into the goal; got:\n{}",
            goal32.smt,
        );
        // The default `compile` stays at the 64-bit fallback.
        let goal64 = compile(&obligation).expect("IndexBound compiles");
        assert!(
            goal64.smt.contains("(declare-const __pb_idx (_ BitVec 64))"),
            "default compile must stay 64-bit; got:\n{}",
            goal64.smt,
        );
    }
}
