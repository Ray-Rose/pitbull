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
    /// `None` when the obligation has no assumptions (every
    /// assertion set with zero assumptions is trivially
    /// consistent, no extra solver call needed).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub consistency_check: Option<String>,
}
/// Compile an obligation into a goal by generating SMT-LIB.
///
/// Returns `None` if the obligation can't be compiled today —
/// either because the kind isn't yet supported (PanicReachability,
/// IndexBound, RecursionDecreases) or because the SMT encoder
/// rejected the specific instance (unsupported type, etc.). The
/// caller treats `None` as "undischarged" — the obligation remains
/// in the report so an auditor sees the gap.
#[must_use]
pub fn compile(obligation: &VcObligation) -> Option<VcGoal> {
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
        // The following kinds need richer encodings than bit-vector
        // arithmetic alone — path-sensitive symbolic execution,
        // termination measures, or `idx < len` reasoning over MIR
        // local state. Tracked as v0.2 follow-up work.
        VcObligationKind::PanicReachability
        | VcObligationKind::IndexBound
        | VcObligationKind::RecursionDecreases => return None,
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
}
