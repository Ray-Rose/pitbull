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
    let smt = match &obligation.kind {
        VcObligationKind::ArithmeticOverflow { op, ty_name } => {
            crate::smt::emit_overflow_problem(ty_name, *op)?
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
            },
            smt: "(check-sat)".into(),
        };
        let s = serde_json::to_string(&goal).expect("serialize");
        let back: VcGoal = serde_json::from_str(&s).expect("deserialize");
        assert_eq!(back, goal);
    }
}
