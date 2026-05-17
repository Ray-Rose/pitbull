//! Verification-condition types.
//!
//! A `VcGoal` is one safety obligation Pitbull asks an SMT solver
//! to discharge. The visitor (pitbull-subset) decides *which* sites
//! generate obligations; this module describes the obligations
//! themselves: where they came from, what they assert, and the
//! SMT-LIB text that encodes them.
use pitbull_subset::mir_api::Span;
use serde::{Deserialize, Serialize};
/// One verification condition. An auditor reviewing a Pitbull run
/// should be able to read the goal's `kind`, `span`, and `smt`
/// fields and reconstruct what was checked.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct VcGoal {
    /// Stable identifier for cross-referencing solver output and
    /// proof certificates. Format: `pb{rule_num}-{kind_tag}-{hash}`
    /// where the hash makes the id unique within one run.
    pub id: String,
    /// Source location of the construct that generated this goal.
    pub span: Span,
    /// What's being checked.
    pub kind: VcGoalKind,
    /// SMT-LIB 2.6 problem text. Self-contained: pipe this directly
    /// to a solver's stdin. Includes `(set-logic ...)`,
    /// `(declare-const ...)`, `(assert ...)`, `(check-sat)`.
    pub smt: String,
}
/// Discriminator for VC goals. Used to route solver results back
/// to PSS-1 rules and to render counterexamples appropriately.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum VcGoalKind {
    /// Arithmetic operation that could overflow / underflow the
    /// declared type. Maps to PSS-1 PB049 (overflow checks).
    ArithmeticOverflow {
        /// Which arithmetic operator.
        op: ArithOp,
        /// Operand type name (e.g. "u32", "i64").
        ty_name: String,
    },
    /// Call to a panic function (e.g. `core::panicking::panic_fmt`)
    /// that the verifier needs to prove unreachable. Maps to PB043.
    /// v0.2 scaffold does not yet emit these — requires
    /// path-sensitive symbolic execution.
    PanicReachability,
    /// Slice / array index that needs `idx < len` proven. Maps to
    /// PB054.
    IndexBound,
    /// Recursive call where the `#[decreases(...)]` measure must
    /// strictly decrease. Maps to PB041.
    RecursionDecreases,
}
/// Arithmetic operators that have associated overflow obligations.
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum ArithOp {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/` — division by zero is also an obligation, encoded as a
    /// separate assertion in the same SMT problem.
    Div,
    /// `%`
    Rem,
    /// `<<` — over-shift (shift amount ≥ bit width) is the
    /// obligation here.
    Shl,
    /// `>>` — same shape as `Shl`.
    Shr,
}
impl ArithOp {
    /// Short tag used in the VC goal id for cross-referencing.
    #[must_use]
    pub fn tag(self) -> &'static str {
        match self {
            ArithOp::Add => "add",
            ArithOp::Sub => "sub",
            ArithOp::Mul => "mul",
            ArithOp::Div => "div",
            ArithOp::Rem => "rem",
            ArithOp::Shl => "shl",
            ArithOp::Shr => "shr",
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn vc_goal_round_trips_through_json() {
        let g = VcGoal {
            id: "pb049-add-abc123".into(),
            span: Span::default(),
            kind: VcGoalKind::ArithmeticOverflow {
                op: ArithOp::Add,
                ty_name: "u32".into(),
            },
            smt: "(check-sat)".into(),
        };
        let s = serde_json::to_string(&g).expect("serialize");
        let back: VcGoal = serde_json::from_str(&s).expect("deserialize");
        assert_eq!(back, g);
    }
    #[test]
    fn arith_op_tags_are_stable() {
        // Cross-referenced by VC goal IDs and proof certificates;
        // changing a tag is a breaking format change.
        assert_eq!(ArithOp::Add.tag(), "add");
        assert_eq!(ArithOp::Sub.tag(), "sub");
        assert_eq!(ArithOp::Mul.tag(), "mul");
        assert_eq!(ArithOp::Div.tag(), "div");
        assert_eq!(ArithOp::Rem.tag(), "rem");
        assert_eq!(ArithOp::Shl.tag(), "shl");
        assert_eq!(ArithOp::Shr.tag(), "shr");
    }
}
