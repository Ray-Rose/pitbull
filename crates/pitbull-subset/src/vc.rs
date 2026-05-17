//! Verification-condition obligation types.
//!
//! The visitor in this crate produces `VcObligation`s — typed
//! descriptions of what needs to be proven about a particular
//! construct, with the source span pointing back at the construct
//! itself. The actual SMT-LIB formulation and solver dispatch live
//! in `pitbull-vc`; this module is intentionally thin so the two
//! crates can share types without `pitbull-subset` taking on a
//! solver dependency.
//!
//! Why a typed-obligation IR instead of pre-formulated SMT-LIB:
//!
//! 1. The visitor and the solver evolve at different paces. A change
//!    to the SMT encoding (e.g. switching `bvuaddo` for an explicit
//!    range check, or moving from BV to integer logic) shouldn't
//!    force visitor changes.
//!
//! 2. Multiple back-ends. PSS-1 §17.1 (Safety Manual §3.3) plans
//!    multi-solver agreement; the same obligation feeds Z3, CVC5,
//!    and Alt-Ergo through different encoding paths.
//!
//! 3. Auditability. An auditor reading `VcObligation::ArithmeticOverflow
//!    { op: Add, ty_name: "u32" }` immediately understands what the
//!    obligation is. The same audit against raw SMT-LIB requires
//!    SMT-LIB literacy.
use crate::mir_api::Span;
use serde::{Deserialize, Serialize};
/// A single proof obligation the visitor wants discharged.
///
/// `id` is intentionally a string rather than an integer so it can
/// carry rule + kind + index information legibly in stderr / SARIF
/// output. Format: `pb{nnn}-{tag}-{seq}` where `nnn` is the PSS-1
/// rule the obligation discharges, `tag` is the kind discriminator
/// (e.g. `add`, `mul`, `panic`), and `seq` is a per-run counter.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcObligation {
    /// Stable cross-reference identifier (see format note above).
    pub id: String,
    /// Where in the source the obligation originates.
    pub span: Span,
    /// What's being claimed.
    pub kind: VcObligationKind,
    /// Spec-derived premises the solver gets as additional
    /// hypotheses when discharging this obligation. Each string is
    /// an SMT-LIB 2 assertion *form* (the full `(assert ...)`
    /// directive, not just the predicate body) that the compiler
    /// splices verbatim into the problem before `(check-sat)`.
    ///
    /// v0.2 O.1 (this commit): assumptions are raw SMT-LIB strings
    /// fed straight from `pitbull.toml`. The user wires
    /// operand-to-variable bindings manually.
    /// v0.2 O.2 (next commit): the configuration uses a small
    /// predicate grammar (`<ident> <cmp> <int>`), and the visitor
    /// translates predicate variable names to `lhs`/`rhs` via
    /// shadow `Body::arg_names`.
    /// v0.2 O.3 (final commit): assumptions originate from
    /// `#[pitbull::requires(...)]` tool attributes extracted from
    /// the HIR.
    ///
    /// Each well-formed string is one assertion form, e.g.
    /// `"(assert (bvult lhs #x00000064))"`. Malformed strings get
    /// inlined verbatim — the solver returns an `(error ...)`
    /// which the wrapper surfaces as an `Error` verdict so the
    /// auditor sees the gap.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub assumptions: Vec<String>,
}
/// Discriminator for VC obligations. Each variant maps to one PSS-1
/// rule the v0.1 visitor recognizes but cannot itself prove.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VcObligationKind {
    /// A `BinaryOp` whose result must fit the operand type. Maps
    /// to PB049 (overflow checks). Only emitted when the visitor
    /// can statically determine the operand type.
    ArithmeticOverflow {
        /// Which operator triggers this obligation.
        op: ArithOp,
        /// Operand type name (e.g. `"u32"`, `"i64"`). Both
        /// operands must already be known to share this type; the
        /// visitor refuses to emit an obligation otherwise.
        ty_name: String,
    },
    /// A reachable call to a panic function. Maps to PB043.
    /// v0.1 visitor does not yet emit these; placeholder for the
    /// v0.2 panic-unreachability work.
    PanicReachability,
    /// A `ProjectionElem::Index` that requires `idx < len`. Maps to
    /// PB054. Visitor placeholder; v0.2 work.
    IndexBound,
    /// A recursive call where the `#[decreases(...)]` measure must
    /// strictly decrease. Maps to PB041. Visitor placeholder;
    /// requires call-graph SCC analysis.
    RecursionDecreases,
}
/// Arithmetic operators with associated overflow obligations.
///
/// The string tags returned by `tag()` are stable identifiers
/// referenced by VC IDs and the (future) proof-certificate format —
/// changing them is a breaking format change.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
    /// Short stable tag for VC ids and certificate cross-references.
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
    fn obligation_round_trips_through_json() {
        let o = VcObligation {
            id: "pb049-add-0".into(),
            span: Span::default(),
            kind: VcObligationKind::ArithmeticOverflow {
                op: ArithOp::Add,
                ty_name: "u32".into(),
            },
            assumptions: Vec::new(),
        };
        let s = serde_json::to_string(&o).expect("serialize");
        let back: VcObligation = serde_json::from_str(&s).expect("deserialize");
        assert_eq!(back, o);
    }
    /// Obligations with non-empty assumptions also round-trip
    /// through JSON. (The `skip_serializing_if = "Vec::is_empty"`
    /// attribute on `assumptions` keeps the JSON terse when no
    /// preconditions apply — but the field still works when filled.)
    #[test]
    fn obligation_with_assumptions_round_trips() {
        let o = VcObligation {
            id: "pb049-add-1".into(),
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
        let s = serde_json::to_string(&o).expect("serialize");
        let back: VcObligation = serde_json::from_str(&s).expect("deserialize");
        assert_eq!(back, o);
    }
    #[test]
    fn arith_op_tags_are_stable() {
        // Cross-referenced by VC ids and proof certificates;
        // changing any tag is a breaking format change.
        assert_eq!(ArithOp::Add.tag(), "add");
        assert_eq!(ArithOp::Sub.tag(), "sub");
        assert_eq!(ArithOp::Mul.tag(), "mul");
        assert_eq!(ArithOp::Div.tag(), "div");
        assert_eq!(ArithOp::Rem.tag(), "rem");
        assert_eq!(ArithOp::Shl.tag(), "shl");
        assert_eq!(ArithOp::Shr.tag(), "shr");
    }
}
