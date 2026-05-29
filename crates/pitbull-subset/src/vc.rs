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
    /// Emitted by the visitor (see
    /// `visitor::emit_panic_reachability_obligation`);
    /// `pitbull-vc::compile` returns `None` until v0.3+ path-
    /// sensitive reachability lands, so the wrapper reports
    /// each as "pending". The visitor's emission point is
    /// `is_panic_call_path`-matched call sites (`core::panicking::*`,
    /// `std::panicking::*`, `core::panic_any`, `std::panic_any`,
    /// `std::rt::*`).
    PanicReachability,
    /// A `ProjectionElem::Index` that requires `idx < len`. Maps to
    /// PB054. Emitted by the visitor; `pitbull-vc` compiles to an
    /// SMT problem with unsigned bit-vector idx and len. The
    /// `idx_source_name` carries the source-level identifier the
    /// index resolved to (`Some("i")` for `s[i]` where `i` is a
    /// function parameter, `None` for indices derived from local
    /// computations the visitor can't trace). When `Some`, the
    /// SMT problem includes a `(define-fun <name> () (_ BitVec 64)
    /// idx)` alias so user preconditions written with the source
    /// name (e.g. `(assert (bvult i len))`) constrain the SMT
    /// search space. Without the binding (`None`), the obligation
    /// stays unconstrained — the obligation will report as sat
    /// (counterexample exists) unless the user writes preconditions
    /// referencing `idx` and `len` directly.
    IndexBound {
        /// Source identifier the index local resolved to, when
        /// the index `ProjectionElem::Index(Local)` references a
        /// function-argument slot whose source name is known.
        /// `None` for `ConstantIndex`/`Subslice` (no MIR local
        /// — the offset is a u64 literal), for indices derived
        /// from intermediate `let` bindings (no data-flow trace),
        /// and for arg slots whose source name was anonymized.
        idx_source_name: Option<String>,
    },
    /// A recursive call where the `#[decreases(...)]` measure must
    /// strictly decrease. Maps to PB041. Visitor placeholder;
    /// requires call-graph SCC analysis.
    RecursionDecreases,
    /// A `#[pitbull::ensures("...")]` postcondition that must
    /// hold at every function exit (every `TerminatorKind::Return`,
    /// including the implicit return at end-of-body). Maps to
    /// PB076. Task Q.4 (2026-05-26).
    ///
    /// Emitted by the visitor at `Return` terminators when the
    /// current body has non-empty `current_body_ensures`.
    /// `pitbull-vc::compile` returns `None` for the MVP (matches
    /// PanicReachability today); the wrapper reports the
    /// obligation as "pending". The body-effect encoder needed
    /// to discharge for straight-line bodies lands in Task Q.4a;
    /// path-sensitive control-flow encoding for branchy bodies
    /// lands alongside PB043.
    EnsuresPostcondition {
        /// Source-level name of the binding used in the
        /// postcondition to refer to the return value. Today
        /// always `"result"` (matches Creusot's convention;
        /// lowercase, no SPARK-style capitalization workarounds).
        /// The field is reserved for future per-function
        /// renaming should that ever be useful.
        ret_name: String,
        /// Rust primitive integer type name of the return value
        /// (e.g. `Some("u32")`, `Some("i64")`). The future SMT
        /// encoder uses this to size the bit-vector for `result`.
        ///
        /// `None` when the return type is NOT a primitive integer
        /// (struct, tuple, slice, `()`, etc.). Audit-cleanup
        /// post-Q audit finding M-2 (2026-05-26): this used to be
        /// an EMPTY STRING sentinel, which a future encoder could
        /// misread as "no constraint on `result`" and produce a
        /// vacuously-`unsat` problem — a latent false-discharge
        /// trap for Q.4a. Making it `Option<String>` forces the
        /// encoder to handle the unsupported case explicitly:
        /// `pitbull-vc::compile` refuses to produce a goal for an
        /// `EnsuresPostcondition` whose `ret_ty_name` is `None`
        /// (fail-closed by construction, not by comment). The
        /// obligation is still EMITTED (so the auditor sees the
        /// gap) but can never discharge until the encoder gains
        /// non-int-return support.
        ret_ty_name: Option<String>,
    },
}
impl VcObligationKind {
    /// Canonical PSS-1 rule ID for this obligation kind, as the
    /// printable uppercase string (`"PB049"`, `"PB043"`, `"PB054"`,
    /// `"PB041"`).
    ///
    /// The obligation `id` field carries a lowercase variant
    /// (`"pb049-add-0"`) so that auditors can read trace output and
    /// see at a glance which obligation maps to which kind. This
    /// method surfaces the canonical uppercase form so the wrapper
    /// can include it in verdict lines — and so integration tests
    /// can look for `"PB054"` (the rule's canonical form) rather
    /// than `"pb054-idx-"` (the obligation-id format).
    ///
    /// Returning `&'static str` so the wrapper can format with no
    /// allocation per verdict line.
    #[must_use]
    pub fn rule_id(&self) -> &'static str {
        match self {
            VcObligationKind::ArithmeticOverflow { .. } => "PB049",
            VcObligationKind::PanicReachability => "PB043",
            VcObligationKind::IndexBound { .. } => "PB054",
            VcObligationKind::RecursionDecreases => "PB041",
            VcObligationKind::EnsuresPostcondition { .. } => "PB076",
        }
    }
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
    /// Each obligation kind maps to its PSS-1 rule ID. Pins the
    /// kind→rule mapping so the integration test's contains-check
    /// (`stderr.contains("PB054")`) remains stable across the
    /// obligation-id format choice.
    #[test]
    fn rule_id_for_each_kind() {
        assert_eq!(
            VcObligationKind::ArithmeticOverflow {
                op: ArithOp::Add,
                ty_name: "u32".into(),
            }
            .rule_id(),
            "PB049",
        );
        assert_eq!(VcObligationKind::PanicReachability.rule_id(), "PB043");
        assert_eq!(
            VcObligationKind::IndexBound { idx_source_name: None }.rule_id(),
            "PB054",
        );
        assert_eq!(
            VcObligationKind::IndexBound {
                idx_source_name: Some("i".into()),
            }
            .rule_id(),
            "PB054",
        );
        assert_eq!(VcObligationKind::RecursionDecreases.rule_id(), "PB041");
        assert_eq!(
            VcObligationKind::EnsuresPostcondition {
                ret_name: "result".into(),
                ret_ty_name: Some("u32".into()),
            }
            .rule_id(),
            "PB076",
        );
        // M-2: non-primitive return type carries None; rule_id
        // is still PB076 (the rule fires regardless of whether
        // the encoder can handle the return type).
        assert_eq!(
            VcObligationKind::EnsuresPostcondition {
                ret_name: "result".into(),
                ret_ty_name: None,
            }
            .rule_id(),
            "PB076",
        );
    }
    /// Task Q.4 (2026-05-26): EnsuresPostcondition serdes
    /// round-trips cleanly through JSON. The struct-variant fields
    /// (`ret_name`, `ret_ty_name`) survive a serialize/deserialize
    /// cycle — needed because SubsetReport is JSON-serialized for
    /// SARIF emission and for proof-certificate (planned).
    #[test]
    fn ensures_postcondition_round_trips_through_json() {
        let o = VcObligation {
            id: "pb076-ensures-0".into(),
            span: Span::default(),
            kind: VcObligationKind::EnsuresPostcondition {
                ret_name: "result".into(),
                ret_ty_name: Some("u32".into()),
            },
            assumptions: vec![
                "(assert (bvult x #x00000064))".into(),
                "(assert (bvult result #x00000065))".into(),
            ],
        };
        let s = serde_json::to_string(&o).expect("serialize");
        let back: VcObligation = serde_json::from_str(&s).expect("deserialize");
        assert_eq!(back, o);
    }
    /// M-2: an EnsuresPostcondition with `ret_ty_name: None`
    /// (non-primitive return) also round-trips. The serde
    /// `Option` representation must survive so a serialized
    /// report's pending obligations re-load with the
    /// unsupported-return marker intact.
    #[test]
    fn ensures_postcondition_none_ret_ty_round_trips() {
        let o = VcObligation {
            id: "pb076-ensures-0".into(),
            span: Span::default(),
            kind: VcObligationKind::EnsuresPostcondition {
                ret_name: "result".into(),
                ret_ty_name: None,
            },
            assumptions: Vec::new(),
        };
        let s = serde_json::to_string(&o).expect("serialize");
        let back: VcObligation = serde_json::from_str(&s).expect("deserialize");
        assert_eq!(back, o);
    }
}
