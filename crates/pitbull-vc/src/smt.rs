//! SMT-LIB 2 emission for verification conditions.
//!
//! The format is the standard SMT-LIB 2.6 textual problem
//! description: a `set-logic` directive, type declarations, free
//! variables, the negated safety property (asserted), and
//! `check-sat`. A solver returns:
//!
//! - **`unsat`** → the negated property is unsatisfiable → the
//!   safety property holds for all inputs → **verified**.
//! - **`sat`** → the negated property has a model → a
//!   counterexample input exists → **violation**.
//! - **`unknown`** → solver couldn't decide within its limits →
//!   **inconclusive**.
//!
//! ## Today
//!
//! `emit_overflow_problem` covers arithmetic overflow for the
//! primitive integer types. Bit-vector encoding so we get exact
//! two's-complement semantics matching Rust's `Wrapping<T>` /
//! `overflow-checks` posture. PSS-1 PB049 requires
//! `overflow-checks = true` in release builds — i.e. overflow
//! should be impossible. The SMT problem we emit asks "does
//! there exist an input where this op overflows?" If `unsat`,
//! we've proven the obligation.
//!
//! ## Future
//!
//! - `emit_panic_unreachable_problem`: path-sensitive symbolic
//!   reasoning to prove panic call sites unreachable (PB043).
//!   Requires a richer encoding than bit-vector arithmetic alone.
//! - `emit_decreasing_measure_problem`: termination measures for
//!   recursion (PB041).
use pitbull_subset::ArithOp;
/// SMT bit-width used for index bound checks.
///
/// Slice / array indices in Rust are `usize`, which is target-
/// pointer-width-dependent. PSS-1 PB052 has the user pin the
/// target pointer width in `pitbull.toml`'s `[verification]`
/// table, but the v0.2 scaffold doesn't yet thread that down to
/// the SMT layer. Hardcoded to 64 here on the assumption that
/// v0.2 targets x86_64 / aarch64 / wasm64. When the threading
/// lands, this constant becomes a parameter resolved from the
/// `SubsetConfig.verification.target_pointer_width` field.
///
/// Rationale for hard-coding 64 vs 32: false-negative direction
/// is asymmetric — a 64-bit encoding can model 32-bit problems
/// (the extra bits are unconstrained, the solver finds the same
/// counterexample), but a 32-bit encoding can't model 64-bit
/// problems (the solver may report unsat for a problem with a
/// 64-bit-only counterexample). So choosing the wider default
/// keeps the encoding sound across both target widths until the
/// proper threading is wired.
const INDEX_SMT_BITS: u32 = 64;
/// Information about a primitive integer type for SMT encoding.
struct IntInfo {
    /// Bit width.
    bits: u32,
    /// Signed or unsigned (affects which bit-vector predicate to
    /// use for the overflow check).
    signed: bool,
}
impl IntInfo {
    fn from_name(name: &str) -> Option<Self> {
        let (signed, rest) = if let Some(r) = name.strip_prefix('u') {
            (false, r)
        } else if let Some(r) = name.strip_prefix('i') {
            (true, r)
        } else {
            return None;
        };
        let bits = match rest {
            "8" => 8,
            "16" => 16,
            "32" => 32,
            "64" => 64,
            "128" => 128,
            // usize/isize are platform-dependent. PSS-1 PB052 has the
            // user pin target pointer width in pitbull.toml; v0.2
            // scaffold doesn't yet thread that here, so usize/isize
            // are rejected.
            _ => return None,
        };
        Some(Self { bits, signed })
    }
}
/// Emit an SMT-LIB 2 problem that asks "is overflow possible for
/// `lhs <op> rhs` where both operands have type `ty_name`?".
///
/// Returns `None` if the type isn't a supported primitive integer.
///
/// Solver semantics:
/// - `unsat` ⇒ overflow is impossible ⇒ PSS-1 PB049 obligation
///   discharged ⇒ safe.
/// - `sat`   ⇒ a witness exists ⇒ obligation NOT discharged ⇒
///   the rule fires (the counterexample is the SAT model).
///
/// The encoded predicate uses SMT-LIB bit-vector overflow predicates:
/// - `bvuaddo` / `bvsaddo` for `+`
/// - `bvusubo` / `bvssubo` for `-`
/// - `bvumulo` / `bvsmulo` for `*`
/// (Division/remainder/shift overflow predicates land in a follow-up.)
#[must_use]
pub fn emit_overflow_problem(ty_name: &str, op: ArithOp) -> Option<String> {
    emit_overflow_problem_with_assumptions(ty_name, op, &[])
}
/// Emit a SAT-CHECK-ONLY problem for the given assumptions: just
/// the declarations + each assumption + `(check-sat)`. NO safety
/// predicate, NO negation.
///
/// Used as a precondition-consistency guard (red-team finding F1):
/// if the solver returns `unsat` here, the assumptions are
/// LOGICALLY CONTRADICTORY. Under contradictory hypotheses, the
/// main check-sat would also return unsat for any safety
/// property — silently "proving" the code safe via vacuous
/// implication. The dispatch layer refuses to claim discharge
/// when this consistency check is unsat.
///
/// Returns `None` for unsupported types (matching the rest of the
/// module's behavior).
#[must_use]
pub fn emit_consistency_check(
    ty_name: &str,
    assumptions: &[String],
) -> Option<String> {
    let info = IntInfo::from_name(ty_name)?;
    let bits = info.bits;
    let mut smt = format!(
        "(set-logic QF_BV)\n\
         (declare-const lhs (_ BitVec {bits}))\n\
         (declare-const rhs (_ BitVec {bits}))\n",
    );
    for assumption in assumptions {
        smt.push_str(assumption);
        if !assumption.ends_with('\n') {
            smt.push('\n');
        }
    }
    smt.push_str("(check-sat)\n");
    Some(smt)
}
/// Same as `emit_overflow_problem`, but each entry in `assumptions`
/// is spliced verbatim into the problem (between the variable
/// declarations and the overflow predicate). The assumptions
/// arrive from `VcObligation.assumptions`, ultimately rooted in
/// `pitbull.toml`'s `[verification.preconditions]` table.
///
/// Each assumption must already pass
/// `pitbull_subset::predicate::validate_assertion_form` — that's
/// the visitor's job upstream, and it ensures each string is a
/// single balanced-paren `(assert ...)` directive.
///
/// Ordering: assumptions appear BEFORE the overflow predicate.
/// SMT-LIB asserts are conjunctive, so the solver gets the
/// preconditions as hypotheses when checking the obligation.
#[must_use]
pub fn emit_overflow_problem_with_assumptions(
    ty_name: &str,
    op: ArithOp,
    assumptions: &[String],
) -> Option<String> {
    let info = IntInfo::from_name(ty_name)?;
    let overflow_predicate = match (op, info.signed) {
        (ArithOp::Add, false) => "bvuaddo",
        (ArithOp::Add, true) => "bvsaddo",
        (ArithOp::Sub, false) => "bvusubo",
        (ArithOp::Sub, true) => "bvssubo",
        (ArithOp::Mul, false) => "bvumulo",
        (ArithOp::Mul, true) => "bvsmulo",
        // Div/Rem/Shl/Shr need different encoding shapes — defer.
        (ArithOp::Div | ArithOp::Rem | ArithOp::Shl | ArithOp::Shr, _) => {
            return None;
        }
    };
    let bits = info.bits;
    // QF_BV: quantifier-free bit-vector logic, the decidable
    // fragment Z3 and CVC5 both handle natively.
    let mut smt = format!(
        "(set-logic QF_BV)\n\
         (declare-const lhs (_ BitVec {bits}))\n\
         (declare-const rhs (_ BitVec {bits}))\n",
    );
    for assumption in assumptions {
        smt.push_str(assumption);
        if !assumption.ends_with('\n') {
            smt.push('\n');
        }
    }
    smt.push_str(&format!(
        "(assert ({overflow_predicate} lhs rhs))\n\
         (check-sat)\n",
    ));
    Some(smt)
}
/// Emit an SMT-LIB 2 problem that asks "is `idx >= len`
/// satisfiable, given the assumptions?" — i.e. the negation of
/// the safety property `idx < len`.
///
/// Solver semantics:
/// - `unsat` ⇒ the negation has no model ⇒ `idx < len` always
///   holds under the assumptions ⇒ PSS-1 PB054 obligation
///   discharged ⇒ safe.
/// - `sat`   ⇒ a counterexample exists ⇒ obligation NOT
///   discharged ⇒ the rule fires.
///
/// Both `idx` and `len` are declared as `INDEX_SMT_BITS`-wide
/// unsigned bit-vectors. The variable names (`idx`, `len`) are
/// the canonical SMT bindings users target in preconditions —
/// `#[pitbull::requires("idx < len")]` translates to
/// `(assert (bvult idx len))` and constrains the solver.
///
/// Without bindings (the visitor doesn't yet thread the index
/// operand and slice place into the obligation), this problem
/// is always satisfiable (idx=1, len=0 is a model). That's
/// correct: the obligation IS unproven without operand bindings
/// or preconditions. The wrapper surfaces this as "NOT
/// DISCHARGED (sat — counterexample exists)" which is the
/// honest audit verdict. Once binding lands, well-constrained
/// problems return `unsat` and the obligation discharges.
///
/// Assumptions are spliced verbatim between the declarations
/// and the negated-safety assertion, exactly as
/// `emit_overflow_problem_with_assumptions` does — same audit
/// posture, same lex-validation upstream contract.
#[must_use]
pub fn emit_index_bound_problem_with_assumptions(
    assumptions: &[String],
) -> String {
    let mut smt = format!(
        "(set-logic QF_BV)\n\
         (declare-const idx (_ BitVec {INDEX_SMT_BITS}))\n\
         (declare-const len (_ BitVec {INDEX_SMT_BITS}))\n",
    );
    for assumption in assumptions {
        smt.push_str(assumption);
        if !assumption.ends_with('\n') {
            smt.push('\n');
        }
    }
    // Negation of safety: we want to prove `idx < len`. The
    // solver checks the negation `idx >= len`. `bvuge` is the
    // unsigned greater-or-equal predicate for bit-vectors —
    // matches Rust's slice-index semantics (indices are usize,
    // never negative).
    smt.push_str("(assert (bvuge idx len))\n(check-sat)\n");
    smt
}
/// Convenience wrapper: emit an SMT-LIB problem with no
/// assumptions. Useful in tests; production path uses the
/// `_with_assumptions` variant directly.
#[must_use]
pub fn emit_index_bound_problem() -> String {
    emit_index_bound_problem_with_assumptions(&[])
}
/// Sat-check-only variant for the consistency-check guard
/// (red-team F1): declarations + assumptions + check-sat, NO
/// safety predicate. The dispatcher runs this first when
/// assumptions are present; an `unsat` here means the
/// assumptions are logically contradictory, so a downstream
/// `unsat` on the main problem would be vacuously true.
///
/// Mirrors `emit_consistency_check` for ArithmeticOverflow.
#[must_use]
pub fn emit_index_bound_consistency_check(
    assumptions: &[String],
) -> String {
    let mut smt = format!(
        "(set-logic QF_BV)\n\
         (declare-const idx (_ BitVec {INDEX_SMT_BITS}))\n\
         (declare-const len (_ BitVec {INDEX_SMT_BITS}))\n",
    );
    for assumption in assumptions {
        smt.push_str(assumption);
        if !assumption.ends_with('\n') {
            smt.push('\n');
        }
    }
    smt.push_str("(check-sat)\n");
    smt
}
#[cfg(test)]
mod tests {
    use super::*;
    /// Pin the SMT-LIB output for u32 + u32 unsigned overflow.
    /// A diff here means someone changed the verification semantics —
    /// catch it in review.
    #[test]
    fn u32_add_unsigned_overflow_problem() {
        let smt = emit_overflow_problem("u32", ArithOp::Add)
            .expect("u32 + is supported");
        assert!(
            smt.contains("(set-logic QF_BV)"),
            "must declare QF_BV logic; got:\n{smt}",
        );
        assert!(
            smt.contains("(declare-const lhs (_ BitVec 32))"),
            "must declare 32-bit lhs; got:\n{smt}",
        );
        assert!(
            smt.contains("(declare-const rhs (_ BitVec 32))"),
            "must declare 32-bit rhs; got:\n{smt}",
        );
        assert!(
            smt.contains("(assert (bvuaddo lhs rhs))"),
            "must use unsigned-add-overflow predicate; got:\n{smt}",
        );
        assert!(
            smt.contains("(check-sat)"),
            "must terminate with check-sat; got:\n{smt}",
        );
    }
    /// Signed variant: i32 + i32 uses bvsaddo (signed predicate).
    #[test]
    fn i32_add_signed_overflow_uses_bvsaddo() {
        let smt = emit_overflow_problem("i32", ArithOp::Add)
            .expect("i32 + is supported");
        assert!(
            smt.contains("(assert (bvsaddo lhs rhs))"),
            "signed types must use bvsaddo; got:\n{smt}",
        );
    }
    /// Width derivation works for every supported primitive int.
    #[test]
    fn all_primitive_widths_supported() {
        for ty in ["u8", "u16", "u32", "u64", "u128", "i8", "i16", "i32", "i64", "i128"] {
            assert!(
                emit_overflow_problem(ty, ArithOp::Mul).is_some(),
                "expected {ty} * to produce an SMT problem",
            );
        }
    }
    /// usize / isize are intentionally rejected today (pending the
    /// pitbull.toml target-pointer-width threading in v0.2 follow-up).
    #[test]
    fn usize_isize_rejected_pending_pointer_width_threading() {
        assert!(emit_overflow_problem("usize", ArithOp::Add).is_none());
        assert!(emit_overflow_problem("isize", ArithOp::Add).is_none());
    }
    /// Div / rem / shifts return None today (encoding differs;
    /// scaffolded for follow-up commit).
    #[test]
    fn div_rem_shifts_return_none_today() {
        for op in [ArithOp::Div, ArithOp::Rem, ArithOp::Shl, ArithOp::Shr] {
            assert!(
                emit_overflow_problem("u32", op).is_none(),
                "expected u32 {op:?} to defer SMT emission",
            );
        }
    }
    /// Pin the IndexBound SMT-LIB shape. Catches accidental
    /// changes to the bit-width, variable names, or safety
    /// predicate.
    #[test]
    fn index_bound_problem_basic() {
        let smt = emit_index_bound_problem();
        assert!(
            smt.contains("(set-logic QF_BV)"),
            "must declare QF_BV logic; got:\n{smt}",
        );
        assert!(
            smt.contains("(declare-const idx (_ BitVec 64))"),
            "must declare 64-bit idx; got:\n{smt}",
        );
        assert!(
            smt.contains("(declare-const len (_ BitVec 64))"),
            "must declare 64-bit len; got:\n{smt}",
        );
        assert!(
            smt.contains("(assert (bvuge idx len))"),
            "must assert the negated safety predicate (idx >= len); got:\n{smt}",
        );
        assert!(
            smt.ends_with("(check-sat)\n"),
            "must terminate with check-sat; got:\n{smt}",
        );
    }
    /// Unsigned predicate: `bvuge` (not `bvsge`). Slice indices
    /// are usize, never negative — using the signed predicate
    /// would let the solver consider negative-idx counterexamples
    /// that can't occur in Rust. Pin the unsigned shape so an
    /// accidental signed-ification gets caught.
    #[test]
    fn index_bound_uses_unsigned_predicate() {
        let smt = emit_index_bound_problem();
        assert!(
            smt.contains("bvuge"),
            "must use unsigned ge predicate; got:\n{smt}",
        );
        assert!(
            !smt.contains("bvsge"),
            "must NOT use signed ge predicate (slice indices are usize); got:\n{smt}",
        );
    }
    /// Assumptions splice in BEFORE the safety predicate so the
    /// solver sees them as hypotheses, matching the overflow
    /// encoding's contract.
    #[test]
    fn index_bound_with_assumptions_orders_correctly() {
        let assumptions = vec![
            "(assert (bvult idx #x0000000000000064))".into(),
            "(assert (= len #x000000000000000a))".into(),
        ];
        let smt = emit_index_bound_problem_with_assumptions(&assumptions);
        let assume1_idx = smt
            .find("(assert (bvult idx #x0000000000000064))")
            .expect("first assumption present");
        let assume2_idx = smt
            .find("(assert (= len #x000000000000000a))")
            .expect("second assumption present");
        let safety_idx = smt
            .find("(assert (bvuge idx len))")
            .expect("safety predicate present");
        assert!(
            assume1_idx < safety_idx && assume2_idx < safety_idx,
            "assumptions must come before the safety predicate; \
             assume1={assume1_idx}, assume2={assume2_idx}, safety={safety_idx}",
        );
    }
    /// Consistency check has the same declarations + assumptions
    /// but NO safety predicate — used by the dispatcher to check
    /// assumptions aren't contradictory before claiming
    /// discharge.
    #[test]
    fn index_bound_consistency_check_omits_safety_predicate() {
        let cs = emit_index_bound_consistency_check(&[
            "(assert (bvult idx #x0000000000000064))".into(),
        ]);
        assert!(cs.contains("(declare-const idx (_ BitVec 64))"));
        assert!(cs.contains("(declare-const len (_ BitVec 64))"));
        assert!(cs.contains("(assert (bvult idx #x0000000000000064))"));
        assert!(
            !cs.contains("bvuge"),
            "consistency check must NOT contain the safety predicate; got:\n{cs}",
        );
        assert!(cs.ends_with("(check-sat)\n"));
    }
}
