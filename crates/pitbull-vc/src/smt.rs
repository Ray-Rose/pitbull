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
//! - `emit_index_bound_problem`: `idx < len` proofs for slice
//!   indexing (PB054).
//! - `emit_panic_unreachable_problem`: path-sensitive symbolic
//!   reasoning to prove panic call sites unreachable (PB043).
//!   Requires a richer encoding than bit-vector arithmetic alone.
//! - `emit_decreasing_measure_problem`: termination measures for
//!   recursion (PB041).
use pitbull_subset::ArithOp;
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
    Some(format!(
        "(set-logic QF_BV)\n\
         (declare-const lhs (_ BitVec {bits}))\n\
         (declare-const rhs (_ BitVec {bits}))\n\
         (assert ({overflow_predicate} lhs rhs))\n\
         (check-sat)\n"
    ))
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
}
