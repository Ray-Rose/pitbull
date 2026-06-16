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
/// pointer-width-dependent. The user pins the target pointer width in
/// `pitbull.toml`'s `[subset]` table — the field
/// `SubsetConfig.subset.target_pointer_width` ALREADY EXISTS and is
/// validated (16/32/64) by `config.rs`. What is deferred is only the
/// PLUMBING: the v0.2 scaffold does not yet thread that value down to the
/// SMT layer, so this is hardcoded to 64. When the plumbing lands, this
/// constant becomes a parameter resolved from that field.
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
/// The encoded violation predicate depends on the operator (Task R,
/// 2026-05-28 — extended from overflow-only to full arithmetic AoRTE):
/// - `+` / `-` / `*` → SMT-LIB overflow predicates `bvuaddo`/`bvsaddo`,
///   `bvusubo`/`bvssubo`, `bvumulo`/`bvsmulo`.
/// - `/` / `%` → division-by-zero `(= rhs 0)`, plus (signed only) the
///   `MIN / -1` overflow `(and (= lhs MIN) (= rhs -1))`, combined with
///   `or`.
/// - `<<` / `>>` → over-shift `(bvuge rhs <bit-width>)` — a shift
///   amount at or beyond the value's bit width is UB-adjacent and
///   panics under debug assertions.
///
/// In every case the asserted predicate is the *violation* (the
/// negated safety property): `unsat` ⇒ the violation is impossible ⇒
/// the operation is safe; `sat` ⇒ a counterexample input exists.
#[must_use]
pub fn emit_overflow_problem(ty_name: &str, op: ArithOp) -> Option<String> {
    emit_overflow_problem_with_assumptions(ty_name, op, &[])
}
/// Format `value` as a `bits`-wide SMT-LIB hex literal (`#x...`).
/// All Pitbull-supported integer widths (8/16/32/64/128) are
/// multiples of 4, so a hex literal is always exact. Used for the
/// division and over-shift violation constants (zero, signed MIN,
/// -1, bit-width).
fn bv_hex(value: u128, bits: u32) -> String {
    let hex_digits = (bits / 4) as usize;
    let mask: u128 = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
    format!("#x{:0width$X}", value & mask, width = hex_digits)
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
    let bits = info.bits;
    // Build the VIOLATION predicate (the negated safety property)
    // as a complete SMT-LIB term, one per operator family.
    let violation: String = match op {
        // Overflow predicates: `bvXaddo`/`bvXsubo`/`bvXmulo` is true
        // exactly when the operation overflows the operand width.
        ArithOp::Add | ArithOp::Sub | ArithOp::Mul => {
            let pred = match (op, info.signed) {
                (ArithOp::Add, false) => "bvuaddo",
                (ArithOp::Add, true) => "bvsaddo",
                (ArithOp::Sub, false) => "bvusubo",
                (ArithOp::Sub, true) => "bvssubo",
                (ArithOp::Mul, false) => "bvumulo",
                (ArithOp::Mul, true) => "bvsmulo",
                // Unreachable: outer match already pinned Add/Sub/Mul.
                _ => unreachable!("outer match restricts to Add/Sub/Mul"),
            };
            format!("({pred} lhs rhs)")
        }
        // Division / remainder (Task R): the violation is
        // division-by-zero `(= rhs 0)` and, for SIGNED types only,
        // the `MIN / -1` overflow `(and (= lhs MIN) (= rhs -1))`.
        // Both `/` and `%` share the identical violation set in
        // Rust (both panic on zero divisor; both overflow on
        // `MIN % -1` / `MIN / -1`).
        ArithOp::Div | ArithOp::Rem => {
            let zero = bv_hex(0, bits);
            if info.signed {
                let min = bv_hex(1u128 << (bits - 1), bits); // 100..0
                let neg_one = bv_hex(u128::MAX, bits); // 111..1 (two's-complement -1)
                format!(
                    "(or (= rhs {zero}) (and (= lhs {min}) (= rhs {neg_one})))",
                )
            } else {
                format!("(= rhs {zero})")
            }
        }
        // Shift (Task R): the violation is an over-shift — a shift
        // amount at or beyond the value's bit width. In Rust this
        // is debug-assert UB (`attempt to shift left with overflow`).
        // `rhs` is the shift amount; the visitor only emits this
        // obligation when lhs and rhs share the operand type, so
        // `rhs` is `bits` wide and the comparison is well-sorted.
        // Unsigned compare because a shift amount is never negative.
        ArithOp::Shl | ArithOp::Shr => {
            let width = bv_hex(u128::from(bits), bits);
            format!("(bvuge rhs {width})")
        }
        // Unary negation (audit 2026-05-29). `-(x)` overflows exactly
        // when `x == iN::MIN` — the signed minimum has no positive
        // counterpart in two's complement, so its negation is
        // unrepresentable and panics in debug. The operand is in the
        // `lhs` position; `rhs` is unused. Rust has no unsigned unary
        // `-`, so the visitor only emits this for signed types; if an
        // unsigned type somehow reaches here, fail closed (return None
        // → the obligation is reported "pending"/undischarged rather
        // than encoded with a meaningless predicate).
        ArithOp::Neg => {
            if !info.signed {
                return None;
            }
            let min = bv_hex(1u128 << (bits - 1), bits); // 100..0 = iN::MIN
            format!("(= lhs {min})")
        }
    };
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
    smt.push_str(&format!("(assert {violation})\n(check-sat)\n"));
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
/// unsigned bit-vectors. The canonical SMT names (`idx`, `len`)
/// are always present so user preconditions can target them
/// directly.
///
/// Task P.2 binding: when `idx_alias` is `Some(name)`, the
/// problem additionally emits a `(define-fun |<name>| () (_
/// BitVec N) idx)` directive, aliasing the source-level
/// identifier (e.g. `i` for a function arg named `i`) to the
/// SMT `idx` variable. The visitor extracts the source name
/// from the MIR local that the `ProjectionElem::Index`
/// references; this lets user preconditions written using the
/// source name — `(assert (bvult i len))` — desugar to the
/// safety-relevant `(assert (bvult idx len))` and constrain
/// the solver.
///
/// Without an alias (and without any preconditions), the
/// problem is always satisfiable (idx=1, len=0 is a model) and
/// the obligation reports as undischarged. That's correct: the
/// obligation IS unproven in that case.
///
/// Audit-cleanup (audit finding F4, 2026-05-26): alias names
/// are wrapped in SMT-LIB quoted-symbol syntax (`|name|`) so
/// any Rust identifier is well-formed in the SMT problem —
/// including Rust raw identifiers (`r#let`, `r#match`) whose
/// rustc-parsed `info.name` is an SMT-LIB reserved word that
/// would otherwise produce `(define-fun let () ... idx)` and
/// trigger a Z3 parse error. Quoted symbols accept any
/// character except `|` and `\`; both are forbidden in Rust
/// identifiers, so no escaping is needed.
///
/// Audit-cleanup (audit finding F3, 2026-05-26): the canonical
/// SMT variable names have been renamed to `__pb_idx` and
/// `__pb_len` (defense-in-depth: Rust identifiers cannot start
/// with `__pb_`-style sequences that would collide). The
/// user-facing convention stays the same — `idx` and `len`
/// are emitted as `define-fun` aliases bound to the internal
/// names, so existing pitbull.toml preconditions continue to
/// work unchanged. The collision case (`fn at(s, idx) { s[idx] }`
/// where the arg is named `idx`) now resolves cleanly: the
/// arg alias and the canonical `idx` alias both coexist
/// without name conflict.
///
/// Assumptions are spliced between the declarations/aliases and
/// the negated-safety assertion, exactly as
/// `emit_overflow_problem_with_assumptions` does — same audit
/// posture, same lex-validation upstream contract.
#[must_use]
pub fn emit_index_bound_problem_with_assumptions(
    idx_alias: Option<&str>,
    assumptions: &[String],
) -> String {
    let mut smt = format!(
        "(set-logic QF_BV)\n\
         (declare-const __pb_idx (_ BitVec {INDEX_SMT_BITS}))\n\
         (declare-const __pb_len (_ BitVec {INDEX_SMT_BITS}))\n\
         (define-fun idx () (_ BitVec {INDEX_SMT_BITS}) __pb_idx)\n\
         (define-fun len () (_ BitVec {INDEX_SMT_BITS}) __pb_len)\n",
    );
    // Source-name alias (Task P.2). The arg name is wrapped in
    // SMT-LIB quoted-symbol syntax so any Rust identifier is
    // syntactically valid in the SMT problem (audit finding F4).
    if let Some(name) = idx_alias {
        // Skip when the source-arg name collides with one of the
        // canonical user-facing aliases `idx` or `len`. Per SMT-LIB
        // 2.6 §3.1, `idx` and `|idx|` denote the SAME symbol, so
        // emitting both `(define-fun idx () ...)` and
        // `(define-fun |idx| () ...)` produces a duplicate-symbol
        // parse error from Z3 → SolverResult::Error → undischarged
        // verdict with no clear cause for the user. Audit-cleanup
        // post-Q.3 red-team finding M-RT-Q.B (2026-05-26): the
        // canonical aliases already cover the case `arg name == idx`,
        // so we just skip the source-name alias when it would collide.
        if name != "idx" && name != "len" {
            smt.push_str(&format!(
                "(define-fun |{name}| () (_ BitVec {INDEX_SMT_BITS}) __pb_idx)\n",
            ));
        }
    }
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
    // never negative). Uses the internal canonical names since
    // `idx`/`len` are now aliases (define-fun forwards either
    // way; using the canonical names directly keeps the safety
    // predicate independent of alias-rewrite ordering).
    smt.push_str("(assert (bvuge __pb_idx __pb_len))\n(check-sat)\n");
    smt
}
/// Convenience wrapper: emit an SMT-LIB problem with no
/// assumptions and no idx alias. Useful in tests; production
/// path uses the `_with_assumptions` variant directly.
#[must_use]
pub fn emit_index_bound_problem() -> String {
    emit_index_bound_problem_with_assumptions(None, &[])
}
/// Sat-check-only variant for the consistency-check guard
/// (red-team F1): declarations + alias + assumptions +
/// check-sat, NO safety predicate. The dispatcher runs this
/// first when assumptions are present; an `unsat` here means
/// the assumptions are logically contradictory, so a downstream
/// `unsat` on the main problem would be vacuously true.
///
/// Mirrors `emit_consistency_check` for ArithmeticOverflow.
/// The `idx_alias` argument must be passed the SAME way as for
/// the main problem so that an assumption referencing the
/// source-level identifier resolves identically in both
/// problems — otherwise the consistency check would see a
/// different model and the F1 guard could mis-fire.
#[must_use]
pub fn emit_index_bound_consistency_check(
    idx_alias: Option<&str>,
    assumptions: &[String],
) -> String {
    let mut smt = format!(
        "(set-logic QF_BV)\n\
         (declare-const __pb_idx (_ BitVec {INDEX_SMT_BITS}))\n\
         (declare-const __pb_len (_ BitVec {INDEX_SMT_BITS}))\n\
         (define-fun idx () (_ BitVec {INDEX_SMT_BITS}) __pb_idx)\n\
         (define-fun len () (_ BitVec {INDEX_SMT_BITS}) __pb_len)\n",
    );
    if let Some(name) = idx_alias {
        // Skip when the source-arg name collides with one of the
        // canonical user-facing aliases `idx` or `len`. Per SMT-LIB
        // 2.6 §3.1, `idx` and `|idx|` denote the SAME symbol, so
        // emitting both `(define-fun idx () ...)` and
        // `(define-fun |idx| () ...)` produces a duplicate-symbol
        // parse error from Z3 → SolverResult::Error → undischarged
        // verdict with no clear cause for the user. Audit-cleanup
        // post-Q.3 red-team finding M-RT-Q.B (2026-05-26): the
        // canonical aliases already cover the case `arg name == idx`,
        // so we just skip the source-name alias when it would collide.
        if name != "idx" && name != "len" {
            smt.push_str(&format!(
                "(define-fun |{name}| () (_ BitVec {INDEX_SMT_BITS}) __pb_idx)\n",
            ));
        }
    }
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
    /// Task R: Div/Rem on UNSIGNED types encode only the
    /// division-by-zero violation `(= rhs 0)` — no signed MIN/-1
    /// arm. Pins the exact predicate.
    #[test]
    fn div_rem_unsigned_emits_div_by_zero_only() {
        for op in [ArithOp::Div, ArithOp::Rem] {
            let smt = emit_overflow_problem("u32", op).expect("u32 div/rem supported");
            assert!(
                smt.contains("(assert (= rhs #x00000000))"),
                "u32 {op:?} must assert div-by-zero `(= rhs 0)`; got:\n{smt}",
            );
            assert!(
                !smt.contains("(and"),
                "unsigned {op:?} must NOT carry the signed MIN/-1 arm; got:\n{smt}",
            );
        }
    }
    /// Task R: Div/Rem on SIGNED types encode div-by-zero OR the
    /// `MIN / -1` overflow. For i32: MIN = #x80000000, -1 =
    /// #xFFFFFFFF.
    #[test]
    fn div_rem_signed_emits_div_by_zero_or_min_neg_one() {
        for op in [ArithOp::Div, ArithOp::Rem] {
            let smt = emit_overflow_problem("i32", op).expect("i32 div/rem supported");
            assert!(
                smt.contains("(or (= rhs #x00000000) (and (= lhs #x80000000) (= rhs #xFFFFFFFF)))"),
                "i32 {op:?} must assert div-by-zero OR MIN/-1; got:\n{smt}",
            );
        }
    }
    /// Task R: Shl/Shr encode the over-shift violation — shift
    /// amount >= bit width, unsigned compare. For u32, width = 32
    /// = #x00000020.
    #[test]
    fn shl_shr_emits_over_shift() {
        for op in [ArithOp::Shl, ArithOp::Shr] {
            let smt = emit_overflow_problem("u32", op).expect("u32 shift supported");
            assert!(
                smt.contains("(assert (bvuge rhs #x00000020))"),
                "u32 {op:?} must assert over-shift `(bvuge rhs 32)`; got:\n{smt}",
            );
        }
    }
    /// Audit 2026-05-29: unary negation `-(x)` encodes the
    /// signed-minimum overflow `(= lhs iN::MIN)` — the only value
    /// whose negation overflows a signed integer. Unsigned negation
    /// does not exist in Rust, so the encoder returns `None` (fail
    /// closed) rather than emitting a meaningless predicate.
    #[test]
    fn neg_emits_signed_min_overflow() {
        // i32: MIN = #x80000000, operand declared 32 bits wide.
        let smt = emit_overflow_problem("i32", ArithOp::Neg).expect("i32 neg supported");
        assert!(
            smt.contains("(assert (= lhs #x80000000))"),
            "i32 neg must assert `(= lhs iN::MIN)`; got:\n{smt}",
        );
        assert!(
            smt.contains("(declare-const lhs (_ BitVec 32))"),
            "operand declared at the right width; got:\n{smt}",
        );
        // i8: MIN = #x80.
        let smt8 = emit_overflow_problem("i8", ArithOp::Neg).expect("i8 neg supported");
        assert!(
            smt8.contains("(assert (= lhs #x80))"),
            "i8 neg MIN = #x80; got:\n{smt8}",
        );
        // Unsigned negation is not representable in Rust → unsupported.
        assert!(
            emit_overflow_problem("u32", ArithOp::Neg).is_none(),
            "unsigned neg must be unsupported (None), not encoded",
        );
    }
    /// Task R: the division/shift constants are width-correct
    /// across the supported integer widths.
    #[test]
    fn div_shift_constants_width_correct() {
        // u8 div-by-zero: 8-bit zero = #x00.
        let smt = emit_overflow_problem("u8", ArithOp::Div).expect("u8");
        assert!(smt.contains("(= rhs #x00)"), "u8 zero; got:\n{smt}");
        // i8 MIN = #x80, -1 = #xFF.
        let smt = emit_overflow_problem("i8", ArithOp::Div).expect("i8");
        assert!(smt.contains("(= lhs #x80)") && smt.contains("(= rhs #xFF)"), "i8 MIN/-1; got:\n{smt}");
        // u64 shift width = 64 = #x0000000000000040.
        let smt = emit_overflow_problem("u64", ArithOp::Shl).expect("u64");
        assert!(smt.contains("(bvuge rhs #x0000000000000040)"), "u64 width; got:\n{smt}");
    }
    /// Pin the IndexBound SMT-LIB shape. Catches accidental
    /// changes to the bit-width, variable names, or safety
    /// predicate.
    ///
    /// Audit-cleanup (audit finding F3, 2026-05-26): canonical
    /// SMT variables are now `__pb_idx` / `__pb_len` with
    /// user-facing `idx` / `len` aliases. The `__pb_`-prefix
    /// internal names cannot collide with valid Rust
    /// identifiers (no Rust ident starts with `__pb_`-style
    /// double-underscore-keyword sequences in practice).
    #[test]
    fn index_bound_problem_basic() {
        let smt = emit_index_bound_problem();
        assert!(
            smt.contains("(set-logic QF_BV)"),
            "must declare QF_BV logic; got:\n{smt}",
        );
        assert!(
            smt.contains("(declare-const __pb_idx (_ BitVec 64))"),
            "must declare 64-bit __pb_idx; got:\n{smt}",
        );
        assert!(
            smt.contains("(declare-const __pb_len (_ BitVec 64))"),
            "must declare 64-bit __pb_len; got:\n{smt}",
        );
        assert!(
            smt.contains("(define-fun idx () (_ BitVec 64) __pb_idx)"),
            "must alias `idx` to `__pb_idx`; got:\n{smt}",
        );
        assert!(
            smt.contains("(define-fun len () (_ BitVec 64) __pb_len)"),
            "must alias `len` to `__pb_len`; got:\n{smt}",
        );
        assert!(
            smt.contains("(assert (bvuge __pb_idx __pb_len))"),
            "must assert the negated safety predicate (__pb_idx >= __pb_len); got:\n{smt}",
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
        let smt = emit_index_bound_problem_with_assumptions(None, &assumptions);
        let assume1_idx = smt
            .find("(assert (bvult idx #x0000000000000064))")
            .expect("first assumption present");
        let assume2_idx = smt
            .find("(assert (= len #x000000000000000a))")
            .expect("second assumption present");
        let safety_idx = smt
            .find("(assert (bvuge __pb_idx __pb_len))")
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
        let cs = emit_index_bound_consistency_check(None, &[
            "(assert (bvult idx #x0000000000000064))".into(),
        ]);
        assert!(cs.contains("(declare-const __pb_idx (_ BitVec 64))"));
        assert!(cs.contains("(declare-const __pb_len (_ BitVec 64))"));
        assert!(cs.contains("(define-fun idx () (_ BitVec 64) __pb_idx)"));
        assert!(cs.contains("(assert (bvult idx #x0000000000000064))"));
        assert!(
            !cs.contains("bvuge"),
            "consistency check must NOT contain the safety predicate; got:\n{cs}",
        );
        assert!(cs.ends_with("(check-sat)\n"));
    }
    /// Task P.2: passing `Some("i")` as the alias emits a
    /// `(define-fun |i| () (_ BitVec 64) __pb_idx)` directive
    /// so user preconditions referencing `i` constrain the SMT
    /// problem. Audit-cleanup F4: alias is wrapped in
    /// quoted-symbol syntax `|name|` so any Rust identifier
    /// (including raw idents) produces a well-formed directive.
    #[test]
    fn index_bound_with_alias_emits_define_fun() {
        let smt = emit_index_bound_problem_with_assumptions(Some("i"), &[]);
        assert!(
            smt.contains("(define-fun |i| () (_ BitVec 64) __pb_idx)"),
            "alias should emit a define-fun aliasing the source name to __pb_idx; got:\n{smt}",
        );
        // The alias must appear AFTER the __pb_idx declaration
        // (it references it) and BEFORE the safety predicate.
        let pb_idx_decl = smt.find("(declare-const __pb_idx").expect("__pb_idx decl");
        let alias = smt.find("(define-fun |i|").expect("alias");
        let safety = smt.find("(assert (bvuge __pb_idx __pb_len))").expect("safety");
        assert!(
            pb_idx_decl < alias,
            "alias must come after __pb_idx declaration; decl={pb_idx_decl}, alias={alias}",
        );
        assert!(
            alias < safety,
            "alias must come before safety predicate; alias={alias}, safety={safety}",
        );
    }
    /// Audit-cleanup post-Q.3 red-team finding M-RT-Q.B
    /// (2026-05-26): when the source-arg name is `idx` or `len`,
    /// the source-name alias is SKIPPED to avoid a duplicate
    /// define-fun (per SMT-LIB 2.6 §3.1, `idx` and `|idx|`
    /// denote the SAME symbol — emitting both produces a Z3
    /// parse error → solver error → undischarged with no clear
    /// cause). The earlier F3 fix mistakenly thought `|idx|`
    /// and `idx` were distinct quoted vs simple symbols; the
    /// red-team caught this. The canonical user-facing aliases
    /// `idx` / `len` already cover the case — when arg is named
    /// `idx`, user preconditions referencing `idx` correctly
    /// resolve via the canonical alias.
    #[test]
    fn index_bound_alias_with_canonical_name_skipped() {
        for collision in ["idx", "len"] {
            let smt = emit_index_bound_problem_with_assumptions(Some(collision), &[]);
            // The canonical alias `(define-fun idx () ... __pb_idx)`
            // is still present (that's the always-emitted one).
            // What MUST NOT be present is a DUPLICATE source-name
            // alias `(define-fun |idx| () ... __pb_idx)`.
            assert!(
                !smt.contains(&format!("(define-fun |{collision}|")),
                "arg name `{collision}` collides with canonical alias; source-name \
                 alias must be skipped to avoid Z3 duplicate-define-fun error. Got:\n{smt}",
            );
        }
    }
    /// Non-collision arg names still produce the source-name
    /// alias (the normal Q.3-supported path).
    #[test]
    fn index_bound_alias_with_non_canonical_name_emitted() {
        for arg_name in ["i", "x", "my_var", "index_value"] {
            let smt = emit_index_bound_problem_with_assumptions(Some(arg_name), &[]);
            assert!(
                smt.contains(&format!("(define-fun |{arg_name}| () (_ BitVec 64) __pb_idx)")),
                "non-collision arg name `{arg_name}` must produce the quoted-symbol \
                 alias; got:\n{smt}",
            );
        }
    }
    /// Audit-cleanup F4: Rust raw identifiers (`r#let`, `r#match`)
    /// produce source names that ARE SMT-LIB reserved words.
    /// Pre-cleanup, the alias would have been emitted as
    /// `(define-fun let () (_ BitVec 64) idx)`, which Z3 rejects
    /// as a parse error (the user sees "solver error" with no
    /// clear cause). Post-cleanup, the quoted-symbol wrapping
    /// makes the directive well-formed: `(define-fun |let| ()
    /// (_ BitVec 64) __pb_idx)`. Z3 accepts it as a regular
    /// symbol distinct from the `let` keyword.
    #[test]
    fn index_bound_alias_with_smt_reserved_word_well_formed() {
        for reserved in ["let", "match", "forall", "exists", "true", "false", "or", "and", "not"] {
            let smt = emit_index_bound_problem_with_assumptions(Some(reserved), &[]);
            assert!(
                smt.contains(&format!("(define-fun |{reserved}| () (_ BitVec 64) __pb_idx)")),
                "SMT reserved word `{reserved}` must be wrapped in quoted-symbol syntax; got:\n{smt}",
            );
        }
    }
    /// Task P.2: the assumption can reference the aliased name
    /// and the resulting SMT problem is well-formed (declarations
    /// come first, alias comes after __pb_idx, assumption
    /// references the alias, safety predicate uses __pb_idx).
    #[test]
    fn index_bound_alias_lets_assumption_reference_source_name() {
        let smt = emit_index_bound_problem_with_assumptions(
            Some("i"),
            &["(assert (bvult i len))".into()],
        );
        // Alias must appear before the assumption.
        let alias = smt.find("(define-fun |i|").expect("alias");
        let assumption = smt.find("(assert (bvult i len))").expect("assumption");
        assert!(
            alias < assumption,
            "alias must be defined before the assumption uses it; \
             alias={alias}, assumption={assumption}",
        );
    }
}
