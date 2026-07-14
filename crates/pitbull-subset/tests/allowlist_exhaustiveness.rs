//! Exhaustiveness gate for the integer trusted-total allow-list (the TCB
//! surface `visitor.rs::is_trusted_total_library_call` +
//! `is_panicking_int_method`).
//!
//! ## Why this file exists
//!
//! Two consecutive deep audits each found a CRITICAL **false discharge** of the
//! exact same shape in `is_trusted_total_library_call`:
//!
//! - 2026-07-09: `Ord::clamp` + the slice `sort` family (evicted).
//! - 2026-07-12: the `wrapping_`/`overflowing_`/`saturating_` **div/rem**
//!   members (evicted).
//!
//! Both are one bug class: a **broad allow-list glob trusts a whole method
//! family, but some members of that family panic.** `is_trusted_total_library_call`
//! trusts any integer method whose path `contains("::wrapping_")` /
//! `"::checked_"` / `"::saturating_"` / `"::overflowing_"` / `"::unbounded_"` /
//! `"::from_"` / `"::to_"`. A panicking member swept in by one of those globs —
//! and NOT positively caught by the deny matcher that runs first — is silently
//! "verified" (exit 0). That is the cardinal sin (a false discharge of unsafe
//! code).
//!
//! Prior tests hand-picked a few method names. This gate instead **enumerates
//! every member of each trust-granting glob** (reviewed against the Rust 1.94
//! stdlib integer API on 2026-07-13) and, for each, asserts the classifier's
//! decision against a **runtime-anchored ground truth** — a probe that actually
//! calls the method on a witness input and observes whether it panics. If a
//! future stdlib bump adds a panicking member to one of these families, or a
//! refactor widens a glob, this test fails instead of the next auditor finding
//! it as a live false discharge.
//!
//! ## The invariant asserted per entry
//!
//! - `Panics` ⟹ `is_panicking_int_method(path)` is true (positively caught,
//!   routed to a PB043 obligation, never silently accepted) AND
//!   `is_trusted_total_library_call(path)` is false (**the soundness guard**:
//!   no panicking method is trusted).
//! - `Total` ⟹ `is_panicking_int_method(path)` is false (not a false reject)
//!   AND `is_trusted_total_library_call(path)` is true (the glob still trusts
//!   it — an eviction that over-reached would false-reject provably safe code).
//!
//! The runtime probe anchors the LABEL to reality: a `Panics` entry must
//! actually panic on its witness input, and a `Total` entry must not. So a
//! mislabel (the failure mode that plants these bugs — "I assumed the whole
//! family was total") cannot pass silently; the ground-truth arm catches it.
//!
//! Complements the shape-level ground truth in
//! `aorte_proofs.rs::control_panicking_int_methods_do_panic_safe_ones_do_not`.

use pitbull_subset::visitor::{is_panicking_int_method, is_trusted_total_library_call};
use std::hint::black_box;

/// Ground-truth totality of an integer method on its witness input.
#[derive(Clone, Copy, Debug)]
enum G {
    /// Never panics on any input (the witness is an adversarial one).
    Total,
    /// Panics on the witness input (zero divisor, overflow under
    /// overflow-checks, or over-shift — the property that bars trust).
    Panics,
}
use G::{Panics, Total};

/// `true` iff calling `f` unwinds. `f` is a bare `fn()` (non-capturing
/// closures coerce), which is `UnwindSafe`, so no `AssertUnwindSafe` is needed.
/// The global panic hook is intentionally left in place (matching
/// `aorte_proofs.rs`) — muting it would race sibling tests that also
/// `catch_unwind` in parallel. Expect witnessed panics to print to stderr; the
/// assertions, not the noise, are the signal.
fn panics(f: fn()) -> bool {
    std::panic::catch_unwind(f).is_err()
}

/// The complete membership of each trust-granting integer family glob, plus the
/// panicking plain-method families the deny matcher must also catch. Witness
/// inputs `black_box(_)` the operand that drives the panic so it is a RUNTIME
/// event, never a const-evaluable one the deny-by-default `unconditional_panic`
/// lint would reject at compile time.
#[rustfmt::skip]
const TABLE: &[(&str, G, fn())] = &[
    // ---- `wrapping_*` family (complete) ----------------------------------
    // Mixed: add/sub/mul/neg/abs/pow/shl/shr and the signed/unsigned offset
    // forms wrap (total); ONLY div/rem/div_euclid/rem_euclid panic (÷0).
    ("core::num::<impl i32>::wrapping_add",          Total,  || { let _ = i32::MAX.wrapping_add(black_box(1)); }),
    ("core::num::<impl i32>::wrapping_sub",          Total,  || { let _ = i32::MIN.wrapping_sub(black_box(1)); }),
    ("core::num::<impl i32>::wrapping_mul",          Total,  || { let _ = i32::MAX.wrapping_mul(black_box(2)); }),
    ("core::num::<impl i32>::wrapping_neg",          Total,  || { let _ = black_box(i32::MIN).wrapping_neg(); }),
    ("core::num::<impl i32>::wrapping_abs",          Total,  || { let _ = black_box(i32::MIN).wrapping_abs(); }),
    ("core::num::<impl i32>::wrapping_pow",          Total,  || { let _ = i32::MAX.wrapping_pow(black_box(2)); }),
    ("core::num::<impl i32>::wrapping_shl",          Total,  || { let _ = 1i32.wrapping_shl(black_box(100)); }),
    ("core::num::<impl i32>::wrapping_shr",          Total,  || { let _ = 256i32.wrapping_shr(black_box(100)); }),
    ("core::num::<impl i32>::wrapping_add_unsigned", Total,  || { let _ = 5i32.wrapping_add_unsigned(black_box(3u32)); }),
    ("core::num::<impl i32>::wrapping_sub_unsigned", Total,  || { let _ = 5i32.wrapping_sub_unsigned(black_box(3u32)); }),
    ("core::num::<impl u32>::wrapping_add_signed",   Total,  || { let _ = 5u32.wrapping_add_signed(black_box(-2i32)); }),
    ("core::num::<impl i32>::wrapping_div",          Panics, || { let _ = 5i32.wrapping_div(black_box(0)); }),
    ("core::num::<impl u32>::wrapping_rem",          Panics, || { let _ = 5u32.wrapping_rem(black_box(0)); }),
    ("core::num::<impl i64>::wrapping_div_euclid",   Panics, || { let _ = 5i64.wrapping_div_euclid(black_box(0)); }),
    ("core::num::<impl i32>::wrapping_rem_euclid",   Panics, || { let _ = 5i32.wrapping_rem_euclid(black_box(0)); }),

    // ---- `overflowing_*` family (complete) -------------------------------
    // Same split: only div/rem/div_euclid/rem_euclid panic (÷0). The rest
    // return `(value, overflowed)` and never panic.
    ("core::num::<impl i32>::overflowing_add",          Total,  || { let _ = i32::MAX.overflowing_add(black_box(1)); }),
    ("core::num::<impl i32>::overflowing_sub",          Total,  || { let _ = i32::MIN.overflowing_sub(black_box(1)); }),
    ("core::num::<impl i32>::overflowing_mul",          Total,  || { let _ = i32::MAX.overflowing_mul(black_box(2)); }),
    ("core::num::<impl i32>::overflowing_neg",          Total,  || { let _ = black_box(i32::MIN).overflowing_neg(); }),
    ("core::num::<impl i32>::overflowing_abs",          Total,  || { let _ = black_box(i32::MIN).overflowing_abs(); }),
    ("core::num::<impl i32>::overflowing_pow",          Total,  || { let _ = i32::MAX.overflowing_pow(black_box(2)); }),
    ("core::num::<impl i32>::overflowing_shl",          Total,  || { let _ = 1i32.overflowing_shl(black_box(100)); }),
    ("core::num::<impl i32>::overflowing_shr",          Total,  || { let _ = 256i32.overflowing_shr(black_box(100)); }),
    ("core::num::<impl i32>::overflowing_add_unsigned", Total,  || { let _ = 5i32.overflowing_add_unsigned(black_box(3u32)); }),
    ("core::num::<impl i32>::overflowing_sub_unsigned", Total,  || { let _ = 5i32.overflowing_sub_unsigned(black_box(3u32)); }),
    ("core::num::<impl u32>::overflowing_add_signed",   Total,  || { let _ = 5u32.overflowing_add_signed(black_box(-2i32)); }),
    ("core::num::<impl u32>::overflowing_div",          Panics, || { let _ = 5u32.overflowing_div(black_box(0)); }),
    ("core::num::<impl i32>::overflowing_rem",          Panics, || { let _ = 5i32.overflowing_rem(black_box(0)); }),
    ("core::num::<impl i32>::overflowing_div_euclid",   Panics, || { let _ = 5i32.overflowing_div_euclid(black_box(0)); }),
    ("core::num::<impl i64>::overflowing_rem_euclid",   Panics, || { let _ = 5i64.overflowing_rem_euclid(black_box(0)); }),

    // ---- `saturating_*` family (complete) --------------------------------
    // add/sub/mul/neg/abs/pow and offset forms saturate (total). ONLY
    // `saturating_div` panics (÷0). NB: there is no `saturating_rem`,
    // `saturating_shl/shr`, or `saturating_*_euclid` in std.
    ("core::num::<impl i32>::saturating_add",          Total,  || { let _ = i32::MAX.saturating_add(black_box(1)); }),
    ("core::num::<impl i32>::saturating_sub",          Total,  || { let _ = i32::MIN.saturating_sub(black_box(1)); }),
    ("core::num::<impl i32>::saturating_mul",          Total,  || { let _ = i32::MAX.saturating_mul(black_box(2)); }),
    ("core::num::<impl i32>::saturating_neg",          Total,  || { let _ = black_box(i32::MIN).saturating_neg(); }),
    ("core::num::<impl i32>::saturating_abs",          Total,  || { let _ = black_box(i32::MIN).saturating_abs(); }),
    ("core::num::<impl i32>::saturating_pow",          Total,  || { let _ = i32::MAX.saturating_pow(black_box(2)); }),
    ("core::num::<impl i32>::saturating_add_unsigned", Total,  || { let _ = 5i32.saturating_add_unsigned(black_box(3u32)); }),
    ("core::num::<impl i32>::saturating_sub_unsigned", Total,  || { let _ = 5i32.saturating_sub_unsigned(black_box(3u32)); }),
    ("core::num::<impl u32>::saturating_add_signed",   Total,  || { let _ = 5u32.saturating_add_signed(black_box(-2i32)); }),
    ("core::num::<impl i32>::saturating_div",          Panics, || { let _ = 5i32.saturating_div(black_box(0)); }),

    // ---- `checked_*` family (representative; uniformly total) -------------
    // Every `checked_*` returns `Option`/`None` on the bad input, so the whole
    // family is total. The div/rem members are the calibration complement to
    // the panicking `wrapping_/overflowing_/saturating_` div/rem above: same
    // suffix, opposite verdict, because they carry no wrap/sat/overflow glob.
    ("core::num::<impl i32>::checked_add",          Total, || { let _ = i32::MAX.checked_add(black_box(1)); }),
    ("core::num::<impl i32>::checked_mul",          Total, || { let _ = i32::MAX.checked_mul(black_box(2)); }),
    ("core::num::<impl i32>::checked_div",          Total, || { let _ = 5i32.checked_div(black_box(0)); }),
    ("core::num::<impl u32>::checked_rem",          Total, || { let _ = 5u32.checked_rem(black_box(0)); }),
    ("core::num::<impl i64>::checked_div_euclid",   Total, || { let _ = 5i64.checked_div_euclid(black_box(0)); }),
    ("core::num::<impl i32>::checked_rem_euclid",   Total, || { let _ = 5i32.checked_rem_euclid(black_box(0)); }),
    ("core::num::<impl i32>::checked_pow",          Total, || { let _ = i32::MAX.checked_pow(black_box(2)); }),
    ("core::num::<impl i32>::checked_shl",          Total, || { let _ = 1i32.checked_shl(black_box(100)); }),
    ("core::num::<impl u32>::checked_next_multiple_of", Total, || { let _ = 5u32.checked_next_multiple_of(black_box(0)); }),

    // ---- `unbounded_*` family (complete; uniformly total) ----------------
    // The shift saturates to 0 past the bit width — no over-shift panic.
    ("core::num::<impl u32>::unbounded_shl", Total, || { let _ = 1u32.unbounded_shl(black_box(100)); }),
    ("core::num::<impl u32>::unbounded_shr", Total, || { let _ = 256u32.unbounded_shr(black_box(100)); }),

    // ---- `from_*` / `to_*` byte conversions ------------------------------
    // The `_bytes` conversions are total; `from_str_radix` is the ONE `from_`
    // that panics (radix outside 2..=36), and must be caught by the deny
    // matcher before the `contains("::from_")` trust glob sees it.
    ("core::num::<impl u32>::from_le_bytes",  Total,  || { let _ = u32::from_le_bytes(black_box([1, 2, 3, 4])); }),
    ("core::num::<impl u32>::to_le_bytes",    Total,  || { let _ = 5u32.to_le_bytes(); }),
    ("core::num::<impl i32>::from_str_radix", Panics, || { let _ = i32::from_str_radix("5", black_box(37)); }),

    // ---- `strict_*` family (representative; uniformly panicking) ----------
    // The whole family panics on overflow ALWAYS (not just under
    // overflow-checks) + div/rem on ÷0. Caught by `contains("::strict_")`.
    ("core::num::<impl i32>::strict_add",          Panics, || { let _ = i32::MAX.strict_add(black_box(1)); }),
    ("core::num::<impl i32>::strict_sub",          Panics, || { let _ = i32::MIN.strict_sub(black_box(1)); }),
    ("core::num::<impl i32>::strict_mul",          Panics, || { let _ = i32::MAX.strict_mul(black_box(2)); }),
    ("core::num::<impl i32>::strict_neg",          Panics, || { let _ = black_box(i32::MIN).strict_neg(); }),
    ("core::num::<impl i32>::strict_div",          Panics, || { let _ = 5i32.strict_div(black_box(0)); }),
    ("core::num::<impl i32>::strict_rem",          Panics, || { let _ = 5i32.strict_rem(black_box(0)); }),
    ("core::num::<impl i32>::strict_pow",          Panics, || { let _ = i32::MAX.strict_pow(black_box(2)); }),
    ("core::num::<impl i32>::strict_shl",          Panics, || { let _ = 1i32.strict_shl(black_box(100)); }),
    ("core::num::<impl i32>::strict_add_unsigned", Panics, || { let _ = i32::MAX.strict_add_unsigned(black_box(1u32)); }),

    // ---- plain panicking int methods (not family-glob members) -----------
    // The operator form is caught by PB049; the METHOD form must be caught by
    // the deny matcher (else silently accepted — the 2026-06-14 finding class).
    ("core::num::<impl u32>::pow",             Panics, || { let _ = u32::MAX.pow(black_box(2)); }),
    ("core::num::<impl i32>::abs",             Panics, || { let _ = black_box(i32::MIN).abs(); }),
    ("core::num::<impl i32>::div_euclid",      Panics, || { let _ = 5i32.div_euclid(black_box(0)); }),
    ("core::num::<impl i32>::rem_euclid",      Panics, || { let _ = 5i32.rem_euclid(black_box(0)); }),
    ("core::num::<impl u32>::div_ceil",        Panics, || { let _ = 5u32.div_ceil(black_box(0)); }),
    ("core::num::<impl u32>::next_multiple_of", Panics, || { let _ = 5u32.next_multiple_of(black_box(0)); }),
    ("core::num::<impl u32>::ilog2",           Panics, || { let _ = black_box(0u32).ilog2(); }),
    ("core::num::<impl u32>::ilog10",          Panics, || { let _ = black_box(0u32).ilog10(); }),
    ("core::num::<impl i32>::isqrt",           Panics, || { let _ = black_box(-1i32).isqrt(); }),

    // ---- plain total int methods (confirmed on the allow-list) -----------
    // The safe siblings the deny matcher must let through AND the allow-list
    // must keep trusting (a broad-glob eviction would false-reject these).
    ("core::num::<impl u32>::midpoint",     Total, || { let _ = 4u32.midpoint(black_box(6)); }),
    ("core::num::<impl u32>::abs_diff",     Total, || { let _ = 4u32.abs_diff(black_box(6)); }),
    ("core::num::<impl i32>::unsigned_abs", Total, || { let _ = black_box(i32::MIN).unsigned_abs(); }),
    ("core::num::<impl u32>::isqrt",        Total, || { let _ = black_box(u32::MAX).isqrt(); }),
    ("core::num::<impl u32>::count_ones",   Total, || { let _ = black_box(0xF0F0u32).count_ones(); }),
];

/// Every member of each trust-granting integer family glob is classified
/// correctly against a runtime-anchored ground truth: no panicking member is
/// trusted-total (soundness), no total member is denied (no false reject), and
/// every panicking member is positively caught (routed to PB043).
#[test]
fn int_family_allowlist_is_exhaustively_sound() {
    for &(path, g, probe) in TABLE {
        let panicked = panics(probe);
        match g {
            Panics => {
                assert!(
                    panicked,
                    "GROUND TRUTH broken: {path} is labelled Panics but did not \
                     panic on its witness input — the label (or the stdlib) drifted",
                );
                assert!(
                    is_panicking_int_method(path),
                    "DENY GAP: {path} panics but is_panicking_int_method misses it \
                     — it would fall through to the 'assume walked elsewhere' arm \
                     and be silently accepted",
                );
                assert!(
                    !is_trusted_total_library_call(path),
                    "SOUNDNESS (cardinal sin): panicking {path} is trusted-total — \
                     a false discharge; a broad allow-list glob is swallowing it",
                );
            }
            Total => {
                assert!(
                    !panicked,
                    "GROUND TRUTH broken: {path} is labelled Total but panicked on \
                     its witness input — the label (or the stdlib) drifted",
                );
                assert!(
                    !is_panicking_int_method(path),
                    "FALSE REJECT: total {path} is flagged panicking by the deny \
                     matcher — provably safe code would be rejected",
                );
                assert!(
                    is_trusted_total_library_call(path),
                    "FALSE REJECT: total {path} is no longer trusted-total — a glob \
                     eviction over-reached and now rejects provably safe code",
                );
            }
        }
    }
}

/// Sanity: every table entry is filed under an integer-method path (the
/// `num::<impl` rendering the classifier keys on) and the table is non-trivial.
/// Guards against a typo'd path that would make the assertions above vacuous
/// (a mis-rendered path is classified as "not an int method" and could pass the
/// Total arm for the wrong reason).
#[test]
fn table_paths_are_well_formed_int_methods() {
    assert!(TABLE.len() >= 60, "exhaustiveness table shrank unexpectedly: {}", TABLE.len());
    for &(path, _, _) in TABLE {
        assert!(
            path.contains("num::<impl "),
            "table entry is not an int-method rendering (classifier keys on \
             `num::<impl`): {path}",
        );
    }
}
