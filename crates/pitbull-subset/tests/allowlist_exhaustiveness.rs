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

use pitbull_subset::visitor::{
    is_panicking_char_method, is_panicking_index_or_slice_call, is_panicking_int_method,
    is_panicking_library_call, is_trusted_total_library_call,
};
use std::cmp::Ordering;
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

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

// ===================================================================
// The NON-INTEGER surfaces (audit 2026-07-15)
// ===================================================================
//
// The integer table above was the retrospective half of this gate: it anchors
// the families where audits had already found bugs. The slice / str / char /
// Option / Result / cmp surfaces carried NO runtime-anchored ground truth at
// all — their labels rested entirely on the author's reading of the stdlib
// docs, which is the exact epistemic position that planted the `clamp`, `sort`,
// and `wrapping_div` false discharges. This half closes that.
//
// The same invariant applies, against the matcher that owns each surface:
//   Panics ⟹ some `is_panicking_*` matcher catches it AND it is NOT trusted.
//   Total  ⟹ it IS trusted (no false reject of provably safe code).
//
// A note on `sort`'s witness, because it is subtle and load-bearing. Rust 1.81+
// `sort`/`sort_unstable` panic on a non-total `Ord` — but only OPPORTUNISTICALLY:
// the detection fires when the algorithm observes an inconsistency, not on every
// bad comparator. An "always return Less" impl (the obvious adversarial choice)
// makes the input look ALREADY SORTED, so the sort never compares enough to
// notice and does NOT panic — verified empirically at n = 8…5000. A STATEFUL
// comparator whose answers vary across calls for the same pair does panic,
// deterministically, from n ≈ 50 up. The naive witness would have "proven" these
// methods total and argued for un-evicting them: a mislabel that reads as
// evidence. Hence `Chaos` below, at n = 200.

/// A comparator that violates totality by ANSWERING DIFFERENTLY across calls
/// (a deterministic xorshift over a call counter). This is what actually trips
/// Rust's `sort` order-violation detection; see the note above for why the
/// obvious "always Less" impl does not.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
struct Chaos(u32);
static CHAOS_TICK: AtomicUsize = AtomicUsize::new(0);
impl PartialOrd for Chaos {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Chaos {
    fn cmp(&self, _other: &Self) -> Ordering {
        let t = CHAOS_TICK.fetch_add(1, AtomicOrdering::Relaxed) as u64;
        let mut x = t ^ 0x9E37_79B9_7F4A_7C15;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        match x % 3 {
            0 => Ordering::Less,
            1 => Ordering::Equal,
            _ => Ordering::Greater,
        }
    }
}

/// Which deny matcher owns a given path's surface. `is_trusted_total_library_call`
/// consults ALL of them as its deny guard, so a `Panics` entry must be caught by
/// the one that owns it — asserting the specific matcher (rather than just "not
/// trusted") is what pins the routing to a precise PB043 instead of a generic gap.
fn any_deny_matcher(path: &str) -> bool {
    is_panicking_library_call(path)
        || is_panicking_int_method(path)
        || is_panicking_index_or_slice_call(path)
        || is_panicking_char_method(path)
}

/// The non-integer trusted/denied surfaces, each anchored to a runtime probe.
/// Paths are the real `item.name()` renderings (pinned by the classification
/// unit tests in `visitor.rs`).
#[rustfmt::skip]
const NON_INT_TABLE: &[(&str, G, fn())] = &[
    // ---- slice: PANICKING (denied) --------------------------------------
    ("core::slice::<impl [T]>::split_at",        Panics, || { let v = [1u8, 2, 3]; let _ = black_box(v.split_at(black_box(4))); }),
    ("core::slice::<impl [T]>::split_at_mut",    Panics, || { let mut v = [1u8, 2, 3]; let _ = black_box(v.split_at_mut(black_box(9))); }),
    ("core::slice::<impl [T]>::chunks",          Panics, || { let v = [1u8, 2, 3]; let _ = black_box(v.chunks(black_box(0)).count()); }),
    ("core::slice::<impl [T]>::chunks_exact",    Panics, || { let v = [1u8, 2, 3]; let _ = black_box(v.chunks_exact(black_box(0)).count()); }),
    ("core::slice::<impl [T]>::rchunks",         Panics, || { let v = [1u8, 2, 3]; let _ = black_box(v.rchunks(black_box(0)).count()); }),
    ("core::slice::<impl [T]>::rchunks_exact",   Panics, || { let v = [1u8, 2, 3]; let _ = black_box(v.rchunks_exact(black_box(0)).count()); }),
    ("core::slice::<impl [T]>::windows",         Panics, || { let v = [1u8, 2, 3]; let _ = black_box(v.windows(black_box(0)).count()); }),
    ("core::slice::<impl [T]>::swap",            Panics, || { let mut v = [1u8, 2, 3]; v.swap(black_box(0), black_box(9)); }),
    ("core::slice::<impl [T]>::swap_with_slice", Panics, || { let mut a = [1u8, 2, 3]; let mut b = [4u8, 5]; a.swap_with_slice(black_box(&mut b)); }),
    ("core::slice::<impl [T]>::rotate_left",     Panics, || { let mut v = [1u8, 2, 3]; v.rotate_left(black_box(4)); }),
    ("core::slice::<impl [T]>::rotate_right",    Panics, || { let mut v = [1u8, 2, 3]; v.rotate_right(black_box(9)); }),
    ("core::slice::<impl [T]>::copy_from_slice", Panics, || { let mut a = [0u8; 3]; let b = [1u8; 4]; a.copy_from_slice(black_box(&b)); }),
    ("core::slice::<impl [T]>::clone_from_slice", Panics, || { let mut a = [1u8, 2, 3]; let b = [4u8, 5]; a.clone_from_slice(black_box(&b)); }),
    ("core::slice::<impl [T]>::copy_within",     Panics, || { let mut a = [1u8, 2, 3]; a.copy_within(black_box(1..9), black_box(0)); }),
    ("core::slice::<impl [T]>::select_nth_unstable", Panics, || { let mut v = [3u8, 1, 2]; let _ = v.select_nth_unstable(black_box(5)); }),
    ("core::slice::<impl [T]>::as_chunks",       Panics, || { let v = [1u8, 2, 3, 4]; let _ = black_box(v.as_chunks::<0>()); }),
    ("core::slice::<impl [T]>::as_rchunks",      Panics, || { let v = [1u8, 2, 3, 4]; let _ = black_box(v.as_rchunks::<0>()); }),
    // The 2026-07-09 evictions. `Chaos` at n=200 — see the note above.
    ("core::slice::<impl [T]>::sort",            Panics, || { let mut v: Vec<Chaos> = (0..200).map(Chaos).collect(); v.sort(); black_box(&v); }),
    ("core::slice::<impl [T]>::sort_unstable",   Panics, || { let mut v: Vec<Chaos> = (0..200).map(Chaos).collect(); v.sort_unstable(); black_box(&v); }),

    // ---- slice: TOTAL (trusted) ------------------------------------------
    // Each witness is the ADVERSARIAL input for its panicking sibling: the
    // `_checked` / Option-returning forms must absorb it, not panic.
    ("core::slice::<impl [T]>::len",              Total, || { let v = [1u8, 2, 3]; assert_eq!(black_box(v.len()), 3); }),
    ("core::slice::<impl [T]>::is_empty",         Total, || { let v: [u8; 0] = []; let _ = black_box(black_box(v).is_empty()); }),
    ("core::slice::<impl [T]>::first",            Total, || { let v: [u8; 0] = []; assert!(black_box(v.first()).is_none()); }),
    ("core::slice::<impl [T]>::last",             Total, || { let v: [u8; 0] = []; assert!(black_box(v.last()).is_none()); }),
    ("core::slice::<impl [T]>::first_chunk",      Total, || { let v = [1u8, 2, 3]; assert!(black_box(v.first_chunk::<8>()).is_none()); }),
    ("core::slice::<impl [T]>::last_chunk",       Total, || { let v = [1u8, 2, 3]; assert!(black_box(v.last_chunk::<9>()).is_none()); }),
    ("core::slice::<impl [T]>::split_first",      Total, || { let v: [u8; 0] = []; assert!(black_box(v.split_first()).is_none()); }),
    ("core::slice::<impl [T]>::split_last",       Total, || { let v: [u8; 0] = []; assert!(black_box(v.split_last()).is_none()); }),
    ("core::slice::<impl [T]>::split_first_chunk", Total, || { let v = [1u8, 2, 3]; assert!(black_box(v.split_first_chunk::<9>()).is_none()); }),
    ("core::slice::<impl [T]>::split_last_chunk", Total, || { let v = [1u8, 2, 3]; assert!(black_box(v.split_last_chunk::<9>()).is_none()); }),
    ("core::slice::<impl [T]>::get",              Total, || { let v = [1u8, 2, 3]; assert!(black_box(v.get(black_box(17))).is_none()); }),
    ("core::slice::<impl [T]>::get_mut",          Total, || { let mut v = [1u8, 2, 3]; assert!(black_box(v.get_mut(black_box(9))).is_none()); }),
    ("core::slice::<impl [T]>::split_at_checked", Total, || { let v = [1u8, 2, 3]; assert!(black_box(v.split_at_checked(black_box(9))).is_none()); }),
    ("core::slice::<impl [T]>::split_at_mut_checked", Total, || { let mut v = [1u8, 2, 3]; assert!(black_box(v.split_at_mut_checked(black_box(9))).is_none()); }),
    // `binary_search` with the SAME non-total `Ord` that panics `sort`: it
    // returns a wrong answer but never panics — the distinction the 2026-07-09
    // audit drew when it kept this trusted while evicting `sort`.
    ("core::slice::<impl [T]>::binary_search",    Total, || { let v: Vec<Chaos> = (0..64).map(Chaos).collect(); let _ = black_box(v.binary_search(&Chaos(7))); }),
    ("core::slice::<impl [T]>::fill",             Total, || { let mut v = [0u8; 4]; v.fill(black_box(7)); black_box(&v); }),
    ("core::slice::<impl [T]>::reverse",          Total, || { let mut v = [1u8, 2, 3]; v.reverse(); black_box(&v); }),
    ("core::slice::<impl [T]>::contains",         Total, || { let v = [1u8, 2, 3]; assert!(!black_box(v.contains(&9))); }),
    ("core::slice::<impl [T]>::starts_with",      Total, || { let v = [1u8, 2, 3]; assert!(!black_box(v.starts_with(&[9]))); }),
    ("core::slice::<impl [T]>::ends_with",        Total, || { let v = [1u8, 2, 3]; assert!(!black_box(v.ends_with(&[9]))); }),

    // ---- str -------------------------------------------------------------
    // Non-char-boundary is the adversarial witness: the range-index form
    // panics, `get` absorbs it.
    ("core::str::<impl str>::split_at",           Panics, || { let s = "é"; let _ = black_box(s.split_at(black_box(1))); }),
    ("core::str::<impl str>::get",                Total,  || { let s = "é"; assert!(black_box(s.get(black_box(0..1))).is_none()); }),
    ("core::str::<impl str>::split_at_checked",   Total,  || { let s = "é"; assert!(black_box(s.split_at_checked(black_box(1))).is_none()); }),
    ("core::str::<impl str>::len",                Total,  || { assert_eq!(black_box("abc").len(), 3); }),
    ("core::str::<impl str>::is_empty",           Total,  || { assert!(!black_box("abc").is_empty()); }),
    ("core::str::<impl str>::as_bytes",           Total,  || { let _ = black_box(black_box("abc").as_bytes()); }),
    ("core::str::<impl str>::contains",           Total,  || { assert!(!black_box("abc").contains('x')); }),
    ("core::str::<impl str>::starts_with",        Total,  || { assert!(!black_box("abc").starts_with('x')); }),
    ("core::str::<impl str>::ends_with",          Total,  || { assert!(!black_box("abc").ends_with('x')); }),
    // Range indexing lowers to the Index trait, not a projection — PB054 never
    // sees it, so the deny matcher must.
    ("std::ops::Index::index",                    Panics, || { let v = [1u8, 2, 3]; let _ = black_box(&v[black_box(0..9)]); }),
    ("std::ops::IndexMut::index_mut",             Panics, || { let mut v = [1u8, 2, 3]; let s = &mut v[black_box(0..9)]; black_box(s); }),

    // ---- char ------------------------------------------------------------
    ("std::char::from_digit",                              Panics, || { let _ = black_box(char::from_digit(black_box(5), black_box(37))); }),
    ("std::char::methods::<impl char>::to_digit",          Panics, || { let _ = black_box(black_box('5').to_digit(black_box(37))); }),
    ("std::char::methods::<impl char>::is_digit",          Panics, || { let _ = black_box(black_box('5').is_digit(black_box(37))); }),
    ("std::char::methods::<impl char>::encode_utf8",       Panics, || { let mut b = [0u8; 1]; let _ = black_box('é'.encode_utf8(black_box(&mut b))); }),
    ("std::char::methods::<impl char>::encode_utf16",      Panics, || { let mut b: [u16; 0] = []; let _ = black_box('x'.encode_utf16(black_box(&mut b))); }),
    ("std::char::methods::<impl char>::is_alphabetic",     Total,  || { assert!(black_box('a').is_alphabetic()); }),
    ("std::char::methods::<impl char>::to_ascii_uppercase", Total, || { let _ = black_box(black_box('a').to_ascii_uppercase()); }),
    ("std::char::methods::<impl char>::len_utf8",          Total,  || { assert_eq!(black_box('é').len_utf8(), 2); }),
    ("std::char::methods::<impl char>::len_utf16",         Total,  || { assert_eq!(black_box('é').len_utf16(), 1); }),
    ("std::char::methods::<impl char>::eq_ignore_ascii_case", Total, || { assert!(black_box('a').eq_ignore_ascii_case(&'A')); }),
    ("core::char::from_u32",                               Total,  || { assert!(black_box(char::from_u32(black_box(0xD800))).is_none()); }),

    // ---- Option / Result -------------------------------------------------
    // The four panicking members, each on its adversarial variant.
    ("core::option::Option::<u32>::unwrap",     Panics, || { let x: Option<u32> = black_box(None); let _ = x.unwrap(); }),
    ("core::option::Option::<u32>::expect",     Panics, || { let x: Option<u32> = black_box(None); let _ = x.expect("boom"); }),
    ("core::result::Result::<u32, u8>::unwrap", Panics, || { let r: Result<u32, u8> = black_box(Err(1)); let _ = r.unwrap(); }),
    ("core::result::Result::<u32, u8>::unwrap_err", Panics, || { let r: Result<u32, u8> = black_box(Ok(1)); let _ = r.unwrap_err(); }),
    ("core::result::Result::<u32, u8>::expect", Panics, || { let r: Result<u32, u8> = black_box(Err(1)); let _ = r.expect("boom"); }),
    // The total combinators, each on the variant that would trip `unwrap`.
    // NB the boolean probes just CALL the method under `black_box` and discard
    // the result — the observable under test is "does it unwind", not the value.
    // Wrapping them in `assert!(!x.is_some())` invites clippy to rewrite the
    // call into its sibling (`is_none`), which would silently probe a method
    // other than the one the path names.
    ("core::option::Option::<u32>::is_some",    Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.is_some()); }),
    ("core::option::Option::<u32>::is_none",    Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.is_none()); }),
    ("core::option::Option::<u32>::unwrap_or",  Total, || { let x: Option<u32> = black_box(None); assert_eq!(x.unwrap_or(5), 5); }),
    ("core::option::Option::<u32>::unwrap_or_default", Total, || { let x: Option<u32> = black_box(None); assert_eq!(x.unwrap_or_default(), 0); }),
    ("core::option::Option::<u32>::map",        Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.map(|v| v + 1)); }),
    ("core::option::Option::<u32>::and_then",   Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.and_then(|v| v.checked_add(1))); }),
    ("core::option::Option::<u32>::filter",     Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.filter(|v| *v > 0)); }),
    ("core::option::Option::<u32>::or",         Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.or(Some(1))); }),
    ("core::option::Option::<u32>::xor",        Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.xor(Some(1))); }),
    ("core::option::Option::<u32>::zip",        Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.zip(Some(1u32))); }),
    ("core::option::Option::<u32>::take",       Total, || { let mut x: Option<u32> = black_box(None); let _ = black_box(x.take()); }),
    ("core::option::Option::<u32>::replace",    Total, || { let mut x: Option<u32> = black_box(None); let _ = black_box(x.replace(3)); }),
    ("core::option::Option::<u32>::get_or_insert", Total, || { let mut x: Option<u32> = black_box(None); let _ = black_box(*x.get_or_insert(9)); }),
    ("core::option::Option::<u32>::ok_or",      Total, || { let x: Option<u32> = black_box(None); let _ = black_box(x.ok_or(1u8)); }),
    ("core::option::Option::<u32>::flatten",    Total, || { let x: Option<Option<u32>> = black_box(Some(None)); let _ = black_box(x.flatten()); }),
    ("core::option::Option::<u32>::transpose",  Total, || { let x: Option<Result<u32, u8>> = black_box(Some(Ok(1))); let _ = black_box(x.transpose()); }),
    ("core::result::Result::<u32, u8>::is_ok",  Total, || { let r: Result<u32, u8> = black_box(Err(1)); let _ = black_box(r.is_ok()); }),
    ("core::result::Result::<u32, u8>::ok",     Total, || { let r: Result<u32, u8> = black_box(Err(1)); assert!(black_box(r.ok()).is_none()); }),
    ("core::result::Result::<u32, u8>::err",    Total, || { let r: Result<u32, u8> = black_box(Err(1)); assert!(black_box(r.err()).is_some()); }),
    ("core::result::Result::<u32, u8>::map_err", Total, || { let r: Result<u32, u8> = black_box(Err(1)); let _ = black_box(r.map_err(|e| e + 1)); }),
    ("core::result::Result::<u32, u8>::unwrap_or", Total, || { let r: Result<u32, u8> = black_box(Err(1)); assert_eq!(r.unwrap_or(7), 7); }),

    // ---- cmp -------------------------------------------------------------
    // `clamp` panics on `min > max` — the 2026-07-09 eviction. Its total
    // siblings take the SAME non-total `Ord` without panicking.
    ("std::cmp::Ord::clamp", Panics, || { let _ = black_box(black_box(5i32).clamp(black_box(10), black_box(0))); }),
    ("std::cmp::Ord::min",   Total,  || { let _ = black_box(std::cmp::min(Chaos(1), Chaos(2))); }),
    ("std::cmp::Ord::max",   Total,  || { let _ = black_box(std::cmp::max(Chaos(1), Chaos(2))); }),
    ("std::cmp::Ord::cmp",   Total,  || { let _ = black_box(Chaos(1).cmp(&Chaos(2))); }),
];

/// Every entry of the non-integer trusted/denied surface is classified
/// correctly against a runtime-anchored ground truth: no panicking method is
/// trusted-total (the cardinal sin), no total method is denied (no false
/// reject), and every panicking method is positively caught by a deny matcher
/// (so it routes to PB043 rather than falling through to "assume walked
/// elsewhere").
#[test]
fn non_int_allowlist_is_sound_against_runtime_truth() {
    for &(path, g, probe) in NON_INT_TABLE {
        let panicked = panics(probe);
        match g {
            Panics => {
                assert!(
                    panicked,
                    "GROUND TRUTH broken: {path} is labelled Panics but did not panic \
                     on its witness — the label, the witness, or the stdlib drifted. \
                     (For the sort family this is expected to be delicate: order-violation \
                     detection is opportunistic, so the witness must be a STATEFUL \
                     comparator, not an always-Less one.)",
                );
                assert!(
                    any_deny_matcher(path),
                    "DENY GAP: {path} panics but no is_panicking_* matcher catches it — \
                     it would fall through to the 'assume walked elsewhere' arm and be \
                     silently accepted",
                );
                assert!(
                    !is_trusted_total_library_call(path),
                    "SOUNDNESS (cardinal sin): panicking {path} is trusted-total — a \
                     false discharge",
                );
            }
            Total => {
                assert!(
                    !panicked,
                    "GROUND TRUTH broken: {path} is labelled Total but panicked on its \
                     witness — the label (or the stdlib) drifted",
                );
                assert!(
                    !any_deny_matcher(path),
                    "FALSE REJECT: total {path} is flagged panicking by a deny matcher",
                );
                assert!(
                    is_trusted_total_library_call(path),
                    "FALSE REJECT: total {path} is not trusted-total — provably safe code \
                     would be rejected",
                );
            }
        }
    }
}

/// The witness for the `sort` family must be a genuine order violation that the
/// stdlib DETECTS — the property the `Panics` label above depends on.
///
/// Pinned separately because it is the one label in this file that a plausible
/// witness gets WRONG: an "always return Less" comparator makes the input look
/// pre-sorted, so no inconsistency is ever observed and `sort` does not panic
/// (verified at n = 8…5000). A reviewer reaching for the obvious witness would
/// conclude these methods are total and argue to un-evict them — a mislabel
/// that reads as evidence. This test states the trap so the next person hits it
/// as a failing assertion rather than a false discharge.
#[test]
fn sort_order_violation_witness_is_genuine() {
    assert!(
        panics(|| {
            let mut v: Vec<Chaos> = (0..200).map(Chaos).collect();
            v.sort();
            black_box(&v);
        }),
        "the stateful comparator must trip Rust's order-violation detection — if this \
         stops panicking, the sort entries above are no longer runtime-anchored and \
         `sort`/`sort_unstable` must be re-verified by hand before trusting this file",
    );
    // The naive witness does NOT panic. Pinned so the trap is documented as an
    // executable fact, not a comment someone edits away.
    #[derive(PartialEq, Eq, Clone, Copy)]
    struct AlwaysLess(u32);
    impl PartialOrd for AlwaysLess {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for AlwaysLess {
        fn cmp(&self, _other: &Self) -> Ordering {
            Ordering::Less
        }
    }
    assert!(
        !panics(|| {
            let mut v: Vec<AlwaysLess> = (0..200).map(AlwaysLess).collect();
            v.sort();
            black_box(&v);
        }),
        "an always-Less comparator is expected NOT to panic (the input looks already \
         sorted). If this DOES panic the detection got stricter — good news, but the \
         note explaining the witness choice is now stale and should be updated.",
    );
}

/// Guards the non-integer table against the vacuity a typo'd path would cause:
/// a mis-rendered path matches no classifier arm, so it is neither trusted nor
/// denied — which would silently satisfy a `Panics` row's two negative-ish
/// assertions for entirely the wrong reason. Every path must therefore be
/// recognized by SOME arm.
#[test]
fn non_int_table_paths_are_classified_by_some_arm() {
    assert!(
        NON_INT_TABLE.len() >= 70,
        "non-integer exhaustiveness table shrank unexpectedly: {}",
        NON_INT_TABLE.len(),
    );
    for &(path, g, _) in NON_INT_TABLE {
        let recognized = any_deny_matcher(path) || is_trusted_total_library_call(path);
        assert!(
            recognized,
            "table entry `{path}` is recognized by NO classifier arm — the rendering is \
             probably wrong, which makes its {g:?} row vacuous",
        );
    }
}
