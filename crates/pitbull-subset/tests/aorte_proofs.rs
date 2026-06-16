//! Empirical AoRTE soundness net — the property-test harness the Safety
//! Manual promises ("positive AoRTE proofs ... pass under fuzzed inputs").
//!
//! ## What this is and why it exists
//!
//! Pitbull's whole value is the claim "if I report *verified*, the function
//! exhibits no Absence-of-Runtime-Errors failure mode (panic / overflow /
//! out-of-bounds index / div-by-zero) on ANY input." The deep audit
//! (2026-06-14) found two false discharges of exactly this class (`unwrap`,
//! `x.pow(y)`) that a static audit had to *reason* its way to. An EMPIRICAL
//! net catches that class automatically: take functions Pitbull does (or
//! would) verify, hammer them with many inputs, and assert none ever
//! panics. A panic on a verified function would be a counterexample-by-
//! construction — the gold-standard soundness report (Safety Manual §6).
//!
//! This is the foundation of that net. It runs ENTIRELY on stable Rust with
//! NO external dependency: a small deterministic xorshift PRNG (so any
//! failure is reproducible from the fixed seed, and there is no reliance on
//! wall-clock / entropy). Two kinds of proof:
//!
//! 1. **Unconditional AoRTE proofs** — functions that are AoRTE-safe on
//!    EVERY input (no precondition needed: guarded indexing, wrapping /
//!    saturating arithmetic, modular addressing). Fuzzed over their full
//!    input domain, with a correctness oracle where one exists. Pitbull
//!    verifies these with no precondition, so "verified ⟹ never panics"
//!    must hold for ALL inputs — which is exactly what we fuzz.
//!
//! 2. **Precondition-respecting proofs** — Pitbull's *discharged-under-a-
//!    precondition* shapes (e.g. `at(s, i)` discharged under `i < len`,
//!    `add_one(x)` discharged under `x < 100`). We fuzz ONLY the input
//!    domain the precondition admits and assert no panic — a direct
//!    empirical check that Pitbull's precondition is SUFFICIENT for safety
//!    (i.e. that its SMT discharge is sound, not just internally consistent).
//!
//! ## Differential framing (and the next increment)
//!
//! These functions mirror the `tests/corpus/accept/` shapes Pitbull verifies;
//! this file is the empirical confirmation that those verdicts are
//! panic-free under fuzzing. The full end-to-end differential — run the
//! `pitbull-rustc` wrapper on each function AND fuzz it in the same test,
//! asserting `verified ⟹ fuzz-clean` programmatically — is the next
//! increment (it needs the nightly wrapper subprocess, like the corpus
//! e2e). Until then the link is by construction + this comment.

/// Deterministic xorshift64* PRNG. Reproducible (fixed seed at each call
/// site), dependency-free, and `no_std`-shaped. A failing fuzz case is
/// therefore reproducible by re-running with the same seed and iteration.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        // Avoid the all-zero state (xorshift's fixed point); any nonzero
        // seed is fine.
        Rng(seed | 1)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }
    /// Uniform-ish value in `[0, n)`; returns 0 when `n == 0` (modulo by a
    /// constant-checked nonzero otherwise — itself AoRTE-safe).
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() % n as u64) as usize
        }
    }
    /// A random byte vector of length in `[0, max_len]`.
    fn bytes(&mut self, max_len: usize) -> Vec<u8> {
        let len = self.below(max_len + 1);
        (0..len).map(|_| self.next_u64() as u8).collect()
    }
}

/// Fuzz-iteration budget per proof. Large enough to exercise edge cases
/// (empty slices, boundary indices, MIN/MAX operands) without making the
/// stable suite slow. Deterministic, so this is a fixed amount of work.
const ITERS: usize = 200_000;

// =====================================================================
// 1. Unconditional AoRTE proofs — safe on EVERY input.
// =====================================================================

/// CRC-32 (IEEE 802.3), bitwise (table-free, so no array indexing at all).
/// Pure wrapping bit ops — AoRTE-safe on any input. This is one of the
/// positive AoRTE proofs PSS-1 §15 names.
fn crc32_ieee(data: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    let mut i = 0usize;
    while i < data.len() {
        crc ^= u32::from(data[i]); // i < len ⇒ in-bounds
        let mut bit = 0;
        while bit < 8 {
            // mask is 0x0000_0000 or 0xFFFF_FFFF depending on the low bit.
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
            bit += 1;
        }
        i += 1;
    }
    !crc
}

#[test]
fn crc32_known_answer_and_never_panics() {
    // Known answer: CRC-32/IEEE of the canonical check string is 0xCBF43926.
    assert_eq!(
        crc32_ieee(b"123456789"),
        0xCBF4_3926,
        "CRC-32 must match the canonical check value",
    );
    // Empirical AoRTE: never panics on any byte string, and is deterministic.
    let mut rng = Rng::new(0xC0FF_EE00_1234_5678);
    for _ in 0..ITERS {
        let data = rng.bytes(64);
        let a = crc32_ieee(&data);
        let b = crc32_ieee(&data);
        assert_eq!(a, b, "CRC must be a pure function (got {a:#x} then {b:#x})");
    }
}

/// Guarded binary search over a sorted slice. Returns `Some(idx)` with
/// `arr[idx] == target`, else `None`. AoRTE-safe: `mid < hi <= len` keeps
/// `arr[mid]` in bounds; `lo + (hi-lo)/2` and `mid + 1` cannot overflow for
/// a real slice (`len <= isize::MAX`).
fn binary_search(arr: &[u32], target: u32) -> Option<usize> {
    let mut lo = 0usize;
    let mut hi = arr.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2; // in [lo, hi)
        let v = arr[mid]; // mid < hi <= len ⇒ in-bounds
        if v == target {
            return Some(mid);
        } else if v < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}

#[test]
fn binary_search_matches_linear_and_never_panics() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0001);
    for _ in 0..ITERS / 4 {
        // Build a SORTED array (the binary-search precondition).
        let len = rng.below(33);
        let mut arr: Vec<u32> = (0..len).map(|_| rng.next_u32() % 256).collect();
        arr.sort_unstable();
        let target = rng.next_u32() % 256;

        let found = binary_search(&arr, target);
        // Oracle: the result must agree with a linear scan on the contract.
        match found {
            Some(idx) => assert_eq!(arr[idx], target, "Some(idx) must point at target"),
            None => assert!(
                !arr.contains(&target),
                "None must mean target absent (arr={arr:?}, target={target})",
            ),
        }
    }
}

/// Ring-buffer addressing with a power-of-two capacity: `(head + offset) &
/// mask` where `mask == cap - 1`. Wrapping add + bitwise AND ⇒ the result is
/// always in `[0, cap)`, so the subsequent `buf[idx]` can never be OOB.
fn ring_index(head: usize, offset: usize, mask: usize) -> usize {
    head.wrapping_add(offset) & mask
}

#[test]
fn ring_index_always_in_capacity_and_never_panics() {
    let mut rng = Rng::new(0x21A6_B0FF_0000_0001);
    for _ in 0..ITERS {
        // Power-of-two capacity in {1,2,4,...,2^15}.
        let pow = rng.below(16);
        let cap = 1usize << pow;
        let mask = cap - 1;
        let head = rng.next_u64() as usize;
        let offset = rng.next_u64() as usize;
        let idx = ring_index(head, offset, mask);
        assert!(idx < cap, "ring index {idx} must be < cap {cap}");
    }
}

/// In-place insertion sort with guarded indexing. AoRTE-safe: `a.swap(j-1,
/// j)` runs only while `0 < j <= i < len`, so both indices are in bounds;
/// `j - 1` is guarded by `j > 0`. (PSS-1 §15 names insertion sort.)
fn insertion_sort(a: &mut [u32]) {
    let mut i = 1;
    while i < a.len() {
        let mut j = i;
        while j > 0 && a[j - 1] > a[j] {
            a.swap(j - 1, j);
            j -= 1;
        }
        i += 1;
    }
}

#[test]
fn insertion_sort_correct_and_never_panics() {
    let mut rng = Rng::new(0x1235_0820_0000_0001);
    // Sort is O(n^2); ITERS/8 over arrays up to 32 is still ~25k sorts.
    for _ in 0..ITERS / 8 {
        let len = rng.below(33);
        let orig: Vec<u32> = (0..len).map(|_| rng.next_u32() % 1000).collect();
        let mut mine = orig.clone();
        insertion_sort(&mut mine);
        // Oracle: equal to std's sort of the same input ⇒ sorted AND a
        // permutation (the two properties §15 asks for).
        let mut reference = orig.clone();
        reference.sort_unstable();
        assert_eq!(mine, reference, "insertion_sort must match std sort");
    }
}

/// CRC-16/CCITT-FALSE (poly 0x1021, init 0xFFFF), bitwise — pure wrapping
/// shift/xor, AoRTE-safe on any input. Shift amounts (8, 1) are < 16, so no
/// over-shift; `u8 -> u16` is a widening cast. (PSS-1 §15 names CRC-CCITT.)
fn crc16_ccitt(data: &[u8]) -> u16 {
    let mut crc: u16 = 0xFFFF;
    let mut i = 0usize;
    while i < data.len() {
        crc ^= (data[i] as u16) << 8; // i < len ⇒ in-bounds
        let mut bit = 0;
        while bit < 8 {
            crc = if crc & 0x8000 != 0 { (crc << 1) ^ 0x1021 } else { crc << 1 };
            bit += 1;
        }
        i += 1;
    }
    crc
}

#[test]
fn crc16_ccitt_known_answer_and_never_panics() {
    // Canonical CRC-16/CCITT-FALSE check value for "123456789" is 0x29B1.
    assert_eq!(crc16_ccitt(b"123456789"), 0x29B1, "CRC-16/CCITT-FALSE check value");
    let mut rng = Rng::new(0xCC17_0000_0000_0001);
    for _ in 0..ITERS {
        let data = rng.bytes(64);
        let a = crc16_ccitt(&data);
        assert_eq!(a, crc16_ccitt(&data), "CRC-16 must be a pure function");
    }
}

/// Fixed-point (Q16.16) PID step with saturating integral and wrapping
/// products widened to `i64` (so `i32 * i32` cannot overflow). Saturating /
/// wrapping / shift / clamp are all total — AoRTE-safe on any input.
/// (PSS-1 §15 names a PID controller.)
fn pid_step(setpoint: i32, measured: i32, integral: &mut i32, kp: i32, ki: i32) -> i32 {
    let error = setpoint.wrapping_sub(measured);
    *integral = integral.saturating_add(error);
    let p = (kp as i64).wrapping_mul(error as i64) >> 16;
    let i_term = (ki as i64).wrapping_mul(*integral as i64) >> 16;
    p.wrapping_add(i_term).clamp(i32::MIN as i64, i32::MAX as i64) as i32
}

#[test]
fn pid_step_never_panics() {
    let mut rng = Rng::new(0x91D0_0000_0000_0001);
    // Oracle: with zero gains, the output is 0 regardless of inputs.
    let mut zero_integ = 0i32;
    assert_eq!(
        pid_step(rng.next_u32() as i32, rng.next_u32() as i32, &mut zero_integ, 0, 0),
        0,
        "zero-gain PID output must be 0",
    );
    // Fuzz with arbitrary gains/inputs and a PERSISTENT integral term (so the
    // saturating accumulation is exercised across iterations).
    let mut integral = 0i32;
    for _ in 0..ITERS {
        let out = pid_step(
            rng.next_u32() as i32,
            rng.next_u32() as i32,
            &mut integral,
            rng.next_u32() as i32,
            rng.next_u32() as i32,
        );
        // Must never panic; the result is always a valid i32 by construction.
        let _ = out;
    }
}

/// Branchless median-of-three (a voting reducer). `min`/`max` are total — no
/// indexing, no arithmetic — so this is AoRTE-safe AND Pitbull emits ZERO
/// obligations on it (see the e2e differential, where it is a 2nd
/// `verified ⟹ fuzz-clean` proof). (PSS-1 §15 names a voting reducer.)
fn median3(a: u32, b: u32, c: u32) -> u32 {
    a.min(b).max(a.max(b).min(c))
}

#[test]
fn median3_correct_and_never_panics() {
    let mut rng = Rng::new(0x3ED1_0000_0000_0001);
    for _ in 0..ITERS {
        let (a, b, c) = (rng.next_u32() % 1000, rng.next_u32() % 1000, rng.next_u32() % 1000);
        let m = median3(a, b, c);
        let mut sorted = [a, b, c];
        sorted.sort_unstable();
        assert_eq!(m, sorted[1], "median3({a},{b},{c}) must be the middle value");
    }
}

// =====================================================================
// 2. Precondition-respecting proofs — Pitbull's discharged-under-a-
//    -precondition shapes. We fuzz ONLY the admitted input domain and
//    assert no panic: an empirical check that the precondition Pitbull
//    discharges against is actually SUFFICIENT for AoRTE-safety.
// =====================================================================

/// The `tests/corpus/accept/PB054_bounded_index.rs` shape: Pitbull
/// discharges `s[i]` under the precondition `i < len`.
fn at(s: &[u8], i: usize) -> u8 {
    s[i]
}

#[test]
fn pb054_at_is_safe_under_its_precondition() {
    let mut rng = Rng::new(0x0B0A_1DEC_0054_0001);
    let mut nonempty_seen = 0u64;
    for _ in 0..ITERS {
        let s = rng.bytes(64);
        if s.is_empty() {
            continue; // the precondition `i < len` is unsatisfiable here
        }
        nonempty_seen += 1;
        // PRECONDITION: i < len. Fuzz only the admitted domain.
        let i = rng.below(s.len());
        // Must never panic, and must return the indexed byte.
        assert_eq!(at(&s, i), s[i]);
    }
    assert!(nonempty_seen > 1000, "fuzz should exercise the in-bounds domain");
}

/// The headline `add_one` demo: Pitbull discharges the `x + 1` overflow
/// (PB049) under the precondition `x < 100`. Empirically confirm the
/// precondition is sufficient (no overflow in debug semantics).
fn add_one(x: u32) -> u32 {
    x + 1
}

#[test]
fn pb049_add_one_no_overflow_under_precondition() {
    let mut rng = Rng::new(0x0ADD_0001_0049_0001);
    for _ in 0..ITERS {
        // PRECONDITION: x < 100. (Without it, x = u32::MAX overflows — which
        // is exactly why Pitbull REQUIRES the precondition.)
        let x = rng.next_u32() % 100;
        let y = add_one(x);
        // No overflow ⇒ y == x + 1 exactly, and y <= 100.
        assert_eq!(y, x + 1);
        assert!(y <= 100);
    }
}

/// Fixed-point gain scale (Q-format), audio-DSP style: `(sample * gain) /
/// divisor`. Pitbull discharges BOTH AoRTE obligations end-to-end by 2-of-2
/// (z3 + cvc5) agreement (verified 2026-06-16, Track-B frontier #1): the
/// `sample * gain` overflow (PB049) under `sample < 65536 && gain < 65536`
/// (so the product is `< 2^32`), and the `/ divisor` division-by-zero (PB049)
/// under `divisor > 0`. This is the empirical half: fuzz ONLY the admitted
/// domain and assert the precondition set is SUFFICIENT (no overflow / no
/// div-by-zero), with a wide-arithmetic oracle that would catch a silent
/// overflow.
fn scale_q(sample: u32, gain: u32, divisor: u32) -> u32 {
    (sample * gain) / divisor
}

#[test]
fn pb049_scale_q_safe_under_precondition() {
    let mut rng = Rng::new(0x5CA1_E000_0049_0001);
    for _ in 0..ITERS {
        // PRECONDITION: sample < 65536, gain < 65536 (⇒ product < 2^32, no mul
        // overflow), divisor > 0 (no division by zero). Fuzz only this domain.
        let sample = rng.next_u32() % 65536;
        let gain = rng.next_u32() % 65536;
        let divisor = 1 + (rng.next_u32() % 4096); // divisor >= 1
        let out = scale_q(sample, gain, divisor);
        // Wide-arithmetic oracle: the true product fits u32 (so the u32 mul did
        // NOT overflow) and the division is exact. A silent overflow in
        // `scale_q` would make `out` disagree with this u64 computation.
        let oracle = ((u64::from(sample) * u64::from(gain)) / u64::from(divisor)) as u32;
        assert_eq!(out, oracle, "scale_q({sample},{gain},{divisor}) must match the wide oracle");
    }
}

/// Adversarial control: confirm the harness WOULD catch a real overflow if
/// the precondition were dropped. `add_one(u32::MAX)` overflows; under
/// `overflow-checks` (debug/test) that is a panic. We assert the panic
/// happens — proving the fuzz net has teeth (a function Pitbull verified
/// WITHOUT a sufficient precondition would be caught here).
#[test]
fn control_unconstrained_add_one_does_overflow() {
    let panicked = std::panic::catch_unwind(|| add_one(u32::MAX)).is_err();
    assert!(
        panicked,
        "add_one(u32::MAX) must overflow-panic in test (overflow-checks on) — \
         this proves the AoRTE net would catch a discharge with an INSUFFICIENT \
         precondition; if this ever stops panicking, the net has lost its teeth",
    );
}

/// Ground-truth control for the second deep-audit finding (2026-06-14 #2).
/// Each of these `core` methods was being silently reported `verified` (exit
/// 0) before `is_panicking_int_method` was extended to catch it. This test
/// pins the GROUND TRUTH the matcher relies on — that every one genuinely
/// panics on the witnessed input — so the enumeration is anchored to runtime
/// reality, not to a list that could quietly drift. (If any entry ever stops
/// panicking, the corresponding matcher arm is dead and we want this to flag
/// it.) The SAFE siblings (unsigned `isqrt`, `midpoint`) must NOT panic — the
/// signedness/precision boundary the matcher must respect to avoid a false
/// REJECT of total code.
#[test]
fn control_panicking_int_methods_do_panic_safe_ones_do_not() {
    let p = |f: fn()| std::panic::catch_unwind(f).is_err();
    // Must panic — these are the false-discharge class the matcher now flags.
    assert!(p(|| { let _ = (-1i32).isqrt(); }), "signed isqrt(-1) must panic");
    assert!(p(|| { let _ = 5u32.next_multiple_of(0); }), "next_multiple_of(_,0) must panic");
    assert!(p(|| { let _ = 5u32.div_ceil(0); }), "div_ceil(_,0) must panic");
    assert!(p(|| { let _ = u32::MAX.strict_add(1); }), "strict_add overflow must panic");
    assert!(p(|| { let _ = u32::MAX.strict_mul(2); }), "strict_mul overflow must panic");
    assert!(p(|| { let _ = i32::MIN.strict_neg(); }), "strict_neg(MIN) must panic");
    assert!(p(|| { let _ = 1u32.strict_shl(32); }), "strict_shl over-shift must panic");
    // `black_box` the step so the panic is a RUNTIME event (which is what we
    // assert) rather than a const-evaluable one clippy rejects at compile time
    // (`clippy::iterator_step_by_zero` is deny-by-default — it AGREES this
    // panics; here we want to observe the panic, not be stopped by the lint).
    assert!(
        p(|| {
            let _ = (0u32..10).step_by(std::hint::black_box(0)).count();
        }),
        "step_by(0) must panic",
    );
    // `from_str_radix` and the char radix methods panic on radix ∉ 2..=36.
    // `black_box` the radix inline (keeping each closure non-capturing, so it
    // still coerces to `fn()`) so it is a runtime value — the matcher's whole
    // point is a radix the caller has not bounded.
    assert!(p(|| { let _ = i32::from_str_radix("5", std::hint::black_box(37)); }), "from_str_radix(_,37) must panic");
    assert!(p(|| { let _ = 'a'.to_digit(std::hint::black_box(37)); }), "to_digit(_,37) must panic");
    assert!(p(|| { let _ = 'a'.is_digit(std::hint::black_box(37)); }), "is_digit(_,37) must panic");
    assert!(p(|| { let _ = std::char::from_digit(5, std::hint::black_box(37)); }), "from_digit(_,37) must panic");
    // Completeness-net additions: encode into an undersized buffer, and a
    // zero const chunk size (`black_box`ed so it is a runtime panic, not a
    // const-eval one).
    assert!(p(|| { let mut b = [0u8; 1]; let _ = '\u{20AC}'.encode_utf8(&mut b); }), "encode_utf8 small-buf must panic");
    assert!(p(|| { let mut b = [0u16; 0]; let _ = 'x'.encode_utf16(&mut b); }), "encode_utf16 small-buf must panic");
    assert!(p(|| { let s: &[u8] = &[1, 2, 3, 4]; let _ = s.as_chunks::<0>(); }), "as_chunks::<0> must panic");
    assert!(p(|| { let s: &[u8] = &[1, 2, 3, 4]; let _ = s.as_rchunks::<0>(); }), "as_rchunks::<0> must panic");
    // Must NOT panic — total siblings the matcher must let through (no false
    // reject). A regression that flags these would degrade Pitbull to
    // rejecting provably-safe code.
    assert!(!p(|| { let _ = 5u32.isqrt(); }), "UNSIGNED isqrt is total");
    assert!(!p(|| { let _ = 4u32.midpoint(6); }), "midpoint is total");
    assert!(!p(|| { let _ = 4u32.abs_diff(6); }), "abs_diff is total");
    assert!(!p(|| { let _ = 'a'.is_alphabetic(); }), "char::is_alphabetic is total");
    assert!(!p(|| { let _ = 'a'.len_utf8(); }), "char::len_utf8 is total");
    // The same calls with a sufficient buffer / nonzero chunk size do NOT
    // panic — Pitbull's conservative fail-closed on the family is a false
    // REJECT here (acceptable), never a runtime panic.
    assert!(!p(|| { let mut b = [0u8; 4]; let _ = '\u{20AC}'.encode_utf8(&mut b); }), "encode_utf8 big-buf is total");
    assert!(!p(|| { let s: &[u8] = &[1, 2, 3, 4]; let _ = s.as_chunks::<2>(); }), "as_chunks::<2> is total");
}
