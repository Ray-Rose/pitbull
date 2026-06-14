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
