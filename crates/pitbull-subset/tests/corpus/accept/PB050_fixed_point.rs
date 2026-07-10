//! Corpus accept: fixed-point substitute for floating-point area.
//!
//! Expectation: PSS-1 accepts. The area computation uses fixed-point
//! arithmetic in `i64` (Q32.32-style), avoiding PB050. Indexing safety,
//! overflow-freedom, and termination are obligations the verifier
//! discharges; PSS-1 subset is satisfied.
#![allow(dead_code)]
/// Pi scaled by 2^16 ≈ 3.14159 * 65536 = 205887.
const PI_Q16: i64 = 205_887;
/// Q16.16 multiply: (a * b) >> 16, wrapping (total on any input).
///
/// Deliberately carries NO `#[pitbull::requires]`: `wrapping_mul` + a
/// constant shift are total, so none is needed — and as of the 2026-07-09
/// deep audit a call to a precondition-carrying function records a
/// fail-closed coverage gap (call-site discharge is unimplemented; a callee
/// verified ASSUMING its preconditions must not be silently callable). This
/// file's earlier `requires(a >= 0 && b >= 0)` on `q16_mul` was exactly that
/// unproven-at-call-site shape.
#[pitbull::pure]
fn q16_mul(a: i64, b: i64) -> i64 {
    (a.wrapping_mul(b)) >> 16
}
#[pitbull::verify]
#[pitbull::requires(radius_q16 >= 0 && radius_q16 < 1_000_000)]
fn area_q16(radius_q16: i64) -> i64 {
    let r2 = q16_mul(radius_q16, radius_q16);
    q16_mul(PI_Q16, r2)
}
