//! Corpus accept: fixed-point substitute for floating-point area.
//!
//! Expectation: PSS-1 accepts. The area computation uses fixed-point
//! arithmetic in `i64` (Q32.32-style), avoiding PB050. Indexing safety,
//! overflow-freedom, and termination are obligations the verifier
//! discharges; PSS-1 subset is satisfied.
#![allow(dead_code)]
/// Pi scaled by 2^16 ≈ 3.14159 * 65536 = 205887.
const PI_Q16: i64 = 205_887;
/// Q16.16 multiply: (a * b) >> 16, clamped to i64 range.
#[pitbull::pure]
#[pitbull::requires(a >= 0 && b >= 0)]
fn q16_mul(a: i64, b: i64) -> i64 {
    (a.wrapping_mul(b)) >> 16
}
#[pitbull::verify]
#[pitbull::requires(radius_q16 >= 0 && radius_q16 < 1_000_000)]
fn area_q16(radius_q16: i64) -> i64 {
    let r2 = q16_mul(radius_q16, radius_q16);
    q16_mul(PI_Q16, r2)
}
