//! Corpus accept: recursion with `#[decreases]`.
//!
//! Expectation: PSS-1 accepts. The decreases clause discharges PB041; the
//! AoRTE proof obligation on `n.wrapping_mul` succeeds because `n <= 12`
//! and 12! fits in `u32`. The precondition `n <= 12` is what makes the
//! safety claim true.
#![allow(dead_code)]
#[pitbull::verify]
#[pitbull::requires(n <= 12)]
#[pitbull::ensures(result >= 1)]
#[pitbull::decreases(n)]
fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}
