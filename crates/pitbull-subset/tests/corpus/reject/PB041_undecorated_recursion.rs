//! Corpus reject: PB041 — recursion without `#[decreases]`.
//!
//! Expectation: PSS-1 rejects with PB041 because `factorial` is recursive
//! but has no termination measure.
#![allow(dead_code)]
#[pitbull::verify]
fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n.wrapping_mul(factorial(n - 1))
    }
}
