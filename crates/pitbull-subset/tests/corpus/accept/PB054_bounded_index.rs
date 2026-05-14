//! Corpus accept: bounded slice access.
//!
//! Expectation: PSS-1 accepts. The `requires` clause makes the index safe;
//! the verifier discharges the bounds-check obligation.
#![allow(dead_code)]
#[pitbull::verify]
#[pitbull::requires(i < s.len())]
fn nth_byte(s: &[u8], i: usize) -> u8 {
    s[i]
}
/// The idiomatic alternative: structured access through `get`, with the
/// unreachability of the `None` branch proven from `i < s.len()`.
#[pitbull::verify]
#[pitbull::requires(i < s.len())]
fn nth_byte_get(s: &[u8], i: usize) -> u8 {
    match s.get(i) {
        Some(b) => *b,
        // The verifier proves this arm is unreachable from the precondition.
        None => unreachable!(),
    }
}
