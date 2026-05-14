//! Corpus reject: PB054 — unguarded slice index.
//!
//! Expectation: PSS-1 fires PB054 because `s[i]` cannot be discharged
//! without a precondition relating `i` to `s.len()`.
#![allow(dead_code)]
#[pitbull::verify]
fn first_byte_unsafe(s: &[u8], i: usize) -> u8 {
    s[i]
}
