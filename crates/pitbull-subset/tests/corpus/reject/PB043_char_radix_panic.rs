//! Corpus reject: PB043 — `char` radix methods that PANIC when `radix` is
//! outside `2..=36` (`to_digit`, `is_digit`, and the `char::from_digit` free
//! fn).
//!
//! Expectation: PSS-1 fires PB043. `to_digit`/`from_digit` return an
//! `Option`, but the radix check is a SEPARATE `panic!` that runs before the
//! `Option` is produced — so a runtime `radix` the caller has not bounded
//! panics inside un-walked `core`, invisible to the operator/projection
//! paths. Found in the 2026-06-14 #2 boundary sweep (the same one that caught
//! the extended int-method family); the visitor now recognizes them at the
//! call site (`is_panicking_char_method`) and emits a PanicReachability
//! obligation, so the wrapper surfaces `(PB043)`. The radix-free `char`
//! methods are total and NOT rejected (see `accept/PB043_char_radix_total.rs`).
#![allow(dead_code)]
#[pitbull::verify]
fn digit_value(c: char, radix: u32) -> u32 {
    c.to_digit(radix).unwrap_or(0) // to_digit panics if radix > 36
}
#[pitbull::verify]
fn classify(c: char, radix: u32) -> bool {
    c.is_digit(radix) // is_digit panics if radix > 36
}
#[pitbull::verify]
fn render(n: u32, radix: u32) -> char {
    core::char::from_digit(n, radix).unwrap_or('?') // from_digit panics if radix > 36
}
