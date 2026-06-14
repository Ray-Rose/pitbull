//! Corpus accept: PB043 — radix-free `char` methods are TOTAL and must NOT
//! be rejected. Calibration complement to `reject/PB043_char_radix_panic.rs`:
//! only the `radix`-taking methods (`to_digit`/`is_digit`/`from_digit`) can
//! panic; the classification/conversion methods below are panic-free on every
//! input.
//!
//! Expectation: PB043 does NOT appear in the wrapper's diagnostics.
#![allow(dead_code)]
#[pitbull::verify]
fn is_letter(c: char) -> bool {
    c.is_alphabetic() // total
}
#[pitbull::verify]
fn is_ws(c: char) -> bool {
    c.is_whitespace() // total
}
#[pitbull::verify]
fn upper(c: char) -> char {
    c.to_ascii_uppercase() // total
}
#[pitbull::verify]
fn utf8_len(c: char) -> usize {
    c.len_utf8() // total
}
#[pitbull::verify]
fn from_scalar(x: u32) -> Option<char> {
    core::char::from_u32(x) // total: returns None for non-scalar values
}
