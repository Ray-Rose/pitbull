//! Corpus accept: PB043 — TOTAL integer methods adjacent to the panicking
//! ones must NOT be rejected. This is the calibration complement to
//! `reject/PB043_int_method_panic.rs`: a visitor that flagged every method
//! named like a panicking one would also reject these, which are provably
//! panic-free on every input.
//!
//!   - UNSIGNED `isqrt` is total (only the SIGNED impls panic, on `self < 0`),
//!     so the signedness discrimination in `is_panicking_int_method` must let
//!     it through.
//!   - `wrapping_*` / `checked_*` / `saturating_*` never panic.
//!   - `midpoint` and `abs_diff` are total.
//!
//! Expectation: PB043 does NOT appear in the wrapper's diagnostics (the
//! wrapper verifies the crate — these emit zero obligations).
#![allow(dead_code)]
#[pitbull::verify]
fn unsigned_isqrt(x: u32) -> u32 {
    x.isqrt() // total: u32 is never negative
}
#[pitbull::verify]
fn wrapping_sum(x: u32, y: u32) -> u32 {
    x.wrapping_add(y) // total: wraps, never panics
}
#[pitbull::verify]
fn saturating_product(x: u32, y: u32) -> u32 {
    x.saturating_mul(y) // total: saturates, never panics
}
#[pitbull::verify]
fn mid(x: u32, y: u32) -> u32 {
    x.midpoint(y) // total
}
#[pitbull::verify]
fn distance(x: u32, y: u32) -> u32 {
    x.abs_diff(y) // total
}
