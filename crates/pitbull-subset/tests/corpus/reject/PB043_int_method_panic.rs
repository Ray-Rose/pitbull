//! Corpus reject: PB043 — panicking integer methods and iterator adapters
//! (`isqrt` on a signed int, `next_multiple_of`, `div_ceil`, the `strict_*`
//! family, `Iterator::step_by`).
//!
//! Expectation: PSS-1 fires PB043 because each panics at runtime — signed
//! `isqrt` when `self < 0`; `next_multiple_of` / `div_ceil` on a zero rhs
//! (and on overflow); every `strict_*` op on overflow (ALWAYS, not just under
//! `overflow-checks`); `step_by(0)` asserts a non-zero step at construction.
//! Like `pow`/`abs`, the panic lives INSIDE the un-walked `core` method, so
//! the operator-form overflow path (PB049) never sees it. A second deep audit
//! (2026-06-14 #2) PROVED these produced a false "verified" (exit 0)
//! end-to-end; the visitor now recognizes them at the call site
//! (`is_panicking_int_method`) and emits a PanicReachability obligation, so
//! the wrapper surfaces `(PB043)`. The UNSIGNED `isqrt` is total and is NOT
//! rejected (see `accept/PB043_int_method_total.rs`).
#![allow(dead_code)]
#[pitbull::verify]
fn signed_isqrt(x: i32) -> i32 {
    x.isqrt() // panics if x < 0
}
#[pitbull::verify]
fn next_multiple(x: u32, m: u32) -> u32 {
    x.next_multiple_of(m) // panics if m == 0
}
#[pitbull::verify]
fn div_ceiling(x: u32, y: u32) -> u32 {
    x.div_ceil(y) // panics if y == 0
}
#[pitbull::verify]
fn strict_sum(x: u32, y: u32) -> u32 {
    x.strict_add(y) // panics on overflow, always
}
#[pitbull::verify]
fn strided(n: u32, k: usize) -> usize {
    (0u32..n).step_by(k).count() // step_by(0) panics at construction
}
