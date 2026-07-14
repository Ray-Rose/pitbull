//! Corpus reject: PB043 — `wrapping_`/`overflowing_`/`saturating_` division
//! and remainder methods, which PANIC on a zero divisor.
//!
//! Expectation: PSS-1 fires PB043 because every method below panics at runtime
//! when the divisor is `0`. The `wrapping` / `saturating` / `overflowing`
//! semantics only tame the `iN::MIN / -1` OVERFLOW case — the divide-by-zero
//! panic is untouched (`5i32.wrapping_div(0)` panics exactly like `5i32 / 0`).
//! Like `div_ceil` / `div_euclid`, the panic lives INSIDE the un-walked `core`
//! method, so the operator-form path (PB049) never sees it.
//!
//! CRITICAL false-discharge fix (audit 2026-07-12): these method forms were
//! trusted-as-total via the broad `contains("::wrapping_")` /
//! `contains("::saturating_")` / `contains("::overflowing_")` allow-list globs
//! in `is_trusted_total_library_call`, so a call like `x.wrapping_div(0)` was
//! silently "verified" (exit 0) while the operator form `x / 0` was correctly
//! obligated. This is the same defect class as the 2026-07-09 `Ord::clamp` /
//! slice-`sort` eviction — missed by that pass. The visitor now recognizes the
//! panicking div/rem members at the call site (`is_panicking_int_method`) and
//! emits a PanicReachability obligation, so the wrapper surfaces `(PB043)`.
//! The total `checked_div` / `checked_rem` forms return `Option` and are NOT
//! rejected (see `accept/PB043_div_rem_method_total.rs`).
#![allow(dead_code)]
#[pitbull::verify]
fn wrap_div(x: i32, y: i32) -> i32 {
    x.wrapping_div(y) // panics if y == 0
}
#[pitbull::verify]
fn wrap_rem(x: u32, y: u32) -> u32 {
    x.wrapping_rem(y) // panics if y == 0
}
#[pitbull::verify]
fn sat_div(x: i32, y: i32) -> i32 {
    x.saturating_div(y) // panics if y == 0 (saturation only tames MIN/-1)
}
#[pitbull::verify]
fn over_div(x: u32, y: u32) -> u32 {
    x.overflowing_div(y).0 // panics if y == 0
}
#[pitbull::verify]
fn over_rem(x: i32, y: i32) -> i32 {
    x.overflowing_rem(y).0 // panics if y == 0
}
#[pitbull::verify]
fn wrap_div_euclid(x: i64, y: i64) -> i64 {
    x.wrapping_div_euclid(y) // panics if y == 0
}
#[pitbull::verify]
fn wrap_rem_euclid(x: i32, y: i32) -> i32 {
    x.wrapping_rem_euclid(y) // panics if y == 0
}
