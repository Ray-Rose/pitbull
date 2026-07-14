//! Corpus accept: PB043 — the TOTAL `checked_` division/remainder methods must
//! NOT be rejected. This is the calibration complement to
//! `reject/PB043_div_rem_method_panic.rs`: the fix that catches the panicking
//! `wrapping_`/`overflowing_`/`saturating_` div/rem members must NOT also flag
//! the `checked_` forms, which return `Option` and are panic-free on every
//! input (a zero divisor yields `None`, not a panic).
//!
//! `checked_div` / `checked_rem` / `checked_div_euclid` / `checked_rem_euclid`
//! carry no `wrapping_/overflowing_/saturating_` segment, so the new
//! panicking-div/rem clause in `is_panicking_int_method` leaves them alone, and
//! `is_trusted_total_library_call` keeps trusting them as total. `unwrap_or`
//! is itself total (it cannot panic), so the whole body is panic-free.
//!
//! Expectation: PB043 does NOT appear in the wrapper's diagnostics.
#![allow(dead_code)]
#[pitbull::verify]
fn checked_division(x: i32, y: i32) -> i32 {
    x.checked_div(y).unwrap_or(0) // None on y == 0 — total, never panics
}
#[pitbull::verify]
fn checked_remainder(x: u32, y: u32) -> u32 {
    x.checked_rem(y).unwrap_or(0) // total
}
#[pitbull::verify]
fn checked_div_euclid(x: i64, y: i64) -> i64 {
    x.checked_div_euclid(y).unwrap_or(0) // total
}
#[pitbull::verify]
fn checked_rem_euclid(x: i32, y: i32) -> i32 {
    x.checked_rem_euclid(y).unwrap_or(0) // total
}
