//! Corpus reject: PB043 — panicking slice methods (`copy_from_slice`,
//! `swap`, `rotate_left`).
//!
//! Expectation: PSS-1 fires PB043 because each of these panics at runtime
//! (length mismatch / out-of-bounds index / `mid > len`). The panic lives
//! INSIDE the un-walked `core` slice method, and — unlike element indexing
//! `v[i]` (a PB054 projection) — these are library `Call`s the projection
//! path never sees. The deep audit (2026-06-14) PROVED these produced a
//! false "verified" (exit 0) end-to-end; the visitor now recognizes them at
//! the call site (`is_panicking_index_or_slice_call`) and emits a
//! PanicReachability obligation, so the wrapper surfaces `(PB043)`.
#![allow(dead_code)]
#[pitbull::verify]
fn copy_it(dst: &mut [u8], src: &[u8]) {
    dst.copy_from_slice(src);
}
#[pitbull::verify]
fn swap_it(s: &mut [u8], a: usize, b: usize) {
    s.swap(a, b);
}
