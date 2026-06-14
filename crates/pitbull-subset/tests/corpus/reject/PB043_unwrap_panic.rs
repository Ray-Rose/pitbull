//! Corpus reject: PB043 — panic-bearing library call (`Option::unwrap`).
//!
//! Expectation: PSS-1 fires PB043 because `x.unwrap()` panics on `None`.
//! The panic lives INSIDE `core`'s `Option::unwrap`, which the v0.2
//! wrapper does not walk and has no prelude model for — so the visitor
//! recognizes the call at the SITE (`is_panicking_library_call`) and
//! emits a PanicReachability obligation; the wrapper surfaces `(PB043)`.
//! Pre-fix (reachability-integrity audit 2026-06-14) this was silently
//! accepted — a false "verified" on ubiquitous code.
#![allow(dead_code)]
#[pitbull::verify]
fn unwrap_panics(x: Option<u32>) -> u32 {
    x.unwrap()
}
