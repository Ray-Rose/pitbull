//! Corpus accept: an immutable `static` with a primitive type.
//!
//! Expectation: PSS-1 accepts. The static is not `mut` and its type is
//! a plain `u32` with no interior mutability. PB018 does not fire,
//! and visit_ty walks the primitive type cleanly.
#![allow(dead_code)]
static MAX_RETRIES: u32 = 5;
#[pitbull::verify]
fn over_threshold(count: u32) -> bool {
    count > MAX_RETRIES
}
