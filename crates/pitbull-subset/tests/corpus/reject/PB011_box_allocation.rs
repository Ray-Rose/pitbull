//! Corpus reject: PB011 — `Box<T>` heap allocation.
//!
//! Expectation: PSS-1 rejects with PB011 because the function body
//! constructs a `Box<u32>`.
#![allow(dead_code)]
#[pitbull::verify]
fn make_boxed(x: u32) -> u32 {
    let b: Box<u32> = Box::new(x);
    *b
}
