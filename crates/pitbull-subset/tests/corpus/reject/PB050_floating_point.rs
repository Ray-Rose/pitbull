//! Corpus reject: PB050 — floating-point type.
//!
//! Expectation: PSS-1 rejects with PB050 on the `f32` arithmetic.
#![allow(dead_code)]
#[pitbull::verify]
fn area(radius: f32) -> f32 {
    let pi: f32 = 3.141_592_6;
    pi * radius * radius
}
