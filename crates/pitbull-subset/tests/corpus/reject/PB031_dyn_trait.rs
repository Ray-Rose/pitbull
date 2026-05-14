//! Corpus reject: PB031 — `dyn Trait` trait object.
//!
//! Expectation: PSS-1 rejects with PB031 because the parameter is `&dyn`.
#![allow(dead_code)]
trait Greet {
    fn greet(&self) -> u32;
}
#[pitbull::verify]
fn dispatch(g: &dyn Greet) -> u32 {
    g.greet()
}
