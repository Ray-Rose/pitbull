//! Corpus accept: generic trait dispatch (monomorphized).
//!
//! Expectation: PSS-1 accepts this file. The dispatch is static after
//! monomorphization, so PB031 does not fire.
#![allow(dead_code)]
trait Greet {
    #[pitbull::pure]
    fn greet(&self) -> u32;
}
struct Hello;
impl Greet for Hello {
    #[pitbull::pure]
    fn greet(&self) -> u32 { 1 }
}
#[pitbull::verify]
fn dispatch<G: Greet>(g: &G) -> u32 {
    g.greet()
}
#[pitbull::verify]
fn caller() -> u32 {
    let h = Hello;
    dispatch(&h)
}
