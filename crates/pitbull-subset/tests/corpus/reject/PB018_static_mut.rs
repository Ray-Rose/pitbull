//! Corpus reject: PB018 — `static mut` declaration.
//!
//! Expectation: PSS-1 rejects with PB018. The reachability driver visits
//! the static-item kind (closed in v0.1 audit pass); the visitor's
//! `visit_static_item` fires PB018 on the mutability flag.
#![allow(dead_code)]
static mut COUNTER: u32 = 0;
#[pitbull::verify]
fn get_and_increment() -> u32 {
    // Even though the body uses an `unsafe` block to access COUNTER, the
    // declaration of COUNTER itself triggers PB018 at the item level
    // before any body-level checks fire.
    unsafe {
        let v = COUNTER;
        COUNTER = v.wrapping_add(1);
        v
    }
}
