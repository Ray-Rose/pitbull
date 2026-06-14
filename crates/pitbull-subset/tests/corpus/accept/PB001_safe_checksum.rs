//! Corpus accept: PB001 — safe equivalent of the unsafe-block checksum.
//!
//! Expectation: Pitbull accepts this file. The function computes the same
//! result as `corpus/reject/PB001_unsafe_block.rs` but does so through
//! ordinary slice iteration — no `unsafe` block, no raw pointer.
#![allow(dead_code)]
#[pitbull::pure]
fn checksum_pure(bytes: &[u8]) -> u32 {
    let mut sum: u32 = 0;
    let mut i: usize = 0;
    // Loop variant: bytes.len() - i strictly decreases at each iteration.
    while i < bytes.len() {
        // `u32::from` not `as`: PSS-1 PB051 bans `as` integer casts even
        // when widening; the `From` conversion is the accepted form.
        sum = sum.wrapping_add(u32::from(bytes[i]));
        i += 1;
    }
    sum
}
#[pitbull::verify]
#[pitbull::requires(input.len() <= 65_535)]
fn entry(input: &[u8]) -> u32 {
    checksum_pure(input)
}
