//! Corpus reject: PB001 — `unsafe` block.
//!
//! Expectation: Pitbull rejects this file with rule PB001 on the `unsafe { ... }`
//! site. Each reject corpus file documents the exact rule it triggers in its
//! header so that an auditor walking the corpus knows what each test pins.
#![allow(dead_code)]
fn checksum(bytes: &[u8]) -> u32 {
    let ptr = bytes.as_ptr();
    let len = bytes.len();
    let mut sum: u32 = 0;
    for i in 0..len {
        // PB001: dereference of a raw pointer requires `unsafe`.
        let byte = unsafe { *ptr.add(i) };
        sum = sum.wrapping_add(byte as u32);
    }
    sum
}
#[pitbull::verify]
fn entry(input: &[u8]) -> u32 {
    checksum(input)
}
