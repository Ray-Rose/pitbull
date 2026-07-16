//! Corpus reject: PB021 — the `Cell` family under its `std::` RE-EXPORT
//! rendering, which is the ONLY rendering real std-linked code produces.
//!
//! Expectation: PSS-1 fires PB021 on the `Cell` type. Interior mutability
//! breaks the verification model's assumption that a `&T` is immutable, so the
//! type is outside the subset regardless of which path names it.
//!
//! ## Why this file exists (audit 2026-07-15 — a HIGH false accept)
//!
//! rustc renders a type by the path it was REACHED through. On a std-linked
//! crate (the typical case) `Cell` arrives at the visitor as
//! `std::cell::Cell`, NOT `core::cell::Cell` — and that holds even when the
//! source spells it `core::cell::Cell`, because std re-exports the core types
//! and rustc resolves through the prelude that brought it into scope (verified
//! empirically on the pinned nightly: both spellings render `std::`).
//!
//! `classify_adt` listed BOTH spellings for PB011/PB012/PB015 (`Box`, `Vec`,
//! `Rc`) but only `core::` for PB008/PB021/PB022/PB023. Those four rules were
//! therefore DEAD on every std-linked crate: `fn f(c: Cell<u32>)` reported zero
//! violations. Confirmed with a clean control — under
//! `strict_library_acceptance = false`, `Box<u32>` was rejected (dual-listed)
//! while `Cell<u32>` exited 0 (core-only-listed).
//!
//! Under the DEFAULT config the prelude's fail-closed coverage gap still caught
//! any *call* into the type, so this was not a live false discharge out of the
//! box — but PB021 exists precisely to be the type-level defense that does NOT
//! depend on the call allow-list, and under the documented
//! `strict_library_acceptance = false` migration opt-out nothing caught it.
//!
//! The rules now match on the root-stripped suffix, so every stdlib root
//! (`core::` / `std::` / `alloc::`) triggers the same rule and a newly-added
//! arm cannot reintroduce the asymmetry. Unit-pinned by
//! `visitor.rs::type_rules_fire_under_every_stdlib_root`; this file pins it
//! against REAL MIR, which is the coverage that was missing — every prior test
//! for these rules hand-constructed the `core::` path the adapter never emits.

use std::cell::Cell;

/// Transporting a `Cell` through a signature: the type-level rule must fire on
/// the `std::cell::Cell` rendering the adapter produces.
pub fn passthru(c: &Cell<u32>) -> &Cell<u32> {
    c
}

/// Materializing a `Cell` in a local — the in-body use that reaches
/// `classify_adt` through the local's declared type.
pub fn read_cell(c: Cell<u32>) -> u32 {
    c.get()
}
