//! # `pitbull-subset`
//!
//! Enforcement of the Pitbull Verifiable Subset, version 1 (**PSS-1**).
//!
//! See `docs/PSS-1.md` for the normative specification. This crate is the
//! mechanical enforcer of that specification: it visits the monomorphized,
//! post-cleanup MIR of every item reachable from a `#[pitbull::verify]`
//! entry point and rejects any construct outside the subset.
//!
//! ## Soundness posture
//!
//! This crate is part of the Pitbull *trusted computing base*. A bug here is a
//! soundness bug, full stop. Three design rules limit our exposure:
//!
//! 1. **Exhaustive match arms, no defaults.** Every variant of every MIR enum
//!    is explicitly handled with either an `accept` (with a documented
//!    rationale) or a `reject` (pointing to a PB rule). Adding a new variant
//!    upstream breaks compilation; the audit moves to the new variant, not
//!    around it.
//!
//! 2. **One module per data source.** The `mir_api` module is the *only* place
//!    that imports from `rustc_public`. If the StableMIR API changes shape,
//!    one file changes; the rest of the crate works against our own stable
//!    re-exports.
//!
//! 3. **Diagnostic accumulation, not first-failure abort.** Users see every
//!    violation at once, the same way they would for type errors. This serves
//!    audit too: a hidden second violation cannot be masked by the first.
//!
//! ## Module map
//!
//! - [`rules`]         — the rule registry: PB001..=PB075 as static data.
//! - [`visitor`]       — the exhaustive MIR / item / type visitor.
//! - [`reachability`]  — call-graph traversal from `#[pitbull::verify]` roots.
//! - [`config`]        — `pitbull.toml` parsing.
//! - [`diagnostic`]    — error type, SARIF rendering, miette-backed printing.
//! - [`mir_api`]       — the single import surface for `rustc_public`.
//! - [`mutation`]      — (feature-gated) mutation-testing harness for the
//!                       subset checker itself.
#![warn(missing_docs)]
#![forbid(unsafe_code)]
pub mod config;
pub mod diagnostic;
pub mod mir_api;
pub mod reachability;
pub mod rules;
pub mod visitor;
#[cfg(feature = "mutation-testing")]
pub mod mutation;
pub use config::SubsetConfig;
pub use diagnostic::{Severity, SubsetError, SubsetReport};
pub use rules::{Category, Rule, RuleId, RULES};
pub use visitor::SubsetVisitor;
/// Pitbull subset specification version this crate enforces.
pub const PSS_VERSION: &str = "PSS-1";
/// Number of rules defined in PSS-1.
pub const RULE_COUNT: usize = 75;
