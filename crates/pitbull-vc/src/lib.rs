//! # `pitbull-vc`
//!
//! Verification-condition generation and SMT dispatch for the Pitbull
//! deductive verifier. This is the v0.2 spine: the v0.1 subset
//! enforcer (`pitbull-subset`) decides what's in the verifiable
//! subset; `pitbull-vc` discharges the proof obligations the subset
//! enforcer tags but cannot itself prove.
//!
//! ## What lives here
//!
//! - [`VcGoal`] — a single verification condition: a span, a kind
//!   discriminator (overflow / panic-reachability / index-bound /
//!   recursion-decreases), and the SMT-LIB formulation.
//! - [`smt`] — SMT-LIB 2 emission. Today: bit-vector overflow
//!   problems for the primitive integer types. Future: panic
//!   unreachability via path-sensitive symbolic execution; bound
//!   checks; termination measures.
//! - [`solver`] — invocation of external SMT solvers (Z3 today;
//!   CVC5, Alt-Ergo to follow). Gracefully handles "solver not
//!   installed" because v0.2 scaffold must run on developer
//!   machines without the full solver stack.
//!
//! ## What doesn't live here yet
//!
//! - Proof-certificate format (signed solver outputs + replay).
//!   Planned for v0.3.
//! - Multi-solver agreement (2-of-3 voting). v0.1 spec is single-Z3
//!   for the scaffold; multi-solver lands when `solver` grows
//!   adapters for CVC5 and Alt-Ergo.
//! - Counterexample rendering. When a solver returns SAT (i.e. the
//!   safety property is *violatable*), we want a human-readable
//!   trace, not an SMT-LIB model. Planned for v0.2 iteration after
//!   the basic pipeline works.
//! - MIR → Coma → Why3 path (Creusot-fork lineage). The v0.2
//!   scaffold takes a shortcut and emits SMT-LIB directly for
//!   simple obligations (arithmetic overflow). The Why3 layer
//!   lands when functional-correctness predicates need it (v0.3+).
//!
//! ## Soundness posture
//!
//! Per PSS-1 §17.1 + Safety Manual §3.3, the SMT solver is part of
//! Pitbull's TCB. v0.2 mitigates with:
//!
//! 1. Replayable proof certificates (planned).
//! 2. Multi-solver agreement gate (planned).
//! 3. SMT-LIB problems pinned via snapshot tests (today) so that
//!    a refactor that quietly weakens a check is caught by a diff
//!    on the SMT text, not just a solver re-run.
//!
//! Until those land, treat this crate as research-grade. The crate's
//! API is stable enough to wire into pitbull-driver; the *proof
//! results* should not be relied on for safety claims until the
//! multi-solver gate is in place.

#![warn(missing_docs)]
#![forbid(unsafe_code)]

pub mod smt;
pub mod solver;
pub mod vc;

pub use solver::SolverResult;
pub use vc::{ArithOp, VcGoal, VcGoalKind};
