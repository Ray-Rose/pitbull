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
//! - [`solver`] — invocation of external SMT solvers through the
//!   multi-solver AGREEMENT GATE (Task S): a generic `Solver`
//!   descriptor (Z3, CVC5, Alt-Ergo), parallel `run_solvers`, and a
//!   pure `vote()` policy. Gracefully handles "solver not installed"
//!   because the scaffold must run on developer machines without the
//!   full solver stack.
//!
//! ## What doesn't live here yet
//!
//! - Proof-certificate format (signed solver outputs + replay).
//!   Planned for v0.3.
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
//! 1. Multi-solver agreement gate (DONE, Task S 2026-05-28): an
//!    obligation discharges only when `threshold` DISTINCT solvers
//!    independently agree `unsat` with zero `sat` votes; a `sat`/
//!    `unsat` split is a fail-closed `DISAGREEMENT`. Defends against a
//!    single buggy/hostile solver on `PATH`. See [`solver::vote`].
//! 2. SMT-LIB problems pinned via snapshot tests (today) so that
//!    a refactor that quietly weakens a check is caught by a diff
//!    on the SMT text, not just a solver re-run.
//! 3. Replayable proof certificates (planned for v0.3).
//!
//! The agreement gate is in place, but the crate remains
//! research-grade pending proof certificates and a broader audited
//! corpus: treat *proof results* as high-assurance-in-progress, not a
//! certified safety claim.

#![warn(missing_docs)]
#![forbid(unsafe_code)]

pub mod cert;
pub mod smt;
pub mod solver;
pub mod vc;

// Re-export the typed-obligation half from pitbull-subset so
// downstream code can import the whole VC surface from one place.
pub use pitbull_subset::{ArithOp, VcObligation, VcObligationKind};
pub use cert::{CertificateBundle, ObligationCertificate, ReplayOutcome};
pub use solver::SolverResult;
pub use vc::{compile, compile_with_index_bits, VcGoal};
