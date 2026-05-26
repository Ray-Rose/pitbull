//! # `pitbull-spec`
//!
//! User-facing attribute macros for the Pitbull deductive verifier.
//!
//! ## Design
//!
//! Every macro in this crate is a *compile-time no-op*. The attributes carry
//! specification data — preconditions, postconditions, invariants, decreases
//! clauses, trust justifications — but they do not emit any runtime code.
//! Pitbull's verifier consumes these attributes through `rustc_public`'s AST
//! and MIR reflection; rustc itself ignores them.
//!
//! This separation is deliberate. It means:
//!
//! 1. A crate that uses Pitbull specs builds and runs identically with or
//!    without Pitbull installed. Specs do not become runtime checks; they
//!    are *proof-time* assertions only.
//!
//! 2. The verifier's view of the program (the AST + MIR) is the same view
//!    the compiler has. There is no shadow program.
//!
//! 3. We can add new specification constructs without breaking downstream
//!    compilation. A specification that Pitbull does not yet understand is
//!    simply unenforced; it does not break the build.
//!
//! ## PSS-1 alignment
//!
//! - `#[verify]`               — declares a verification entry point.
//! - `#[requires(expr)]`       — precondition.
//! - `#[ensures(expr)]`        — postcondition.
//! - `#[invariant(expr)]`      — loop invariant.
//! - `#[decreases(expr)]`      — termination measure for recursion (PB041, PB044).
//! - `#[variant(expr)]`        — termination measure for loops (PB042).
//! - `#[pure]`                 — function is side-effect-free, callable in specs (PB064).
//! - `#[trusted]`              — assume the spec without proving the body (PB067).
//! - `#[justification("...")]` — required companion to `#[trusted]` (PB067).
//! - `#[ghost]`                — code present only for proof, erased before codegen.
//!
//! Prophecy syntax (`^x` for the future value of a mutable borrow) is
//! intentionally not exposed in v0.1 (PB070). It returns in v0.2 after the
//! tutorial and counterexample UX are in place.
// Defense-in-depth (audit-cleanup F11, 2026-05-26): the workspace
// `[lints]` configuration already sets `unsafe_code = "forbid"`, but
// inner `#![forbid(unsafe_code)]` is harder to silently undo via a
// future `[lints]` reconfiguration. The proc-macro crate is TCB-
// critical (it shapes what the wrapper sees at HIR level) so the
// belt-and-suspenders inner attr matches the other three crate
// roots.
#![forbid(unsafe_code)]
use proc_macro::TokenStream;
/// Marks a function as a verification entry point.
///
/// Pitbull verifies the function body and the transitive closure of its
/// monomorphized callees against PSS-1. Items not reachable from any
/// `#[verify]` entry point are not checked.
#[proc_macro_attribute]
pub fn verify(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Precondition.
///
/// The expression is evaluated in spec mode and must hold at function entry.
/// Callers are obligated to prove it; the function body may assume it.
#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Postcondition.
///
/// The expression is evaluated in spec mode and must hold at every function
/// exit (every `return`, including the implicit return). The special
/// identifier `result` binds to the returned value; `old(e)` refers to the
/// value of `e` at function entry.
#[proc_macro_attribute]
pub fn ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Loop invariant.
///
/// Attach to a `loop`, `while`, or `for` statement. The invariant must hold
/// before the loop, be preserved by every iteration, and is available to the
/// verifier after the loop alongside the loop's exit condition.
#[proc_macro_attribute]
pub fn invariant(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Termination measure for recursion (PSS-1 PB041 and PB044).
///
/// The expression must evaluate to a value of a well-founded type
/// (mathematical `Int` bounded below, structural ADT, lexicographic tuple).
/// Every recursive call site must reduce the measure.
#[proc_macro_attribute]
pub fn decreases(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Termination measure for loops (PSS-1 PB042).
///
/// Distinct from `decreases` only by attachment site. Same semantics.
#[proc_macro_attribute]
pub fn variant(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Marks a function as pure: no side effects, no panics, no allocation, and
/// callable from specification contexts (PSS-1 PB064, PB066).
///
/// Pure functions form the specification language. They are checked for
/// purity by the verifier; calling a non-pure function from a pure body is
/// a subset error.
#[proc_macro_attribute]
pub fn pure(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Trust the specification of this item without proving its body (PSS-1 PB067).
///
/// Required companion: `#[justification("...")]` or a `## Pitbull justification`
/// section in the doc comment. Pitbull refuses to verify a crate that contains
/// `#[trusted]` items lacking justifications.
///
/// Trust budget is surfaced in the report and may cause builds to fail per
/// PSS-1 PB068.
#[proc_macro_attribute]
pub fn trusted(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Companion attribute to `#[trusted]` recording the human-readable rationale.
#[proc_macro_attribute]
pub fn justification(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
/// Marks code as ghost: present for proof, erased before codegen.
///
/// Ghost code may reference values, build auxiliary witnesses, and assert
/// properties; it must not influence the executable program.
#[proc_macro_attribute]
pub fn ghost(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
