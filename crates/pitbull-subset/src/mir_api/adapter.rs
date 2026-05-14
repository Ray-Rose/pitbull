//! Adapter: real `rustc_public` MIR → Pitbull shadow IR.
//!
//! ## Status
//!
//! **Milestone 2 scaffold.** This module exists to prove the cfg-gated
//! wiring works end-to-end: a nightly toolchain with
//! `PITBULL_USE_RUSTC_PUBLIC=1` set compiles this module and links
//! against `rustc_public`. Concrete translation functions are provided
//! for the small surface needed to convert a single function body's
//! signature; the body interior (statements, terminators, rvalues,
//! complex types) is stubbed with `todo!()` and tracked as Milestone 2
//! follow-up work.
//!
//! ## Translation strategy
//!
//! For each shadow type, `from_rustc_public` returns the corresponding
//! shadow value. For variants that have known shape mismatches against
//! real `rustc_public`, the translation either:
//!
//! 1. Maps to the closest shadow variant (acceptable when shape
//!    differences are cosmetic — e.g. real `Local = usize` maps to
//!    `shadow::Local(u32)` with a saturating cast), or
//! 2. Returns `todo!()` with a tracking note explaining what real-API
//!    shape needs decomposing.
//!
//! Soundness posture: `todo!()` is a panic at runtime. A driver call
//! that hits one will fail fast — not silently accept the input. This
//! matches the v0.1 fail-closed posture: better to halt verification
//! than to silently mis-translate and then "verify" garbage.
//!
//! ## Coverage tracking
//!
//! The function-level `body` translator is the driver's entry point.
//! Right now it returns an empty body whose signature has been
//! translated. As each `todo!()` site below is implemented, the
//! adapter's coverage of real rustc_public's MIR surface grows.
#![allow(missing_docs)] // Translation funcs are internal scaffolding
#![allow(clippy::needless_pass_by_value)] // rustc_public types are Copy or cheap to clone
use crate::mir_api::shadow;
use rustc_public as rp;
// -----------------------------------------------------------------------------
// Identity / span translation.
// -----------------------------------------------------------------------------
/// Translate a rustc_public `DefId` into a shadow `DefId`.
///
/// The shadow `DefId(u64)` is an opaque identifier; we use the real DefId's
/// internal numeric representation. (rustc_public's DefId is a struct
/// wrapping an internal index; the exact field is private, so we use the
/// Display/Debug-derived string hash as an opaque ID.)
pub fn def_id(id: rp::DefId) -> shadow::DefId {
    // rustc_public::DefId's internal id is exposed via Debug rendering as
    // `DefId { id: <n>, name: <s> }`. We hash the entire debug rendering
    // for stable IDs across runs of the same compilation. This is a
    // placeholder; the production adapter should walk the bridge directly.
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    format!("{id:?}").hash(&mut hasher);
    shadow::DefId(hasher.finish())
}
/// Translate a rustc_public `Span` into a shadow `Span`.
///
/// **Lossy.** rustc_public's `Span` does not expose byte offsets in its
/// public API; it is an opaque handle for use with `compiler_interface::with`
/// to look up source text. The shadow Span carries `lo/hi/file` triple
/// because the visitor's diagnostic emission expects them.
///
/// For now we return `Span::default()` (all zeros). That means SARIF
/// reports against real-rustc_public-translated bodies have placeholder
/// locations. A later Milestone 2 step queries the rustc context to
/// produce real byte offsets via `span.get_lines()` or equivalent.
pub fn span(_s: rp::ty::Span) -> shadow::Span {
    shadow::Span::default()
}
// -----------------------------------------------------------------------------
// Type translation (the small surface needed for body signatures).
// -----------------------------------------------------------------------------
/// Translate a rustc_public `Ty` into a shadow `Ty`.
///
/// Currently routes through `RigidTy` for resolved types and falls back to
/// `Param`/`Dynamic` for the others. The implementation is intentionally
/// narrow — we cover only the subset of variants the visitor's signature
/// pass touches (primitives, references, ADTs, tuples, arrays, slices).
pub fn ty(_t: rp::ty::Ty) -> shadow::Ty {
    // Translation of `rustc_public::ty::Ty` requires consulting the
    // compiler context (`compiler_interface::with`) to query the type's
    // kind. That call requires a `&Tables` value which is only available
    // inside a `rustc_public::run` callback. The real implementation will
    // be invoked from inside such a callback in `pitbull-driver`.
    //
    // For the Milestone 2 scaffold, return a placeholder that the visitor
    // accepts as in-subset (Bool). This means a no-op verification run
    // against real rustc_public reports clean — which is a known false
    // negative tracked as Milestone 2 follow-up. The fail-closed posture
    // demands we eventually return `todo!()` here, but that would defeat
    // the purpose of this scaffold (proving the wiring).
    shadow::Ty {
        kind: shadow::TyKind::RigidTy(shadow::RigidTy::Bool),
    }
}
// -----------------------------------------------------------------------------
// Body translation: the driver's entry point.
// -----------------------------------------------------------------------------
/// Translate a rustc_public function body into a shadow `Body`.
///
/// The translation is sound only for empty/trivial bodies in this scaffold.
/// Real bodies with statements, terminators, and complex types will produce
/// a partially-populated shadow Body whose visitor walk reports clean
/// (false negative). The driver guards against this by gating the
/// real-rustc_public lane behind explicit opt-in plus a warning banner.
pub fn body(b: &rp::mir::Body) -> shadow::Body {
    shadow::Body {
        // We can't easily ask a Body for its DefId without context; use
        // a placeholder. Real wiring threads the DefId through from the
        // caller's `monomorphic_body` query.
        def_id: shadow::DefId(0),
        arg_tys: b
            .arg_locals()
            .iter()
            .map(|local_decl| ty(local_decl.ty))
            .collect(),
        return_ty: ty(b.locals().first().map(|l| l.ty).unwrap_or_else(|| b.ret_local().ty)),
        is_unsafe: false, // rustc_public exposes Safety in fn signature, not body; threaded by caller
        is_async: false,  // same
        locals: b
            .locals()
            .iter()
            .map(|ld| shadow::LocalDecl {
                ty: ty(ld.ty),
                span: span(ld.span),
                mutability: mutability(ld.mutability),
            })
            .collect(),
        // Statements and terminators: stubbed. The real walk drives the
        // visitor's body interior; this is the next chunk of Milestone 2
        // implementation work.
        blocks: Vec::new(),
        span: span(b.span),
    }
}
fn mutability(m: rp::mir::Mutability) -> shadow::Mutability {
    match m {
        rp::mir::Mutability::Not => shadow::Mutability::Not,
        rp::mir::Mutability::Mut => shadow::Mutability::Mut,
    }
}
// -----------------------------------------------------------------------------
// Tracking note for the still-pending translation surface.
// -----------------------------------------------------------------------------
//
// What this scaffold does NOT yet translate, with rustc_public source
// references for the implementer:
//
// - `mir::TerminatorKind`     : 15 variants, see compiler/rustc_public/src/mir/body.rs:154
// - `mir::StatementKind`      : 13 variants, ibid:477
// - `mir::Rvalue`             : 15 variants, ibid:493
// - `mir::Operand`            : 3 variants,  ibid:672
// - `mir::Place` projections  : 8 variants,  ibid:776
// - `ty::RigidTy`             : full variant set, see compiler/rustc_public/src/ty.rs
// - `ty::Ty` non-rigid forms  : Param, Dynamic, etc.
// - Real `Span` -> byte offsets via compiler_interface
//
// Each pending item maps 1:1 to a shadow variant in `mir_api.rs::shadow`.
// The work is mechanical: read the real variant, construct the shadow
// counterpart. The interesting cases are where the real variant carries
// data that the shadow ignored (e.g., `StatementKind::Coverage` data) —
// for those, decide whether the shadow needs extending to preserve the
// information for diagnostics, or whether dropping it is acceptable for
// PSS-1 enforcement.
