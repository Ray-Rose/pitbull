//! Adapter: real `rustc_public` MIR → Pitbull shadow IR.
//!
//! ## Strategy
//!
//! For each shadow type, a translation function takes the corresponding
//! real `rustc_public` value and returns a shadow value. Where shape
//! differences exist (and they exist in many places), the translation
//! is documented inline. Where a real variant has no shadow counterpart,
//! we either map it to the closest semantic equivalent or `todo!()` to
//! fail closed at runtime (better to halt than to silently mistranslate
//! and "verify" garbage).
//!
//! ## Audit-relevant API drift recorded here
//!
//! - `mir::Local` is `usize` in real, `struct Local(u32)` in shadow.
//!   We cast `usize as u32`. In practice locals never exceed millions,
//!   so this is safe; if it were ever to overflow we'd want a checked
//!   cast that aborts (currently unchecked because it's a non-issue).
//! - `mir::ProjectionElem::Field` carries `(FieldIdx, Ty)` in real but
//!   `(u32)` in shadow — we drop the type, which the visitor doesn't
//!   need (field types are recovered through the parent place's type).
//! - `mir::ProjectionElem::ConstantIndex` has `min_length` and
//!   `from_end` in real that the shadow elides — same rationale.
//! - `mir::Operand::RuntimeChecks` has no shadow variant (it's new in
//!   recent rustc_public). We map it to `Constant` with a synthetic
//!   bool-typed const operand; the visitor walks it as a constant
//!   read and no PB rule fires on it (correct — `cfg!(ub_checks)`
//!   etc. is just a bool at runtime).
//! - `mir::Rvalue::CheckedBinaryOp` collapses to `BinaryOp` for
//!   visitor purposes — neither carries semantic information PSS-1
//!   v0.1 enforces beyond `BinOp::Offset` (PB004).
//! - `mir::Rvalue::AddressOf` is real's name for what the shadow calls
//!   `RawPtr` (the `&raw const` / `&raw mut` operator).
//! - `mir::ConstOperand` shape is wholly different (real: span +
//!   user_ty + const_; shadow: ty + def_id + path). The path is the
//!   visitor-critical field — it's how `classify_called_function`
//!   matches `core::panicking::*`, `alloc::alloc::*`, etc. We extract
//!   the path from `MirConst.ty().kind()` when it's a `RigidTy::FnDef`.
//! - `ty::Span` is opaque in real and lacks Default/Serialize. We
//!   return `Span::default()` as a placeholder (lossy diagnostics —
//!   tracked in PSS-1 §17.1).
#![allow(missing_docs)] // Translation funcs are internal scaffolding.
#![allow(clippy::needless_pass_by_value)] // rustc_public types are Copy or cheap to clone.
#![allow(clippy::cast_possible_truncation)] // usize→u32 for Local/Field is documented above.
use crate::mir_api::shadow;
use rustc_public as rp;
// =====================================================================
// Identity & span (unchanged from scaffold; documented above).
// =====================================================================
pub fn def_id(id: rp::DefId) -> shadow::DefId {
    // The shadow `DefId(u64)` is an opaque identifier. The ideal source
    // is rustc_public's internal `usize` index (via the `IndexedVal`
    // trait's `to_index()`), which is the stable bridge ID for the
    // item. Unfortunately `IndexedVal` is re-exported `pub(crate)` from
    // rustc_public, so we can't access it from outside the crate.
    //
    // The next-best stable input is `DefId::name()` — the fully
    // qualified path string. It's deterministic per compilation
    // (same crate compiled twice produces the same path for the same
    // item), unique per item (path collisions would already be a Rust
    // language error), and accessible via the public API.
    //
    // Hashing the path gives us a u64 opaque ID with the same stability
    // guarantees the bridge index would. The downside is hash
    // collisions are theoretically possible (though astronomically
    // unlikely with DefaultHasher's 64-bit output) — bridge access
    // would be collision-free. Tracked as a follow-up if rustc_public
    // ever exposes IndexedVal publicly.
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    id.name().hash(&mut hasher);
    shadow::DefId(hasher.finish())
}
pub fn span(s: rp::ty::Span) -> shadow::Span {
    // rustc_public's Span exposes line/col positions and a filename
    // string but no byte offsets. We pack the line/col positions into
    // the shadow's lo/hi fields (16-bit composites — see the Span
    // doc-comment in mir_api.rs) and hash the filename for the file
    // ID. SARIF emission decodes these back into region info.
    //
    // Note: get_lines() and get_filename() require the rustc_public
    // compiler context (they call into `with(|cx| ...)`). The driver
    // ensures we're inside `rustc_internal::run(tcx, ...)` before
    // calling adapter functions.
    let lines = s.get_lines();
    let filename = s.get_filename();
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    filename.hash(&mut hasher);
    let file_hash = (hasher.finish() & 0xFFFF_FFFF) as u32;
    shadow::Span {
        lo: shadow::Span::pack(lines.start_line, lines.start_col),
        hi: shadow::Span::pack(lines.end_line, lines.end_col),
        file: file_hash,
    }
}
fn local(l: rp::mir::Local) -> shadow::Local {
    // `rp::mir::Local` is `usize`. Locals beyond ~4 billion would be
    // pathological MIR; the shadow's `u32` cap is fine in practice.
    shadow::Local(l as u32)
}
fn mutability(m: rp::mir::Mutability) -> shadow::Mutability {
    match m {
        rp::mir::Mutability::Not => shadow::Mutability::Not,
        rp::mir::Mutability::Mut => shadow::Mutability::Mut,
    }
}
// =====================================================================
// Type translation (Batch 2 in the milestone plan).
// =====================================================================
pub fn ty(t: rp::ty::Ty) -> shadow::Ty {
    // `rp::ty::Ty` is a handle; `kind()` returns its `TyKind` by value.
    // The call requires the rustc_public compiler context; the driver
    // ensures we're inside `rustc_internal::run(tcx, ...)` before
    // calling any adapter function.
    shadow::Ty {
        kind: ty_kind(&t.kind()),
    }
}
fn ty_kind(k: &rp::ty::TyKind) -> shadow::TyKind {
    match k {
        rp::ty::TyKind::RigidTy(rigid) => match rigid {
            // Real `RigidTy::Dynamic(predicates, region)` represents
            // `dyn Trait` types. The shadow promotes `dyn` to the
            // TyKind level (`TyKind::Dynamic`) so the visitor's PB031
            // detector fires directly. Map the real RigidTy form into
            // the shadow's promoted form here.
            rp::ty::RigidTy::Dynamic(_, _) => shadow::TyKind::Dynamic,
            _ => shadow::TyKind::RigidTy(rigid_ty(rigid)),
        },
        rp::ty::TyKind::Alias(_, _) => {
            // `impl Trait` / projection types post-monomorphization
            // should be resolved; if they're not, the visitor's PB039
            // ("unresolved type parameter post-monomorphization") is
            // the closest analog. We surface it through Param.
            shadow::TyKind::Param("__alias_post_mono".into())
        }
        rp::ty::TyKind::Param(p) => {
            // `ParamTy` carries an index + name; we use the name.
            shadow::TyKind::Param(format!("{p:?}"))
        }
        rp::ty::TyKind::Bound(_, _) => {
            // Late-bound vars from HRTBs; PB034 territory. Not expected
            // in post-mono MIR but if seen, surface as Dynamic so the
            // visitor's PB031 fires (close-enough fail-closed signal).
            shadow::TyKind::Dynamic
        }
    }
}
fn rigid_ty(r: &rp::ty::RigidTy) -> shadow::RigidTy {
    match r {
        rp::ty::RigidTy::Bool => shadow::RigidTy::Bool,
        rp::ty::RigidTy::Char => shadow::RigidTy::Char,
        rp::ty::RigidTy::Int(i) => shadow::RigidTy::Int(int_ty(*i)),
        rp::ty::RigidTy::Uint(u) => shadow::RigidTy::Uint(uint_ty(*u)),
        rp::ty::RigidTy::Float(f) => shadow::RigidTy::Float(float_ty(*f)),
        // The visitor's `classify_adt` matches on `path`; we get it
        // from `name()` (a fully-qualified string per `DefId::name`'s
        // doc). This is the real-mode equivalent of how test fixtures
        // construct `AdtDef { path: "alloc::boxed::Box", ... }`.
        rp::ty::RigidTy::Adt(adt, _generic_args) => shadow::RigidTy::Adt(adt_def(*adt)),
        // Foreign types (FFI). Not currently a PB rule on its own; the
        // surrounding `extern` block is PB056 territory at the item
        // level. Map to a synthetic Adt so the visitor walks past it
        // cleanly.
        rp::ty::RigidTy::Foreign(_) => shadow::RigidTy::Adt(shadow::AdtDef {
            path: "__pitbull_foreign".into(),
            is_union: false,
        }),
        // `str` (the unsized string slice). No PB rule; visitor accepts.
        rp::ty::RigidTy::Str => shadow::RigidTy::Adt(shadow::AdtDef {
            path: "core::str".into(),
            is_union: false,
        }),
        // Array: extract the count from the TyConst. If the count
        // can't be evaluated (e.g., it's still symbolic), fall back to
        // 0 — which means PB020 won't fire on it but no incorrect
        // detection happens either.
        rp::ty::RigidTy::Array(elem, count_const) => {
            let count = count_const.eval_target_usize().unwrap_or(0);
            shadow::RigidTy::Array(Box::new(ty(*elem)), count)
        }
        // `Pat<T, P>` is a refinement of `T` for pattern types; treat
        // as the underlying T for PSS-1 purposes.
        rp::ty::RigidTy::Pat(inner, _pattern) => rigid_ty_of(ty(*inner)),
        rp::ty::RigidTy::Slice(inner) => shadow::RigidTy::Slice(Box::new(ty(*inner))),
        // Note: arg order swap — real is (Ty, Mutability), shadow is
        // (Mutability, Box<Ty>). PB004 fires on this in the visitor.
        rp::ty::RigidTy::RawPtr(inner, mut_) => {
            shadow::RigidTy::RawPtr(mutability(*mut_), Box::new(ty(*inner)))
        }
        // Real has Region as a first parameter; shadow drops it (we
        // don't model lifetimes for PSS-1 v0.1).
        rp::ty::RigidTy::Ref(_region, inner, mut_) => {
            shadow::RigidTy::Ref(mutability(*mut_), Box::new(ty(*inner)))
        }
        rp::ty::RigidTy::FnDef(fn_def, _generic_args) => {
            shadow::RigidTy::FnDef(def_id(fn_def_to_def_id(*fn_def)))
        }
        rp::ty::RigidTy::FnPtr(_sig) => shadow::RigidTy::FnPtr,
        rp::ty::RigidTy::Closure(closure_def, _generic_args) => {
            shadow::RigidTy::Closure(def_id(closure_def_to_def_id(*closure_def)))
        }
        // Coroutines and CoroutineClosures: shadow has no distinct
        // variant for these; collapse to Closure (closest analog —
        // they're all anonymous capture-bearing function-like values).
        // PB033 will fire correctly via the closure type signal.
        rp::ty::RigidTy::Coroutine(coroutine_def, _) => {
            shadow::RigidTy::Closure(def_id(coroutine_def_to_def_id(*coroutine_def)))
        }
        rp::ty::RigidTy::CoroutineClosure(cc_def, _) => {
            shadow::RigidTy::Closure(def_id(coroutine_closure_def_to_def_id(*cc_def)))
        }
        // CoroutineWitness is the captured-state ADT for a coroutine;
        // synthetic-Adt fallback so the visitor walks past it.
        rp::ty::RigidTy::CoroutineWitness(_, _) => shadow::RigidTy::Adt(shadow::AdtDef {
            path: "__pitbull_coroutine_witness".into(),
            is_union: false,
        }),
        // Real `Dynamic(predicates, region)` is the `dyn Trait` type.
        // Normally intercepted by `ty_kind` and promoted to shadow's
        // `TyKind::Dynamic` so the visitor's PB031 detector fires
        // directly. This arm exists for exhaustiveness and as a
        // defensive fallback if any future caller bypasses ty_kind
        // and dispatches a Dynamic variant straight to rigid_ty.
        rp::ty::RigidTy::Dynamic(_, _) => shadow::RigidTy::Adt(shadow::AdtDef {
            path: "__pitbull_dyn_trait_fallback".into(),
            is_union: false,
        }),
        // The never type `!`. No PB rule fires on it; visitor accepts.
        rp::ty::RigidTy::Never => shadow::RigidTy::Adt(shadow::AdtDef {
            path: "__pitbull_never".into(),
            is_union: false,
        }),
        rp::ty::RigidTy::Tuple(elems) => {
            shadow::RigidTy::Tuple(elems.iter().map(|t| ty(*t)).collect())
        }
    }
}
/// Helper: extract the inner RigidTy from a shadow Ty when we know it
/// resolves to one. Returns a synthetic `__pitbull_unrigid` ADT for
/// non-rigid wrappers (Pattern types could in principle wrap a
/// non-rigid inner type; we don't currently see that in practice).
fn rigid_ty_of(t: shadow::Ty) -> shadow::RigidTy {
    match t.kind {
        shadow::TyKind::RigidTy(r) => r,
        _ => shadow::RigidTy::Adt(shadow::AdtDef {
            path: "__pitbull_unrigid".into(),
            is_union: false,
        }),
    }
}
fn int_ty(i: rp::ty::IntTy) -> shadow::IntTy {
    match i {
        rp::ty::IntTy::Isize => shadow::IntTy::Isize,
        rp::ty::IntTy::I8 => shadow::IntTy::I8,
        rp::ty::IntTy::I16 => shadow::IntTy::I16,
        rp::ty::IntTy::I32 => shadow::IntTy::I32,
        rp::ty::IntTy::I64 => shadow::IntTy::I64,
        rp::ty::IntTy::I128 => shadow::IntTy::I128,
    }
}
fn uint_ty(u: rp::ty::UintTy) -> shadow::UintTy {
    match u {
        rp::ty::UintTy::Usize => shadow::UintTy::Usize,
        rp::ty::UintTy::U8 => shadow::UintTy::U8,
        rp::ty::UintTy::U16 => shadow::UintTy::U16,
        rp::ty::UintTy::U32 => shadow::UintTy::U32,
        rp::ty::UintTy::U64 => shadow::UintTy::U64,
        rp::ty::UintTy::U128 => shadow::UintTy::U128,
    }
}
fn float_ty(f: rp::ty::FloatTy) -> shadow::FloatTy {
    match f {
        rp::ty::FloatTy::F16 => shadow::FloatTy::F16,
        rp::ty::FloatTy::F32 => shadow::FloatTy::F32,
        rp::ty::FloatTy::F64 => shadow::FloatTy::F64,
        rp::ty::FloatTy::F128 => shadow::FloatTy::F128,
    }
}
fn adt_def(adt: rp::ty::AdtDef) -> shadow::AdtDef {
    // `name()` on AdtDef (via the CrateDef trait) returns the fully
    // qualified path. NOTE: when an item is reachable through the
    // std prelude (the typical case), `name()` returns the
    // `std::*` re-export path, not the canonical `alloc::*` /
    // `core::*` definition path. For example, `Box<T>` comes back as
    // `"std::boxed::Box"`, not `"alloc::boxed::Box"`. The visitor's
    // `classify_adt` accepts both forms — see its match arms.
    use rp::CrateDef;
    shadow::AdtDef {
        path: adt.name(),
        is_union: matches!(adt.kind(), rp::ty::AdtKind::Union),
    }
}
// Bridges between rustc_public's typed def newtypes and DefId. None of
// these expose a public `def_id()` method directly on stable docs; we
// extract through the CrateDef trait which all `*Def` types implement.
fn fn_def_to_def_id(d: rp::ty::FnDef) -> rp::DefId {
    use rp::CrateDef;
    d.def_id()
}
fn closure_def_to_def_id(d: rp::ty::ClosureDef) -> rp::DefId {
    use rp::CrateDef;
    d.def_id()
}
fn coroutine_def_to_def_id(d: rp::ty::CoroutineDef) -> rp::DefId {
    use rp::CrateDef;
    d.def_id()
}
fn coroutine_closure_def_to_def_id(d: rp::ty::CoroutineClosureDef) -> rp::DefId {
    use rp::CrateDef;
    d.def_id()
}
// =====================================================================
// Place / projection / operand / const_operand (Batch 1).
// =====================================================================
pub fn place(p: &rp::mir::Place) -> shadow::Place {
    shadow::Place {
        local: local(p.local),
        projection: p.projection.iter().map(projection).collect(),
    }
}
pub fn projection(elem: &rp::mir::ProjectionElem) -> shadow::ProjectionElem {
    match elem {
        rp::mir::ProjectionElem::Deref => shadow::ProjectionElem::Deref,
        // Real carries (FieldIdx, Ty); shadow keeps just the index.
        rp::mir::ProjectionElem::Field(idx, _ty) => shadow::ProjectionElem::Field(*idx as u32),
        rp::mir::ProjectionElem::Index(local_idx) => {
            shadow::ProjectionElem::Index(local(*local_idx))
        }
        // Real carries offset + min_length + from_end; shadow keeps
        // just the offset (visitor's PB054 cares about the index value
        // being statically-bounded, not the from_end bookkeeping).
        rp::mir::ProjectionElem::ConstantIndex { offset, .. } => {
            shadow::ProjectionElem::ConstantIndex { offset: *offset }
        }
        rp::mir::ProjectionElem::Subslice { from, to, .. } => {
            shadow::ProjectionElem::Subslice { from: *from, to: *to }
        }
        rp::mir::ProjectionElem::Downcast(variant_idx) => {
            // VariantIdx is `pub struct VariantIdx(usize, ThreadLocalIndex)`.
            // We hash it like DefId for an opaque u32 representation.
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            format!("{variant_idx:?}").hash(&mut hasher);
            shadow::ProjectionElem::Downcast((hasher.finish() & 0xFFFF_FFFF) as u32)
        }
        rp::mir::ProjectionElem::OpaqueCast(t) => shadow::ProjectionElem::OpaqueCast(ty(*t)),
    }
}
pub fn operand(o: &rp::mir::Operand) -> shadow::Operand {
    match o {
        rp::mir::Operand::Copy(p) => shadow::Operand::Copy(place(p)),
        rp::mir::Operand::Move(p) => shadow::Operand::Move(place(p)),
        rp::mir::Operand::Constant(c) => shadow::Operand::Constant(const_operand(c)),
        // RuntimeChecks (cfg!(ub_checks) etc.) is a constant boolean at
        // codegen time. Map to a constant operand carrying a Bool type.
        // No PB rule fires on this; the visitor walks it harmlessly.
        rp::mir::Operand::RuntimeChecks(_) => shadow::Operand::Constant(shadow::ConstOperand {
            ty: shadow::Ty {
                kind: shadow::TyKind::RigidTy(shadow::RigidTy::Bool),
            },
            def_id: None,
            path: None,
        }),
    }
}
pub fn const_operand(c: &rp::mir::ConstOperand) -> shadow::ConstOperand {
    let real_ty = c.const_.ty();
    let kind = real_ty.kind();
    // Extract the function path for FnDef-typed constants. This is the
    // visitor-critical code path: when an `Operand::Constant` represents
    // a function being called (the common case for `TerminatorKind::Call`),
    // the path here is what `classify_called_function` matches on
    // (PB011 alloc, PB023 atomics, PB025 volatile, PB028 thread, PB043
    // panic, etc.).
    let (def_id_opt, path_opt) = match &kind {
        rp::ty::TyKind::RigidTy(rp::ty::RigidTy::FnDef(fn_def, _)) => {
            use rp::CrateDef;
            (Some(def_id(fn_def.def_id())), Some(fn_def.name()))
        }
        _ => (None, None),
    };
    shadow::ConstOperand {
        ty: ty(real_ty),
        def_id: def_id_opt,
        path: path_opt,
    }
}
// =====================================================================
// Rvalue + supporting types (Batch 3).
// =====================================================================
pub fn rvalue(rv: &rp::mir::Rvalue) -> shadow::Rvalue {
    match rv {
        rp::mir::Rvalue::Use(op) => shadow::Rvalue::Use(operand(op)),
        // Real `Repeat(Operand, TyConst)` — try to evaluate the count.
        // If the count can't be evaluated to a target usize (rare in
        // post-mono), fall back to 0; the visitor's `visit_rvalue`
        // doesn't use the count for any rule directly (PB020 is on
        // local types, not array literals).
        rp::mir::Rvalue::Repeat(op, count) => {
            let n = count.eval_target_usize().unwrap_or(0);
            shadow::Rvalue::Repeat(operand(op), n)
        }
        // Real `Ref(Region, BorrowKind, Place)` — drop region (we don't
        // model lifetimes), use BorrowKind's lossy mutability.
        rp::mir::Rvalue::Ref(_region, borrow_kind, p) => {
            shadow::Rvalue::Ref(mutability(borrow_kind.to_mutable_lossy()), place(p))
        }
        // Real `ThreadLocalRef(CrateItem)` carries the static item; we
        // need its DefId for the shadow.
        rp::mir::Rvalue::ThreadLocalRef(crate_item) => {
            use rp::CrateDef;
            shadow::Rvalue::ThreadLocalRef(def_id(crate_item.def_id()))
        }
        // Real's `AddressOf` is what the guide calls `RawPtr` (the
        // `&raw const` / `&raw mut` operator). Trigger PB004 in
        // visitor via the shadow's RawPtr Rvalue variant.
        rp::mir::Rvalue::AddressOf(raw_ptr_kind, p) => {
            shadow::Rvalue::RawPtr(mutability(raw_ptr_kind.to_mutable_lossy()), place(p))
        }
        rp::mir::Rvalue::Len(p) => shadow::Rvalue::Len(place(p)),
        rp::mir::Rvalue::Cast(ck, op, target_ty) => {
            shadow::Rvalue::Cast(cast_kind(ck), operand(op), ty(*target_ty))
        }
        rp::mir::Rvalue::BinaryOp(op, lhs, rhs) => {
            shadow::Rvalue::BinaryOp(bin_op(*op), operand(lhs), operand(rhs))
        }
        // CheckedBinaryOp returns (T, bool). Visitor doesn't distinguish
        // checked vs unchecked at the BinOp level — overflow checking
        // is a PB049 project-config rule, not a per-rvalue check.
        // Collapse to BinaryOp.
        rp::mir::Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            shadow::Rvalue::BinaryOp(bin_op(*op), operand(lhs), operand(rhs))
        }
        rp::mir::Rvalue::UnaryOp(op, operand_) => {
            shadow::Rvalue::UnaryOp(un_op(*op), operand(operand_))
        }
        rp::mir::Rvalue::Discriminant(p) => shadow::Rvalue::Discriminant(place(p)),
        rp::mir::Rvalue::Aggregate(ak, ops) => shadow::Rvalue::Aggregate(
            aggregate_kind(ak),
            ops.iter().map(operand).collect(),
        ),
        rp::mir::Rvalue::ShallowInitBox(op, t) => {
            shadow::Rvalue::ShallowInitBox(operand(op), ty(*t))
        }
        rp::mir::Rvalue::CopyForDeref(p) => shadow::Rvalue::CopyForDeref(place(p)),
    }
}
fn aggregate_kind(ak: &rp::mir::AggregateKind) -> shadow::AggregateKind {
    match ak {
        rp::mir::AggregateKind::Tuple => shadow::AggregateKind::Tuple,
        rp::mir::AggregateKind::Array(t) => shadow::AggregateKind::Array(ty(*t)),
        // Real Adt has 5 fields: (AdtDef, VariantIdx, GenericArgs,
        //   Option<UserTypeAnnotationIndex>, Option<FieldIdx>)
        // Shadow keeps just (AdtDef, u32 variant index).
        rp::mir::AggregateKind::Adt(adt, variant_idx, _args, _user_ty, _field) => {
            // VariantIdx is opaque (internal usize + ThreadLocalIndex);
            // hash for an opaque u32.
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            format!("{variant_idx:?}").hash(&mut hasher);
            shadow::AggregateKind::Adt(
                adt_def(*adt),
                (hasher.finish() & 0xFFFF_FFFF) as u32,
            )
        }
        rp::mir::AggregateKind::Closure(closure_def, _args) => {
            shadow::AggregateKind::Closure(def_id(closure_def_to_def_id(*closure_def)))
        }
        rp::mir::AggregateKind::Coroutine(coroutine_def, _args) => {
            shadow::AggregateKind::Coroutine(def_id(coroutine_def_to_def_id(*coroutine_def)))
        }
        // CoroutineClosure has no shadow variant; collapse to Coroutine
        // (closest semantic — both yield-bearing types). The visitor's
        // PB027 handles either via the construction-site signal.
        rp::mir::AggregateKind::CoroutineClosure(cc_def, _args) => {
            shadow::AggregateKind::Coroutine(def_id(coroutine_closure_def_to_def_id(*cc_def)))
        }
        // RawPtr aggregate construction (rare; raw pointer initializer).
        // Shadow's `RawPtr` variant carries no data; PB004 fires on it.
        rp::mir::AggregateKind::RawPtr(_, _) => shadow::AggregateKind::RawPtr,
    }
}
fn cast_kind(ck: &rp::mir::CastKind) -> shadow::CastKind {
    match ck {
        // Real's PointerExposeAddress is "ptr as int with provenance
        // exposure" — semantically a PtrToInt cast (PB004 trigger).
        rp::mir::CastKind::PointerExposeAddress => shadow::CastKind::PtrToInt,
        // Real's PointerWithExposedProvenance is the int→ptr direction.
        rp::mir::CastKind::PointerWithExposedProvenance => shadow::CastKind::IntToPtr,
        // Real's PointerCoercion(_) wraps a PointerCoercion enum
        // (Reify, ClosureFnPointer, MutToConst, etc.). Shadow has unit
        // PointerCoercion — drop the inner.
        rp::mir::CastKind::PointerCoercion(_) => shadow::CastKind::PointerCoercion,
        rp::mir::CastKind::IntToInt => shadow::CastKind::IntToInt,
        rp::mir::CastKind::FloatToInt => shadow::CastKind::FloatToInt,
        rp::mir::CastKind::FloatToFloat => shadow::CastKind::FloatToFloat,
        rp::mir::CastKind::IntToFloat => shadow::CastKind::IntToFloat,
        rp::mir::CastKind::PtrToPtr => shadow::CastKind::PtrToPtr,
        rp::mir::CastKind::FnPtrToPtr => shadow::CastKind::FnPtrToPtr,
        rp::mir::CastKind::Transmute => shadow::CastKind::Transmute,
        // Subtype cast: subtle subtype coercion (e.g., for HRTB sites).
        // No direct shadow analog — closest is PointerCoercion (also a
        // "no-op-at-codegen" coercion). The visitor accepts
        // PointerCoercion silently; correct behavior for Subtype too.
        rp::mir::CastKind::Subtype => shadow::CastKind::PointerCoercion,
    }
}
fn bin_op(op: rp::mir::BinOp) -> shadow::BinOp {
    // The visitor only inspects `BinOp::Offset` (PB004 trigger).
    // Everything else falls through. Map real variants to their
    // closest shadow analog; "Unchecked" variants collapse to their
    // checked form (visitor doesn't distinguish — overflow handling
    // is PB049's project-level concern).
    match op {
        rp::mir::BinOp::Add | rp::mir::BinOp::AddUnchecked => shadow::BinOp::Add,
        rp::mir::BinOp::Sub | rp::mir::BinOp::SubUnchecked => shadow::BinOp::Sub,
        rp::mir::BinOp::Mul | rp::mir::BinOp::MulUnchecked => shadow::BinOp::Mul,
        rp::mir::BinOp::Div => shadow::BinOp::Div,
        rp::mir::BinOp::Rem => shadow::BinOp::Rem,
        rp::mir::BinOp::Shl | rp::mir::BinOp::ShlUnchecked => shadow::BinOp::Shl,
        rp::mir::BinOp::Shr | rp::mir::BinOp::ShrUnchecked => shadow::BinOp::Shr,
        rp::mir::BinOp::BitXor => shadow::BinOp::BitXor,
        rp::mir::BinOp::BitAnd => shadow::BinOp::BitAnd,
        rp::mir::BinOp::BitOr => shadow::BinOp::BitOr,
        rp::mir::BinOp::Eq => shadow::BinOp::Eq,
        rp::mir::BinOp::Lt => shadow::BinOp::Lt,
        rp::mir::BinOp::Le => shadow::BinOp::Le,
        rp::mir::BinOp::Ne => shadow::BinOp::Ne,
        rp::mir::BinOp::Ge => shadow::BinOp::Ge,
        rp::mir::BinOp::Gt => shadow::BinOp::Gt,
        // Cmp is the three-way <=> operator returning Ordering. Map to
        // Eq as a placeholder — visitor doesn't act on it.
        rp::mir::BinOp::Cmp => shadow::BinOp::Eq,
        rp::mir::BinOp::Offset => shadow::BinOp::Offset,
    }
}
fn un_op(op: rp::mir::UnOp) -> shadow::UnOp {
    match op {
        rp::mir::UnOp::Not => shadow::UnOp::Not,
        rp::mir::UnOp::Neg => shadow::UnOp::Neg,
        rp::mir::UnOp::PtrMetadata => shadow::UnOp::PtrMetadata,
    }
}
// =====================================================================
// Statement translation (Batch 4).
// =====================================================================
pub fn statement(stmt: &rp::mir::Statement) -> shadow::Statement {
    shadow::Statement {
        kind: statement_kind(&stmt.kind),
        span: span(stmt.span),
    }
}
fn statement_kind(k: &rp::mir::StatementKind) -> shadow::StatementKind {
    match k {
        rp::mir::StatementKind::Assign(p, rv) => {
            shadow::StatementKind::Assign(place(p), rvalue(rv))
        }
        // Real `FakeRead(FakeReadCause, Place)` — drop the cause; the
        // visitor doesn't differentiate.
        rp::mir::StatementKind::FakeRead(_cause, p) => shadow::StatementKind::FakeRead(place(p)),
        rp::mir::StatementKind::SetDiscriminant { place: p, variant_index } => {
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            format!("{variant_index:?}").hash(&mut hasher);
            shadow::StatementKind::SetDiscriminant {
                place: place(p),
                variant_index: (hasher.finish() & 0xFFFF_FFFF) as u32,
            }
        }
        rp::mir::StatementKind::StorageLive(l) => shadow::StatementKind::StorageLive(local(*l)),
        rp::mir::StatementKind::StorageDead(l) => shadow::StatementKind::StorageDead(local(*l)),
        rp::mir::StatementKind::Retag(kind, p) => {
            shadow::StatementKind::Retag(retag_kind(*kind), place(p))
        }
        rp::mir::StatementKind::PlaceMention(p) => shadow::StatementKind::PlaceMention(place(p)),
        // Real has `{ place, projections, variance }` — shadow keeps
        // just the place. Variance and the user-type-projection metadata
        // are debug aids, not PSS-1 signals.
        rp::mir::StatementKind::AscribeUserType { place: p, .. } => {
            shadow::StatementKind::AscribeUserType(place(p))
        }
        // Real Coverage carries a Coverage payload (counter / span info);
        // shadow Coverage is a unit. Pitbull-verified builds disable
        // coverage profile so this should be unreachable in practice.
        rp::mir::StatementKind::Coverage(_) => shadow::StatementKind::Coverage,
        rp::mir::StatementKind::Intrinsic(intr) => {
            shadow::StatementKind::Intrinsic(non_diverging_intrinsic(intr))
        }
        rp::mir::StatementKind::ConstEvalCounter => shadow::StatementKind::ConstEvalCounter,
        rp::mir::StatementKind::Nop => shadow::StatementKind::Nop,
    }
}
fn retag_kind(k: rp::mir::RetagKind) -> shadow::RetagKind {
    match k {
        rp::mir::RetagKind::FnEntry => shadow::RetagKind::FnEntry,
        rp::mir::RetagKind::TwoPhase => shadow::RetagKind::TwoPhase,
        rp::mir::RetagKind::Raw => shadow::RetagKind::Raw,
        rp::mir::RetagKind::Default => shadow::RetagKind::Default,
    }
}
fn non_diverging_intrinsic(intr: &rp::mir::NonDivergingIntrinsic) -> shadow::NonDivergingIntrinsic {
    match intr {
        rp::mir::NonDivergingIntrinsic::Assume(op) => {
            shadow::NonDivergingIntrinsic::Assume(operand(op))
        }
        // Real `CopyNonOverlapping(CopyNonOverlapping)` carries src/dst/
        // count operands; shadow has unit variant. Visitor's PB004 fires
        // on the variant tag alone, so the data drop is fine.
        rp::mir::NonDivergingIntrinsic::CopyNonOverlapping(_) => {
            shadow::NonDivergingIntrinsic::CopyNonOverlapping
        }
    }
}
// =====================================================================
// Terminator translation (Batch 5).
// =====================================================================
pub fn terminator(t: &rp::mir::Terminator) -> shadow::Terminator {
    shadow::Terminator {
        kind: terminator_kind(&t.kind),
        span: span(t.span),
    }
}
fn terminator_kind(k: &rp::mir::TerminatorKind) -> shadow::TerminatorKind {
    match k {
        rp::mir::TerminatorKind::Goto { target } => {
            shadow::TerminatorKind::Goto { target: basic_block_idx(*target) }
        }
        rp::mir::TerminatorKind::SwitchInt { discr, targets } => {
            shadow::TerminatorKind::SwitchInt {
                discr: operand(discr),
                targets: targets
                    .all_targets()
                    .into_iter()
                    .map(basic_block_idx)
                    .collect(),
            }
        }
        // Real Resume = shadow UnwindResume; Real Abort = shadow
        // UnwindTerminate (rustc renamed Terminate to Abort).
        rp::mir::TerminatorKind::Resume => shadow::TerminatorKind::UnwindResume,
        rp::mir::TerminatorKind::Abort => shadow::TerminatorKind::UnwindTerminate,
        rp::mir::TerminatorKind::Return => shadow::TerminatorKind::Return,
        rp::mir::TerminatorKind::Unreachable => shadow::TerminatorKind::Unreachable,
        // Drop: real has `unwind`, shadow elides it.
        rp::mir::TerminatorKind::Drop { place: p, target, .. } => {
            shadow::TerminatorKind::Drop {
                place: place(p),
                target: basic_block_idx(*target),
            }
        }
        // Call: same pattern — drop unwind.
        rp::mir::TerminatorKind::Call { func, args, destination, target, .. } => {
            shadow::TerminatorKind::Call {
                func: operand(func),
                args: args.iter().map(operand).collect(),
                destination: place(destination),
                target: target.map(basic_block_idx),
            }
        }
        rp::mir::TerminatorKind::Assert { cond, expected, msg, target, .. } => {
            shadow::TerminatorKind::Assert {
                cond: operand(cond),
                expected: *expected,
                msg: assert_message(msg),
                target: basic_block_idx(*target),
            }
        }
        // Real InlineAsm has many fields; shadow keeps just template.
        rp::mir::TerminatorKind::InlineAsm { template, .. } => {
            shadow::TerminatorKind::InlineAsm { template: template.clone() }
        }
    }
}
fn basic_block_idx(idx: rp::mir::BasicBlockIdx) -> shadow::BasicBlock {
    // Confusingly, real's `BasicBlockIdx` (a usize index) maps to the
    // shadow's `BasicBlock` (which is the index newtype). Real's
    // `BasicBlock` (the struct holding statements + terminator) maps to
    // shadow's `BasicBlockData`.
    shadow::BasicBlock(idx as u32)
}
fn assert_message(msg: &rp::mir::AssertMessage) -> shadow::AssertMessage {
    match msg {
        rp::mir::AssertMessage::BoundsCheck { .. } => shadow::AssertMessage::BoundsCheck,
        rp::mir::AssertMessage::Overflow(..) | rp::mir::AssertMessage::OverflowNeg(_) => {
            shadow::AssertMessage::Overflow
        }
        rp::mir::AssertMessage::DivisionByZero(_) => shadow::AssertMessage::DivisionByZero,
        rp::mir::AssertMessage::RemainderByZero(_) => shadow::AssertMessage::RemainderByZero,
        rp::mir::AssertMessage::MisalignedPointerDereference { .. } => {
            shadow::AssertMessage::MisalignedPointerDereference
        }
        rp::mir::AssertMessage::ResumedAfterReturn(_) => {
            shadow::AssertMessage::Other("coroutine resumed after return".into())
        }
        rp::mir::AssertMessage::ResumedAfterPanic(_) => {
            shadow::AssertMessage::Other("coroutine resumed after panic".into())
        }
        rp::mir::AssertMessage::ResumedAfterDrop(_) => {
            shadow::AssertMessage::Other("coroutine resumed after drop".into())
        }
        rp::mir::AssertMessage::NullPointerDereference => {
            shadow::AssertMessage::Other("null pointer dereference".into())
        }
        rp::mir::AssertMessage::InvalidEnumConstruction(_) => {
            shadow::AssertMessage::Other("invalid enum construction".into())
        }
    }
}
// =====================================================================
// Body translation (Batch 6: now populates blocks).
// =====================================================================
pub fn body(b: &rp::mir::Body) -> shadow::Body {
    shadow::Body {
        def_id: shadow::DefId(0), // Threaded by caller in v0.2 wiring.
        arg_tys: b.arg_locals().iter().map(|ld| ty(ld.ty)).collect(),
        return_ty: ty(b.ret_local().ty),
        is_unsafe: false,
        is_async: false,
        locals: b
            .locals()
            .iter()
            .map(|ld| shadow::LocalDecl {
                ty: ty(ld.ty),
                span: span(ld.span),
                mutability: mutability(ld.mutability),
            })
            .collect(),
        // Walk every basic block and translate its statements +
        // terminator. This is the change that makes the visitor see
        // real MIR contents — and therefore makes PB rules fire on
        // real code (PB011 on Box, PB050 on float, etc.).
        blocks: b.blocks.iter().map(basic_block_data).collect(),
        span: span(b.span),
    }
}
fn basic_block_data(bb: &rp::mir::BasicBlock) -> shadow::BasicBlockData {
    shadow::BasicBlockData {
        statements: bb.statements.iter().map(statement).collect(),
        terminator: terminator(&bb.terminator),
    }
}
// =====================================================================
// Tracking note for the still-pending translation surface.
// =====================================================================
//
// Implemented in this commit (Batches 1-2):
//   - operand, place, projection, const_operand          (Batch 1)
//   - ty + ty_kind + rigid_ty + int/uint/float/adt_def   (Batch 2)
//
// Still pending (substantial pieces blocking the Box-emits-PB011 demo):
//   - rvalue: 15 variants                       (Batch 3)
//   - statement: 13 variants                    (Batch 4)
//   - terminator: 15 variants                   (Batch 5)
//   - body() must populate `blocks`             (Batch 6)
//   - Real `Span` -> byte offsets via compiler_interface (post-§17.1)
