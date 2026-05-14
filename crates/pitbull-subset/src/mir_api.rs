//! Single import surface for `rustc_public` (StableMIR).
//!
//! The rest of the crate refers to MIR types through the re-exports here.
//! If the upstream `rustc_public` API shifts shape, this module is the only
//! place that needs to change. This isolation is part of our soundness
//! posture: the `unsafe`-free, audited subset checker depends on a stable
//! interface, not on internal rustc data structures.
//!
//! ## Stability note
//!
//! As of this writing, `rustc_public` is the migration target API for tools
//! formerly using internal rustc crates. The crate is not yet stabilized on
//! stable Rust; it is exposed through the nightly toolchain via the
//! `rustc_private` mechanism. Both Kani and Creusot are migrating to this
//! surface; Pitbull rides the same migration.
//!
//! When upstream stabilizes, we drop the nightly pin from `rust-toolchain.toml`
//! and this module becomes trivial re-exports.
// The full `rustc_public` surface is enormous. We re-export only what the
// subset visitor actually needs, and we name the imports explicitly to avoid
// star-imports masking version-skew breakage.
#[cfg(rustc_public_real)]
pub use rustc_public::{
    mir::{
        BasicBlock, BinOp, Body, Local, LocalDecl, Mutability, NullOp, Operand,
        Place, ProjectionElem, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind, UnOp,
    },
    ty::{AdtDef, FnDef, GenericArgs, IntTy, RigidTy, Ty, TyKind, UintTy},
    CrateDef, DefId, Span,
};
// -----------------------------------------------------------------------------
// Shadow types for testing and out-of-toolchain builds.
//
// When the `rustc-public-real` feature is off, we expose minimal shadow types
// that mirror the rustc_public API surface so that the subset crate compiles
// in isolation (and so its tests can run without a nightly toolchain).
//
// These shadows are *not* used in production verification; they exist solely
// to let `cargo check` work in the CI lane that builds against stable Rust,
// and to support the mutation-testing harness, which fabricates MIR-shaped
// inputs to exercise the visitor.
// -----------------------------------------------------------------------------
#[cfg(not(rustc_public_real))]
mod shadow {
    // The shadow types mirror the rustc_public surface variant-for-variant.
    // Per-field documentation on the named variants of TerminatorKind,
    // ProjectionElem, etc. would be busywork that obscures the dispatch
    // shape — and these types are dead code under `cfg(rustc_public_real)`,
    // where the real rustc_public re-exports take over. Allow missing docs
    // inside the shadow module only; the public re-exports below remain
    // subject to the workspace's `missing_docs = "warn"` policy.
    #![allow(missing_docs)]
    use serde::{Deserialize, Serialize};
    /// Source span. Mirror of `rustc_public::Span`.
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
    pub struct Span {
        /// Byte offset of the start of the span.
        pub lo: u32,
        /// Byte offset of the end of the span.
        pub hi: u32,
        /// File identifier.
        pub file: u32,
    }
    impl Default for Span {
        fn default() -> Self {
            Self { lo: 0, hi: 0, file: 0 }
        }
    }
    /// Definition identifier. Mirror of `rustc_public::DefId`.
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
    pub struct DefId(pub u64);
    /// Mutability of a reference or local.
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    pub enum Mutability {
        /// `&T` reference / `let` binding.
        Not,
        /// `&mut T` reference / `let mut` binding.
        Mut,
    }
    /// Local variable index in a MIR body.
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    pub struct Local(pub u32);
    /// Basic block index.
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    pub struct BasicBlock(pub u32);
    /// Type, shadow form. Only the shape needed for subset detection.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Ty {
        /// The kind discriminator.
        pub kind: TyKind,
    }
    /// Shadow `TyKind`. The full upstream variant set is much larger; we
    /// expose only the shape the visitor inspects.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum TyKind {
        /// A rigid (fully resolved) type.
        RigidTy(RigidTy),
        /// A type parameter still in scope (should not appear post-mono).
        Param(String),
        /// Bound by a `dyn Trait` existential.
        Dynamic,
    }
    /// Shadow rigid types. Matches the subset of `rustc_public::ty::RigidTy`
    /// the visitor pattern-matches on.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum RigidTy {
        /// `bool`.
        Bool,
        /// `char`.
        Char,
        /// Signed integer.
        Int(IntTy),
        /// Unsigned integer.
        Uint(UintTy),
        /// Floating-point.
        Float(FloatTy),
        /// `&T` / `&mut T`.
        Ref(Mutability, Box<Ty>),
        /// `*const T` / `*mut T`.
        RawPtr(Mutability, Box<Ty>),
        /// `[T; N]` array.
        Array(Box<Ty>, u64),
        /// `[T]` slice.
        Slice(Box<Ty>),
        /// `(T1, T2, ...)` tuple.
        Tuple(Vec<Ty>),
        /// `fn(...) -> ...` function pointer.
        FnPtr,
        /// `fn` item def (statically known target).
        FnDef(DefId),
        /// Closure type (anonymous).
        Closure(DefId),
        /// Algebraic data type (struct / enum / union).
        Adt(AdtDef),
    }
    /// Signed integer width.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum IntTy { Isize, I8, I16, I32, I64, I128 }
    /// Unsigned integer width.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum UintTy { Usize, U8, U16, U32, U64, U128 }
    /// Floating-point width.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum FloatTy { F16, F32, F64, F128 }
    /// ADT definition shadow. Stores the type's fully-qualified path so the
    /// visitor can do path-matching against the standard library.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct AdtDef {
        /// Crate-qualified path, e.g. `"alloc::vec::Vec"`.
        pub path: String,
        /// Whether this is a union (PB005).
        pub is_union: bool,
    }
    // -------------------------------------------------------------------------
    // MIR body, blocks, statements, terminators.
    // -------------------------------------------------------------------------
    /// A MIR function body. Shadow form.
    #[derive(Clone, Debug)]
    pub struct Body {
        /// The function this body belongs to.
        pub def_id: DefId,
        /// Signature: argument types, return type.
        pub arg_tys: Vec<Ty>,
        /// Return type.
        pub return_ty: Ty,
        /// Whether the function is declared `unsafe`.
        pub is_unsafe: bool,
        /// Local declarations.
        pub locals: Vec<LocalDecl>,
        /// Basic blocks indexed by `BasicBlock`.
        pub blocks: Vec<BasicBlockData>,
        /// Whether the function is `async`.
        pub is_async: bool,
        /// Source span of the body.
        pub span: Span,
    }
    /// Declaration of a single local variable.
    #[derive(Clone, Debug)]
    pub struct LocalDecl {
        /// Local's type.
        pub ty: Ty,
        /// Source span.
        pub span: Span,
        /// Mutability.
        pub mutability: Mutability,
    }
    /// Contents of a basic block.
    #[derive(Clone, Debug)]
    pub struct BasicBlockData {
        /// Statements in the block.
        pub statements: Vec<Statement>,
        /// The terminator that ends the block.
        pub terminator: Terminator,
    }
    /// A MIR statement with its span.
    #[derive(Clone, Debug)]
    pub struct Statement {
        /// What the statement does.
        pub kind: StatementKind,
        /// Source span.
        pub span: Span,
    }
    /// MIR statement kinds. Mirror of `rustc_public::mir::StatementKind`.
    ///
    /// 13 variants, as of current nightly rustc.
    #[derive(Clone, Debug)]
    pub enum StatementKind {
        /// `place = rvalue`.
        Assign(Place, Rvalue),
        /// Pattern-match read for borrowck.
        FakeRead(Place),
        /// `SetDiscriminant(place, variant)`.
        SetDiscriminant { place: Place, variant_index: u32 },
        /// Deinitialize a place (drop elaboration).
        Deinit(Place),
        /// Mark a local as live (storage start).
        StorageLive(Local),
        /// Mark a local as dead (storage end).
        StorageDead(Local),
        /// Retag for aliasing-model purposes (PB009 signal).
        Retag(RetagKind, Place),
        /// Mention a place without reading it.
        PlaceMention(Place),
        /// Ascribe a user-written type annotation.
        AscribeUserType(Place),
        /// Coverage instrumentation.
        Coverage,
        /// Non-diverging intrinsic (e.g. `assume`).
        Intrinsic(NonDivergingIntrinsic),
        /// Const-eval cycle counter.
        ConstEvalCounter,
        /// No-op.
        Nop,
    }
    /// Kind of a retag operation.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum RetagKind {
        /// Standard retag.
        Default,
        /// Function entry retag.
        FnEntry,
        /// Two-phase borrow retag.
        TwoPhase,
        /// Raw retag.
        Raw,
    }
    /// Non-diverging intrinsic.
    #[derive(Clone, Debug)]
    pub enum NonDivergingIntrinsic {
        /// `assume(cond)`.
        Assume(Operand),
        /// `copy_nonoverlapping`.
        CopyNonOverlapping,
    }
    /// A MIR terminator with its span.
    #[derive(Clone, Debug)]
    pub struct Terminator {
        /// What the terminator does.
        pub kind: TerminatorKind,
        /// Source span.
        pub span: Span,
    }
    /// MIR terminator kinds. Mirror of `rustc_public::mir::TerminatorKind`.
    ///
    /// 15 variants, as of current nightly rustc.
    #[derive(Clone, Debug)]
    pub enum TerminatorKind {
        /// Unconditional jump.
        Goto { target: BasicBlock },
        /// Switch on an integer.
        SwitchInt { discr: Operand, targets: Vec<BasicBlock> },
        /// Resume an unwind in progress.
        UnwindResume,
        /// Terminate due to a panic during unwind.
        UnwindTerminate,
        /// Return from the function.
        Return,
        /// Unreachable code (verifier must prove this).
        Unreachable,
        /// Drop a value.
        Drop { place: Place, target: BasicBlock },
        /// Function call.
        Call {
            /// The callee.
            func: Operand,
            /// Arguments.
            args: Vec<Operand>,
            /// Where to store the result.
            destination: Place,
            /// Continuation block (None means diverging).
            target: Option<BasicBlock>,
        },
        /// Tail call (`become` keyword).
        TailCall { func: Operand, args: Vec<Operand> },
        /// Runtime assertion (overflow, OOB, etc.).
        Assert { cond: Operand, expected: bool, msg: AssertMessage, target: BasicBlock },
        /// Coroutine yield.
        Yield { value: Operand, resume: BasicBlock },
        /// Coroutine drop.
        CoroutineDrop,
        /// Borrowck-only edge (should not appear post-cleanup).
        FalseEdge { real_target: BasicBlock },
        /// Borrowck-only unwind (should not appear post-cleanup).
        FalseUnwind { real_target: BasicBlock },
        /// Inline assembly.
        InlineAsm { template: String },
    }
    /// What an `Assert` terminator checks. Used to classify panics.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum AssertMessage {
        /// Integer overflow.
        Overflow,
        /// Division by zero.
        DivisionByZero,
        /// Remainder by zero.
        RemainderByZero,
        /// Slice index out of bounds.
        BoundsCheck,
        /// Misaligned pointer.
        MisalignedPointerDereference,
        /// Other (user-provided message).
        Other(String),
    }
    // -------------------------------------------------------------------------
    // Rvalues, Operands, Places.
    // -------------------------------------------------------------------------
    /// A MIR place expression.
    #[derive(Clone, Debug)]
    pub struct Place {
        /// The base local.
        pub local: Local,
        /// Field, deref, index projections.
        pub projection: Vec<ProjectionElem>,
    }
    /// A projection on a place.
    #[derive(Clone, Debug)]
    pub enum ProjectionElem {
        /// `*place`.
        Deref,
        /// `place.field`.
        Field(u32),
        /// `place[i]`.
        Index(Local),
        /// `place[constant]`.
        ConstantIndex { offset: u64 },
        /// `place[a..b]`.
        Subslice { from: u64, to: u64 },
        /// Downcast to an enum variant.
        Downcast(u32),
        /// Opaque cast.
        OpaqueCast(Ty),
        /// Subtype.
        Subtype(Ty),
    }
    /// A MIR operand (rvalue argument).
    #[derive(Clone, Debug)]
    pub enum Operand {
        /// Copy from a place.
        Copy(Place),
        /// Move from a place.
        Move(Place),
        /// Constant.
        Constant(ConstOperand),
    }
    /// A MIR constant operand.
    #[derive(Clone, Debug)]
    pub struct ConstOperand {
        /// Type of the constant.
        pub ty: Ty,
        /// User-defined definition (for fn item constants).
        pub def_id: Option<DefId>,
        /// Fully-qualified path string, if this constant resolves to a
        /// named item (e.g. `"core::panicking::panic_fmt"`).
        ///
        /// In the shadow build, this field is set by the test fixture
        /// when constructing a synthetic call site. In the real build,
        /// this field is populated by the rustc_public adapter from the
        /// resolved `DefId`.
        pub path: Option<String>,
    }
    /// MIR rvalues. Mirror of `rustc_public::mir::Rvalue`.
    ///
    /// 15 variants, as of current nightly rustc.
    #[derive(Clone, Debug)]
    pub enum Rvalue {
        /// Use of an operand.
        Use(Operand),
        /// Repeat (`[x; N]`).
        Repeat(Operand, u64),
        /// `&place` or `&mut place`.
        Ref(Mutability, Place),
        /// Reference to a thread-local static (PB019 signal).
        ThreadLocalRef(DefId),
        /// `&raw const place` or `&raw mut place` (PB004 signal).
        RawPtr(Mutability, Place),
        /// `place.len()` (slice length).
        Len(Place),
        /// Cast: `as`, ptr-to-int, int-to-ptr, etc.
        Cast(CastKind, Operand, Ty),
        /// Binary operation.
        BinaryOp(BinOp, Operand, Operand),
        /// Operation on type properties (e.g. `size_of`).
        NullaryOp(NullOp, Ty),
        /// Unary operation.
        UnaryOp(UnOp, Operand),
        /// Discriminant extraction.
        Discriminant(Place),
        /// Aggregate construction (tuple, array, struct, enum).
        Aggregate(AggregateKind, Vec<Operand>),
        /// Shallow-init `Box<T>` (PB013 signal).
        ShallowInitBox(Operand, Ty),
        /// Copy from a deref-eligible place.
        CopyForDeref(Place),
        /// Wrap a value in an unsafe binder.
        WrapUnsafeBinder(Operand, Ty),
    }
    /// Cast kinds, for PB051 detection.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum CastKind {
        /// `int as int`.
        IntToInt,
        /// `float as int`.
        FloatToInt,
        /// `int as float`.
        IntToFloat,
        /// `float as float`.
        FloatToFloat,
        /// Pointer to int.
        PtrToInt,
        /// Int to pointer.
        IntToPtr,
        /// Pointer to pointer.
        PtrToPtr,
        /// Function pointer to pointer.
        FnPtrToPtr,
        /// `core::mem::transmute` (PB007 signal).
        Transmute,
        /// Pointer-coercion (auto-borrow, unsize, etc.).
        PointerCoercion,
    }
    /// Binary operator.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum BinOp {
        /// `+`.
        Add,
        /// `-`.
        Sub,
        /// `*`.
        Mul,
        /// `/`.
        Div,
        /// `%`.
        Rem,
        /// `<<`.
        Shl,
        /// `>>`.
        Shr,
        /// `&`.
        BitAnd,
        /// `|`.
        BitOr,
        /// `^`.
        BitXor,
        /// `==`.
        Eq,
        /// `<`.
        Lt,
        /// `<=`.
        Le,
        /// `!=`.
        Ne,
        /// `>=`.
        Ge,
        /// `>`.
        Gt,
        /// Pointer offset (PB004-adjacent).
        Offset,
    }
    /// Nullary operator.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum NullOp {
        /// `size_of::<T>()`.
        SizeOf,
        /// `align_of::<T>()`.
        AlignOf,
        /// `offset_of`.
        OffsetOf,
        /// `ubchecks` toggle.
        UbChecks,
    }
    /// Unary operator.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum UnOp {
        /// `!`.
        Not,
        /// `-`.
        Neg,
        /// `PtrMetadata` extraction.
        PtrMetadata,
    }
    /// Kind of aggregate value being constructed.
    #[derive(Clone, Debug)]
    pub enum AggregateKind {
        /// Tuple `(a, b, c)`.
        Tuple,
        /// `[a, b, c]`.
        Array(Ty),
        /// Struct / enum literal.
        Adt(AdtDef, u32),
        /// Closure capture environment (PB033 signal).
        Closure(DefId),
        /// Coroutine state (PB027 signal).
        Coroutine(DefId),
        /// `RawPtr` aggregate (raw pointer construction).
        RawPtr,
    }
}
#[cfg(not(rustc_public_real))]
pub use shadow::{
    AdtDef, AggregateKind, AssertMessage, BasicBlock, BasicBlockData, BinOp, Body, CastKind,
    ConstOperand, DefId, FloatTy, IntTy, Local, LocalDecl, Mutability, NonDivergingIntrinsic,
    NullOp, Operand, Place, ProjectionElem, RetagKind, RigidTy, Rvalue, Span, Statement,
    StatementKind, Terminator, TerminatorKind, Ty, TyKind, UintTy, UnOp,
};
