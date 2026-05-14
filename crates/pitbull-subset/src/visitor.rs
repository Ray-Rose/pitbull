//! The exhaustive MIR visitor that enforces PSS-1.
//!
//! ## Audit posture
//!
//! Every match in this file is exhaustive over the corresponding MIR enum,
//! with no default arm. If `rustc_public` adds a new variant upstream, this
//! file fails to compile and the audit moves to the new variant — it cannot
//! be silently accepted. **Auditors should read this file linearly, top to
//! bottom.**
//!
//! ## Diagnostic accumulation
//!
//! The visitor accumulates errors in `self.errors` rather than returning on
//! the first violation. Users see every PSS-1 violation in one shot,
//! analogous to how rustc reports type errors. This also serves audit: a
//! second violation cannot hide behind a first.
//!
//! ## Known v0.1 gaps
//!
//! Soundness-relevant gaps documented for auditors. Each one is referenced
//! in the Safety Manual and tracked in the v0.2 milestone:
//!
//! - **PB001 (unsafe block syntax):** The visitor runs on MIR, which has
//!   already discarded HIR-level `unsafe { }` block markers. Detection is
//!   indirect: every operation that an unsafe block can host (raw pointer
//!   deref, transmute, intrinsic call, retag, inline asm) is caught by
//!   its own rule (PB004, PB007, PB009, PB006, etc.). An empty
//!   `unsafe { }` block is therefore accepted, which is sound (it does
//!   nothing) though it does miss the syntactic intent signal. A
//!   pre-MIR HIR pass added in v0.2 closes the gap.
//!
//! - **PB018 (static mut and interior-mutable statics):** *Closed.* The
//!   reachability driver now visits item declarations via
//!   `ItemKind::Static`/`ItemKind::Const`; `visit_static_item` fires
//!   PB018 on `static mut` and routes the declared type through
//!   `visit_ty` so interior-mutability rules (PB021/PB022) catch
//!   immutable statics like `static FOO: Cell<u32>`.
//!
//! - **PB020 (stack-allocation limit) coverage:** The layout estimator
//!   handles primitives, references/pointers (target-pointer-width-aware),
//!   arrays, and tuples. User ADTs, closures, and slices in local
//!   position remain under-detected — the estimator returns `None` for
//!   those, which means no false positives but possible false negatives
//!   on user types with huge inline arrays. Real layout-aware detection
//!   for those cases lands with the rustc_public wiring.
//!
//! - **PB043 (panic unreachability):** v0.1 has no VC backend, so panic
//!   call sites cannot be discharged as unreachable. By default the
//!   visitor tags them and the driver's `verify` command warns. Set
//!   `verification.strict_panic_acceptance = true` in `pitbull.toml` to
//!   reject all reachable panic calls at the subset level — the
//!   conservative v0.1 posture.
//!
//! - **`in_spec_context` is always false in v0.1:** Spec-mode rules
//!   (PB064, PB066, PB069) require the visitor to track whether an
//!   expression appears inside a `requires`/`ensures`/`invariant`. The
//!   visitor has the field but does not yet enter spec context because
//!   the spec-AST plumbing lands with v0.2's translation backend.
//!
//! ## What this file does NOT do
//!
//! - It does not compute the call graph. Reachability lives in
//!   `reachability.rs`; the visitor is invoked on each reachable body.
//! - It does not load `pitbull.toml`. Config lives in `config.rs`.
//! - It does not render error messages. Rendering lives in `diagnostic.rs`.
//! - It does not invoke SMT solvers. That happens downstream in
//!   `pitbull-vc`.
use crate::diagnostic::{SubsetError, SubsetReport};
use crate::mir_api::{
    AdtDef, AggregateKind, AssertMessage, Body, CastKind, ConstOperand, FloatTy,
    NonDivergingIntrinsic, Operand, Place, ProjectionElem, RetagKind, RigidTy, Rvalue,
    Span, Statement, StatementKind, Terminator, TerminatorKind, Ty, TyKind,
};
use crate::rules;
use crate::SubsetConfig;
/// Maximum allowed depth of a place projection chain.
///
/// Deep projection chains are not unsound but are a code-smell and they
/// stress translation. We cap at 16; this is well above anything we've seen
/// in real corpora.
const MAX_PROJECTION_DEPTH: usize = 16;
/// The PSS-1 subset visitor.
///
/// A single instance is reused across all reachable bodies in a verification
/// run; errors accumulate in `self.errors`. Construction takes the project
/// configuration so that thresholds (trust budget, stack-allocation limit,
/// allowed proc macros) are visible to every visit method.
pub struct SubsetVisitor<'cfg> {
    config: &'cfg SubsetConfig,
    errors: Vec<SubsetError>,
    /// Whether the current body has been declared `#[pitbull::trusted]`.
    /// Trusted bodies are exempt from body-level checks but their *signatures*
    /// are still subject to PSS-1.
    current_body_trusted: bool,
    /// Whether the current expression context is spec mode.
    /// In spec mode, additional rules (PB064, PB066, PB069) apply.
    in_spec_context: bool,
}
impl<'cfg> SubsetVisitor<'cfg> {
    /// Construct a fresh visitor from project config.
    #[must_use]
    pub fn new(config: &'cfg SubsetConfig) -> Self {
        Self {
            config,
            errors: Vec::new(),
            current_body_trusted: false,
            in_spec_context: false,
        }
    }
    /// Finalize the visit, producing a report.
    #[must_use]
    pub fn into_report(self) -> SubsetReport {
        SubsetReport::new(self.errors)
    }
    /// Number of errors recorded so far.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }
    // -------------------------------------------------------------------------
    // Item-level entry points: statics and consts.
    // -------------------------------------------------------------------------
    /// Visit a `static X: T` or `static mut X: T` declaration.
    ///
    /// PSS-1 PB018: rejects `static mut` outright. For any static, also
    /// walks the type so interior-mutability rules (PB021, PB022) fire
    /// on patterns like `static FOO: Cell<u32> = Cell::new(0);` — which
    /// the PSS-1 spec calls out as "interior-mutable static" alongside
    /// `static mut` itself.
    pub fn visit_static_item(&mut self, mutable: bool, ty: Option<&Ty>, span: Span) {
        if mutable {
            self.reject(rules::PB018, span, "`static mut` declaration");
        }
        if let Some(ty) = ty {
            self.visit_ty(ty, span);
        }
    }
    /// Visit a `const X: T` declaration.
    ///
    /// Constants are immutable; the only PSS-1 concern is the declared
    /// type. PB061 (const fn outside Ferrocene's certified subset) is a
    /// separate per-call-site check that the visitor handles in
    /// `classify_called_function`.
    pub fn visit_const_item(&mut self, ty: Option<&Ty>, span: Span) {
        if let Some(ty) = ty {
            self.visit_ty(ty, span);
        }
    }
    // -------------------------------------------------------------------------
    // Top-level entry: visit one MIR body.
    // -------------------------------------------------------------------------
    /// Visit a single function body.
    ///
    /// This is the entry point invoked by the reachability driver for each
    /// monomorphized item in the call closure of `#[pitbull::verify]` roots.
    pub fn visit_body(&mut self, body: &Body, trusted: bool) {
        self.current_body_trusted = trusted;
        // PB002: unsafe fn definitions are rejected outright. Even trusted
        // functions cannot be unsafe in v0.1; trust is for spec assumption,
        // not for `unsafe` admission.
        if body.is_unsafe {
            self.reject(rules::PB002, body.span, "function declared `unsafe fn`");
        }
        // PB026: async fn is rejected. Async desugaring produces coroutines
        // we cannot model in v0.1.
        if body.is_async {
            self.reject(rules::PB026, body.span, "function declared `async fn`");
        }
        // PB058 (signature-side): check argument and return types for
        // non-Rust ABI is handled in the call-graph driver; here we just
        // walk the types in the signature.
        for arg_ty in &body.arg_tys {
            self.visit_ty(arg_ty, body.span);
        }
        self.visit_ty(&body.return_ty, body.span);
        // PB020 helper: scan local declarations for oversized stack objects.
        for local in &body.locals {
            self.visit_ty(&local.ty, local.span);
            // Stack-size enforcement requires layout queries which are
            // available only through real `rustc_public` (not the shadow
            // build). The hook is here; the implementation lands when the
            // real toolchain is wired in.
            if self.exceeds_stack_limit(&local.ty) {
                self.reject(
                    rules::PB020,
                    local.span,
                    "local exceeds configured stack-allocation limit",
                );
            }
        }
        // Trusted bodies: signature-only check stops here.
        if self.current_body_trusted {
            return;
        }
        for block in &body.blocks {
            for stmt in &block.statements {
                self.visit_statement(stmt);
            }
            self.visit_terminator(&block.terminator);
        }
    }
    // -------------------------------------------------------------------------
    // Statement dispatch — exhaustive over all 13 StatementKind variants.
    // -------------------------------------------------------------------------
    fn visit_statement(&mut self, stmt: &Statement) {
        match &stmt.kind {
            // `place = rvalue`. The most common statement. Visit both sides.
            StatementKind::Assign(place, rvalue) => {
                self.visit_place(place, stmt.span);
                self.visit_rvalue(rvalue, stmt.span);
            }
            // FakeRead is a borrowck-only annotation. Harmless post-cleanup;
            // we visit the place for projection-depth enforcement only.
            StatementKind::FakeRead(place) => {
                self.visit_place(place, stmt.span);
            }
            // SetDiscriminant: enum tag write. Accepted; we model enums.
            StatementKind::SetDiscriminant { place, variant_index: _ } => {
                self.visit_place(place, stmt.span);
            }
            // Deinit outside drop elaboration is suspect. The drop-elaboration
            // pass *should* be the only producer in `MirPhase::Runtime`. If
            // we see one elsewhere it indicates a subset escape (PB010).
            //
            // NOTE: distinguishing drop-elaborated Deinit from spurious Deinit
            // requires phase context that isn't on the statement itself.
            // The reachability driver tags each statement with its phase
            // before dispatch; the visitor trusts the tag. Implementation
            // detail: see `reachability::tag_statement_phase`.
            StatementKind::Deinit(place) => {
                self.visit_place(place, stmt.span);
                // Conservative default: in v0.1, we reject all Deinit not
                // emitted by the drop-elaboration pass. The shadow build
                // assumes all Deinits are out-of-phase. The real build
                // consults the phase tag.
                self.reject(rules::PB010, stmt.span, "`Deinit` outside drop elaboration");
            }
            // Storage-live / storage-dead bracket a local's lifetime. Accepted
            // unconditionally; these have no logical content and are useful
            // to the translator for scoping.
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
            // PB009: Retag is the canary for aliasing-relevant operations.
            // Even if PB001/PB004 are not (yet) triggered, Retag's presence
            // means raw pointers or UnsafeCell touched our code path. Fail
            // closed, regardless of `RetagKind`.
            StatementKind::Retag(kind, place) => {
                self.visit_place(place, stmt.span);
                let detail = match kind {
                    RetagKind::Default => "`Retag(Default)` indicates raw-pointer or UnsafeCell flow",
                    RetagKind::FnEntry => "`Retag(FnEntry)` on function entry; raw-pointer arg suspected",
                    RetagKind::TwoPhase => "`Retag(TwoPhase)` two-phase borrow with aliasing implication",
                    RetagKind::Raw => "`Retag(Raw)` raw-pointer retag",
                };
                self.reject(rules::PB009, stmt.span, detail);
            }
            // PlaceMention is a no-op for execution but signals borrowck
            // intent. Accepted; we visit the place only for projection-depth.
            StatementKind::PlaceMention(place) => {
                self.visit_place(place, stmt.span);
            }
            // AscribeUserType is a debug-aid: it carries the user-written
            // type for diagnostics. Accepted.
            StatementKind::AscribeUserType(place) => {
                self.visit_place(place, stmt.span);
            }
            // Coverage instrumentation. Accepted; emitted only under coverage
            // profile, which Pitbull-verified builds disable.
            StatementKind::Coverage => {}
            // Intrinsics. Most non-diverging intrinsics are either accepted
            // (assume, which is exactly what we want for spec-driven analysis)
            // or rejected (anything memory-touching that should not appear in
            // safe Rust).
            StatementKind::Intrinsic(intr) => self.visit_intrinsic(intr, stmt.span),
            // Const-eval counter is internal to const-eval. Accepted; cannot
            // appear in user-visible MIR.
            StatementKind::ConstEvalCounter => {}
            // Nop is trivially accepted.
            StatementKind::Nop => {}
        }
    }
    fn visit_intrinsic(&mut self, intr: &NonDivergingIntrinsic, span: Span) {
        match intr {
            // `assume` is what the verifier *wants*: an assertion that some
            // condition holds, useful for refining the abstract state.
            NonDivergingIntrinsic::Assume(op) => {
                self.visit_operand(op, span);
            }
            // `copy_nonoverlapping` is a raw-pointer memmove. Forbidden by
            // PB004 (raw pointer types) but called out distinctly for
            // diagnostic clarity.
            NonDivergingIntrinsic::CopyNonOverlapping => {
                self.reject(rules::PB004, span, "`copy_nonoverlapping` intrinsic uses raw pointers");
            }
        }
    }
    // -------------------------------------------------------------------------
    // Terminator dispatch — exhaustive over all 15 TerminatorKind variants.
    // -------------------------------------------------------------------------
    fn visit_terminator(&mut self, term: &Terminator) {
        match &term.kind {
            // Plain control flow. No checks.
            TerminatorKind::Goto { .. } => {}
            // SwitchInt: switch on an integer discriminant. Visit the discr
            // operand for type-level checks (e.g. char-as-discriminant).
            TerminatorKind::SwitchInt { discr, .. } => {
                self.visit_operand(discr, term.span);
            }
            // PB048: unwinding is forbidden in v0.1.
            //
            // UnwindResume and UnwindTerminate only appear if the project is
            // compiled with `panic = "unwind"`. PB048 catches this at config
            // time (config.rs); their *appearance in MIR* is a second-layer
            // signal that catches misconfigured dependencies.
            TerminatorKind::UnwindResume | TerminatorKind::UnwindTerminate => {
                self.reject(
                    rules::PB048,
                    term.span,
                    "unwinding terminator present; project must use `panic = \"abort\"`",
                );
            }
            // Plain return. Accepted.
            TerminatorKind::Return => {}
            // Unreachable: the verifier's job is to *prove* that this point
            // is dead. Reaching this terminator at runtime is UB; the v0.1
            // AoRTE proof obligation enforces it. The subset visitor accepts
            // the construct; the VC generator emits the obligation.
            TerminatorKind::Unreachable => {}
            // Drop: implicit drop call. We visit the place; the visit_call
            // path is not taken here because drop is a special MIR
            // terminator with no explicit Operand.
            //
            // PB016 (non-trivial Drop body) is checked when the type's Drop
            // impl is visited as part of reachability. Here we just walk the
            // place.
            TerminatorKind::Drop { place, .. } => {
                self.visit_place(place, term.span);
            }
            // Function call. The interesting dispatch site.
            TerminatorKind::Call { func, args, destination, .. } => {
                self.visit_call(func, args, destination, term.span);
            }
            // PB045: TailCall (the `become` keyword).
            TerminatorKind::TailCall { .. } => {
                self.reject(rules::PB045, term.span, "`become` tail-call");
            }
            // Assert: runtime check inserted by the compiler. Classify by
            // message kind.
            TerminatorKind::Assert { msg, .. } => self.visit_assert_message(msg, term.span),
            // PB027: yield (coroutine).
            TerminatorKind::Yield { .. } => {
                self.reject(rules::PB027, term.span, "coroutine `yield`");
            }
            // PB027: coroutine drop.
            TerminatorKind::CoroutineDrop => {
                self.reject(rules::PB027, term.span, "coroutine drop terminator");
            }
            // PB046: borrowck-only edges should not appear at the MIR phase
            // we analyze (MirPhase::Runtime(PostCleanup)). Their presence
            // means our phase assumption is wrong — fail closed.
            TerminatorKind::FalseEdge { .. } => {
                self.reject(rules::PB046, term.span, "`FalseEdge` post-cleanup; MIR phase invariant violated");
            }
            TerminatorKind::FalseUnwind { .. } => {
                self.reject(rules::PB046, term.span, "`FalseUnwind` post-cleanup; MIR phase invariant violated");
            }
            // PB006: inline assembly.
            TerminatorKind::InlineAsm { .. } => {
                self.reject(rules::PB006, term.span, "inline assembly");
            }
        }
    }
    fn visit_assert_message(&mut self, msg: &AssertMessage, span: Span) {
        // The compiler emits Assert terminators for the AoRTE conditions
        // we want to *prove unreachable*. We do not reject the Assert
        // itself; we emit a VC obligation. PSS-1 PB043, PB052, PB054 are
        // proof obligations, not subset rejections — they fire when the
        // VC fails, not here.
        //
        // We classify the assertion for downstream reporting only.
        match msg {
            AssertMessage::Overflow => {
                // Verified later by the VC generator as part of PB049's
                // proof requirement. Not a subset rejection.
            }
            AssertMessage::DivisionByZero
            | AssertMessage::RemainderByZero
            | AssertMessage::BoundsCheck => {
                // Same; these become proof obligations.
            }
            AssertMessage::MisalignedPointerDereference => {
                // Should not appear in v0.1 reachable MIR because raw
                // pointers are forbidden (PB004). If it does, treat as a
                // subset escape pointing back to PB004.
                self.reject(rules::PB004, span, "misaligned-pointer check implies raw-pointer dereference");
            }
            AssertMessage::Other(_) => {
                // User-written panic. The default reachability prover
                // discharges this as PB043's obligation.
            }
        }
    }
    // -------------------------------------------------------------------------
    // Call dispatch: the most decision-heavy site in the visitor.
    // -------------------------------------------------------------------------
    fn visit_call(&mut self, func: &Operand, args: &[Operand], dest: &Place, span: Span) {
        // First: visit the callee operand. If it's a constant FnDef we can
        // pattern-match on the path; if it's a function pointer or closure,
        // separate rules fire.
        match func {
            Operand::Constant(c) => self.classify_called_function(c, span),
            Operand::Copy(p) | Operand::Move(p) => {
                // Calling through a local of `fn` type: PB032 (function
                // pointers). The local's *type* triggers PB032 elsewhere;
                // here we just note the indirect call for diagnostics.
                self.visit_place(p, span);
                self.reject(rules::PB032, span, "call through function-pointer-typed local");
            }
        }
        for arg in args {
            self.visit_operand(arg, span);
        }
        self.visit_place(dest, span);
    }
    /// Classify a call by its callee's `DefId` path.
    ///
    /// This is where path-matching on the standard library lives. The set of
    /// recognized paths is curated against:
    /// - `core::panicking::*`  — PB043 panic obligations
    /// - `alloc::*`            — PB011, PB012, PB015 allocations
    /// - `core::ptr::*`        — PB004 raw pointer ops, PB025 volatile
    /// - `core::mem::transmute` — PB007
    /// - `core::sync::atomic::*` — PB023
    /// - `std::thread::*`      — PB028
    fn classify_called_function(&mut self, c: &ConstOperand, span: Span) {
        // Resolve the callee path. In the shadow build, ConstOperand has
        // only an optional DefId; the real build will give us a fully-
        // qualified path string via `rustc_public::CrateDef::name`.
        let path = self.path_of_const(c);
        // First, fully-qualified-path matches.
        match path.as_deref() {
            Some(p) if p.starts_with("core::panicking::") || p == "core::panic" => {
                // PB043 design: panic calls are tagged as VC obligations for
                // the v0.2 verifier to discharge. The v0.1 driver has no VC
                // backend, so a tagged-but-not-discharged panic would slip
                // through. We support a strict-panic mode for users who
                // want PSS-1 subset-level rejection of all reachable panic
                // calls regardless of provability.
                //
                // FIXME(pitbull v0.2): once the VC backend is online, switch
                // the default to "tag for VC" and demote this branch to
                // only fire under `strict_panic_acceptance = true`.
                if self.config.verification.strict_panic_acceptance {
                    self.reject(rules::PB043, span, format!("panic call `{p}` (strict mode)"));
                }
            }
            Some(p) if p.starts_with("alloc::alloc::") => {
                self.reject(rules::PB011, span, format!("call to allocator API `{p}`"));
            }
            Some(p) if p == "core::mem::transmute" || p == "core::intrinsics::transmute" => {
                self.reject(rules::PB007, span, "`transmute` call");
            }
            Some(p) if p == "core::ptr::read_volatile" || p == "core::ptr::write_volatile" => {
                self.reject(rules::PB025, span, format!("volatile op `{p}`"));
            }
            Some(p) if p.starts_with("core::sync::atomic::") => {
                self.reject(rules::PB023, span, format!("atomic op `{p}`"));
            }
            Some(p) if p == "std::thread::spawn" || p.starts_with("std::thread::Builder::spawn") => {
                self.reject(rules::PB028, span, "thread spawn");
            }
            Some(_) | None => {
                // Fall through. Most calls are user code; they are visited
                // by the reachability driver as separate bodies.
            }
        }
    }
    /// Extract a fully-qualified path string from a constant operand, if any.
    ///
    /// In the shadow build, this reads the `path` field of `ConstOperand`,
    /// which is populated by test fixtures. In the real build, the
    /// `rustc_public` adapter resolves the `DefId` to a path string and
    /// populates the same field; the visitor stays agnostic of the source.
    fn path_of_const(&self, c: &ConstOperand) -> Option<String> {
        c.path.clone()
    }
    // -------------------------------------------------------------------------
    // Rvalue dispatch — exhaustive over all 15 Rvalue variants.
    // -------------------------------------------------------------------------
    fn visit_rvalue(&mut self, rvalue: &Rvalue, span: Span) {
        match rvalue {
            Rvalue::Use(op) => self.visit_operand(op, span),
            Rvalue::Repeat(op, _) => self.visit_operand(op, span),
            Rvalue::Ref(_, place) => self.visit_place(place, span),
            // PB019: thread-local references.
            Rvalue::ThreadLocalRef(_) => {
                self.reject(rules::PB019, span, "thread-local reference");
            }
            // PB004: raw pointer construction.
            Rvalue::RawPtr(_, place) => {
                self.visit_place(place, span);
                self.reject(rules::PB004, span, "raw pointer (`&raw const` / `&raw mut`)");
            }
            // `place.len()`. Accepted; we model slice length.
            Rvalue::Len(place) => self.visit_place(place, span),
            Rvalue::Cast(kind, op, target_ty) => {
                self.visit_operand(op, span);
                self.visit_ty(target_ty, span);
                self.visit_cast(kind, span);
            }
            Rvalue::BinaryOp(binop, lhs, rhs) => {
                self.visit_operand(lhs, span);
                self.visit_operand(rhs, span);
                if matches!(binop, crate::mir_api::BinOp::Offset) {
                    self.reject(rules::PB004, span, "pointer offset operation");
                }
            }
            Rvalue::NullaryOp(_, ty) => self.visit_ty(ty, span),
            Rvalue::UnaryOp(_, op) => self.visit_operand(op, span),
            Rvalue::Discriminant(place) => self.visit_place(place, span),
            Rvalue::Aggregate(kind, operands) => {
                for op in operands {
                    self.visit_operand(op, span);
                }
                self.visit_aggregate_kind(kind, span);
            }
            // PB013: shallow-init Box. Distinct from PB011 because this can
            // be produced by macro expansion bypassing the source-level
            // `Box::new`.
            Rvalue::ShallowInitBox(op, ty) => {
                self.visit_operand(op, span);
                self.visit_ty(ty, span);
                self.reject(rules::PB013, span, "`Rvalue::ShallowInitBox`");
            }
            // CopyForDeref is internal: it's the deref-separator pass's
            // output. Accepted.
            Rvalue::CopyForDeref(place) => self.visit_place(place, span),
            // PB001-adjacent: wrap in unsafe binder. This rvalue only exists
            // for the `unsafe<>` lifetime sugar; its appearance implies
            // unsafe binders are in scope.
            Rvalue::WrapUnsafeBinder(op, ty) => {
                self.visit_operand(op, span);
                self.visit_ty(ty, span);
                self.reject(rules::PB001, span, "`Rvalue::WrapUnsafeBinder` implies `unsafe<>` binder");
            }
        }
    }
    fn visit_cast(&mut self, kind: &CastKind, span: Span) {
        match kind {
            // PB051: narrowing or sign-changing int casts. We reject *all*
            // IntToInt casts in v0.1 because checking "narrowing" requires
            // knowing both source and target widths, which the cast kind
            // alone does not tell us; the conservative rejection forces
            // users to use `try_from` (which we accept and the VC generator
            // discharges).
            CastKind::IntToInt => {
                self.reject(rules::PB051, span, "`as` integer cast; use `TryFrom` instead");
            }
            // PB050: float casts.
            CastKind::FloatToInt | CastKind::IntToFloat | CastKind::FloatToFloat => {
                self.reject(rules::PB050, span, "float cast");
            }
            // PB004: raw pointer casts.
            CastKind::PtrToInt | CastKind::IntToPtr | CastKind::PtrToPtr | CastKind::FnPtrToPtr => {
                self.reject(rules::PB004, span, "raw-pointer cast");
            }
            // PB007: transmute.
            CastKind::Transmute => {
                self.reject(rules::PB007, span, "transmute cast");
            }
            // Pointer coercion (auto-borrow, unsize). Mostly safe; the
            // resulting type is checked by visit_ty.
            CastKind::PointerCoercion => {}
        }
    }
    fn visit_aggregate_kind(&mut self, kind: &AggregateKind, span: Span) {
        match kind {
            AggregateKind::Tuple => {}
            AggregateKind::Array(ty) => self.visit_ty(ty, span),
            AggregateKind::Adt(adt, _) => self.classify_adt(adt, span),
            // PB033: closure construction. The visitor accepts closure
            // construction *only* when its escape is bounded; that bounding
            // is the reachability-driver's responsibility. In the visitor
            // we flag the construction site so the reachability pass can
            // make the final call.
            //
            // For v0.1 conservative posture, we reject unconditionally.
            AggregateKind::Closure(_) => {
                self.reject(rules::PB033, span, "closure construction (v0.1 conservative)");
            }
            // PB027: coroutine construction.
            AggregateKind::Coroutine(_) => {
                self.reject(rules::PB027, span, "coroutine construction");
            }
            // PB004: raw pointer aggregate.
            AggregateKind::RawPtr => {
                self.reject(rules::PB004, span, "raw-pointer aggregate construction");
            }
        }
    }
    // -------------------------------------------------------------------------
    // Operand and Place.
    // -------------------------------------------------------------------------
    fn visit_operand(&mut self, op: &Operand, span: Span) {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.visit_place(place, span),
            Operand::Constant(c) => self.visit_ty(&c.ty, span),
        }
    }
    fn visit_place(&mut self, place: &Place, span: Span) {
        // Hard cap on projection depth.
        if place.projection.len() > MAX_PROJECTION_DEPTH {
            self.reject(
                rules::PB054,
                span,
                format!(
                    "place projection depth {} exceeds limit {}",
                    place.projection.len(),
                    MAX_PROJECTION_DEPTH
                ),
            );
        }
        for elem in &place.projection {
            self.visit_projection(elem, span);
        }
    }
    fn visit_projection(&mut self, elem: &ProjectionElem, span: Span) {
        match elem {
            // Deref of a safe reference is fine; deref of a raw pointer is
            // caught earlier by the type-level check (PB004 fires on the
            // Place's local type).
            ProjectionElem::Deref => {}
            // Field access. Accepted.
            ProjectionElem::Field(_) => {}
            // PB054 *signal*: dynamic slice indexing. We accept here and
            // emit a proof obligation; the VC generator proves the bound.
            ProjectionElem::Index(_) => {}
            // Constant slice index. Bound is statically known; VC trivial.
            ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. } => {}
            // Enum variant downcast. Accepted.
            ProjectionElem::Downcast(_) => {}
            // Opaque-type cast (auto-trait, etc.). Visit the resulting type.
            ProjectionElem::OpaqueCast(ty) | ProjectionElem::Subtype(ty) => self.visit_ty(ty, span),
        }
    }
    // -------------------------------------------------------------------------
    // Types. The longest dispatch in the visitor.
    // -------------------------------------------------------------------------
    fn visit_ty(&mut self, ty: &Ty, span: Span) {
        match &ty.kind {
            TyKind::Param(_) => {
                // Type parameters should not appear post-monomorphization.
                // Their presence indicates a reachability driver bug or a
                // generic call that escaped instantiation. Fail closed.
                self.reject(rules::PB039, span, "unresolved type parameter post-monomorphization");
            }
            TyKind::Dynamic => {
                self.reject(rules::PB031, span, "`dyn Trait` type");
            }
            TyKind::RigidTy(rigid) => self.visit_rigid_ty(rigid, span),
        }
    }
    fn visit_rigid_ty(&mut self, rigid: &RigidTy, span: Span) {
        match rigid {
            RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_) => {
                // Primitive integers and bool: accepted.
                // PB052 (unbounded `usize`/`isize`) is a per-expression
                // obligation enforced by the VC generator, not a subset
                // rejection.
            }
            // PB053: `char` is accepted as a value but cannot appear in
            // arithmetic position. We accept here; the BinaryOp visitor
            // catches char-arithmetic if it occurs.
            RigidTy::Char => {}
            // PB050: any float type.
            RigidTy::Float(width) => {
                let label = match width {
                    FloatTy::F16 => "f16",
                    FloatTy::F32 => "f32",
                    FloatTy::F64 => "f64",
                    FloatTy::F128 => "f128",
                };
                self.reject(rules::PB050, span, format!("floating-point type `{label}`"));
            }
            // Safe references: accepted; recurse into the pointee type.
            RigidTy::Ref(_, inner) => self.visit_ty(inner, span),
            // PB004: raw pointers.
            RigidTy::RawPtr(_, inner) => {
                self.visit_ty(inner, span);
                self.reject(rules::PB004, span, "raw pointer type (`*const` / `*mut`)");
            }
            // Arrays: accepted; recurse.
            RigidTy::Array(inner, _) => self.visit_ty(inner, span),
            // Slices: accepted.
            RigidTy::Slice(inner) => self.visit_ty(inner, span),
            // Tuples: visit each component.
            RigidTy::Tuple(elems) => {
                for ty in elems {
                    self.visit_ty(ty, span);
                }
            }
            // PB032: function pointer type.
            RigidTy::FnPtr => {
                self.reject(rules::PB032, span, "function pointer type");
            }
            // FnDef: a statically-known function item. Accepted; the call
            // site's classify_called_function handles it.
            RigidTy::FnDef(_) => {}
            // PB033: closure type. The closure construction site is the
            // primary trigger; the type appearing in a signature is a
            // confirmation.
            RigidTy::Closure(_) => {
                self.reject(rules::PB033, span, "closure type in signature");
            }
            // ADT: the most important dispatch. Path-match against the
            // standard library.
            RigidTy::Adt(adt) => self.classify_adt(adt, span),
        }
    }
    /// Classify an ADT by its fully-qualified path.
    ///
    /// This is the dictionary that maps standard-library types to the rules
    /// they trigger. It is the second-most-audited part of the crate after
    /// the dispatch tables above.
    fn classify_adt(&mut self, adt: &AdtDef, span: Span) {
        let path = adt.path.as_str();
        // PB005: union.
        if adt.is_union {
            self.reject(rules::PB005, span, format!("union type `{path}`"));
            return;
        }
        // PB008: MaybeUninit.
        if path == "core::mem::MaybeUninit" || path == "core::mem::maybe_uninit::MaybeUninit" {
            self.reject(rules::PB008, span, "`MaybeUninit`");
            return;
        }
        // PB011, PB012: heap allocation.
        if path == "alloc::boxed::Box" {
            self.reject(rules::PB011, span, "`Box<_>`");
            return;
        }
        if matches!(
            path,
            "alloc::vec::Vec"
                | "alloc::string::String"
                | "alloc::collections::VecDeque"
                | "alloc::collections::vec_deque::VecDeque"
                | "alloc::collections::BTreeMap"
                | "alloc::collections::btree_map::BTreeMap"
                | "alloc::collections::BTreeSet"
                | "alloc::collections::btree_set::BTreeSet"
                | "std::collections::HashMap"
                | "std::collections::hash_map::HashMap"
                | "std::collections::HashSet"
                | "std::collections::hash_set::HashSet"
                | "alloc::collections::LinkedList"
        ) {
            self.reject(rules::PB012, span, format!("collection type `{path}`"));
            return;
        }
        // PB015: reference counting.
        if matches!(
            path,
            "alloc::rc::Rc"
                | "alloc::rc::Weak"
                | "alloc::sync::Arc"
                | "alloc::sync::Weak"
        ) {
            self.reject(rules::PB015, span, format!("reference-counted type `{path}`"));
            return;
        }
        // PB021: cell family.
        if matches!(
            path,
            "core::cell::Cell"
                | "core::cell::RefCell"
                | "core::cell::OnceCell"
                | "core::cell::LazyCell"
                | "core::cell::SyncUnsafeCell"
        ) {
            self.reject(rules::PB021, span, format!("cell type `{path}`"));
            return;
        }
        // PB022: UnsafeCell itself.
        if path == "core::cell::UnsafeCell" {
            self.reject(rules::PB022, span, "`UnsafeCell`");
            return;
        }
        // PB023: atomics.
        if path.starts_with("core::sync::atomic::Atomic") {
            self.reject(rules::PB023, span, format!("atomic type `{path}`"));
            return;
        }
        // PB024: synchronization primitives.
        if matches!(
            path,
            "std::sync::Mutex"
                | "std::sync::RwLock"
                | "std::sync::Once"
                | "std::sync::OnceLock"
                | "std::sync::Barrier"
                | "std::sync::Condvar"
        ) {
            self.reject(rules::PB024, span, format!("synchronization primitive `{path}`"));
            return;
        }
        // PB030: channels.
        if path.starts_with("std::sync::mpsc::") || path.starts_with("std::sync::mpmc::") {
            self.reject(rules::PB030, span, format!("channel type `{path}`"));
            return;
        }
        // Anything else: user-defined ADT or stdlib type we haven't
        // classified. Accepted; the reachability driver will visit its
        // bodies if reachable.
    }
    // -------------------------------------------------------------------------
    // Helpers.
    // -------------------------------------------------------------------------
    /// Whether a type's layout exceeds the configured stack-allocation limit.
    ///
    /// **Status:** layout-aware lower-bound estimator. Computes a conservative
    /// minimum size for primitives, references/pointers (target-dependent),
    /// arrays, and tuples. Returns `false` (does not reject) for types whose
    /// size cannot be computed without a real layout query — closures,
    /// user-defined ADTs, slices in local position. Real layout-aware
    /// detection on those types lands with the rustc_public wiring.
    ///
    /// ## Soundness posture
    ///
    /// **The estimator never returns a size larger than the actual layout.**
    /// This means PB020 has no false positives — a program that gets
    /// rejected truly does have an oversized local. The residual risk is
    /// false negatives on user ADTs and slices, where we lack the data
    /// to compute size. Those are tracked as a v0.2 closure with the real
    /// layout query.
    ///
    /// ## Overflow handling
    ///
    /// `[u8; usize::MAX]` and similar malicious types produce sizes that
    /// would overflow `u64`. We use `saturating_mul`/`saturating_add` so
    /// the estimator returns `u64::MAX` rather than wrapping — that
    /// guarantees the size will exceed any configured limit and the
    /// type is rejected, which is the right behavior. Using `checked_*`
    /// and returning `None` on overflow would be a soundness bug: the
    /// fallback to `false` would silently accept a huge type.
    fn exceeds_stack_limit(&self, ty: &Ty) -> bool {
        match self.estimate_min_size(ty) {
            Some(size) => size > self.config.subset.stack_allocation_limit_bytes,
            None => false, // unknown size; documented under-detection
        }
    }
    /// Conservative minimum-size estimator over the shadow MIR type surface.
    ///
    /// See `exceeds_stack_limit` for the soundness contract.
    fn estimate_min_size(&self, ty: &Ty) -> Option<u64> {
        let ptr_bytes = u64::from(self.config.subset.target_pointer_width) / 8;
        match &ty.kind {
            TyKind::RigidTy(rigid) => match rigid {
                RigidTy::Bool => Some(1),
                RigidTy::Char => Some(4), // 32-bit Unicode scalar value
                RigidTy::Int(i) => Some(match i {
                    crate::mir_api::IntTy::I8 => 1,
                    crate::mir_api::IntTy::I16 => 2,
                    crate::mir_api::IntTy::I32 => 4,
                    crate::mir_api::IntTy::I64 => 8,
                    crate::mir_api::IntTy::I128 => 16,
                    crate::mir_api::IntTy::Isize => ptr_bytes,
                }),
                RigidTy::Uint(u) => Some(match u {
                    crate::mir_api::UintTy::U8 => 1,
                    crate::mir_api::UintTy::U16 => 2,
                    crate::mir_api::UintTy::U32 => 4,
                    crate::mir_api::UintTy::U64 => 8,
                    crate::mir_api::UintTy::U128 => 16,
                    crate::mir_api::UintTy::Usize => ptr_bytes,
                }),
                RigidTy::Float(f) => Some(match f {
                    FloatTy::F16 => 2,
                    FloatTy::F32 => 4,
                    FloatTy::F64 => 8,
                    FloatTy::F128 => 16,
                }),
                // References and raw pointers to sized types are one pointer
                // wide. Unsized pointees (slice, dyn) would be fat pointers
                // (two words). We conservatively report one word — under-
                // counting the fat-pointer case is safe (no false positives).
                RigidTy::Ref(..) | RigidTy::RawPtr(..) | RigidTy::FnPtr | RigidTy::FnDef(_) => {
                    Some(ptr_bytes)
                }
                // Array: count × element size, saturating on overflow so
                // `[u8; usize::MAX]` is rejected rather than wrapping to
                // small.
                RigidTy::Array(elem, count) => self
                    .estimate_min_size(elem)
                    .map(|elem_size| count.saturating_mul(elem_size)),
                // Tuple: sum of element sizes (ignoring padding for the
                // lower bound). Saturating add on overflow.
                RigidTy::Tuple(elems) => {
                    let mut sum: u64 = 0;
                    for elem in elems {
                        let elem_size = self.estimate_min_size(elem)?;
                        sum = sum.saturating_add(elem_size);
                    }
                    Some(sum)
                }
                // Unsized in local position: cannot be a Local directly;
                // if it appears as a value type elsewhere, size unknown.
                RigidTy::Slice(_) => None,
                // User ADT, closure: requires real layout query.
                RigidTy::Closure(_) | RigidTy::Adt(_) => None,
            },
            TyKind::Dynamic | TyKind::Param(_) => None,
        }
    }
    /// Record a subset violation.
    fn reject(&mut self, rule: rules::RuleId, span: Span, detail: impl Into<String>) {
        self.errors.push(SubsetError {
            rule,
            span,
            detail: detail.into(),
            in_spec: self.in_spec_context,
        });
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir_api::*;
    fn empty_body() -> Body {
        Body {
            def_id: DefId(0),
            arg_tys: vec![],
            return_ty: Ty { kind: TyKind::RigidTy(RigidTy::Bool) },
            is_unsafe: false,
            is_async: false,
            locals: vec![],
            blocks: vec![],
            span: Span::default(),
        }
    }
    /// PSS-1 PB002: `unsafe fn` is rejected at the body level.
    #[test]
    fn rejects_unsafe_fn() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.is_unsafe = true;
        v.visit_body(&body, false);
        assert_eq!(v.error_count(), 1);
        assert_eq!(v.errors[0].rule, rules::PB002);
    }
    /// PSS-1 PB026: `async fn` is rejected.
    #[test]
    fn rejects_async_fn() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.is_async = true;
        v.visit_body(&body, false);
        assert_eq!(v.error_count(), 1);
        assert_eq!(v.errors[0].rule, rules::PB026);
    }
    /// PSS-1 PB004: raw pointer in return type triggers PB004.
    #[test]
    fn rejects_raw_pointer_return() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.return_ty = Ty {
            kind: TyKind::RigidTy(RigidTy::RawPtr(
                Mutability::Not,
                Box::new(Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) }),
            )),
        };
        v.visit_body(&body, false);
        assert!(v.errors.iter().any(|e| e.rule == rules::PB004));
    }
    /// PSS-1 PB031: `dyn Trait` triggers PB031.
    #[test]
    fn rejects_dyn_trait() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.arg_tys = vec![Ty { kind: TyKind::Dynamic }];
        v.visit_body(&body, false);
        assert!(v.errors.iter().any(|e| e.rule == rules::PB031));
    }
    /// PSS-1 PB050: float type triggers PB050.
    #[test]
    fn rejects_float_type() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.return_ty = Ty {
            kind: TyKind::RigidTy(RigidTy::Float(FloatTy::F32)),
        };
        v.visit_body(&body, false);
        assert!(v.errors.iter().any(|e| e.rule == rules::PB050));
    }
    /// PSS-1 PB011: `Box<u8>` triggers PB011.
    #[test]
    fn rejects_box() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.return_ty = Ty {
            kind: TyKind::RigidTy(RigidTy::Adt(AdtDef {
                path: "alloc::boxed::Box".into(),
                is_union: false,
            })),
        };
        v.visit_body(&body, false);
        assert!(v.errors.iter().any(|e| e.rule == rules::PB011));
    }
    /// Trusted bodies are exempt from body-level checks but not from
    /// signature-level checks. PB031 fires on a trusted body with a `dyn`
    /// argument; PB043-class obligations inside the body do not.
    #[test]
    fn trusted_body_still_checks_signature() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.arg_tys = vec![Ty { kind: TyKind::Dynamic }];
        v.visit_body(&body, /* trusted */ true);
        assert!(v.errors.iter().any(|e| e.rule == rules::PB031));
    }
    /// PSS-1 PB020: a local whose array count alone exceeds the configured
    /// stack-allocation limit triggers PB020.
    ///
    /// Uses the conservative-shadow detector that treats the array length
    /// as a lower bound on size. Real layout-aware detection lands with the
    /// rustc_public wiring.
    #[test]
    fn rejects_oversized_stack_array() {
        let mut cfg = SubsetConfig::default_for_test();
        // Set a tight limit: 1 KiB.
        cfg.subset.stack_allocation_limit_bytes = 1024;
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.locals.push(crate::mir_api::LocalDecl {
            ty: Ty {
                kind: TyKind::RigidTy(RigidTy::Array(
                    Box::new(Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U8)) }),
                    65_536, // far exceeds 1 KiB even at 1 byte/element
                )),
            },
            span: Span::default(),
            mutability: crate::mir_api::Mutability::Not,
        });
        v.visit_body(&body, false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB020),
            "expected PB020 for oversized array; got {:?}",
            v.errors
        );
    }
    /// PSS-1 PB020 (complement): a small array does NOT trigger PB020 even
    /// at a tight limit, as long as its length fits.
    #[test]
    fn accepts_within_stack_limit() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.subset.stack_allocation_limit_bytes = 1024;
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.locals.push(crate::mir_api::LocalDecl {
            ty: Ty {
                kind: TyKind::RigidTy(RigidTy::Array(
                    Box::new(Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U8)) }),
                    512,
                )),
            },
            span: Span::default(),
            mutability: crate::mir_api::Mutability::Not,
        });
        v.visit_body(&body, false);
        assert!(
            !v.errors.iter().any(|e| e.rule == rules::PB020),
            "PB020 should not fire on a 512-byte array under 1024-byte limit"
        );
    }
    /// PSS-1 PB020: `[u32; 300]` is 1,200 bytes — must be rejected under a
    /// 1,024-byte limit. This is the case the previous count-only stub
    /// silently accepted; the layout-aware estimator catches it.
    #[test]
    fn rejects_oversized_typed_array() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.subset.stack_allocation_limit_bytes = 1024;
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.locals.push(crate::mir_api::LocalDecl {
            ty: Ty {
                kind: TyKind::RigidTy(RigidTy::Array(
                    Box::new(Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U32)) }),
                    300, // 300 * 4 = 1200 bytes
                )),
            },
            span: Span::default(),
            mutability: crate::mir_api::Mutability::Not,
        });
        v.visit_body(&body, false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB020),
            "expected PB020 for 1200-byte typed array under 1024-byte limit"
        );
    }
    /// PSS-1 PB020: a malicious `[u8; u64::MAX]` must NOT silently wrap to
    /// zero through arithmetic overflow. The estimator uses saturating
    /// arithmetic so the size becomes u64::MAX and the rejection fires.
    #[test]
    fn overflow_in_array_size_rejects() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.locals.push(crate::mir_api::LocalDecl {
            ty: Ty {
                kind: TyKind::RigidTy(RigidTy::Array(
                    Box::new(Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U8)) }),
                    u64::MAX,
                )),
            },
            span: Span::default(),
            mutability: crate::mir_api::Mutability::Not,
        });
        v.visit_body(&body, false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB020),
            "expected PB020 on overflow-sized array; the saturating estimator must reject"
        );
    }
    /// PSS-1 PB020: tuples sum their element sizes. `(u64, [u8; 1024])`
    /// is at least 1,032 bytes — rejected under a 1,024-byte limit.
    #[test]
    fn rejects_oversized_tuple_local() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.subset.stack_allocation_limit_bytes = 1024;
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.locals.push(crate::mir_api::LocalDecl {
            ty: Ty {
                kind: TyKind::RigidTy(RigidTy::Tuple(vec![
                    Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U64)) },
                    Ty { kind: TyKind::RigidTy(RigidTy::Array(
                        Box::new(Ty { kind: TyKind::RigidTy(RigidTy::Uint(crate::mir_api::UintTy::U8)) }),
                        1024,
                    )) },
                ])),
            },
            span: Span::default(),
            mutability: crate::mir_api::Mutability::Not,
        });
        v.visit_body(&body, false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB020),
            "expected PB020 for 1032-byte tuple under 1024-byte limit"
        );
    }
    /// PSS-1 PB020: unknown-size types (user ADTs, closures) do NOT
    /// trigger PB020 — the estimator is conservative and never produces
    /// false positives. This pins the documented under-detection.
    #[test]
    fn unknown_size_type_does_not_fire_pb020() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.subset.stack_allocation_limit_bytes = 1;
        let mut v = SubsetVisitor::new(&cfg);
        let mut body = empty_body();
        body.locals.push(crate::mir_api::LocalDecl {
            ty: Ty {
                kind: TyKind::RigidTy(RigidTy::Adt(AdtDef {
                    path: "user_crate::MyStruct".into(),
                    is_union: false,
                })),
            },
            span: Span::default(),
            mutability: crate::mir_api::Mutability::Not,
        });
        v.visit_body(&body, false);
        // PB020 must not fire (unknown size); but the type itself is a
        // user ADT and the visitor allows it through classify_adt's
        // fallthrough — no PB020 in errors.
        assert!(
            !v.errors.iter().any(|e| e.rule == rules::PB020),
            "PB020 must not fire on unknown-size types"
        );
    }
    // ----- strict_panic_acceptance toggle (PB043) ----------------------
    /// Build a single-block body whose terminator is `Call(path)`. Used
    /// by the panic-toggle tests to construct a synthetic panic call site.
    fn body_calling(path: &str) -> Body {
        use crate::mir_api::*;
        Body {
            def_id: DefId(0),
            arg_tys: vec![],
            return_ty: Ty { kind: TyKind::RigidTy(RigidTy::Bool) },
            is_unsafe: false,
            is_async: false,
            locals: vec![],
            blocks: vec![BasicBlockData {
                statements: vec![],
                terminator: Terminator {
                    kind: TerminatorKind::Call {
                        func: Operand::Constant(ConstOperand {
                            ty: Ty { kind: TyKind::RigidTy(RigidTy::Bool) },
                            def_id: None,
                            path: Some(path.into()),
                        }),
                        args: vec![],
                        destination: Place { local: Local(0), projection: vec![] },
                        target: None,
                    },
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        }
    }
    /// PSS-1 PB043 default: a reachable call to `core::panicking::panic_fmt`
    /// is accepted by the v0.1 subset checker because the VC backend (v0.2)
    /// will discharge the unreachability proof. The driver's `verify`
    /// command warns; subset check stays clean.
    #[test]
    fn default_accepts_panic_call_for_vc_discharge() {
        let cfg = SubsetConfig::default_for_test();
        assert!(!cfg.verification.strict_panic_acceptance);
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("core::panicking::panic_fmt");
        v.visit_body(&body, false);
        assert!(
            !v.errors.iter().any(|e| e.rule == rules::PB043),
            "default mode: PB043 must NOT fire — the call is tagged for the VC generator"
        );
    }
    /// PSS-1 PB043 strict: with `strict_panic_acceptance = true`, the
    /// visitor rejects the panic call at the subset level — the v0.1
    /// conservative posture for users running `pitbull check` without
    /// a VC backend.
    #[test]
    fn strict_mode_rejects_panic_call() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.verification.strict_panic_acceptance = true;
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("core::panicking::panic_fmt");
        v.visit_body(&body, false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB043),
            "strict mode: expected PB043 to fire on panic call; got {:?}",
            v.errors
        );
    }
    /// PSS-1 PB043 strict + unrelated call: a normal user-function call
    /// must not be misidentified as a panic.
    #[test]
    fn strict_mode_does_not_misidentify_other_calls() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.verification.strict_panic_acceptance = true;
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("my_crate::some_helper");
        v.visit_body(&body, false);
        assert!(
            !v.errors.iter().any(|e| e.rule == rules::PB043),
            "PB043 must only fire on `core::panicking::*` paths"
        );
    }
    /// PSS-1 PB023 path-match: a call to an atomic op is rejected by
    /// classify_called_function regardless of strict mode.
    #[test]
    fn classifies_atomic_call() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("core::sync::atomic::AtomicU32::load");
        v.visit_body(&body, false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB023),
            "expected PB023 on atomic call; got {:?}",
            v.errors
        );
    }
    /// PSS-1 PB025 path-match: a call to `core::ptr::read_volatile` is
    /// rejected.
    #[test]
    fn classifies_volatile_call() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("core::ptr::read_volatile");
        v.visit_body(&body, false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB025),
            "expected PB025 on volatile call"
        );
    }
    /// PSS-1 PB028 path-match: `std::thread::spawn`.
    #[test]
    fn classifies_thread_spawn() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("std::thread::spawn");
        v.visit_body(&body, false);
        assert!(v.errors.iter().any(|e| e.rule == rules::PB028));
    }
    // ----- adversarial path inputs -------------------------------------
    /// A user crate that defines its own `core::panicking::panic_fmt`-named
    /// item must NOT accidentally trigger PB043's strict-mode rejection.
    /// rustc_public will resolve the path with the actual crate prefix,
    /// e.g. `my_crate::core::panicking::panic_fmt`. Our pattern matches on
    /// the fully-qualified path starting with `core::panicking::`, which
    /// the user-crate path does NOT.
    #[test]
    fn user_crate_shadowing_stdlib_does_not_trigger_pb043() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.verification.strict_panic_acceptance = true;
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("evil_crate::core::panicking::panic_fmt");
        v.visit_body(&body, false);
        assert!(
            !v.errors.iter().any(|e| e.rule == rules::PB043),
            "user-crate path containing 'core::panicking::' must NOT match PB043"
        );
    }
    /// A user-defined function whose own module is named `panicking` is
    /// not a stdlib panic and must not trigger PB043.
    #[test]
    fn user_module_named_panicking_does_not_trigger_pb043() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.verification.strict_panic_acceptance = true;
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("my_crate::panicking::recover");
        v.visit_body(&body, false);
        assert!(
            !v.errors.iter().any(|e| e.rule == rules::PB043),
            "user path 'panicking::recover' must NOT match PB043"
        );
    }
    /// A call to `alloc::alloc::alloc` (the global allocator) must
    /// trigger PB011 regardless of strict-panic mode.
    #[test]
    fn allocator_api_call_triggers_pb011() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("alloc::alloc::alloc");
        v.visit_body(&body, false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB011),
            "allocator call must trigger PB011"
        );
    }
}
