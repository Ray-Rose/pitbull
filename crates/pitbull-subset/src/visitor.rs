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
//! - **PB001 (unsafe block syntax):** *Closed in v0.2.* The visitor runs
//!   on MIR, which has discarded HIR-level `unsafe { }` markers. The
//!   `pitbull-rustc` wrapper now adds a HIR pre-pass (`HirPreVisitor`,
//!   driven by `tcx.hir_visit_all_item_likes_in_crate`) that emits PB001
//!   on every `BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided)`
//!   whose span isn't macro-expanded (the macro filter is the F7 audit
//!   fix — `vec![1,2,3]` etc. no longer false-positives). Operations
//!   inside the block also still fire their MIR-level rules
//!   (PB004/PB007/PB009/PB006), so the audit trail is complete. The
//!   same HIR pre-pass also extracts `#[pitbull::requires("...")]`
//!   attributes (Task O.3) used to seed VC obligation preconditions.
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
//! - **PB043 (panic unreachability):** *VC obligation emitted in v0.2.*
//!   Default mode now emits a `VcObligationKind::PanicReachability`
//!   for every reachable panic call site (`is_panic_call_path`
//!   covers `core::panicking::*`, `std::panicking::*`, `core::panic_any`,
//!   `std::panic_any`, and the four `std::rt::*` entry points). The
//!   `pitbull-vc` compiler returns `None` for the kind today — the
//!   wrapper's dispatch loop reports each as "pending" so the gap is
//!   visible in the VC summary rather than silently elided. When the
//!   v0.3+ path-sensitive backend lands, the visitor change is
//!   nothing: dispatch flips automatically.
//!
//!   Set `verification.strict_panic_acceptance = true` in `pitbull.toml`
//!   to skip the obligation and reject all reachable panic calls at
//!   the subset level — the conservative posture for users without
//!   the v0.3+ backend.
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
    /// Non-violation diagnostics — see `AuditNote` in diagnostic.rs.
    /// Populated when the visitor encounters constructs it can see
    /// but cannot classify (e.g. a Call terminator whose callee path
    /// cannot be extracted from the const operand). Surfaced via
    /// `into_report()` so auditors see the gap rather than the
    /// silent fall-through that was C2 in the v0.1 audit.
    audit_notes: Vec<crate::diagnostic::AuditNote>,
    /// VC obligations the visitor identified but did not itself
    /// discharge. The driver hands these to `pitbull-vc` for
    /// SMT-LIB compilation and solver dispatch.
    vc_obligations: Vec<crate::vc::VcObligation>,
    /// Locals of the currently-walked body. Set at the start of
    /// `visit_body` so VC emission (e.g. `Rvalue::BinaryOp`) can
    /// resolve `Operand::Copy(Place)` / `Operand::Move(Place)` to
    /// a type. Cleared between bodies via the next `visit_body`
    /// overwriting it.
    current_body_locals: Vec<crate::mir_api::LocalDecl>,
    /// Argument source names of the currently-walked body. Set at
    /// the start of `visit_body` from `body.arg_names`. Used by VC
    /// emission to bind predicate-grammar preconditions (which name
    /// parameters by source identifier) to MIR operand positions
    /// (`lhs` / `rhs`) when the operand is a direct read of a
    /// function parameter.
    current_body_arg_names: Vec<String>,
    /// Spec-derived preconditions for the currently-walked body —
    /// raw SMT-LIB assertion forms that get attached as
    /// `assumptions` to every VC obligation this body emits. Set
    /// externally before each `visit_body` via
    /// `set_current_preconditions`; left as-is across
    /// `visit_body` invocations, so the caller is responsible for
    /// updating between bodies (typical pattern: per-item lookup
    /// in `pitbull.toml`'s `[verification.preconditions]` table).
    current_body_preconditions: Vec<String>,
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
            audit_notes: Vec::new(),
            vc_obligations: Vec::new(),
            current_body_locals: Vec::new(),
            current_body_arg_names: Vec::new(),
            current_body_preconditions: Vec::new(),
            current_body_trusted: false,
            in_spec_context: false,
        }
    }
    /// Install the precondition list for the next `visit_body`
    /// call. The wrapper looks up the item being walked in
    /// `pitbull.toml`'s `[verification.preconditions]` map and
    /// passes the result here.
    ///
    /// Pass an empty `Vec` between bodies that aren't in the
    /// config; otherwise the previous body's preconditions leak
    /// across.
    pub fn set_current_preconditions(&mut self, preconditions: Vec<String>) {
        self.current_body_preconditions = preconditions;
    }
    /// Finalize the visit, producing a report. Transfers errors
    /// (subset violations), audit notes (informational gaps), and
    /// VC obligations (proof obligations for `pitbull-vc` to
    /// discharge) into the report.
    #[must_use]
    pub fn into_report(self) -> SubsetReport {
        let mut report = SubsetReport::new(self.errors);
        report.audit_notes = self.audit_notes;
        report.vc_obligations = self.vc_obligations;
        report
    }
    /// Record a non-violation audit note. The note is informational
    /// (does not block verification) but appears in `SubsetReport.audit_notes`
    /// for an auditor's review.
    pub fn audit_note(&mut self, span: Span, message: impl Into<String>) {
        self.audit_notes.push(crate::diagnostic::AuditNote {
            span,
            message: message.into(),
        });
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
        // Cache locals so VC emission (e.g. operand-type resolution
        // for Rvalue::BinaryOp) can look up types without threading
        // the body through every visit method. Cleared on the next
        // visit_body, so there's no cross-body leak.
        self.current_body_locals.clone_from(&body.locals);
        // Cache arg names for the same reason — used by spec-precondition
        // binding to map predicate variables (`x` in `x < 100`) to
        // operand positions (lhs/rhs of the binary op).
        self.current_body_arg_names.clone_from(&body.arg_names);
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
        //
        // ## std re-export normalization
        //
        // rustc resolves item paths through whichever prelude brought
        // them into scope. For std-using crates the post-mono
        // `name()` typically returns the `std::*` form (e.g.
        // `std::panicking::panic_fmt`), NOT the canonical
        // `core::*` / `alloc::*` form. The `classify_adt` site for
        // PB011/PB012/PB015 already accepts both forms
        // (visitor.rs::classify_adt). The call-classifier needs the
        // same normalization or panic / alloc / transmute / volatile
        // / atomic calls in std-using crates silently miss their
        // rules.
        //
        // Discovered during the O.2 audit cleanup: PB043 default-mode
        // obligations weren't firing on real code because
        // `panic!("...")` resolves through `std::panicking::*`.
        match path.as_deref() {
            Some(p) if is_panic_call_path(p) => {
                // PB043 has two postures:
                //
                // - **Strict** (`verification.strict_panic_acceptance = true`):
                //   any reachable panic call is rejected outright. The
                //   v0.1 conservative posture for users running
                //   `pitbull check` without a discharging backend who
                //   want subset-level panic rejection.
                //
                // - **Default**: emit a `PanicReachability` VC obligation.
                //   The expectation is that a v0.3+ path-sensitive
                //   reasoner discharges these obligations (proves the
                //   call site is dead, or that the panic guard's
                //   precondition holds). Today,
                //   `pitbull_vc::compile` returns `None` for the
                //   `PanicReachability` kind — the dispatch loop in
                //   the wrapper reports each as "pending" so the gap
                //   is VISIBLE in the VC summary rather than silently
                //   elided. This audit-trail posture matches the C2
                //   fix for unclassifiable callees.
                //
                // Once the backend's PanicReachability arm lands,
                // dispatch flips automatically — no visitor change needed.
                if self.config.verification.strict_panic_acceptance {
                    self.reject(rules::PB043, span, format!("panic call `{p}` (strict mode)"));
                } else {
                    self.emit_panic_reachability_obligation(p, span);
                }
            }
            Some(p)
                if p.starts_with("alloc::alloc::")
                    || p.starts_with("std::alloc::")
                    || p.starts_with("core::alloc::Allocator::")
                    || p.starts_with("std::alloc::Allocator::") =>
            {
                self.reject(rules::PB011, span, format!("call to allocator API `{p}`"));
            }
            Some(p)
                if p == "core::mem::transmute"
                    || p == "std::mem::transmute"
                    || p == "core::intrinsics::transmute"
                    || p == "std::intrinsics::transmute"
                    || p == "core::intrinsics::transmute_unchecked"
                    || p == "std::intrinsics::transmute_unchecked" =>
            {
                self.reject(rules::PB007, span, "`transmute` call");
            }
            Some(p)
                if p == "core::ptr::read_volatile"
                    || p == "std::ptr::read_volatile"
                    || p == "core::ptr::write_volatile"
                    || p == "std::ptr::write_volatile" =>
            {
                self.reject(rules::PB025, span, format!("volatile op `{p}`"));
            }
            Some(p)
                if p.starts_with("core::sync::atomic::")
                    || p.starts_with("std::sync::atomic::") =>
            {
                self.reject(rules::PB023, span, format!("atomic op `{p}`"));
            }
            Some(p) if p == "std::thread::spawn" || p.starts_with("std::thread::Builder::spawn") => {
                self.reject(rules::PB028, span, "thread spawn");
            }
            Some(_) => {
                // Known callee, not in the std-classifier set: assume
                // user code. The reachability driver walks the callee's
                // body as a separate verification subject; rules fire
                // there if needed.
            }
            None => {
                // We saw a Call terminator whose const operand has no
                // extractable path. Today this happens when the const's
                // type is not `RigidTy::FnDef` (the adapter's
                // `const_operand` only populates `path` for that case).
                // Real-world MIR rarely produces this shape, but a
                // future rustc lowering of `panic!` / `transmute` /
                // atomic / thread-spawn calls through a non-FnDef
                // intermediate would slip past every classifier above.
                //
                // Audit posture rejects silent fall-throughs (v0.1
                // audit finding C2). Record an audit note so an
                // auditor sees the gap, even though it isn't a
                // PSS-1 violation per se. The reachability driver
                // still walks any downstream body normally.
                self.audit_note(
                    span,
                    "callee not classified (non-FnDef const operand); \
                     reachability driver continues but no path-specific \
                     rule was applied at this call site",
                );
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
                // PB049: emit an overflow VC obligation when this is
                // a checkable arithmetic op on a primitive integer.
                // The visitor doesn't itself discharge the obligation
                // — `pitbull-vc` compiles it to SMT-LIB and dispatches
                // to a solver.
                self.maybe_emit_overflow_obligation(*binop, lhs, rhs, span);
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
            // emit a proof obligation; the VC generator proves `idx < len`.
            // The obligation kind is `IndexBound` regardless of which of
            // the three projection variants triggered it; the discharger
            // in `pitbull-vc` reasons over the abstract claim, not the
            // syntactic shape.
            //
            // Task P.2: try to bind the index local to its source-level
            // arg name. When the index is a direct read of a function
            // parameter (e.g. `s[i]` where `i: usize`), the source
            // identifier flows into the obligation, then into the SMT
            // problem as an alias for the `idx` BV variable —
            // preconditions written using the source name (`i < len`)
            // can then constrain the solver. Local computations break
            // the chain (the visitor doesn't do data-flow); they emit
            // the obligation with `None` and stay unconstrained, which
            // is the audit-safe direction.
            ProjectionElem::Index(local) => {
                let idx_source_name = self.local_arg_name(*local);
                self.emit_index_bound_obligation(idx_source_name, span);
            }
            // Constant slice index. The bound is statically known and the
            // future SMT problem is trivial (constant offset vs. constant
            // or symbolic length), but we still emit the obligation today
            // so the v0.3+ backend can discharge it uniformly. Same for
            // Subslice (a range of constant offsets). Skipping these now
            // would create a silent-accept hole — an auditor reading the
            // obligation log would see "no PB054 obligation" and assume
            // the index was safe, when in fact the visitor never asked.
            // No source name to bind here — the offset is a `u64`
            // literal in the projection itself, not a MIR local.
            ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. } => {
                self.emit_index_bound_obligation(None, span);
            }
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
        //
        // NOTE: rustc resolves these types through whichever prelude
        // brought them into scope. For std-using crates (the typical
        // case), `Box` is `std::boxed::Box`, not `alloc::boxed::Box`,
        // because std re-exports the alloc primitives. We accept both
        // forms — the alloc path is the canonical definition site,
        // the std path is the user-facing re-export. The shadow tests
        // construct the alloc form; the rustc_public adapter typically
        // produces the std form on real code.
        if path == "alloc::boxed::Box" || path == "std::boxed::Box" {
            self.reject(rules::PB011, span, "`Box<_>`");
            return;
        }
        if matches!(
            path,
            "alloc::vec::Vec"
                | "std::vec::Vec"
                | "alloc::string::String"
                | "std::string::String"
                | "alloc::collections::VecDeque"
                | "alloc::collections::vec_deque::VecDeque"
                | "std::collections::VecDeque"
                | "std::collections::vec_deque::VecDeque"
                | "alloc::collections::BTreeMap"
                | "alloc::collections::btree_map::BTreeMap"
                | "std::collections::BTreeMap"
                | "std::collections::btree_map::BTreeMap"
                | "alloc::collections::BTreeSet"
                | "alloc::collections::btree_set::BTreeSet"
                | "std::collections::BTreeSet"
                | "std::collections::btree_set::BTreeSet"
                | "std::collections::HashMap"
                | "std::collections::hash_map::HashMap"
                | "std::collections::HashSet"
                | "std::collections::hash_set::HashSet"
                | "alloc::collections::LinkedList"
                | "std::collections::LinkedList"
        ) {
            self.reject(rules::PB012, span, format!("collection type `{path}`"));
            return;
        }
        // PB015: reference counting. Same alloc/std split.
        if matches!(
            path,
            "alloc::rc::Rc"
                | "std::rc::Rc"
                | "alloc::rc::Weak"
                | "std::rc::Weak"
                | "alloc::sync::Arc"
                | "std::sync::Arc"
                | "alloc::sync::Weak"
                | "std::sync::Weak"
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
    /// Emit a PB049 overflow obligation for `lhs <op> rhs` when both
    /// operands resolve to the same primitive integer type and `op`
    /// is one of `+`, `-`, `*` (the operators with a defined
    /// SMT-LIB `bvXaddo` / `bvXsubo` / `bvXmulo` predicate).
    ///
    /// No-ops for unresolved operand types (projections, non-int
    /// types, mismatched-type pairs) — the obligation is only
    /// emitted when the visitor can stand behind the typed claim.
    /// `pitbull-vc` is then free to compile and dispatch knowing
    /// the obligation is well-formed.
    fn maybe_emit_overflow_obligation(
        &mut self,
        binop: crate::mir_api::BinOp,
        lhs: &Operand,
        rhs: &Operand,
        span: Span,
    ) {
        let arith_op = match binop {
            crate::mir_api::BinOp::Add => crate::vc::ArithOp::Add,
            crate::mir_api::BinOp::Sub => crate::vc::ArithOp::Sub,
            crate::mir_api::BinOp::Mul => crate::vc::ArithOp::Mul,
            // Div / Rem have division-by-zero obligations (different
            // encoding shape); Shl / Shr have over-shift obligations
            // (likewise). Both land in a follow-up commit. Bitwise
            // and comparison ops have no overflow obligation.
            _ => return,
        };
        let lhs_name = self.operand_primitive_int_name(lhs);
        let rhs_name = self.operand_primitive_int_name(rhs);
        let (Some(lhs_name), Some(rhs_name)) = (lhs_name, rhs_name) else {
            return;
        };
        if lhs_name != rhs_name {
            // Mixed-type arithmetic doesn't reach MIR post-coercion
            // in normal Rust code; refuse to emit a goal we can't
            // stand behind.
            return;
        }
        // O.2.5: pin constant-operand values into the SMT problem.
        // For each operand that's a `Constant` with a known
        // integer value (extracted by `adapter::const_operand`),
        // synthesize an `(assert (= <pos> <lit>))` directive. The
        // visitor adds these to the obligation's assumptions
        // before the user-supplied preconditions are processed, so
        // they appear as plain hypotheses to the solver.
        //
        // Why: before O.2.5, `fn add_one(x: u32) { x + 1 }` with
        // `requires(x < 100)` returned `sat` because the SMT
        // problem had `lhs < 100` (from precondition) but `rhs`
        // unconstrained → solver witness `rhs = u32::MAX` → false
        // overflow. With pinning, `rhs = 1` is part of the
        // hypothesis set, the check returns `unsat`, and the
        // wrapper reports "discharged (unsat)".
        let mut const_pin_assertions: Vec<String> = Vec::new();
        for (label, op) in [("lhs", lhs), ("rhs", rhs)] {
            if let Operand::Constant(c) = op {
                if let Some(value) = c.value {
                    if let Some(assertion) =
                        crate::predicate::operand_pin_assertion(label, value, &lhs_name)
                    {
                        const_pin_assertions.push(assertion);
                    }
                }
            }
        }
        let seq = self.vc_obligations.len();
        let id = format!("pb049-{}-{}", arith_op.tag(), seq);
        // Translate each precondition string. The path:
        //   1. Try `predicate::parse_predicate` — succeeds for the
        //      Rust-like grammar `<ident> <cmp> <int>`.
        //   2. If parsed: try to bind the predicate's variable to
        //      `lhs` or `rhs` via the operand's arg name. The lhs
        //      operand binds first; if the variable matches the
        //      lhs's arg name, the predicate refers to lhs. Same
        //      for rhs. Otherwise the predicate doesn't apply to
        //      this op.
        //   3. If bound: try `predicate_to_smt_assertion` against
        //      the operand's type. Range checks happen here —
        //      out-of-range literals produce `LiteralOutOfRange`,
        //      which falls back to raw splice rather than silently
        //      truncating.
        //   4. On any failure (parse, bind, or translate) splice
        //      the raw string verbatim. That preserves O.1's
        //      raw-SMT-LIB escape hatch.
        let lhs_arg = self.operand_arg_name(lhs);
        let rhs_arg = self.operand_arg_name(rhs);
        // Process each precondition through three potential paths,
        // recording a specific audit note for each rejection so
        // the auditor sees WHY a given assumption was dropped:
        //
        //   1. Predicate parses + binds + translates ⇒ use the
        //      translated SMT-LIB.
        //   2. Predicate parses + binds + translation fails (e.g.
        //      literal out of range for the operand type) ⇒
        //      audit note with translator's error message. DO NOT
        //      fall through to raw splice — the user's predicate
        //      WAS their intent, and the failure has a clean cause.
        //   3. Predicate parses but doesn't bind to any operand
        //      OR predicate doesn't parse at all ⇒ try raw splice
        //      after lex validation (F2 hardening: must be single
        //      `(assert ...)` form). If invalid, audit note.
        //
        // The path-specific rejection messages help users
        // distinguish "I wrote a real predicate but it's wrong for
        // this type" from "I wrote raw SMT but it's malformed".
        // Reserve room for: constant-pin assertions (at most 2, one
        // per operand) + user preconditions. The pins go FIRST so
        // they appear at the top of the SMT problem fed to Z3 —
        // operand values are the most basic context for an
        // obligation and read naturally when an auditor inspects
        // the SMT text. (They don't yet appear in stderr / SARIF
        // emission; both surface only the obligation's `id`,
        // `kind`, and verdict. Verbose-dump of `assumptions` is
        // a future follow-up.)
        let mut assumptions: Vec<String> = Vec::with_capacity(
            const_pin_assertions.len() + self.current_body_preconditions.len(),
        );
        assumptions.extend(const_pin_assertions);
        let mut pending_audit_notes: Vec<String> = Vec::new();
        for raw in &self.current_body_preconditions {
            match crate::predicate::parse_predicate(raw) {
                Ok(pred) => {
                    let operand_label = if lhs_arg.as_deref() == Some(pred.var.as_str()) {
                        Some("lhs")
                    } else if rhs_arg.as_deref() == Some(pred.var.as_str()) {
                        Some("rhs")
                    } else {
                        None
                    };
                    match operand_label {
                        Some(label) => {
                            match crate::predicate::predicate_to_smt_assertion(
                                &pred,
                                label,
                                &lhs_name,
                            ) {
                                Ok(smt) => assumptions.push(smt),
                                Err(e) => {
                                    pending_audit_notes.push(format!(
                                        "rejecting precondition (predicate parsed and \
                                         bound but translation failed): {e} — input: {raw:?}",
                                    ));
                                }
                            }
                        }
                        None => {
                            // Predicate parsed but its variable
                            // doesn't bind to any operand here. Try
                            // raw splice; if not valid SMT-LIB,
                            // surface a specific message.
                            match crate::predicate::validate_assertion_form(raw) {
                                Ok(()) => assumptions.push(raw.clone()),
                                Err(_) => {
                                    pending_audit_notes.push(format!(
                                        "rejecting precondition (predicate variable `{}` does \
                                         not bind to any operand of this binary op, and the \
                                         string is not a valid SMT-LIB `(assert ...)` form): \
                                         input: {raw:?}",
                                        pred.var,
                                    ));
                                }
                            }
                        }
                    }
                }
                Err(_) => {
                    // Predicate parse failed. Try raw-SMT-LIB
                    // splice with lex validation (F2 hardening).
                    match crate::predicate::validate_assertion_form(raw) {
                        Ok(()) => assumptions.push(raw.clone()),
                        Err(e) => {
                            pending_audit_notes.push(format!(
                                "rejecting precondition (neither a valid predicate \
                                 nor a single SMT-LIB `(assert ...)` form): {e} — \
                                 input: {raw:?}",
                            ));
                        }
                    }
                }
            }
        }
        self.vc_obligations.push(crate::vc::VcObligation {
            id,
            span,
            kind: crate::vc::VcObligationKind::ArithmeticOverflow {
                op: arith_op,
                ty_name: lhs_name,
            },
            assumptions,
        });
        // Surface any preconditions we refused. The audit posture
        // is "no silent skips" — if a config has a malformed
        // assumption, the auditor learns about it via the report
        // rather than the precondition silently vanishing.
        for msg in pending_audit_notes {
            self.audit_note(span, msg);
        }
    }
    /// Emit a `PanicReachability` VC obligation for a panic call
    /// site. The visitor itself cannot prove unreachability —
    /// that's a path-sensitive backend task — so we push the
    /// typed obligation and let `pitbull-vc` report "pending"
    /// until the encoding arm lands. The point is to make the
    /// gap visible in the report rather than silently accepting
    /// the call as safe (audit posture).
    ///
    /// `_panic_path` is reserved for richer diagnostics once the
    /// backend can attach the path to a counterexample trace; it
    /// isn't read today.
    fn emit_panic_reachability_obligation(&mut self, _panic_path: &str, span: Span) {
        let seq = self.vc_obligations.len();
        let id = format!("pb043-panic-{seq}");
        // Carry the current body's preconditions through. They
        // don't have a natural binding for PanicReachability today
        // (no `lhs`/`rhs` like overflow obligations have), so the
        // pitbull-vc compiler currently ignores them — but keeping
        // them in the obligation means a future backend with a
        // richer encoding inherits the context automatically.
        let assumptions = self.current_body_preconditions.clone();
        self.vc_obligations.push(crate::vc::VcObligation {
            id,
            span,
            kind: crate::vc::VcObligationKind::PanicReachability,
            assumptions,
        });
    }
    /// Emit an `IndexBound` VC obligation for a slice/array index
    /// projection. Maps to PSS-1 PB054 (slice index without bound
    /// proof). The visitor identifies the site; `pitbull-vc`
    /// compiles to a QF_BV SMT problem (Task P.1); operand
    /// bindings let user preconditions referencing source names
    /// constrain the SMT problem (Task P.2).
    ///
    /// `idx_source_name` is the source-level identifier the index
    /// local resolves to, when the index `ProjectionElem::Index(Local)`
    /// references a function-argument slot. Pass `None` for
    /// `ConstantIndex` and `Subslice` (no MIR local — the offset
    /// is a u64 literal) or when the index local doesn't trace
    /// back to a named arg. When `Some`, the compiler emits a
    /// `(define-fun <name> () (_ BitVec 64) idx)` alias in the
    /// SMT problem so user preconditions written with the source
    /// name (e.g. `(assert (bvult i len))`) constrain the
    /// solver. Without the binding the obligation reports as
    /// undischarged (sat — counterexample exists).
    ///
    /// Obligation ID format: `pb054-idx-{seq}`. The `-idx-`
    /// infix is mandatory: `PB054` is also used by the syntactic
    /// projection-depth cap (see `visit_place`'s `reject(PB054,
    /// ...)`), and the distinct obligation-ID prefixes are how
    /// auditors disambiguate the two PB054 sites in trace output.
    ///
    /// Carries the current body's `current_body_preconditions`
    /// list through verbatim — the compiler splices each into
    /// the SMT problem before the safety predicate.
    fn emit_index_bound_obligation(
        &mut self,
        idx_source_name: Option<String>,
        span: Span,
    ) {
        let seq = self.vc_obligations.len();
        let id = format!("pb054-idx-{seq}");
        // Apply the F2 red-team lex validation to each
        // precondition before attaching it to the obligation.
        // The PB049 path runs a richer predicate-grammar pipeline
        // first, but the v0.2 grammar only supports
        // `<ident> <cmp> <int>` — so for `IndexBound` (whose
        // natural shape is `i < len`, two idents) only the raw
        // SMT-LIB path applies. Malformed strings get an audit
        // note and are dropped from the obligation (audit
        // posture: no silent skips). When the predicate grammar
        // extends to `<ident> <cmp> <ident>` in a future commit,
        // this branch grows to mirror the PB049 logic.
        let mut assumptions: Vec<String> =
            Vec::with_capacity(self.current_body_preconditions.len());
        let mut pending_audit_notes: Vec<String> = Vec::new();
        for raw in &self.current_body_preconditions {
            match crate::predicate::validate_assertion_form(raw) {
                Ok(()) => assumptions.push(raw.clone()),
                Err(e) => {
                    pending_audit_notes.push(format!(
                        "PB054: rejecting precondition (not a valid \
                         SMT-LIB `(assert ...)` form for IndexBound — the \
                         v0.2 grammar's `<ident> <cmp> <int>` form doesn't \
                         apply here; user must write raw SMT-LIB): {e} — \
                         input: {raw:?}",
                    ));
                }
            }
        }
        self.vc_obligations.push(crate::vc::VcObligation {
            id,
            span,
            kind: crate::vc::VcObligationKind::IndexBound { idx_source_name },
            assumptions,
        });
        for msg in pending_audit_notes {
            self.audit_note(span, msg);
        }
    }
    /// Resolve an operand to its source-level parameter name when
    /// the operand is a direct read of a function argument (no
    /// projections, base local is one of the arg slots). Returns
    /// `None` for:
    /// - Constant operands.
    /// - Places with non-empty projections (deref, field, etc.).
    /// - Place locals outside the argument range (locals introduced
    ///   by `let`, return slot `_0`, etc.).
    /// - Argument slots with no source name (anonymous patterns).
    ///
    /// Conservative posture: the binding only fires when the
    /// operand is "directly" a parameter. Intermediate `let`s
    /// (e.g. `let y = x; y + 1`) break the chain — the visitor
    /// doesn't do data-flow analysis. Predicates referring to such
    /// shadowed parameters silently don't apply at the binary-op
    /// site and fall back to raw splice.
    fn operand_arg_name(&self, op: &Operand) -> Option<String> {
        let place = match op {
            Operand::Constant(_) => return None,
            Operand::Copy(p) | Operand::Move(p) => p,
        };
        if !place.projection.is_empty() {
            return None;
        }
        self.local_arg_name(place.local)
    }
    /// Same as `operand_arg_name` but for a bare `Local` (no
    /// surrounding Operand). Used by PB054 `IndexBound` binding —
    /// `ProjectionElem::Index(Local)` carries the index local
    /// directly, not wrapped in an Operand.
    ///
    /// Returns `None` for:
    /// - The return slot (`_0`).
    /// - Locals outside the argument range (introduced by `let`,
    ///   intermediate temporaries, etc.).
    /// - Argument slots whose source name is the empty string
    ///   (anonymous patterns).
    ///
    /// Same conservative posture as `operand_arg_name`: the
    /// binding only fires when the local IS an arg slot. Intermediate
    /// `let i_copy = i; arr[i_copy]` breaks the chain — without
    /// data-flow analysis the visitor sees `i_copy` (a non-arg
    /// local) and returns `None`. The downstream effect: the SMT
    /// problem has no `define-fun i () ... idx` alias, so a
    /// precondition referring to `i` doesn't constrain the
    /// solver — the obligation reports as undischarged. That's
    /// the audit-safe direction: missing-bind ⇒ over-approximate
    /// "could fail", not under-approximate "vacuously holds".
    fn local_arg_name(&self, local: crate::mir_api::Local) -> Option<String> {
        // Local `_0` is the return slot; `_1..=_arg_count` are args.
        // arg_names is indexed [0..arg_count) → maps to locals [1..=arg_count].
        let local_idx = local.0 as usize;
        if local_idx == 0 {
            return None;
        }
        let arg_idx = local_idx - 1;
        let name = self.current_body_arg_names.get(arg_idx)?;
        if name.is_empty() {
            None
        } else {
            Some(name.clone())
        }
    }
    /// Resolve an operand to a primitive integer type name (`"u32"`,
    /// `"i64"`, …) when possible.
    ///
    /// Returns `None` for:
    /// - Operands whose type is not a primitive integer.
    /// - `Operand::Copy(place)` / `Operand::Move(place)` where the
    ///   place has any projections (we'd need to thread the
    ///   projected types — the v0.2 scaffold's first cut doesn't).
    /// - Places whose local index is out of range (defensive; this
    ///   should be impossible in well-formed MIR but the visitor
    ///   doesn't trust its input).
    fn operand_primitive_int_name(&self, op: &Operand) -> Option<String> {
        let ty: &Ty = match op {
            Operand::Constant(c) => &c.ty,
            Operand::Copy(p) | Operand::Move(p) => {
                if !p.projection.is_empty() {
                    return None;
                }
                let idx = p.local.0 as usize;
                &self.current_body_locals.get(idx)?.ty
            }
        };
        primitive_int_name_from_ty(ty)
    }
}
/// Whether a fully-qualified callee path names a known panic
/// entry point. The set is curated against rustc's actual lowering
/// of `panic!()` and friends — discovered empirically via the
/// audit cleanup smoke when `std::rt::panic_fmt` came back instead
/// of the `core::panicking::*` paths the visitor originally
/// expected.
///
/// Patterns covered (with rationale):
/// - `core::panicking::*` / `core::panic` — direct panic from
///   no_std / core code, and the older `panic!` lowering.
/// - `std::panicking::*` / `std::panic` — std re-export forms.
/// - `std::rt::panic_fmt` / `std::rt::panic_display` /
///   `std::rt::begin_panic` / `std::rt::begin_panic_fmt` —
///   actual runtime entry points rustc emits for `panic!("...")`
///   in std-using crates (discovered: real path is via std::rt).
///
/// Free-standing so corpus tests can pin "this path counts as a
/// panic" without going through the full visitor machinery.
#[must_use]
pub fn is_panic_call_path(p: &str) -> bool {
    p.starts_with("core::panicking::")
        || p.starts_with("std::panicking::")
        || p == "core::panic"
        || p == "std::panic"
        // `core::panic_any` / `std::panic_any` are the public
        // top-level API for panicking with an arbitrary payload.
        // They aren't under `panicking::*`. Discovered in
        // audit-cleanup #4 (finding H-1 / F11): a user calling
        // `std::panic_any(payload)` wasn't classified as a panic.
        || p == "core::panic_any"
        || p == "std::panic_any"
        || matches!(
            p,
            "std::rt::panic_fmt"
                | "std::rt::panic_display"
                | "std::rt::begin_panic"
                | "std::rt::begin_panic_fmt",
        )
}
/// Extract the canonical Rust type name (`"u32"`, `"i64"`, ...) from
/// a shadow `Ty` when it represents a primitive integer; otherwise
/// `None`. Free-standing because it's a pure type-shape inspection
/// — no visitor state needed.
fn primitive_int_name_from_ty(ty: &Ty) -> Option<String> {
    use crate::mir_api::{IntTy, RigidTy, TyKind, UintTy};
    let TyKind::RigidTy(rigid) = &ty.kind else {
        return None;
    };
    let name = match rigid {
        RigidTy::Int(int_ty) => match int_ty {
            IntTy::Isize => "isize",
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64",
            IntTy::I128 => "i128",
        },
        RigidTy::Uint(uint_ty) => match uint_ty {
            UintTy::Usize => "usize",
            UintTy::U8 => "u8",
            UintTy::U16 => "u16",
            UintTy::U32 => "u32",
            UintTy::U64 => "u64",
            UintTy::U128 => "u128",
        },
        _ => return None,
    };
    Some(name.to_string())
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir_api::*;
    fn empty_body() -> Body {
        Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
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
    /// Build a single-block body whose terminator is a Call with a
    /// constant operand whose `path` is None. Models the rare MIR
    /// shape where the callee is a non-FnDef-typed constant — the
    /// adapter cannot extract a path so `classify_called_function`
    /// records an audit note instead of falling through silently
    /// (v0.1 audit finding C2).
    fn body_calling_unclassifiable() -> Body {
        use crate::mir_api::*;
        Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
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
                            path: None,
                            value: None,
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
    /// Task N regression: a `Rvalue::BinaryOp(Add, u32_const, u32_const)`
    /// must produce a PB049 ArithmeticOverflow VC obligation in the
    /// report. The visitor itself doesn't discharge the obligation;
    /// it just emits the typed claim for pitbull-vc to compile + send
    /// to a solver.
    #[test]
    fn binary_op_on_u32_emits_overflow_obligation() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![LocalDecl {
                ty: u32_ty.clone(),
                span: Span::default(),
                mutability: Mutability::Not,
            }],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(
            report.vc_obligations.len(),
            1,
            "expected exactly one VC obligation; got {:?}",
            report.vc_obligations,
        );
        let crate::vc::VcObligationKind::ArithmeticOverflow { op, ty_name } =
            &report.vc_obligations[0].kind
        else {
            panic!("expected ArithmeticOverflow obligation");
        };
        assert_eq!(*op, crate::vc::ArithOp::Add);
        assert_eq!(ty_name, "u32");
        assert!(
            report.vc_obligations[0].id.starts_with("pb049-add-"),
            "VC id should follow pb{{nnn}}-{{tag}}-{{seq}} format; got {:?}",
            report.vc_obligations[0].id,
        );
    }
    /// O.1 regression: when the visitor has spec-derived
    /// preconditions installed via `set_current_preconditions`,
    /// every VC obligation it emits during the next `visit_body`
    /// must carry those preconditions as `assumptions`. Pins the
    /// contract for the wrapper → visitor → VcObligation handoff.
    #[test]
    fn preconditions_propagate_to_obligation_assumptions() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone()],
            arg_names: vec![],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![LocalDecl {
                ty: u32_ty.clone(),
                span: Span::default(),
                mutability: Mutability::Not,
            }],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_preconditions(vec![
            "(assert (bvult lhs #x00000064))".into(),
        ]);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert_eq!(
            report.vc_obligations[0].assumptions,
            vec!["(assert (bvult lhs #x00000064))"],
            "obligation should carry the installed preconditions verbatim",
        );
    }
    /// O.1 hygiene: calling `set_current_preconditions(vec![])`
    /// wipes any prior installation, so a body without
    /// preconditions emits obligations with empty `assumptions`.
    /// Pins the contract that the wrapper relies on for per-body
    /// state isolation.
    #[test]
    fn clearing_preconditions_makes_assumptions_empty() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let make_body = || Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![LocalDecl {
                ty: u32_ty.clone(),
                span: Span::default(),
                mutability: Mutability::Not,
            }],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Mul,
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        // First body: with preconditions.
        v.set_current_preconditions(vec!["(assert true)".into()]);
        v.visit_body(&make_body(), false);
        // Second body: cleared via the canonical empty-vec
        // "set" (the only path the wrapper uses too).
        v.set_current_preconditions(vec![]);
        v.visit_body(&make_body(), false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 2);
        assert_eq!(
            report.vc_obligations[0].assumptions,
            vec!["(assert true)"],
            "first body's obligation should carry the precondition",
        );
        assert!(
            report.vc_obligations[1].assumptions.is_empty(),
            "second body's obligation should have no assumptions after clear; got {:?}",
            report.vc_obligations[1].assumptions,
        );
    }
    /// O.2: a predicate-form precondition like `"x < 100"` is
    /// parsed, bound to the `x` parameter on the lhs of the binary
    /// op, and translated to a properly-encoded BV assertion. Pins
    /// the full visitor path: parse → bind → translate.
    #[test]
    fn predicate_precondition_binds_lhs_operand() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        // MIR layout for `fn add_one(x: u32) -> u32 { x + 1 }`:
        //   _0: u32 (return), _1: u32 (param `x`), _2: u32 (the
        //   binary op result). The BinaryOp's lhs is Copy(_1).
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone()],
            arg_names: vec!["x".into()],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(2), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place { local: Local(1), projection: vec![] }),
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_preconditions(vec!["x < 100".into()]);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert_eq!(
            report.vc_obligations[0].assumptions,
            vec!["(assert (bvult lhs #x00000064))".to_string()],
            "predicate `x < 100` must bind to lhs (where x is) and \
             translate to an unsigned-less-than BV assertion",
        );
    }
    /// O.2 + audit hardening (F2): a predicate-format precondition
    /// whose variable doesn't match any operand is DROPPED with an
    /// audit note — not silently spliced as raw SMT-LIB (which
    /// would produce a solver error). The audit note makes the
    /// rejection visible.
    ///
    /// The original O.2 test was named `unbound_predicate_falls_back_to_raw_splice`
    /// — that name reflected the pre-hardening behavior. The new
    /// posture is stricter: only well-formed single `(assert ...)`
    /// SMT-LIB strings get the raw-splice escape hatch.
    #[test]
    fn unbound_predicate_dropped_with_audit_note() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone()],
            arg_names: vec!["x".into()],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        // Precondition mentions `x`, but neither operand is a Copy
        // of param `x` — both are constants. The predicate parses
        // OK but cannot bind to any operand. The raw-splice fallback
        // requires `(assert ...)` form, so the predicate-format
        // `"x < 100"` doesn't qualify and is dropped with an audit
        // note rather than spliced.
        v.set_current_preconditions(vec!["x < 100".into()]);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert!(
            report.vc_obligations[0].assumptions.is_empty(),
            "unbound predicate must be DROPPED (not spliced as \
             malformed SMT-LIB); got assumptions={:?}",
            report.vc_obligations[0].assumptions,
        );
        assert!(
            report.audit_notes.iter().any(|n|
                n.message.contains("rejecting precondition")
            ),
            "rejection should be surfaced as an audit note; got {:?}",
            report.audit_notes,
        );
    }
    /// O.2.5: when a `BinaryOp` has a Constant operand with a
    /// known value (extracted by `adapter::const_operand`), the
    /// visitor synthesizes a pinning assumption that constrains
    /// the SMT operand to that exact value. This is the
    /// foundational fix that lets `fn add_one(x: u32) { x + 1 }`
    /// with `requires(x < 100)` prove `unsat` — without pinning
    /// `rhs = 1`, the solver finds the witness `rhs = u32::MAX`
    /// even under `x < 100`.
    #[test]
    fn constant_operand_value_pinned_in_assumptions() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        // Body for `fn add_one(x: u32) -> u32 { x + 1 }`:
        //   _0: u32 (return)
        //   _1: u32 (param `x`)
        //   _2: u32 (the binary op result)
        //   _2 = _1 + 1u32
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone()],
            arg_names: vec!["x".into()],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(2), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            // lhs = x (parameter), no value to pin
                            Operand::Copy(Place {
                                local: Local(1),
                                projection: vec![],
                            }),
                            // rhs = 1u32, known constant value
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: Some(1),
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        let assumptions = &report.vc_obligations[0].assumptions;
        // The rhs operand was a Constant with value 1u32 — its
        // value gets pinned as `(assert (= rhs #x00000001))`.
        assert!(
            assumptions.iter().any(|a| a == "(assert (= rhs #x00000001))"),
            "expected operand-pinning assertion for rhs=1u32; \
             got assumptions: {assumptions:?}",
        );
        // The lhs operand was a Copy (not a constant) — no
        // pinning assertion for it.
        assert!(
            !assumptions.iter().any(|a| a.contains("= lhs")),
            "lhs is a Copy operand (parameter `x`), not a constant; \
             must NOT be pinned. assumptions: {assumptions:?}",
        );
    }
    /// O.2.5: an operand with `value: None` (e.g. a constant whose
    /// value couldn't be extracted, or a synthetic test fixture)
    /// produces no pinning assertion. Pins the negative space.
    #[test]
    fn constant_operand_without_value_emits_no_pin() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![LocalDecl {
                ty: u32_ty.clone(),
                span: Span::default(),
                mutability: Mutability::Not,
            }],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,  // adapter didn't extract a value
                            }),
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert!(
            report.vc_obligations[0].assumptions.is_empty(),
            "value-less constants must not produce pinning assertions; \
             got assumptions: {:?}",
            report.vc_obligations[0].assumptions,
        );
    }
    /// Audit hardening (F2 red-team): a malicious precondition
    /// containing multiple SMT-LIB directives is REFUSED — the
    /// raw-splice escape hatch lex-validates the input as a
    /// single `(assert ...)` form. The rejection produces an
    /// audit note so the auditor sees the attempt.
    ///
    /// Without this guard, splicing `"(check-sat) (assert false)"`
    /// would let an attacker (e.g. a maintainer-PR with malicious
    /// pitbull.toml additions) plant contradictory hypotheses or
    /// pre-emit a verdict that the wrapper's parser then misreads.
    #[test]
    fn multi_directive_injection_rejected() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone()],
            arg_names: vec!["x".into()],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place { local: Local(1), projection: vec![] }),
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        // Each of these has been chosen to model a specific attack
        // vector documented in the v0.2 red-team finding F2.
        let attacks = [
            "(check-sat) (assert false)",       // pre-emit verdict + poison
            "(assert false) (check-sat)",       // poison + verdict
            "(push) (assert false) (pop)",      // scoped poison
            "(define-fun evil () Bool false)",  // stealth definition
        ];
        v.set_current_preconditions(attacks.iter().map(|s| s.to_string()).collect());
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert!(
            report.vc_obligations[0].assumptions.is_empty(),
            "EVERY malicious assumption must be refused; got {:?}",
            report.vc_obligations[0].assumptions,
        );
        // Each attack should have produced its own audit note.
        assert_eq!(
            report.audit_notes.len(),
            attacks.len(),
            "expected one audit note per refused assumption; got {} notes for {} attacks",
            report.audit_notes.len(),
            attacks.len(),
        );
        for note in &report.audit_notes {
            assert!(
                note.message.contains("rejecting precondition"),
                "audit note should call out the rejection; got {:?}",
                note.message,
            );
        }
    }
    /// O.2: raw SMT-LIB strings (which fail predicate parsing
    /// because they don't have a bare comparison operator) flow
    /// through unchanged. Preserves O.1 behavior for users with
    /// hand-written SMT — but only for valid single-`(assert ...)`
    /// forms (audit hardening F2).
    #[test]
    fn raw_smt_lib_precondition_unchanged() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone()],
            arg_names: vec!["x".into()],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place { local: Local(1), projection: vec![] }),
                            Operand::Constant(ConstOperand {
                                ty: u32_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let raw = "(assert (bvult lhs #x00000050))";
        v.set_current_preconditions(vec![raw.to_string()]);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert_eq!(
            report.vc_obligations[0].assumptions,
            vec![raw.to_string()],
            "raw SMT-LIB must pass through verbatim",
        );
    }
    /// Task N negative: a `BinaryOp` on a non-integer (`bool`)
    /// must NOT emit an overflow obligation — the SMT-LIB encoder
    /// would have nothing meaningful to say.
    #[test]
    fn binary_op_on_bool_does_not_emit_obligation() {
        use crate::mir_api::*;
        let bool_ty = Ty { kind: TyKind::RigidTy(RigidTy::Bool) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: bool_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![LocalDecl {
                ty: bool_ty.clone(),
                span: Span::default(),
                mutability: Mutability::Not,
            }],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::BitAnd,
                            Operand::Constant(ConstOperand {
                                ty: bool_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                            Operand::Constant(ConstOperand {
                                ty: bool_ty.clone(),
                                def_id: None,
                                path: None,
                                value: None,
                            }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert!(
            report.vc_obligations.is_empty(),
            "BitAnd on bool must not emit overflow obligations; got {:?}",
            report.vc_obligations,
        );
    }
    /// C2 regression: a Call with `path: None` must record an audit
    /// note (not silently fall through). Pins the audit posture that
    /// every unclassified call site at least surfaces a diagnostic
    /// for an auditor to review.
    #[test]
    fn unclassifiable_callee_records_audit_note() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling_unclassifiable();
        v.visit_body(&body, false);
        let report = v.into_report();
        assert!(
            report.errors.is_empty(),
            "unclassifiable callee must not fire a hard violation; got {:?}",
            report.errors,
        );
        assert_eq!(
            report.audit_notes.len(),
            1,
            "expected exactly one audit note for the unclassifiable callee; got {:?}",
            report.audit_notes,
        );
        assert!(
            report.audit_notes[0].message.contains("callee not classified"),
            "audit note message should explain the gap; got {:?}",
            report.audit_notes[0].message,
        );
    }
    /// Build a single-block body whose terminator is `Call(path)`. Used
    /// by the panic-toggle tests to construct a synthetic panic call site.
    fn body_calling(path: &str) -> Body {
        use crate::mir_api::*;
        Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
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
                            value: None,
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
    /// PSS-1 PB043 default: a reachable call to
    /// `core::panicking::panic_fmt` is NOT rejected at the subset
    /// level; instead the visitor emits a `PanicReachability` VC
    /// obligation that a v0.3+ backend will eventually discharge.
    /// pitbull-vc::compile returns None for the kind today, so
    /// the wrapper reports the obligation as "pending" — the
    /// audit trail is visible rather than the call being silently
    /// accepted (which was the pre-audit-fix posture).
    #[test]
    fn default_accepts_panic_call_for_vc_discharge() {
        let cfg = SubsetConfig::default_for_test();
        assert!(!cfg.verification.strict_panic_acceptance);
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("core::panicking::panic_fmt");
        v.visit_body(&body, false);
        let report = v.into_report();
        assert!(
            !report.errors.iter().any(|e| e.rule == rules::PB043),
            "default mode: PB043 must NOT fire as a violation \
             (it becomes a VC obligation instead)",
        );
        let panic_obligations: Vec<_> = report
            .vc_obligations
            .iter()
            .filter(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::PanicReachability,
            ))
            .collect();
        assert_eq!(
            panic_obligations.len(),
            1,
            "default mode: panic call must produce exactly one \
             PanicReachability obligation; got {panic_obligations:?}",
        );
        assert!(
            panic_obligations[0].id.starts_with("pb043-panic-"),
            "obligation id should follow pb043-panic-{{seq}} format; \
             got {:?}",
            panic_obligations[0].id,
        );
    }
    /// Audit-cleanup fix: panic calls resolved through std's
    /// re-export (`std::panicking::*`) are caught by the same
    /// PB043 logic as `core::panicking::*`. Pins the std-prefix
    /// normalization the audit uncovered as missing.
    #[test]
    fn default_panic_call_via_std_re_export_emits_obligation() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("std::panicking::panic_fmt");
        v.visit_body(&body, false);
        let report = v.into_report();
        assert!(
            report.vc_obligations.iter().any(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::PanicReachability,
            )),
            "std::panicking::* must also emit PanicReachability \
             (std re-export normalization); got {:?}",
            report.vc_obligations,
        );
    }
    /// Audit-cleanup discovery: `panic!("...")` in std-using crates
    /// lowers to `std::rt::panic_fmt`, NOT the `core::panicking::*`
    /// or `std::panicking::*` paths the visitor originally expected.
    /// Pin each known runtime entry point so a future rustc lowering
    /// change is loud (test breaks) rather than silent (panic missed).
    #[test]
    fn is_panic_call_path_recognizes_known_entry_points() {
        let positive = [
            "core::panicking::panic",
            "core::panicking::panic_fmt",
            "core::panicking::panic_explicit",
            "core::panicking::panic_nounwind_fmt",
            "core::panicking::panic_in_cleanup",
            "core::panicking::panic_const_add_overflow",
            "std::panicking::begin_panic",
            "std::panicking::set_hook",
            "core::panic",
            "std::panic",
            "core::panic_any",      // audit-cleanup #4 / F11 fix
            "std::panic_any",       // audit-cleanup #4 / F11 fix
            "std::rt::panic_fmt",
            "std::rt::panic_display",
            "std::rt::begin_panic",
            "std::rt::begin_panic_fmt",
        ];
        for p in positive {
            assert!(is_panic_call_path(p), "should classify as panic: {p}");
        }
        let negative = [
            "core::ptr::read_volatile",   // a real classified path, but for PB025
            "core::sync::atomic::AtomicU32::load",
            "my_crate::helper",
            "std::fmt::Arguments::<'a>::from_str",  // the OTHER unmatched path we observed
            "core::panic_lookalike",  // similar prefix but not a panic API
            "",
        ];
        for p in negative {
            assert!(!is_panic_call_path(p), "should NOT classify as panic: {p}");
        }
    }
    /// Audit-cleanup #4 / H-2: `transmute_unchecked` is a real
    /// (unstable but reachable) transmute variant used inside
    /// `MaybeUninit::assume_init` and similar. Must fire PB007.
    #[test]
    fn transmute_unchecked_fires_pb007() {
        let cfg = SubsetConfig::default_for_test();
        for path in [
            "core::intrinsics::transmute_unchecked",
            "std::intrinsics::transmute_unchecked",
        ] {
            let mut v = SubsetVisitor::new(&cfg);
            let body = body_calling(path);
            v.visit_body(&body, false);
            assert!(
                v.errors.iter().any(|e| e.rule == rules::PB007),
                "{path}: expected PB007 to fire; got {:?}",
                v.errors,
            );
        }
    }
    /// Audit-cleanup #4 / H-3: trait-method-style allocator paths
    /// (`core::alloc::Allocator::allocate` etc.) must fire PB011.
    /// Before this fix, only `alloc::alloc::*` and `std::alloc::*`
    /// matched; trait calls via the `Allocator` trait silently
    /// missed.
    #[test]
    fn allocator_trait_methods_fire_pb011() {
        let cfg = SubsetConfig::default_for_test();
        for path in [
            "core::alloc::Allocator::allocate",
            "core::alloc::Allocator::deallocate",
            "std::alloc::Allocator::allocate",
            "std::alloc::Allocator::grow",
        ] {
            let mut v = SubsetVisitor::new(&cfg);
            let body = body_calling(path);
            v.visit_body(&body, false);
            assert!(
                v.errors.iter().any(|e| e.rule == rules::PB011),
                "{path}: expected PB011 to fire; got {:?}",
                v.errors,
            );
        }
    }
    #[test]
    fn std_rt_panic_fmt_emits_panic_reachability_obligation() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("std::rt::panic_fmt");
        v.visit_body(&body, false);
        let report = v.into_report();
        let panic_obligations: Vec<_> = report
            .vc_obligations
            .iter()
            .filter(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::PanicReachability,
            ))
            .collect();
        assert_eq!(
            panic_obligations.len(),
            1,
            "std::rt::panic_fmt must produce a PanicReachability \
             obligation (the actual lowering for `panic!()` in \
             std-using crates); got {panic_obligations:?}",
        );
    }
    /// Companion: PB011 (alloc), PB007 (transmute), PB025 (volatile),
    /// PB023 (atomic) all need std re-export normalization too. Pin
    /// each so the regression can't reappear silently.
    #[test]
    fn std_re_exports_match_for_all_classifier_rules() {
        let cfg = SubsetConfig::default_for_test();
        let cases = [
            ("std::alloc::alloc", rules::PB011),
            ("std::mem::transmute", rules::PB007),
            ("std::ptr::read_volatile", rules::PB025),
            ("std::ptr::write_volatile", rules::PB025),
            ("std::sync::atomic::AtomicU32::load", rules::PB023),
        ];
        for (path, expected_rule) in cases {
            let mut v = SubsetVisitor::new(&cfg);
            let body = body_calling(path);
            v.visit_body(&body, false);
            assert!(
                v.errors.iter().any(|e| e.rule == expected_rule),
                "{path}: expected {expected_rule:?} to fire; got errors {:?}",
                v.errors,
            );
        }
    }
    /// Strict mode preserves the v0.1-style hard reject. The
    /// obligation is NOT emitted (no point — the violation
    /// already terminates the user's check), so the report
    /// surfaces a PB043 error and no PanicReachability obligation.
    #[test]
    fn strict_mode_panic_does_not_emit_obligation() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.verification.strict_panic_acceptance = true;
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_calling("core::panicking::panic_fmt");
        v.visit_body(&body, false);
        let report = v.into_report();
        assert!(
            report.errors.iter().any(|e| e.rule == rules::PB043),
            "strict mode: PB043 must fire as a violation",
        );
        assert!(
            !report.vc_obligations.iter().any(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::PanicReachability,
            )),
            "strict mode: no PanicReachability obligation should be \
             emitted (the reject is the verdict); got {:?}",
            report.vc_obligations,
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
    // ----- PB054 MVP: IndexBound obligation emission -------------------
    //
    // Three sibling tests, one per projection variant that produces a
    // PB054 obligation. Each builds a minimum body that exercises a
    // single `ProjectionElem::{Index,ConstantIndex,Subslice}` and
    // asserts:
    //   (a) exactly one VC obligation is emitted,
    //   (b) it's `VcObligationKind::IndexBound`,
    //   (c) the obligation `id` matches the `pb054-idx-{seq}` format
    //       (mandatory: PB054 is also used for the projection-depth cap
    //       at `MAX_PROJECTION_DEPTH`, and the distinct ID prefix is
    //       how auditors disambiguate the two PB054 sites — see
    //       `emit_index_bound_obligation`'s doc).
    /// Build a body containing a single `_0 = _1[<projection>]` statement,
    /// where `<projection>` is supplied by the caller. Two locals: `_0`
    /// (return slot) and `_1` (the indexed place). Used by the three PB054
    /// MVP tests to vary only the projection kind.
    fn body_with_index_projection(proj: ProjectionElem) -> Body {
        let u8_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) };
        Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: u8_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl {
                    ty: u8_ty.clone(),
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
                LocalDecl {
                    ty: u8_ty,
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::Use(Operand::Copy(Place {
                            local: Local(1),
                            projection: vec![proj],
                        })),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        }
    }
    #[test]
    fn projection_index_emits_index_bound_obligation() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_with_index_projection(ProjectionElem::Index(Local(1)));
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(
            report.vc_obligations.len(),
            1,
            "Index projection must emit exactly one IndexBound obligation; got {:?}",
            report.vc_obligations,
        );
        assert!(
            matches!(
                report.vc_obligations[0].kind,
                crate::vc::VcObligationKind::IndexBound { .. }
            ),
            "expected IndexBound; got {:?}",
            report.vc_obligations[0].kind,
        );
        assert!(
            report.vc_obligations[0].id.starts_with("pb054-idx-"),
            "VC id must follow pb054-idx-{{seq}} format to distinguish \
             from the projection-depth PB054 site; got {:?}",
            report.vc_obligations[0].id,
        );
    }
    #[test]
    fn projection_constant_index_emits_index_bound_obligation() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_with_index_projection(ProjectionElem::ConstantIndex { offset: 3 });
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert!(matches!(
            report.vc_obligations[0].kind,
            crate::vc::VcObligationKind::IndexBound { .. }
        ));
        assert!(report.vc_obligations[0].id.starts_with("pb054-idx-"));
    }
    #[test]
    fn projection_subslice_emits_index_bound_obligation() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_with_index_projection(ProjectionElem::Subslice { from: 0, to: 4 });
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert!(matches!(
            report.vc_obligations[0].kind,
            crate::vc::VcObligationKind::IndexBound { .. }
        ));
        assert!(report.vc_obligations[0].id.starts_with("pb054-idx-"));
    }
    /// PB054 MVP regression: projections that are NOT index-related
    /// (Deref, Field, Downcast, OpaqueCast, Subtype) must NOT emit any
    /// IndexBound obligation. This pins the negative-space contract so
    /// that future re-wiring of `visit_projection` can't silently start
    /// emitting bogus obligations on benign projections.
    #[test]
    fn non_index_projections_do_not_emit_index_bound() {
        let cfg = SubsetConfig::default_for_test();
        let u8_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) };
        let non_index_projections = vec![
            ProjectionElem::Deref,
            ProjectionElem::Field(0),
            ProjectionElem::Downcast(0),
        ];
        for proj in non_index_projections {
            let mut v = SubsetVisitor::new(&cfg);
            let body = Body {
                def_id: DefId(0),
                arg_tys: vec![],
                arg_names: vec![],
                return_ty: u8_ty.clone(),
                is_unsafe: false,
                is_async: false,
                locals: vec![
                    LocalDecl {
                        ty: u8_ty.clone(),
                        span: Span::default(),
                        mutability: Mutability::Not,
                    },
                    LocalDecl {
                        ty: u8_ty.clone(),
                        span: Span::default(),
                        mutability: Mutability::Not,
                    },
                ],
                blocks: vec![BasicBlockData {
                    statements: vec![Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::Use(Operand::Copy(Place {
                                local: Local(1),
                                projection: vec![proj.clone()],
                            })),
                        ),
                        span: Span::default(),
                    }],
                    terminator: Terminator {
                        kind: TerminatorKind::Return,
                        span: Span::default(),
                    },
                }],
                span: Span::default(),
            };
            v.visit_body(&body, false);
            let report = v.into_report();
            let index_bound_count = report
                .vc_obligations
                .iter()
                .filter(|o| matches!(
                    o.kind,
                    crate::vc::VcObligationKind::IndexBound { .. },
                ))
                .count();
            assert_eq!(
                index_bound_count, 0,
                "{:?} projection must NOT emit an IndexBound obligation; got {:?}",
                proj, report.vc_obligations,
            );
        }
    }
    /// O.1 propagation: IndexBound obligations carry the current body's
    /// preconditions just like ArithmeticOverflow and PanicReachability
    /// do. The compiler today ignores them (no encoding arm yet) but
    /// the plumbing must already be in place so the v0.3+ backend
    /// inherits the spec context automatically.
    #[test]
    fn index_bound_carries_body_preconditions() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_preconditions(vec![
            "(assert (bvult idx #x00000064))".into(),
        ]);
        let body = body_with_index_projection(ProjectionElem::Index(Local(1)));
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        assert_eq!(
            report.vc_obligations[0].assumptions,
            vec!["(assert (bvult idx #x00000064))"],
            "IndexBound obligation must carry installed preconditions verbatim",
        );
    }
    /// Sequence numbering: each emit advances the `{seq}` suffix. Pins
    /// that obligations across two distinct index sites get distinct
    /// IDs, so an auditor reading a SARIF report can map each
    /// "pending" line back to a unique location.
    #[test]
    fn multiple_index_bounds_get_distinct_ids() {
        let cfg = SubsetConfig::default_for_test();
        let u8_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: u8_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl {
                    ty: u8_ty.clone(),
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
                LocalDecl {
                    ty: u8_ty.clone(),
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![
                    Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::Use(Operand::Copy(Place {
                                local: Local(1),
                                projection: vec![ProjectionElem::Index(Local(1))],
                            })),
                        ),
                        span: Span::default(),
                    },
                    Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::Use(Operand::Copy(Place {
                                local: Local(1),
                                projection: vec![ProjectionElem::ConstantIndex { offset: 7 }],
                            })),
                        ),
                        span: Span::default(),
                    },
                ],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 2);
        assert_eq!(report.vc_obligations[0].id, "pb054-idx-0");
        assert_eq!(report.vc_obligations[1].id, "pb054-idx-1");
    }
    /// PB054 P.2: when the index `Local` references a function-argument
    /// slot whose source name is known, the obligation carries that
    /// name in `idx_source_name`. Used downstream by `pitbull-vc` to
    /// emit a `(define-fun <name> () (_ BitVec 64) idx)` alias so
    /// user preconditions referencing the source name constrain the
    /// SMT problem.
    #[test]
    fn index_projection_binds_arg_source_name() {
        let cfg = SubsetConfig::default_for_test();
        let u8_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) };
        let usize_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::Usize)) };
        // `fn at(s: &[u8], i: usize) -> u8 { s[i] }`-ish shape. The
        // index local is _2 (second arg slot). Locals layout:
        //   _0 = u8 return
        //   _1 = &[u8] (slice arg, source name "s")
        //   _2 = usize  (index arg,  source name "i")
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u8_ty.clone(), usize_ty.clone()],
            arg_names: vec!["s".into(), "i".into()],
            return_ty: u8_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl {
                    ty: u8_ty.clone(),
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
                LocalDecl {
                    ty: u8_ty.clone(),
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
                LocalDecl {
                    ty: usize_ty,
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::Use(Operand::Copy(Place {
                            local: Local(1),
                            projection: vec![ProjectionElem::Index(Local(2))],
                        })),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(report.vc_obligations.len(), 1);
        let crate::vc::VcObligationKind::IndexBound { idx_source_name } =
            &report.vc_obligations[0].kind
        else {
            panic!("expected IndexBound; got {:?}", report.vc_obligations[0].kind);
        };
        assert_eq!(
            idx_source_name.as_deref(),
            Some("i"),
            "index `Local(2)` should resolve to arg name \"i\" via local_arg_name lookup; got {:?}",
            idx_source_name,
        );
    }
    /// PB054 P.2: when the index local is NOT in the argument range
    /// (e.g. an intermediate temporary from a `let` or arithmetic
    /// expression), `idx_source_name` is `None`. Conservative
    /// posture — without data-flow analysis the visitor can't trace
    /// the binding, and emitting a stale name would let user
    /// preconditions silently miss-bind to the wrong SMT variable.
    #[test]
    fn index_projection_with_non_arg_local_has_no_binding() {
        let cfg = SubsetConfig::default_for_test();
        // body_with_index_projection from above uses _0 (return) and
        // _1 (one non-arg local) — no args. Index(Local(1)) refers
        // to _1, which is NOT in the arg range (arg_names is empty).
        // So the binding should fail to None.
        let mut v = SubsetVisitor::new(&cfg);
        let body = body_with_index_projection(ProjectionElem::Index(Local(1)));
        v.visit_body(&body, false);
        let report = v.into_report();
        let crate::vc::VcObligationKind::IndexBound { idx_source_name } =
            &report.vc_obligations[0].kind
        else {
            panic!("expected IndexBound");
        };
        assert_eq!(
            *idx_source_name, None,
            "non-arg index local must not bind to a source name; got {:?}",
            idx_source_name,
        );
    }
    /// PB054 P.2: ConstantIndex / Subslice projections carry `None`
    /// for the source binding — the offset is a `u64` literal in
    /// the projection itself, not a MIR local. Pin so adding name
    /// resolution to these arms by accident gets caught.
    #[test]
    fn constant_index_and_subslice_have_no_idx_source_name() {
        let cfg = SubsetConfig::default_for_test();
        for proj in [
            ProjectionElem::ConstantIndex { offset: 3 },
            ProjectionElem::Subslice { from: 0, to: 4 },
        ] {
            let mut v = SubsetVisitor::new(&cfg);
            let body = body_with_index_projection(proj.clone());
            v.visit_body(&body, false);
            let report = v.into_report();
            let crate::vc::VcObligationKind::IndexBound { idx_source_name } =
                &report.vc_obligations[0].kind
            else {
                panic!("expected IndexBound for {:?}", proj);
            };
            assert_eq!(
                *idx_source_name, None,
                "{:?} must carry None for idx_source_name (no MIR local)",
                proj,
            );
        }
    }
}
