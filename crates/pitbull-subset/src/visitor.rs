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
    /// Spec-derived POSTCONDITIONS for the currently-walked body —
    /// raw `#[pitbull::ensures("...")]` strings (Q.4, 2026-05-26).
    /// Each must hold at every function exit (TerminatorKind::Return).
    /// Set externally before `visit_body` via `set_current_ensures`;
    /// cleared on body exit per the H-RT2 audit-cleanup pattern
    /// (clears even on the trusted-body early-return — see Q.C fix
    /// in visit_body).
    current_body_ensures: Vec<String>,
    /// Return-value type of the currently-walked body — used by
    /// `emit_ensures_obligation` to size the SMT bit-vector for
    /// the `result` binding. Set in `visit_body` from
    /// `body.return_ty`; reset on body exit alongside the other
    /// per-body fields. None when the return type isn't a
    /// primitive integer (audit-note posture: obligation still
    /// emits with empty `ret_ty_name`, the future encoder skips
    /// non-int return types with a separate audit note).
    current_body_return_ty: Option<crate::mir_api::Ty>,
    /// Captured BODY EFFECT: the SMT expression the return value
    /// `result` equals, in terms of (return-typed) argument names.
    /// `Some` only for soundly-capturable straight-line shapes (a
    /// single block returning a Copy/Move of an arg, or a constant);
    /// `None` otherwise → the ensures obligation stays pending. Q.4a
    /// (2026-05-29).
    current_body_effect: Option<String>,
    /// Whether the current body has been declared `#[pitbull::trusted]`.
    /// Trusted bodies are exempt from body-level checks but their *signatures*
    /// are still subject to PSS-1.
    current_body_trusted: bool,
    /// Whether `emit_ensures_obligation` fired for the current body
    /// (i.e. at least one `TerminatorKind::Return` was visited while
    /// `current_body_ensures` was non-empty). Audit-cleanup M-1
    /// (2026-05-26): a divergent body (infinite loop, `panic!` on
    /// all paths, `-> !`) has NO Return terminator, so an
    /// `#[pitbull::ensures]` on it would silently emit ZERO
    /// obligations — the "no silent skips" anti-pattern. At body
    /// exit, if ensures was non-empty but this flag is still false,
    /// we surface an audit note so the gap is visible. Reset at
    /// each `visit_body` entry.
    saw_return_with_ensures: bool,
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
            current_body_ensures: Vec::new(),
            current_body_return_ty: None,
            current_body_effect: None,
            current_body_trusted: false,
            saw_return_with_ensures: false,
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
    /// Install the postcondition list for the next `visit_body`
    /// call. Mirror of `set_current_preconditions` for the
    /// `#[pitbull::ensures("...")]` path (Q.4, 2026-05-26).
    ///
    /// The wrapper looks up the item being walked in
    /// `cfg.verification.ensures` (config-side) and the HIR
    /// pre-pass's `ensures` map (attribute-side), merges them,
    /// and passes the result here. Just like preconditions, the
    /// list is cleared on body exit so a future caller that
    /// forgets to call this between bodies inherits no stale
    /// ensures — see the H-RT2/M-RT-Q.C pattern.
    pub fn set_current_ensures(&mut self, ensures: Vec<String>) {
        self.current_body_ensures = ensures;
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
    /// Record a COVERAGE-GAP audit note: a safety-relevant check that could
    /// not run, with NO compensating VC obligation emitted. It is folded
    /// into the wrapper's exit code (fail closed, via
    /// `verification.fail_on_coverage_gaps`) so the gap is visible to a CI
    /// gate, not just on stderr (the "no silent skips" posture). This is the
    /// FAIL-CLOSED DEFAULT: an audit note is a coverage gap unless its site
    /// explicitly opts out via [`audit_transparency`]. A future note added
    /// here therefore fails closed by default rather than silently passing.
    pub fn audit_note(&mut self, span: Span, message: impl Into<String>) {
        self.audit_notes.push(crate::diagnostic::AuditNote {
            span,
            message: message.into(),
            kind: crate::diagnostic::AuditNoteKind::CoverageGap,
        });
    }
    /// Record a TRANSPARENCY audit note: informational only and MUST NOT
    /// affect the verdict. Use this only when the situation is already
    /// reflected elsewhere — the check ran and concluded safe (e.g. a
    /// value-preserving cast accepted), a VC obligation was emitted
    /// alongside (so an undischarged obligation already drives the exit
    /// code), or it records a user `#[pitbull::trusted]` opt-in.
    pub fn audit_transparency(&mut self, span: Span, message: impl Into<String>) {
        self.audit_notes.push(crate::diagnostic::AuditNote {
            span,
            message: message.into(),
            kind: crate::diagnostic::AuditNoteKind::Transparency,
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
        // Q.4 (2026-05-26): cache the return type so
        // `emit_ensures_obligation` can size the SMT bit-vector
        // for `result`. Cleared on body exit alongside other
        // per-body fields.
        self.current_body_return_ty = Some(body.return_ty.clone());
        // Q.4a: capture the body effect (what `result` equals) for the
        // soundly-capturable straight-line shapes, so emit_ensures_obligation
        // can build a dischargeable SMT problem. None for anything else.
        self.current_body_effect = self.capture_body_effect(body);
        // M-1 (2026-05-26): reset the per-body "saw a return with
        // ensures" flag. Set true in emit_ensures_obligation; checked
        // at body exit to catch divergent bodies whose ensures
        // would otherwise silently produce no obligation.
        self.saw_return_with_ensures = false;
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
        // Trusted bodies: signature-only check stops here. The
        // precondition clear (H-RT2 below) MUST run before this
        // return so the belt-and-suspenders guarantee holds for
        // trusted bodies too. Audit-cleanup post-Q.3 red-team
        // finding M-RT-Q.C (2026-05-26): pre-cleanup the clear
        // ran AFTER the trust early-return, so a trusted body
        // followed by an untrusted body that forgot to call
        // `set_current_preconditions` would leak. Not exploitable
        // today (the wrapper always sets) but a documented
        // guarantee silently didn't hold.
        if self.current_body_trusted {
            // Q.4 (2026-05-26): on a trusted body, ensures
            // strings would otherwise be silently ignored — we
            // skip emitting the obligation (trust means
            // body-content is assumed correct), but surface an
            // audit note so the gap is VISIBLE. Caller-side
            // propagation of trusted ensures (so callers can use
            // them as hypotheses) is out of scope for the MVP.
            if !self.current_body_ensures.is_empty() {
                self.audit_transparency(
                    body.span,
                    "PB076: ensures on trusted body — assumed but not \
                     proven; caller-side propagation of trusted \
                     postconditions is out of scope for the v0.2 MVP",
                );
            }
            self.clear_per_body_state();
            return;
        }
        for block in &body.blocks {
            for stmt in &block.statements {
                self.visit_statement(stmt);
            }
            self.visit_terminator(&block.terminator);
        }
        // M-1 (2026-05-26): a body with `#[pitbull::ensures]` but
        // NO `TerminatorKind::Return` (diverges — infinite loop,
        // `panic!`/`unreachable!` on every path, `-> !`) never
        // reached `emit_ensures_obligation`, so its postcondition
        // would silently produce zero obligations. Surface the gap
        // as an audit note so an auditor doesn't read "0
        // obligations" as "postcondition checked". (Today the
        // ensures obligation is "pending" anyway, but this keeps
        // the "no silent skips" invariant once Q.4a's encoder makes
        // the obligation dischargeable.)
        if !self.current_body_ensures.is_empty() && !self.saw_return_with_ensures {
            // Audit finding (2026-05-26 full-codebase sweep,
            // sharpening the earlier M-1): a returning body with
            // `#[ensures]` emits a "pending" obligation → undischarged
            // → exit 1, but a divergent body previously emitted only
            // a NON-BLOCKING audit note → exit 0. That asymmetry is
            // wrong under fail-closed posture: "we emitted zero
            // obligations for a declared ensures" could mean the
            // function genuinely diverges OR that the adapter missed
            // a Return terminator (our bug). Either way we must NOT
            // claim success. Emit the obligation at the body span so
            // it flows through the same pending → undischarged → exit-1
            // path as a returning body, then add the explanatory note.
            self.emit_ensures_obligation(body.span);
            // Transparency: emit_ensures_obligation above already pushed the
            // (fail-closed, undischarged) obligation, so the exit code
            // reflects the divergent-ensures case; this note just explains it.
            self.audit_transparency(
                body.span,
                "PB076: function declares `#[pitbull::ensures]` but its body \
                 has no return point (it diverges — infinite loop, always \
                 panics, or `-> !`), OR the MIR adapter did not surface a \
                 return terminator. The postcondition obligation is emitted \
                 at the body span and reported undischarged (fail closed): \
                 we will not report success for a declared postcondition we \
                 could not attach to an exit point. If the divergence is \
                 intentional, the ensures is dead and should be removed.",
            );
        }
        // Audit finding H-RT2 (2026-05-26): clear preconditions
        // at body exit so the next `visit_body` cannot
        // accidentally inherit them. The wrapper calls
        // `set_current_preconditions` (and Q.4 `set_current_ensures`)
        // before every `visit_body` — clearing here is a
        // belt-and-suspenders guard for future callers
        // (alt-drivers, tests, refactors) that might forget.
        //
        // We DON'T clear at body ENTRY because the wrapper's
        // contract is "set, then visit" — clearing at entry
        // would zero out what was just set.
        self.clear_per_body_state();
    }
    /// Clear per-body state that's set externally before
    /// `visit_body`. Run at body exit AND before the
    /// trusted-body early-return so the H-RT2 belt-and-suspenders
    /// guarantee holds uniformly. (Audit finding M-RT-Q.C
    /// 2026-05-26.)
    fn clear_per_body_state(&mut self) {
        self.current_body_preconditions.clear();
        self.current_body_ensures.clear();
        self.current_body_return_ty = None;
        self.current_body_effect = None;
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
            // Plain return. Accepted, but Q.4 (2026-05-26) emits
            // a `PB076 EnsuresPostcondition` obligation here if
            // the current body has non-empty
            // `current_body_ensures`. One obligation per return
            // point (a body with multiple early-returns produces
            // N obligations sharing the postcondition list and
            // body-effect summary, but with distinct
            // span+sequence ids).
            TerminatorKind::Return => {
                self.emit_ensures_obligation(term.span);
            }
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
            Some(p) if is_panicking_library_call(p) || is_panicking_int_method(p) => {
                // Two families of un-walked-`core` panics caught at the call
                // site (the panic lives INSIDE a `core` fn the v0.2 wrapper
                // does NOT walk, and there is no prelude model yet, so without
                // catching it HERE the call falls through the `Some(_)`
                // "assume walked elsewhere" arm and is SILENTLY ACCEPTED):
                //   1. Option/Result `unwrap`/`expect`/`unwrap_err`/`expect_err`
                //      — panic on the wrong variant (violating the README's
                //      "no reachable `unwrap`/`expect`"); and
                //   2. primitive-int inherent methods that panic on overflow
                //      or a zero/`MIN` argument — `pow`/`abs`/`div_euclid`/
                //      `rem_euclid`/`next_power_of_two`/`ilog*`. The OPERATOR
                //      form (`x * y`, `x / y`) is caught by PB049, but the
                //      METHOD form (`x.pow(y)`) was silently "verified"
                //      despite the README's unqualified "no integer arithmetic
                //      overflow" claim (deep-audit 2026-06-14).
                // Both are treated exactly like a `panic!` call site (PB043):
                // strict mode rejects; default mode emits a (pending)
                // PanicReachability obligation — the honest "cannot prove this
                // won't panic" (undischarged → fail closed), never a silent pass.
                if self.config.verification.strict_panic_acceptance {
                    self.reject(
                        rules::PB043,
                        span,
                        format!("panicking library call `{p}` (strict mode)"),
                    );
                } else {
                    self.emit_panic_reachability_obligation(p, span);
                }
            }
            Some(_) => {
                // A known callee path not matched by any classifier above.
                // Trust-boundary posture (audit 2026-06-14 — replaces the
                // old "the reachability driver walks the callee's body"
                // claim, which described the test-only `ReachabilityDriver`
                // that production does NOT run):
                //   - An IN-CRATE callee is forced to be walked by the #27
                //     reachability gate in the wrapper (or the run fails
                //     closed), so its own rules fire when it is visited as a
                //     separate subject.
                //   - A NON-LOCAL callee (core/std/alloc, a dependency) is
                //     NOT walked. Such functions are TRUSTED to be total
                //     (panic-free) — modelling them precisely is the
                //     prelude's job in v0.3+. The KNOWN panic-bearing
                //     exceptions (the `unwrap`/`expect` family just above,
                //     and `core::panicking::*`) are already caught, so the
                //     residual trusted surface is the total stdlib. This
                //     boundary is documented in docs/SAFETY-MANUAL.md §3.
                // Either way, nothing to reject at THIS call site.
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
                self.visit_cast(kind, op, target_ty, span);
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
            Rvalue::UnaryOp(unop, op) => {
                self.visit_operand(op, span);
                // Exhaustive over `UnOp` (no `_` wildcard — audit
                // 2026-05-29). Unary negation of a signed integer can
                // overflow (`-(iN::MIN)`), so it carries a PB049
                // obligation. `Not` (bitwise/logical complement) and
                // `PtrMetadata` are total — they cannot panic or
                // overflow — so they emit nothing.
                match unop {
                    crate::mir_api::UnOp::Neg => {
                        self.maybe_emit_neg_overflow_obligation(op, span);
                    }
                    crate::mir_api::UnOp::Not | crate::mir_api::UnOp::PtrMetadata => {}
                }
            }
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
    fn visit_cast(&mut self, kind: &CastKind, op: &Operand, target_ty: &Ty, span: Span) {
        match kind {
            // PB051: narrowing or sign-changing int casts. The cast kind
            // alone does not tell us the source/target widths, so by
            // default we reject every `IntToInt` cast and direct users to
            // `TryFrom` (which we accept and the VC generator discharges).
            //
            // EXEMPTION (#31, 2026-06-13): a cast of an integer CONSTANT
            // whose value provably fits the target type is value-
            // preserving — there is nothing to truncate or sign-change, so
            // PB051's rationale ("truncation needs an explicit obligation")
            // does not apply and accepting it is sound. This is what
            // unblocks shift code: rustc lowers `x << 4` with an implicit
            // `const 4_i32 as u32` — the untyped literal `4` defaults to
            // i32 and is cast to the value type SOLELY for the shift-
            // overflow bounds check (the real `Shl` uses the original
            // operand). That synthetic cast, and any other value-
            // preserving constant cast, is now accepted. Every NON-constant
            // cast and every value-CHANGING constant cast (narrowing like
            // `300 as u8`, sign-flipping like `-1 as u32`, or an
            // unsupported target width) still fails closed via the `None`
            // arm. See `value_preserving_int_cast` for the soundness gate.
            CastKind::IntToInt => match Self::value_preserving_int_cast(op, target_ty) {
                Some((value, src_name, tgt_name)) => self.audit_transparency(
                    span,
                    format!(
                        "PB051: `as` integer cast accepted — constant {value} is \
                         value-preserving from {src_name} to {tgt_name} (no \
                         truncation or sign-change). Non-constant or value-changing \
                         casts remain rejected.",
                    ),
                ),
                None => self.reject(
                    rules::PB051,
                    span,
                    "`as` integer cast (non-constant or value-changing); use `TryFrom` instead",
                ),
            },
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
    /// PB051 value-preservation gate (SOUNDNESS-CRITICAL). Returns
    /// `Some((value, src_ty_name, tgt_ty_name))` ONLY when `op` is an
    /// integer constant whose value is representable in BOTH its own
    /// (source) type and the cast's `target_ty` — i.e. the `IntToInt`
    /// cast provably preserves the value, with no truncation and no
    /// sign-change. In every other case it returns `None`, so the caller
    /// fails closed and PB051 still fires:
    ///   - a non-constant operand (a variable read like `copy _2`, which
    ///     includes a shift amount bound via `let s = 4; x << s`),
    ///   - a constant whose integer value couldn't be extracted,
    ///   - a value outside the target range (narrowing / sign-flipping),
    ///   - a non-primitive or unsupported-width source/target (`u128`,
    ///     `usize`/`isize`), rejected by `value_fits_in_int_ty`.
    ///
    /// The SOURCE-range check is not redundant with the target check: it
    /// rejects the one lossy-extraction case — a `u128` constant above
    /// `i128::MAX`, which the adapter stores as a negative `i128` — by
    /// failing closed rather than trusting the wrapped value.
    fn value_preserving_int_cast(
        op: &Operand,
        target_ty: &Ty,
    ) -> Option<(i128, String, String)> {
        let Operand::Constant(c) = op else {
            return None;
        };
        let value = c.value?;
        let src_name = primitive_int_name_from_ty(&c.ty)?;
        let tgt_name = primitive_int_name_from_ty(target_ty)?;
        if crate::predicate::value_fits_in_int_ty(value, &src_name)
            && crate::predicate::value_fits_in_int_ty(value, &tgt_name)
        {
            Some((value, src_name, tgt_name))
        } else {
            None
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
            // PB053: `char` is accepted as a value type. Char arithmetic
            // is not expressible in safe Rust (`char` implements no
            // `Add`/`Sub`/… ), and char comparisons lower to total `BinOp`
            // ops that cannot panic or overflow — so there is no MIR
            // operation here to reject. PB053 is reserved; no per-construct
            // check is wired because none is reachable through safe Rust.
            // (Earlier comment claimed the BinaryOp visitor catches
            // char-arithmetic; it does not — corrected 2026-06-14 audit.)
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
        // Synthetic ADT placeholders emitted by the rustc_public adapter
        // (`mir_api/adapter.rs`) for real `RigidTy` variants that have no
        // shadow analog (Foreign, CoroutineWitness, a Dynamic that reached
        // `rigid_ty`, Never, and the non-rigid inner of a pattern type).
        // These are NOT real user/library types: the bare `__pitbull_*`
        // single-segment path is unconstructable from Rust source (a real
        // type path is always `crate::...`, never a bare segment), so any
        // ADT carrying this prefix came from the adapter. We MUST classify
        // them explicitly and fail closed by default — letting them reach
        // the accept-everything fall-through below would be a fail-OPEN: an
        // unanalyzable or already-forbidden construct silently "verified"
        // because the visitor didn't recognize it (adapter accept-on-unknown
        // audit, 2026-06-14). Each maps to the rule its real construct would
        // have triggered; an UNKNOWN synthetic (a future adapter mapping not
        // yet classified here) also fails closed via the catch-all.
        if let Some(kind) = path.strip_prefix("__pitbull_") {
            match kind {
                // The never type `!` is uninhabited and benign — it appears
                // in ordinary safe diverging code (panicking helpers, `loop
                // {}`, `match` arms that never yield a value). Accept it;
                // rejecting would be a false positive on safe code.
                "never" => {}
                // `dyn Trait` that reached `rigid_ty` instead of the
                // `TyKind::Dynamic` fast path. PB031 is the primary detector;
                // this is defense-in-depth for a Dynamic nested in a RigidTy.
                "dyn_trait_fallback" => {
                    self.reject(rules::PB031, span, "`dyn Trait` type (rigid-ty fallback)");
                }
                // Coroutine captured-state witness. Coroutines / `async` are
                // PB026 / PB027; the witness type confirms their presence.
                "coroutine_witness" => {
                    self.reject(rules::PB027, span, "coroutine witness type");
                }
                // Foreign (`extern`) type. The FFI surface is PB056.
                "foreign" => {
                    self.reject(rules::PB056, span, "foreign (`extern`) type");
                }
                // `__pitbull_unrigid`: the non-rigid inner of a pattern type,
                // which `rigid_ty_of` could not destructure (it may have
                // erased a `dyn`/type-parameter). Plus, via the catch-all,
                // ANY future synthetic placeholder not classified above.
                // Fail closed — never silently accept a type the pipeline
                // could not analyze. PB039 ("unresolvable") is the closest
                // existing rule for "the visitor cannot reason about this".
                "unrigid" => {
                    self.reject(rules::PB039, span, "unanalyzable type (non-rigid pattern inner)");
                }
                other => {
                    self.reject(
                        rules::PB039,
                        span,
                        format!(
                            "unclassified synthetic adapter type `__pitbull_{other}` — \
                             failing closed (no sound model)"
                        ),
                    );
                }
            }
            // Synthetic namespace fully handled above (any rejection was
            // already pushed). This is the last classification step, so we
            // fall off the end of the function — no early return needed.
        }
        // Anything else (a non-synthetic path that skipped the block above):
        // a user-defined ADT or stdlib type we haven't classified. Accepted;
        // the reachability driver will visit its bodies if reachable.
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
    ///
    /// Audit-cleanup (audit finding N1, 2026-05-26): when the
    /// visitor *can't* emit an obligation for an arithmetic
    /// binop (projected operand, non-int type, mismatched types),
    /// surface an audit note rather than silently returning.
    /// Reason: code like `fn add_tuple(p: (u32, u32)) -> u32 { p.0 + p.1 }`
    /// lowers to a BinaryOp on `Place`s with `ProjectionElem::Field`,
    /// where `operand_primitive_int_name` returns `None` —
    /// pre-audit the obligation was silently dropped. An auditor
    /// reading a report of zero obligations and zero undischarged
    /// would conclude the code was verified when in fact no check
    /// ran. The audit posture is "no silent skips"; surfacing the
    /// gap meets that contract.
    fn maybe_emit_overflow_obligation(
        &mut self,
        binop: crate::mir_api::BinOp,
        lhs: &Operand,
        rhs: &Operand,
        span: Span,
    ) {
        use crate::mir_api::BinOp;
        let arith_op = match binop {
            BinOp::Add => crate::vc::ArithOp::Add,
            BinOp::Sub => crate::vc::ArithOp::Sub,
            BinOp::Mul => crate::vc::ArithOp::Mul,
            // Task R (2026-05-28): Div / Rem now emit a real
            // obligation — division-by-zero plus, for signed types,
            // `MIN / -1` overflow. `pitbull-vc` encodes the
            // violation predicate. Both operands share the operand
            // type in Rust, so the same-type guard below holds.
            BinOp::Div => crate::vc::ArithOp::Div,
            BinOp::Rem => crate::vc::ArithOp::Rem,
            // Task R: Shl / Shr emit the over-shift obligation
            // (shift amount >= bit width). NOTE: a shift's amount
            // may have a DIFFERENT type than the value being
            // shifted (`u32 << u8`). The same-type guard below
            // emits the obligation only when both operands resolve
            // to the SAME type (so the SMT bit-vectors are the same
            // sort and `(bvuge rhs width)` is well-formed); a
            // mixed-width shift falls through to that guard's audit
            // note rather than producing a malformed SMT problem.
            // That is the audit-safe direction (no silent skip;
            // mixed-width shifts surface as an explicit gap). Full
            // mixed-width over-shift encoding is a follow-up.
            BinOp::Shl => crate::vc::ArithOp::Shl,
            BinOp::Shr => crate::vc::ArithOp::Shr,
            // Bitwise and comparison ops have no overflow/panic
            // obligation — they are total functions over their input
            // bit-patterns. `Offset` is pointer arithmetic, which is
            // unreachable here because raw pointers are PB004-rejected
            // upstream; if it somehow appears it has no integer-overflow
            // obligation either. Silent acceptance of these is correct
            // (they cannot panic), not a skip.
            BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::Eq
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Ne
            | BinOp::Ge
            | BinOp::Gt
            | BinOp::Offset => return,
        };
        let lhs_name = self.operand_primitive_int_name(lhs);
        let rhs_name = self.operand_primitive_int_name(rhs);
        let (Some(lhs_name), Some(rhs_name)) = (lhs_name, rhs_name) else {
            // Audit finding N1: at least one operand's type wasn't
            // resolvable. Most common cause: projected operand
            // (`p.0 + p.1`). Audit-safe direction is over-
            // approximate "we tried to check but couldn't" rather
            // than silently treating it as verified. The note
            // surfaces in the report so an auditor sees the gap
            // and can either rewrite the body to bring the
            // operands into a checkable position or accept the
            // scaffold limitation explicitly.
            self.audit_note(
                span,
                format!(
                    "PB049: BinaryOp {arith_op:?} skipped — operand type \
                     unresolvable (likely a projected operand like `p.0 + \
                     p.1`, or a non-primitive-int type). v0.2 scaffold can \
                     only emit overflow obligations when both operands are \
                     direct reads of locals with primitive-integer types. \
                     This gap is tracked for v0.3+ projection-type resolution.",
                ),
            );
            return;
        };
        // #25 (2026-06-14): a mixed-width SHIFT no longer silently passes.
        // Pre-fix, `x: u32 << y: u8` (amount type ≠ value type) emitted only
        // an audit note and NO obligation — so the over-shift went unchecked
        // and the wrapper exited 0 ("verified") even though `y >= 32` panics:
        // a fail-OPEN. Now a mixed-width shift FALLS THROUGH and emits the
        // over-shift obligation at the VALUE width (`lhs_name`). Rust's
        // over-shift check is `(amount as V) >= bits_of(V)` (unsigned, at the
        // value width — verified against real MIR), so the amount (`rhs`) is
        // constrained ONLY when modelling it at V is provably exact:
        //   - a CONSTANT amount whose value FITS V is pinned to `(amount as
        //     V)` by the const-pin below → `(bvuge rhs bits_V)` is the exact
        //     check → safe constants discharge (`x << 4`), over-shifting
        //     constants stay `sat`;
        //   - otherwise (variable amount, or a constant that does NOT fit V
        //     and would truncate under the pin, hiding a real over-shift) the
        //     amount is left FREE → `(bvuge rhs bits_V)` is `sat` → the
        //     obligation does NOT discharge → fail CLOSED (exit 1).
        // Fully discharging a VARIABLE mixed-width amount (modelling it at its
        // own width with zero/sign-extend) is the tracked follow-up.
        let is_shift =
            matches!(arith_op, crate::vc::ArithOp::Shl | crate::vc::ArithOp::Shr);
        let mixed_width_shift = lhs_name != rhs_name && is_shift;
        if lhs_name != rhs_name && !is_shift {
            // Add/Sub/Mul/Div/Rem with differing operand types is
            // unreachable in well-formed MIR post-coercion; surface the
            // anomaly rather than emit a malformed same-sort problem.
            self.audit_note(
                span,
                format!(
                    "PB049: BinaryOp {arith_op:?} skipped — operand types \
                     differ ({lhs_name} vs {rhs_name}). Should be unreachable \
                     in well-formed MIR post-coercion; if you see this note, \
                     the visitor encountered an unusual lowering and the gap \
                     is worth investigating.",
                ),
            );
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
                    // #25: for a mixed-width shift, pin the AMOUNT (rhs) ONLY
                    // when its value fits the value type V — then the pin
                    // renders `(amount as V)` exactly. A non-fitting value
                    // would truncate under the pin (e.g. `u8 << 256` → 0) and
                    // hide a real over-shift, so leave it free (→ sat → fail
                    // closed) instead. (Same-width shifts and Add/Sub/… are
                    // unaffected: `mixed_width_shift` is false for them.)
                    if mixed_width_shift
                        && label == "rhs"
                        && !crate::predicate::value_fits_in_int_ty(value, &lhs_name)
                    {
                        continue;
                    }
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
        // Variable mixed-width discharge (safe subset, 2026-06-14). For a
        // mixed-width shift we model the amount at the VALUE width V (a free
        // V-wide `rhs`). Binding a precondition to it is SOUND only when that
        // modelling is a sound over-approximation: the amount type must be
        // UNSIGNED and no wider than V. Then the real (narrower) amount
        // zero-extends into `rhs`, both the precondition and the over-shift
        // `(bvuge rhs bits_V)` compare UNSIGNED at V, and zero-extension
        // preserves unsigned comparisons against a literal that fits the
        // amount type — so proving `precond ⟹ rhs < bits_V` for ALL V-wide
        // `rhs` implies it for the real amount (e.g. `u32 << y:u8` +
        // `requires(y < 32)` discharges). A SIGNED amount (a negative value
        // over-shifts yet satisfies a signed `< bits_V` bound) or a WIDER
        // amount (truncating to V would hide high bits) is NOT sound to model
        // at V, so it is left UNBOUND → free `rhs` → `(bvuge rhs bits_V)` is
        // `sat` → fail CLOSED. Discharging those needs modelling the amount at
        // its OWN width (zero/sign-extend) — the tracked follow-up.
        let rhs_arg = if mixed_width_shift {
            let sound_at_value_width = matches!(
                (
                    crate::predicate::int_type_info(&rhs_name),
                    crate::predicate::int_type_info(&lhs_name),
                ),
                (Some((false, a_bits)), Some((_, v_bits))) if a_bits <= v_bits
            );
            if sound_at_value_width {
                self.operand_arg_name(rhs)
            } else {
                None
            }
        } else {
            self.operand_arg_name(rhs)
        };
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
            // Transparency: a VC obligation was emitted just above, so a
            // refused precondition only makes that obligation HARDER to
            // discharge (fewer assumptions = fail-closed) — the exit code
            // already reflects it via the (likely undischarged) obligation.
            self.audit_transparency(span, msg);
        }
    }
    /// Emit a PB049 `ArithmeticOverflow` obligation for unary
    /// negation `-(op)` (audit 2026-05-29). The single operand is
    /// carried in the `lhs` SMT position; `pitbull-vc` encodes the
    /// violation predicate `(= lhs iN::MIN)` (the only value whose
    /// negation overflows a signed integer). Mirrors the binary
    /// `maybe_emit_overflow_obligation` for the single-operand case:
    /// constant-pins the operand and binds a precondition on the
    /// operand's source name to `lhs` so `requires("x > -128")`-style
    /// contracts can discharge.
    fn maybe_emit_neg_overflow_obligation(&mut self, op: &Operand, span: Span) {
        let Some(ty_name) = self.operand_primitive_int_name(op) else {
            // Operand type unresolvable (projected operand, or a
            // non-primitive-int type such as a float — float negation
            // cannot overflow). Audit-safe direction: surface the gap
            // rather than silently treat the negation as verified,
            // matching the binary path's N1 posture.
            self.audit_note(
                span,
                "PB049: unary negation skipped — operand type unresolvable \
                 (projected operand, or a non-primitive-int type like a float \
                 whose negation cannot overflow). The v0.2 visitor emits the \
                 negation-overflow obligation only for direct reads of \
                 signed-integer locals; this gap is tracked for v0.3+."
                    .to_string(),
            );
            return;
        };
        // Only SIGNED integer negation can overflow (`-(iN::MIN)`).
        // Rust has no unsigned unary `-`, so MIR never produces Neg on
        // an unsigned type; if one somehow appears, negation cannot
        // panic, so there is nothing to prove. The `i` prefix is the
        // same signedness discriminator `pitbull-vc::IntInfo` uses.
        if !ty_name.starts_with('i') {
            return;
        }
        // Constant-pin the operand if it is a literal (mirrors the
        // binary path's O.2.5 pinning), then process preconditions:
        // a predicate bound to the operand's source name translates
        // against `lhs`; anything else falls back to the F2-validated
        // raw-SMT splice; failures surface as audit notes.
        let mut assumptions: Vec<String> = Vec::new();
        if let Operand::Constant(c) = op {
            if let Some(value) = c.value {
                if let Some(assertion) =
                    crate::predicate::operand_pin_assertion("lhs", value, &ty_name)
                {
                    assumptions.push(assertion);
                }
            }
        }
        let op_arg = self.operand_arg_name(op);
        let mut pending_audit_notes: Vec<String> = Vec::new();
        for raw in &self.current_body_preconditions {
            match crate::predicate::parse_predicate(raw) {
                Ok(pred) if op_arg.as_deref() == Some(pred.var.as_str()) => {
                    match crate::predicate::predicate_to_smt_assertion(&pred, "lhs", &ty_name) {
                        Ok(smt) => assumptions.push(smt),
                        Err(e) => pending_audit_notes.push(format!(
                            "rejecting precondition (parsed and bound to the negation \
                             operand but translation failed): {e} — input: {raw:?}",
                        )),
                    }
                }
                // Parsed-but-unbound, or unparsable: try the raw
                // SMT-LIB splice behind the F2 lex guard.
                _ => match crate::predicate::validate_assertion_form(raw) {
                    Ok(()) => assumptions.push(raw.clone()),
                    Err(e) => pending_audit_notes.push(format!(
                        "rejecting precondition (not bindable to the negation operand \
                         and not a valid SMT-LIB `(assert ...)` form): {e} — input: {raw:?}",
                    )),
                },
            }
        }
        let seq = self.vc_obligations.len();
        let id = format!("pb049-{}-{}", crate::vc::ArithOp::Neg.tag(), seq);
        self.vc_obligations.push(crate::vc::VcObligation {
            id,
            span,
            kind: crate::vc::VcObligationKind::ArithmeticOverflow {
                op: crate::vc::ArithOp::Neg,
                ty_name,
            },
            assumptions,
        });
        for msg in pending_audit_notes {
            // Transparency: a VC obligation was emitted just above, so a
            // refused precondition only makes that obligation HARDER to
            // discharge (fewer assumptions = fail-closed) — the exit code
            // already reflects it via the (likely undischarged) obligation.
            self.audit_transparency(span, msg);
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
        // Apply F2 lex validation to each precondition before
        // attaching to the obligation. Today `pitbull-vc::compile`
        // returns `None` for `PanicReachability` so the
        // assumptions never reach the solver, but pinning the
        // validation contract now prevents a future PB043 backend
        // from accidentally accepting a multi-directive injection
        // via the assumptions field. Audit-cleanup (audit finding
        // F8, 2026-05-26): consistency with the
        // `ArithmeticOverflow` and `IndexBound` paths.
        let mut assumptions: Vec<String> =
            Vec::with_capacity(self.current_body_preconditions.len());
        let mut pending_audit_notes: Vec<String> = Vec::new();
        for raw in &self.current_body_preconditions {
            match crate::predicate::validate_assertion_form(raw) {
                Ok(()) => assumptions.push(raw.clone()),
                Err(e) => {
                    pending_audit_notes.push(format!(
                        "PB043: rejecting precondition (not a valid SMT-LIB \
                         `(assert ...)` form): {e} — input: {raw:?}",
                    ));
                }
            }
        }
        self.vc_obligations.push(crate::vc::VcObligation {
            id,
            span,
            kind: crate::vc::VcObligationKind::PanicReachability,
            assumptions,
        });
        for msg in pending_audit_notes {
            // Transparency: a VC obligation was emitted just above, so a
            // refused precondition only makes that obligation HARDER to
            // discharge (fewer assumptions = fail-closed) — the exit code
            // already reflects it via the (likely undischarged) obligation.
            self.audit_transparency(span, msg);
        }
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
        // Each precondition string goes through three potential
        // paths, in order:
        //   1. `parse_ident_vs_ident_predicate` — `i < len`-style
        //      (vision-audit #2 / Phase B 2026-05-26). Translates
        //      with target type `u64` (IndexBound's canonical
        //      width). The two idents must resolve in the SMT
        //      problem; we check against the known-name set
        //      {`idx`, `len`, idx_source_name?} and audit-note
        //      otherwise.
        //   2. `parse_predicate` — `i < 100`-style ident-vs-int.
        //      Same name binding rules; literal range-checked
        //      against u64.
        //   3. `validate_assertion_form` — raw SMT-LIB splice
        //      (O.1 escape hatch). For preconditions that
        //      reference symbols our parser doesn't know.
        //
        // On any failure, emit a precondition-specific audit
        // note so the auditor sees exactly which path rejected
        // and why. Audit posture: no silent skips.
        let known_smt_names: Vec<&str> = {
            let mut v = vec!["idx", "len"];
            if let Some(name) = &idx_source_name {
                v.push(name.as_str());
            }
            v
        };
        let mut assumptions: Vec<String> =
            Vec::with_capacity(self.current_body_preconditions.len());
        let mut pending_audit_notes: Vec<String> = Vec::new();
        for raw in &self.current_body_preconditions {
            // Path 1: ident-vs-ident.
            if let Ok(p) = crate::predicate::parse_ident_vs_ident_predicate(raw) {
                if known_smt_names.contains(&p.lhs.as_str())
                    && known_smt_names.contains(&p.rhs.as_str())
                {
                    match crate::predicate::ident_vs_ident_to_smt_assertion(&p, "u64") {
                        Ok(smt) => {
                            assumptions.push(smt);
                            continue;
                        }
                        Err(e) => {
                            pending_audit_notes.push(format!(
                                "PB054: rejecting precondition (ident-vs-ident \
                                 parsed but translation failed): {e} — input: {raw:?}",
                            ));
                            continue;
                        }
                    }
                }
                pending_audit_notes.push(format!(
                    "PB054: rejecting precondition (ident-vs-ident parsed \
                     but at least one side does not resolve in the SMT \
                     problem). Known names: {known_smt_names:?}; got \
                     lhs={:?} rhs={:?}; input: {raw:?}",
                    p.lhs, p.rhs,
                ));
                continue;
            }
            // Path 2: ident-vs-int.
            if let Ok(p) = crate::predicate::parse_predicate(raw) {
                if known_smt_names.contains(&p.var.as_str()) {
                    // `var` resolves; translate vs u64 (IndexBound
                    // canonical width). The translator emits
                    // `(assert (bv<op> <var> <hex-literal>))`.
                    match crate::predicate::predicate_to_smt_assertion(&p, &p.var, "u64") {
                        Ok(smt) => {
                            assumptions.push(smt);
                            continue;
                        }
                        Err(e) => {
                            pending_audit_notes.push(format!(
                                "PB054: rejecting precondition (predicate parsed \
                                 and bound but translation failed): {e} — input: {raw:?}",
                            ));
                            continue;
                        }
                    }
                }
                // Predicate parses but var doesn't resolve. Fall
                // through to raw-splice; if it's valid SMT it
                // gets through.
            }
            // Path 3: raw SMT-LIB splice (with F2 lex validation).
            match crate::predicate::validate_assertion_form(raw) {
                Ok(()) => assumptions.push(raw.clone()),
                Err(e) => {
                    pending_audit_notes.push(format!(
                        "PB054: rejecting precondition (not a recognized \
                         predicate form nor a valid SMT-LIB `(assert ...)` \
                         form): {e} — input: {raw:?}",
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
            // Transparency: a VC obligation was emitted just above, so a
            // refused precondition only makes that obligation HARDER to
            // discharge (fewer assumptions = fail-closed) — the exit code
            // already reflects it via the (likely undischarged) obligation.
            self.audit_transparency(span, msg);
        }
    }
    /// Emit a `PB076 EnsuresPostcondition` VC obligation at a
    /// `TerminatorKind::Return`. Task Q.4 (2026-05-26).
    ///
    /// Only emits when `current_body_ensures` is non-empty. The
    /// obligation carries:
    /// - `ret_name = "result"` (Creusot's lowercase convention)
    /// - `ret_ty_name = primitive_int_name_from_ty(&body.return_ty)`
    ///   or empty string when the return type isn't a primitive
    ///   integer (the future encoder rejects non-int return types
    ///   with an audit note rather than producing a malformed
    ///   SMT problem).
    ///
    /// `assumptions` is the merge of preconditions (carried for
    /// caller-context propagation) plus each ensures string,
    /// each passing F2 lex validation before attachment. The
    /// `pitbull-vc::compile` returns `None` for the MVP; the
    /// wrapper surfaces each obligation as "pending". The
    /// body-effect encoder that produces a real SMT problem
    /// lands in Q.4a.
    ///
    /// Obligation id format: `pb076-ensures-{seq}`.
    fn emit_ensures_obligation(&mut self, term_span: Span) {
        if self.current_body_ensures.is_empty() {
            return;
        }
        self.saw_return_with_ensures = true;
        let seq = self.vc_obligations.len();
        let id = format!("pb076-ensures-{seq}");
        let ret_ty_name = self
            .current_body_return_ty
            .as_ref()
            .and_then(primitive_int_name_from_ty);
        // Q.4a: build the dischargeable SMT problem (declarations +
        // preconditions + captured body effect + negated postcondition).
        // Returns `(None, None, Some(reason))` and leaves the obligation
        // PENDING when the return type is non-primitive, the body effect
        // wasn't captured, or a postcondition couldn't be translated —
        // fail closed; never guess the body.
        let (discharge_smt, consistency_smt, why_pending) =
            self.build_ensures_smt(ret_ty_name.as_deref());
        if let Some(reason) = why_pending {
            // Transparency: the EnsuresPostcondition obligation is pushed
            // just below regardless, and reports "pending" → undischarged →
            // exit code; this note only explains why it stayed pending.
            self.audit_transparency(term_span, reason);
        }
        self.vc_obligations.push(crate::vc::VcObligation {
            id,
            span: term_span,
            kind: crate::vc::VcObligationKind::EnsuresPostcondition {
                ret_name: "result".into(),
                ret_ty_name,
                discharge_smt,
                consistency_smt,
            },
            // Preconditions are baked into `discharge_smt`; the generic
            // `assumptions` field is unused for the ensures obligation.
            assumptions: Vec::new(),
        });
    }
    /// Build the ensures discharge + consistency SMT problems (Q.4a).
    /// Returns `(discharge, consistency, pending_reason)`. `discharge`
    /// is `Some` only when the return type is a primitive integer, the
    /// body effect was captured, and EVERY postcondition translated;
    /// otherwise it is `None` (pending) and `pending_reason` explains
    /// why (surfaced as an audit note). `consistency` is `Some` only
    /// when there are preconditions (the F1 vacuous-precondition guard).
    ///
    /// SMT shape:
    /// ```text
    /// (set-logic QF_BV)
    /// (declare-const result (_ BitVec W)) (declare-const <arg> ...) ...
    /// <preconditions over args>                  ; assumed
    /// (assert (= result <captured body effect>)) ; the body
    /// (assert (not (and <postconditions>)))      ; negated goal
    /// (check-sat)                                ; unsat ⇒ holds
    /// ```
    fn build_ensures_smt(
        &self,
        ret_ty: Option<&str>,
    ) -> (Option<String>, Option<String>, Option<String>) {
        let Some(ret_ty) = ret_ty else {
            return (
                None,
                None,
                Some(
                    "PB076: ensures on a function whose return type is not a primitive \
                     integer — cannot size the `result` bit-vector, so the postcondition \
                     cannot be discharged; obligation pending."
                        .to_string(),
                ),
            );
        };
        let Some((_signed, bits)) = crate::predicate::int_type_info(ret_ty) else {
            return (
                None,
                None,
                Some(format!(
                    "PB076: unsupported return type {ret_ty} for ensures discharge; pending.",
                )),
            );
        };
        let Some(effect) = self.current_body_effect.clone() else {
            return (
                None,
                None,
                Some(
                    "PB076: could not capture the function's return value (body effect) — \
                     only single-block straight-line returns of a (return-typed) argument \
                     or a constant are captured today; arithmetic, branches, and calls stay \
                     pending (arithmetic body effects land in the Q.4b follow-up)."
                        .to_string(),
                ),
            );
        };
        // SMT variable scopes — SOUNDNESS-CRITICAL split (audit 2026-05-31).
        // POSTCONDITIONS may reference `result` (the return value) plus the
        // return-typed args; PRECONDITIONS may reference the args ONLY.
        // `result` is the OUTPUT: a precondition that constrains it would be
        // assumed as a (circular) hypothesis ABOUT the output, which can
        // vacuously discharge a false postcondition — e.g. `requires(result <
        // 100)` + `ensures(result < 100)` on `fn f(x:u8)->u8 { x }` would make
        // the main check `result=x ∧ result<100 ∧ ¬(result<100)` unsat and
        // "discharge", though f(200)=200. Excluding `result` from the
        // precondition scope makes such a precondition untranslatable, so the
        // obligation stays pending (fail closed).
        let mut known_post: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        known_post.insert("result".to_string());
        let mut known_pre: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut ret_typed_args: Vec<String> = Vec::new();
        for (i, name) in self.current_body_arg_names.iter().enumerate() {
            if name.is_empty() {
                continue;
            }
            // `result` is the reserved SMT binding for the return value.
            // A parameter of the same name would emit a duplicate
            // `(declare-const result ...)` and conflate input with
            // output — fail closed rather than risk an ambiguous encoding.
            if name == "result" {
                return (
                    None,
                    None,
                    Some(
                        "PB076: a function parameter is named `result`, which collides \
                         with the reserved binding for the return value — cannot \
                         disambiguate input from output; obligation pending."
                            .to_string(),
                    ),
                );
            }
            // Parameter `i` is MIR local `i + 1`.
            if let Some(ld) = self.current_body_locals.get(i + 1) {
                if primitive_int_name_from_ty(&ld.ty).as_deref() == Some(ret_ty) {
                    known_post.insert(name.clone());
                    known_pre.insert(name.clone());
                    ret_typed_args.push(name.clone());
                }
            }
        }
        // Preconditions → assumption asserts. If ANY precondition can't
        // be translated, the WHOLE obligation is PENDING — we attempt a
        // discharge only when EVERY assumption is faithfully encoded.
        // Dropping an assumption is sound against false discharge (fewer
        // assumptions only makes `unsat` harder), but it can yield a
        // spurious counterexample/refutation; failing closed to
        // "pending" is the more honest posture and matches the rule
        // "fail closed for anything we can't soundly capture".
        let mut assumptions: Vec<String> = Vec::new();
        for raw in &self.current_body_preconditions {
            match translate_spec_to_assert(raw, &known_pre, ret_ty) {
                Some(a) => assumptions.push(a),
                None => {
                    return (
                        None,
                        None,
                        Some(format!(
                            "PB076: precondition {raw:?} could not be translated to a \
                             well-sorted assumption over the return-typed arguments — use \
                             `<ident> <cmp> <literal>` or `<ident> <cmp> <ident>` over \
                             those arg names (preconditions may NOT reference `result`, the \
                             output; raw SMT-LIB specs are deferred); obligation pending.",
                        )),
                    );
                }
            }
        }
        // Postconditions → inner terms. If ANY can't be translated, the
        // WHOLE obligation is pending: we must never silently drop a
        // postcondition we can't verify and then report the rest as
        // discharged.
        let mut post_terms: Vec<String> = Vec::new();
        for raw in &self.current_body_ensures {
            match translate_spec_to_term(raw, &known_post, ret_ty) {
                Some(t) => post_terms.push(t),
                None => {
                    return (
                        None,
                        None,
                        Some(format!(
                            "PB076: postcondition {raw:?} could not be translated — use \
                             `result <cmp> <literal>` or `result <cmp> <return-typed arg>` \
                             (raw SMT-LIB specs are deferred); obligation pending.",
                        )),
                    );
                }
            }
        }
        if post_terms.is_empty() {
            return (None, None, None);
        }
        let mut decls = format!("(declare-const result (_ BitVec {bits}))\n");
        for arg in &ret_typed_args {
            decls.push_str(&format!("(declare-const {arg} (_ BitVec {bits}))\n"));
        }
        let mut discharge = String::from("(set-logic QF_BV)\n");
        discharge.push_str(&decls);
        for a in &assumptions {
            discharge.push_str(a);
            if !a.ends_with('\n') {
                discharge.push('\n');
            }
        }
        discharge.push_str(&format!("(assert (= result {effect}))\n"));
        let negated = if post_terms.len() == 1 {
            format!("(not {})", post_terms[0])
        } else {
            format!("(not (and {}))", post_terms.join(" "))
        };
        discharge.push_str(&format!("(assert {negated})\n(check-sat)\n"));
        let consistency = if assumptions.is_empty() {
            None
        } else {
            // F1 vacuous-precondition guard. The check must reflect the FULL
            // hypothesis set the main check assumes — the preconditions AND
            // the captured body effect `(= result <effect>)` — so that a
            // hypothesis contradicting the body effect is detected as vacuity
            // (defense-in-depth alongside the input-only precondition scope
            // above). A consistency `unsat` ⇒ the main check's `unsat` is
            // vacuous ⇒ the wrapper refuses to claim discharge.
            let mut c = String::from("(set-logic QF_BV)\n");
            c.push_str(&decls);
            for a in &assumptions {
                c.push_str(a);
                if !a.ends_with('\n') {
                    c.push('\n');
                }
            }
            c.push_str(&format!("(assert (= result {effect}))\n"));
            c.push_str("(check-sat)\n");
            Some(c)
        };
        (Some(discharge), consistency, None)
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
    /// Q.4a/Q.4b body-effect capture (SOUNDNESS-CRITICAL). Returns the
    /// SMT expression that the return value `result` equals, in terms of
    /// return-typed argument names — but ONLY for shapes we can capture
    /// with certainty. For ANY other shape it returns `None`, and the
    /// `#[ensures]` obligation then stays pending (never a guess).
    ///
    /// Captured shape: a LINEAR chain of basic blocks ending in `Return`,
    /// where every non-final block ends in `Goto` or an `Assert` (we
    /// follow the `Assert`'s SUCCESS target — assert failure panics and
    /// never returns, so the asserted condition is irrelevant to the
    /// returning value). Any branch (`SwitchInt`), call, drop, tail call,
    /// yield, or back-edge (loop) makes the body uncapturable. Within the
    /// chain, the return local `_0` must resolve to: a Copy/Move of a
    /// return-typed argument; an integer constant; the `.0` field of a
    /// captured checked-arithmetic result; or an `Add`/`Sub`/`Mul` over
    /// two captured return-typed operands.
    ///
    /// Q.4b note on arithmetic: `Add`/`Sub`/`Mul` are encoded as the
    /// WRAPPING bit-vector ops `bvadd`/`bvsub`/`bvmul`, which are modular
    /// over 2^width — exactly Rust's wrapping semantics and exactly the
    /// value the overflow-check's success path produces. Modelling the
    /// wrap over the FULL input range (instead of excluding the
    /// overflow-panic region the `Assert` guards) is an
    /// over-approximation: `unsat` still means "the postcondition holds
    /// for every input that actually returns", so discharge stays sound;
    /// at worst it is conservative (a postcondition that holds only
    /// because overflow would have panicked stays pending/sat).
    ///
    /// Every captured value is return-typed, so the resulting expression
    /// is a single uniform `BitVec<ret-width>` sort — matching `result`.
    fn capture_body_effect(&self, body: &crate::mir_api::Body) -> Option<String> {
        use crate::mir_api::{StatementKind, TerminatorKind};
        let ret_ty = primitive_int_name_from_ty(&body.return_ty)?;
        // local → SMT expr for a return-typed SCALAR value held there.
        let mut env: std::collections::HashMap<u32, String> =
            std::collections::HashMap::new();
        // local → SMT expr for the `.0` field of a checked-arithmetic
        // tuple result held there (`_t = Add(a,b)` makes `_t.0` the
        // wrapping sum). Kept separate from `env` because the whole tuple
        // is NOT a return-typed scalar — only its `.0` projection is.
        let mut checked: std::collections::HashMap<u32, String> =
            std::collections::HashMap::new();
        // Seed return-typed parameters by the SAME criterion
        // `build_ensures_smt` uses to DECLARE them (the cached
        // `current_body_arg_names` + `current_body_locals[i+1].ty`), so
        // the names that can appear in the captured effect are EXACTLY
        // the SMT variables that get declared — undeclared-symbol
        // mismatch is impossible by construction, not merely fail-closed.
        // MIR `Local(i+1)` is the i-th parameter.
        for (i, name) in self.current_body_arg_names.iter().enumerate() {
            if name.is_empty() {
                continue;
            }
            if let Some(ld) = self.current_body_locals.get(i + 1) {
                if primitive_int_name_from_ty(&ld.ty).as_deref() == Some(ret_ty.as_str()) {
                    env.insert((i as u32) + 1, name.clone());
                }
            }
        }
        // Walk the linear block chain from bb0, following Goto /
        // Assert-success until Return. A revisited block is a back-edge
        // (loop) → fail closed. The visited set also bounds the walk.
        let mut current: u32 = 0;
        let mut visited: std::collections::HashSet<u32> =
            std::collections::HashSet::new();
        loop {
            if !visited.insert(current) {
                return None; // back-edge / loop — uncapturable
            }
            let block = body.blocks.get(current as usize)?;
            for stmt in &block.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if !place.projection.is_empty() {
                    // Write through a projection — invalidate the base
                    // local's scalar value AND any checked-arith result
                    // (fail closed).
                    env.remove(&place.local.0);
                    checked.remove(&place.local.0);
                    continue;
                }
                let l = place.local.0;
                match self.capture_rvalue(rvalue, &env, &checked, &ret_ty) {
                    Some(e) => {
                        // Store under BOTH maps: a whole read (`move _l`)
                        // resolves via `env` (gated by a return-type check
                        // on `_l`), a `.0` read (`move (_l.0)`) resolves
                        // via `checked`. The captured expr is return-typed
                        // either way, so both reads are sound.
                        env.insert(l, e.clone());
                        checked.insert(l, e);
                    }
                    None => {
                        env.remove(&l);
                        checked.remove(&l);
                    }
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Return => return env.get(&0).cloned(),
                TerminatorKind::Goto { target } => current = target.0,
                // An `Assert` (overflow / bounds / div-by-zero) only gates
                // control flow; its success target is the sole path that
                // returns. Follow it; the asserted condition is not
                // modelled (sound — it would only ADD an assumption).
                TerminatorKind::Assert { target, .. } => current = target.0,
                // Branches, calls, drops, tail calls, yields, unreachable,
                // unwinds, inline asm — uncapturable. Fail closed.
                _ => return None,
            }
        }
    }
    /// Capture an rvalue as a return-typed SMT expression, or `None`.
    /// Handles a `Use` (copy/move/const/`.0`-of-checked) and the
    /// same-type arithmetic ops `Add`/`Sub`/`Mul`/`Div`/`Rem`; every
    /// other rvalue is uncapturable (fail closed).
    fn capture_rvalue(
        &self,
        rvalue: &Rvalue,
        env: &std::collections::HashMap<u32, String>,
        checked: &std::collections::HashMap<u32, String>,
        ret_ty: &str,
    ) -> Option<String> {
        use crate::mir_api::BinOp;
        match rvalue {
            Rvalue::Use(op) => self.capture_operand(op, env, checked, ret_ty),
            // Same-type integer arithmetic (Q.4b add/sub/mul, Q.4c
            // div/rem). All encodings are verified against Z3 to match
            // Rust EXACTLY:
            //   - `bvadd`/`bvsub`/`bvmul` are modular over 2^width =
            //     Rust's wrapping (and the value the overflow check's
            //     success path yields).
            //   - `bvsdiv`/`bvudiv` = Rust `/` (truncate toward zero).
            //   - `bvsrem`/`bvurem` = Rust `%` (remainder with the
            //     DIVIDEND's sign). NOTE: signed `%` is `bvsrem`, NOT
            //     `bvsmod` (which takes the divisor's sign) — they differ
            //     (e.g. `7 % -2` is `1` vs `-1`).
            // The panic guards (overflow, div-by-zero, signed MIN/-1) are
            // NOT modelled: we capture the op over the FULL input range, a
            // sound over-approximation (the returning inputs are a subset,
            // so `unsat` still means "holds for every returning input").
            // Arithmetic operands are same-type (uniform width). Shifts
            // (Q.4d): `<<` = `bvshl`; `>>` = `bvashr` (arithmetic,
            // sign-filling) for a SIGNED value, `bvlshr` (logical) for an
            // UNSIGNED one — selected by the VALUE's signedness, verified
            // vs Z3. The shift AMOUNT may be a different integer type, so
            // it goes through `capture_shift_amount` (rendered at the
            // value width); over-shift amounts are not excluded — the SMT
            // op yields the same sound over-approximation as the other
            // panic guards. Bitwise ops stay deferred — fail closed.
            Rvalue::BinaryOp(op, a, b) => {
                let signed = crate::predicate::int_type_info(ret_ty).map(|(s, _)| s)?;
                let smt_op = match op {
                    BinOp::Add => "bvadd",
                    BinOp::Sub => "bvsub",
                    BinOp::Mul => "bvmul",
                    BinOp::Div if signed => "bvsdiv",
                    BinOp::Div => "bvudiv",
                    BinOp::Rem if signed => "bvsrem",
                    BinOp::Rem => "bvurem",
                    BinOp::Shl => "bvshl",
                    BinOp::Shr if signed => "bvashr",
                    BinOp::Shr => "bvlshr",
                    _ => return None,
                };
                let ea = self.capture_operand(a, env, checked, ret_ty)?;
                let eb = match op {
                    BinOp::Shl | BinOp::Shr => {
                        self.capture_shift_amount(b, env, checked, ret_ty)?
                    }
                    _ => self.capture_operand(b, env, checked, ret_ty)?,
                };
                Some(format!("({smt_op} {ea} {eb})"))
            }
            // Casts, refs, len, aggregates, etc. — uncapturable. Fail
            // closed; never invent a body effect.
            _ => None,
        }
    }
    /// Capture an operand as a return-typed SMT expression, or `None`.
    /// A whole-local read (`move _l`) and a constant require the operand
    /// type to equal the return type (uniform `BitVec` sort). A `.0`
    /// field read resolves a captured checked-arithmetic result, whose
    /// `.0` is return-typed by construction.
    fn capture_operand(
        &self,
        op: &Operand,
        env: &std::collections::HashMap<u32, String>,
        checked: &std::collections::HashMap<u32, String>,
        ret_ty: &str,
    ) -> Option<String> {
        use crate::mir_api::ProjectionElem;
        match op {
            Operand::Copy(p) | Operand::Move(p) => {
                if p.projection.is_empty() {
                    // Whole-local read: require the local to be
                    // return-typed, then resolve its scalar value.
                    if self.operand_primitive_int_name(op).as_deref() != Some(ret_ty) {
                        return None;
                    }
                    env.get(&p.local.0).cloned()
                } else if p.projection.len() == 1
                    && matches!(p.projection[0], ProjectionElem::Field(0))
                {
                    // `_t.0` of a captured checked-arithmetic tuple. Its
                    // `.0` is the wrapping result — return-typed by
                    // construction (we only record `checked[_t]` for an
                    // Add/Sub/Mul over return-typed operands), so no extra
                    // type check is required (and `operand_primitive_int_name`
                    // can't see the projected field's type regardless).
                    checked.get(&p.local.0).cloned()
                } else {
                    // Deref, nested fields, indexing, multi-element
                    // projections — uncapturable.
                    None
                }
            }
            Operand::Constant(c) => {
                if self.operand_primitive_int_name(op).as_deref() != Some(ret_ty) {
                    return None;
                }
                let v = c.value?;
                crate::predicate::format_int_literal_for_ty(v, ret_ty)
            }
        }
    }
    /// Capture a SHIFT AMOUNT operand as a value-width SMT expression, or
    /// `None`. The amount's own integer type may differ from the value's,
    /// but SMT shifts need both operands at the value width:
    ///   - a CONSTANT amount is rendered at the value's width directly —
    ///     only its (small, non-negative) value matters, and an over-shift
    ///     amount renders fine because the SMT op then yields the sound
    ///     over-approximation of the over-shift panic;
    ///   - a VARIABLE amount is accepted ONLY when it is already the
    ///     return type (same width, already declared as an SMT var). A
    ///     narrower/wider variable amount would need zero-extend/truncate
    ///     plus its own declaration — deferred (fail closed).
    fn capture_shift_amount(
        &self,
        op: &Operand,
        env: &std::collections::HashMap<u32, String>,
        checked: &std::collections::HashMap<u32, String>,
        ret_ty: &str,
    ) -> Option<String> {
        match op {
            Operand::Constant(c) => {
                let v = c.value?;
                crate::predicate::format_int_literal_for_ty(v, ret_ty)
            }
            Operand::Copy(_) | Operand::Move(_) => {
                self.capture_operand(op, env, checked, ret_ty)
            }
        }
    }
}
// ---------------------------------------------------------------------------
// Q.4a spec-translation gate (SOUNDNESS-CRITICAL, free functions).
//
// These translate a user-authored spec string (a precondition or a
// postcondition) into SMT-LIB, admitting ONLY forms whose every
// identifier is one of the SMT-bound names in `known` (= {result} ∪
// the return-typed argument names, all declared at the return width).
// Any shape that doesn't fit returns `None`; the caller turns that
// into "obligation pending" — never a guess about what the body or
// the spec means. Restricting to the uniform return width keeps every
// emitted symbol one consistent BitVec sort, so the solver can never
// silently coerce a mismatched operand.
// ---------------------------------------------------------------------------
/// Strip the outer `(assert <term>)` wrapper, returning `<term>`.
/// Delegates the single-directive / no-injection check to
/// `validate_assertion_form`, so a multi-directive or quoted-symbol
/// string is rejected (`None`) rather than mis-stripped.
fn strip_assert(s: &str) -> Option<String> {
    crate::predicate::validate_assertion_form(s).ok()?;
    let t = s.trim();
    // `validate_assertion_form` guarantees a leading `(assert` and a
    // single balanced top-level directive, so the final byte is that
    // assert's own close-paren.
    let inner = t.strip_prefix("(assert")?.strip_suffix(')')?.trim();
    if inner.is_empty() {
        return None;
    }
    Some(inner.to_string())
}
/// Translate a spec string into a single SMT-LIB `(assert ...)`.
/// Two structured forms are accepted, each over names bound in
/// `known`: an ident-vs-ident comparison (`result <= n`, both sides
/// bound), and an ident-vs-literal comparison (`result < 101`, the
/// literal range-checked against `ret_ty`). Anything else — including
/// raw `(assert ...)` SMT, deferred this increment — returns `None`.
/// `ret_ty` drives the signed-vs-unsigned operator choice and the
/// literal range; every ident is the same `ret_ty` width, so the
/// produced assertion is well-sorted by construction.
fn translate_spec_to_assert(
    raw: &str,
    known: &std::collections::HashSet<String>,
    ret_ty: &str,
) -> Option<String> {
    // 1. ident-vs-ident (`result <= n`, `lo == hi`).
    if let Ok(p) = crate::predicate::parse_ident_vs_ident_predicate(raw) {
        if known.contains(&p.lhs) && known.contains(&p.rhs) {
            return crate::predicate::ident_vs_ident_to_smt_assertion(&p, ret_ty).ok();
        }
        // Matched the shape but an operand isn't an SMT-bound name —
        // fail closed rather than emit an assertion over a free
        // (undeclared) symbol.
        return None;
    }
    // 2. ident-vs-literal (`result < 101`, `result == 0`).
    if let Ok(p) = crate::predicate::parse_predicate(raw) {
        if known.contains(&p.var) {
            // The SMT symbol name IS the source ident (we declared it
            // under that exact name).
            return crate::predicate::predicate_to_smt_assertion(&p, &p.var, ret_ty).ok();
        }
        return None;
    }
    // Raw-SMT specs and every other shape stay pending this increment.
    None
}
/// Translate a spec string into the inner SMT term (no `(assert )`
/// wrapper) for embedding in `(not (and ...))`. `None` ⇒ untranslatable.
fn translate_spec_to_term(
    raw: &str,
    known: &std::collections::HashSet<String>,
    ret_ty: &str,
) -> Option<String> {
    let assertion = translate_spec_to_assert(raw, known, ret_ty)?;
    strip_assert(&assertion)
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
/// Whether a fully-qualified callee path names a standard-library
/// `Option`/`Result` combinator that PANICS on the wrong variant —
/// `unwrap`, `expect`, `unwrap_err`, `expect_err`.
///
/// ## Why this is soundness-critical (audit 2026-06-14)
///
/// The panic these raise lives INSIDE the library function (in `core`),
/// not at the call site. The v0.2 wrapper walks only `all_local_items()`;
/// it does NOT transitively walk into `core`, and there is no prelude
/// model for these functions yet. A call to `x.unwrap()` lowers to
/// `Call(core::option::Option::<T>::unwrap, …)`, whose body (with the
/// real `core::panicking::panic` call) is never visited. Without
/// recognizing the call HERE it falls through `classify_called_function`'s
/// "assume walked elsewhere" (`Some(_)`) arm and is SILENTLY ACCEPTED — a
/// false "verified" on ubiquitous code, directly violating the README's
/// "No reachable `panic!`, `unwrap`, `expect`, or `unreachable!` call
/// site" guarantee. The visitor treats a match exactly like a `panic!`
/// site (PB043): strict mode rejects; default mode emits a pending
/// `PanicReachability` obligation, so the verdict is the honest "cannot
/// prove this won't panic" (undischarged) rather than a silent pass.
///
/// ## Matching
///
/// Post-monomorphization the path carries generic args, e.g.
/// `core::option::Option::<u32>::unwrap` (plus the `std::` re-export
/// form), so we anchor on the `option::Option` / `result::Result` type
/// qualifier via `contains` (robust to the `<T>` infix and to the
/// `<.. as ..>` trait-impl rendering) and the panicking method name.
/// Intentionally conservative: a (rare) user extension method named
/// `unwrap` on `Option` that does NOT panic would also be flagged — but
/// the fail direction is safe (an extra obligation, never a missed one),
/// the correct posture for a soundness-first tool. The non-panicking
/// combinators end in `_or` / `_or_default` / `_or_else`, not a bare
/// `::unwrap`/`::expect`, so they are NOT matched.
///
/// Free-standing so corpus / unit tests can pin the classification
/// without the full visitor machinery, mirroring `is_panic_call_path`.
#[must_use]
pub fn is_panicking_library_call(p: &str) -> bool {
    if !(p.contains("option::Option") || p.contains("result::Result")) {
        return false;
    }
    p.ends_with("::unwrap")
        || p.ends_with("::expect")
        || p.ends_with("::unwrap_err")
        || p.ends_with("::expect_err")
}
/// Whether `p` names a primitive-integer inherent method that PANICS — on
/// overflow or a zero/`MIN` argument: `pow`, `abs`, `div_euclid`,
/// `rem_euclid`, `next_power_of_two`, `ilog`/`ilog2`/`ilog10`.
///
/// ## Why (deep-audit 2026-06-14)
///
/// Same un-walked-`core` mechanism as [`is_panicking_library_call`]: the
/// panic lives inside the `core` method, which the wrapper never walks. The
/// OPERATOR forms (`x * y`, `x / y`, `x % y`) are caught by PB049 in the MIR
/// visitor, but the METHOD forms lower to a `Call(core::num::<impl T>::…)`
/// whose overflow/zero `Assert` is inside the un-walked callee — so
/// `fn f(x:u32,y:u32)->u32 { x.pow(y) }` was reported `verified` despite
/// overflowing, contradicting the README's (formerly unqualified) "No
/// integer arithmetic overflow" guarantee. Routed through the same
/// fail-closed PB043 handling so it is honestly undischarged, not silently
/// passed.
///
/// ## Matching
///
/// Anchored on the `num::<impl …>` inherent-impl rendering rustc produces
/// for primitive-int methods (verified empirically: the path is
/// `core::num::<impl u32>::pow`), so a user method merely *named* `pow` is
/// not matched. The NON-panicking families end in different suffixes and are
/// correctly excluded: `wrapping_*` / `overflowing_*` (`::wrapping_pow`,
/// `::overflowing_pow` end `_pow`, not `::pow`), `checked_*`, `saturating_*`,
/// `unsigned_abs` (`_abs`, not `::abs`), `abs_diff` (`_diff`), `isqrt`.
#[must_use]
pub fn is_panicking_int_method(p: &str) -> bool {
    if !p.contains("num::<impl") {
        return false;
    }
    p.ends_with("::pow")
        || p.ends_with("::abs")
        || p.ends_with("::div_euclid")
        || p.ends_with("::rem_euclid")
        || p.ends_with("::next_power_of_two")
        || p.ends_with("::ilog")
        || p.ends_with("::ilog2")
        || p.ends_with("::ilog10")
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
    // ----- adapter synthetic-ADT accept-on-unknown closure -------------
    // The rustc_public adapter maps real RigidTy variants with no shadow
    // analog to synthetic `__pitbull_*` placeholder ADTs. classify_adt
    // must classify these EXPLICITLY (fail closed) rather than let them
    // reach the user-ADT accept fall-through (adapter accept-on-unknown
    // audit, 2026-06-14). These tests run on stable (the adapter itself
    // is nightly-only, so the synthetic paths are constructed by hand).
    fn body_returning_synthetic(path: &str) -> Body {
        let mut body = empty_body();
        body.return_ty = Ty {
            kind: TyKind::RigidTy(RigidTy::Adt(AdtDef {
                path: path.into(),
                is_union: false,
            })),
        };
        body
    }
    /// `__pitbull_dyn_trait_fallback` (a `dyn Trait` that reached rigid_ty)
    /// must fire PB031, not be silently accepted.
    #[test]
    fn synthetic_dyn_trait_fallback_rejected_pb031() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_returning_synthetic("__pitbull_dyn_trait_fallback"), false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB031),
            "dyn-trait fallback synthetic must fire PB031; got {:?}",
            v.errors,
        );
    }
    /// `__pitbull_coroutine_witness` must fire PB027.
    #[test]
    fn synthetic_coroutine_witness_rejected_pb027() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_returning_synthetic("__pitbull_coroutine_witness"), false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB027),
            "coroutine-witness synthetic must fire PB027; got {:?}",
            v.errors,
        );
    }
    /// `__pitbull_foreign` (an `extern` type) must fire PB056.
    #[test]
    fn synthetic_foreign_rejected_pb056() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_returning_synthetic("__pitbull_foreign"), false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB056),
            "foreign synthetic must fire PB056; got {:?}",
            v.errors,
        );
    }
    /// `__pitbull_unrigid` (a non-rigid pattern inner that may have erased
    /// a dyn/type-param) must fail closed via PB039.
    #[test]
    fn synthetic_unrigid_rejected_pb039() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_returning_synthetic("__pitbull_unrigid"), false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB039),
            "unrigid synthetic must fire PB039; got {:?}",
            v.errors,
        );
    }
    /// Fail-closed DEFAULT for the synthetic namespace: a FUTURE adapter
    /// placeholder not yet classified here must STILL be rejected, so
    /// adding a new synthetic mapping can never silently reopen the
    /// accept-on-unknown hole.
    #[test]
    fn synthetic_unknown_fails_closed_pb039() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_returning_synthetic("__pitbull_some_future_kind"), false);
        assert!(
            v.errors.iter().any(|e| e.rule == rules::PB039),
            "unknown synthetic must fail closed (PB039); got {:?}",
            v.errors,
        );
    }
    /// `__pitbull_never` (the `!` type) is benign and MUST be accepted —
    /// rejecting it would false-positive on safe diverging code (panicking
    /// helpers, `loop {}`, value-less `match` arms).
    #[test]
    fn synthetic_never_accepted() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_returning_synthetic("__pitbull_never"), false);
        assert!(
            v.errors.is_empty(),
            "__pitbull_never must be accepted (benign uninhabited type); got {:?}",
            v.errors,
        );
    }
    /// A genuine user ADT must STILL flow through the accept fall-through —
    /// the synthetic-namespace closure must not over-reach onto real types.
    #[test]
    fn real_user_adt_still_accepted_after_synthetic_closure() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_returning_synthetic("user_crate::MyStruct"), false);
        assert!(
            v.errors.is_empty(),
            "a real user ADT must remain accepted; got {:?}",
            v.errors,
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
    /// Audit finding N1: when a `BinaryOp::Add` (or Sub/Mul) has
    /// projected operands like `p.0 + p.1`, the visitor previously
    /// silently dropped the PB049 obligation — an auditor reading
    /// the report would see "0 obligations" and conclude the body
    /// was verified, when in fact no check ran. This test pins
    /// the audit-cleanup fix: the obligation is still NOT emitted
    /// (the visitor cannot construct a typed claim about projected
    /// operands today), but a `PB049: ... skipped` audit note now
    /// surfaces the gap.
    #[test]
    fn n1_projected_operand_emits_audit_note_for_skipped_pb049() {
        use crate::mir_api::*;
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        // `fn add_tuple(p: (u32, u32)) -> u32 { p.0 + p.1 }`-style
        // shape: BinaryOp::Add with operands that have
        // ProjectionElem::Field projections.
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone()],
            arg_names: vec!["p".into()],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl {
                    ty: u32_ty.clone(),
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
                LocalDecl {
                    ty: u32_ty.clone(),
                    span: Span::default(),
                    mutability: Mutability::Not,
                },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place {
                                local: Local(1),
                                projection: vec![ProjectionElem::Field(0)],
                            }),
                            Operand::Copy(Place {
                                local: Local(1),
                                projection: vec![ProjectionElem::Field(1)],
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
        // No obligation emitted (operand type unresolvable).
        assert!(
            report.vc_obligations.is_empty(),
            "projected operand should NOT emit a PB049 obligation today \
             (the visitor cannot construct a typed claim); got: {:?}",
            report.vc_obligations,
        );
        // But an audit note must surface the gap. Pre-audit (silent
        // skip) this list was empty — the gap was invisible.
        let pb049_skip_notes: Vec<_> = report
            .audit_notes
            .iter()
            .filter(|n| n.message.starts_with("PB049: BinaryOp"))
            .filter(|n| n.message.contains("skipped"))
            .collect();
        assert_eq!(
            pb049_skip_notes.len(),
            1,
            "exactly one PB049-skipped audit note expected; got {:?}",
            report.audit_notes,
        );
        // M1 (deep-audit 2026-06-14): the skip note MUST be a CoverageGap so
        // it folds into the fail-closed exit code — this is the exact
        // `p.0 + p.1` fail-open M1 closes. Pinning the kind here catches a
        // future refactor that flips this site to `audit_transparency`
        // (which would silently re-open exit-0 on unmodelable arithmetic).
        assert_eq!(
            report.coverage_gap_count(),
            1,
            "the PB049 projected-operand skip must be a CoverageGap; got {:?}",
            report.audit_notes,
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
    /// M1: the unclassifiable-callee note is a COVERAGE GAP (no rule could
    /// be applied at the call site, no obligation emitted), so it is counted
    /// by `coverage_gap_count()` and folds into the fail-closed exit code.
    #[test]
    fn unclassifiable_callee_note_is_coverage_gap() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_calling_unclassifiable(), false);
        let report = v.into_report();
        assert_eq!(
            report.coverage_gap_count(),
            1,
            "an unclassifiable callee is a coverage gap; got {:?}",
            report.audit_notes,
        );
        assert!(
            report
                .audit_notes
                .iter()
                .all(|n| n.kind == crate::diagnostic::AuditNoteKind::CoverageGap),
            "all notes here must be CoverageGap; got {:?}",
            report.audit_notes,
        );
    }
    /// M1: a clean body has zero coverage gaps (so it can't false-positive
    /// the fail-closed exit code).
    #[test]
    fn clean_body_has_no_coverage_gaps() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&empty_body(), false);
        assert_eq!(v.into_report().coverage_gap_count(), 0);
    }
    /// M1: the divergent-`ensures` note is TRANSPARENCY — an
    /// EnsuresPostcondition obligation is emitted alongside it (which drives
    /// the exit code via undischarged), so the note itself must NOT
    /// double-count as a coverage gap.
    #[test]
    fn divergent_ensures_note_is_transparency() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result > 0".to_string()]);
        // empty_body has no blocks → no Return terminator → divergent.
        v.visit_body(&empty_body(), false);
        let report = v.into_report();
        assert!(
            report.audit_notes.iter().any(|n| n.message.contains("no return point")),
            "expected the divergent-ensures explanatory note; got {:?}",
            report.audit_notes,
        );
        assert_eq!(
            report.coverage_gap_count(),
            0,
            "the divergent-ensures note is Transparency (its obligation already \
             drives the exit code); got {:?}",
            report.audit_notes,
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
    // ----- panic-bearing library calls (unwrap/expect) -----------------
    // Reachability-integrity fix (audit 2026-06-14): the panic inside
    // `Option`/`Result::unwrap`/`expect` is in `core` (not walked, no
    // prelude model), so it must be caught at the CALL SITE or it is
    // silently accepted — a false "verified" on `x.unwrap()`.
    /// `is_panicking_library_call` recognizes the panic-bearing
    /// Option/Result combinators (incl. post-mono generic-arg and
    /// `std::` re-export forms) and does NOT match the non-panicking
    /// `unwrap_or*` family or unrelated calls.
    #[test]
    fn is_panicking_library_call_classification() {
        let positive = [
            "core::option::Option::<u32>::unwrap",
            "core::option::Option::unwrap",
            "std::option::Option::<i64>::expect",
            "core::result::Result::<u8, E>::unwrap",
            "core::result::Result::<T, E>::unwrap_err",
            "std::result::Result::<T, E>::expect_err",
        ];
        for p in positive {
            assert!(is_panicking_library_call(p), "should be a panicking lib call: {p}");
        }
        let negative = [
            "core::option::Option::<u32>::unwrap_or",
            "core::option::Option::<u32>::unwrap_or_default",
            "core::option::Option::<u32>::unwrap_or_else",
            "core::option::Option::<u32>::is_some",
            "core::option::Option::<u32>::map",
            "my_crate::Thing::unwrap_widget", // user fn, not Option/Result
            "core::result::Result::<T, E>::is_ok",
            "",
        ];
        for p in negative {
            assert!(!is_panicking_library_call(p), "should NOT be a panicking lib call: {p}");
        }
    }
    /// Default mode: a call to `Option::unwrap` emits a PanicReachability
    /// obligation (the honest "cannot prove this won't panic"), NOT a
    /// silent accept. This is the headline reachability-integrity fix.
    #[test]
    fn default_unwrap_call_emits_panic_reachability_obligation() {
        let cfg = SubsetConfig::default_for_test();
        assert!(!cfg.verification.strict_panic_acceptance);
        for path in [
            "core::option::Option::<u32>::unwrap",
            "std::option::Option::<u32>::expect",
            "core::result::Result::<u32, ()>::unwrap",
            "core::result::Result::<u32, ()>::unwrap_err",
        ] {
            let mut v = SubsetVisitor::new(&cfg);
            v.visit_body(&body_calling(path), false);
            let report = v.into_report();
            assert!(
                !report.errors.iter().any(|e| e.rule == rules::PB043),
                "{path}: default mode must NOT hard-reject (obligation instead); got {:?}",
                report.errors,
            );
            assert!(
                report.vc_obligations.iter().any(|o| matches!(
                    o.kind,
                    crate::vc::VcObligationKind::PanicReachability,
                )),
                "{path}: must emit a PanicReachability obligation; got {:?}",
                report.vc_obligations,
            );
        }
    }
    /// Strict mode: `Option::unwrap` is a hard PB043 reject (no
    /// obligation), mirroring the strict-mode `panic!` posture.
    #[test]
    fn strict_mode_unwrap_call_rejects_pb043() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.verification.strict_panic_acceptance = true;
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_calling("core::option::Option::<u32>::unwrap"), false);
        let report = v.into_report();
        assert!(
            report.errors.iter().any(|e| e.rule == rules::PB043),
            "strict mode: unwrap must hard-reject PB043; got {:?}",
            report.errors,
        );
        assert!(
            !report.vc_obligations.iter().any(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::PanicReachability,
            )),
            "strict mode emits no obligation (the reject already terminates the check)",
        );
    }
    /// Negative: the non-panicking `unwrap_or` must NOT be flagged —
    /// neither a reject nor an obligation (it cannot panic on the empty
    /// variant). Guards against over-reach that would false-positive on
    /// safe code.
    #[test]
    fn unwrap_or_is_not_flagged_as_panic() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_calling("core::option::Option::<u32>::unwrap_or"), false);
        let report = v.into_report();
        assert!(
            !report.errors.iter().any(|e| e.rule == rules::PB043),
            "unwrap_or must not hard-reject; got {:?}",
            report.errors,
        );
        assert!(
            !report.vc_obligations.iter().any(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::PanicReachability,
            )),
            "unwrap_or must not emit a PanicReachability obligation; got {:?}",
            report.vc_obligations,
        );
    }
    // ----- panicking primitive-int methods (pow/abs/div_euclid/...) -----
    // Deep-audit 2026-06-14: same un-walked-core mechanism as unwrap/expect;
    // the OPERATOR form is PB049 but the METHOD form was silently accepted.
    /// `is_panicking_int_method` matches the panic-bearing inherent int
    /// methods (in the `num::<impl …>` rendering) and excludes the
    /// non-panicking `checked_/wrapping_/overflowing_/saturating_/unsigned_`
    /// families.
    #[test]
    fn is_panicking_int_method_classification() {
        let positive = [
            "core::num::<impl u32>::pow",
            "core::num::<impl i32>::abs",
            "core::num::<impl i32>::div_euclid",
            "core::num::<impl i64>::rem_euclid",
            "core::num::<impl u32>::next_power_of_two",
            "core::num::<impl u32>::ilog2",
        ];
        for p in positive {
            assert!(is_panicking_int_method(p), "should be a panicking int method: {p}");
        }
        let negative = [
            "core::num::<impl u32>::wrapping_add",
            "core::num::<impl u32>::wrapping_pow",
            "core::num::<impl u32>::checked_pow",
            "core::num::<impl u32>::overflowing_pow",
            "core::num::<impl u32>::saturating_pow",
            "core::num::<impl i32>::unsigned_abs",
            "core::num::<impl u32>::abs_diff",
            "core::num::<impl u32>::isqrt",
            "core::num::<impl u32>::count_ones",
            "my_crate::Widget::pow", // a user method named pow, not num::<impl>
        ];
        for p in negative {
            assert!(!is_panicking_int_method(p), "should NOT be a panicking int method: {p}");
        }
    }
    /// Default mode: `x.pow(y)` / `x.abs()` / `x.div_euclid(y)` emit a
    /// PanicReachability obligation (honest "cannot prove no overflow"), so
    /// the method-form overflow is no longer silently "verified".
    #[test]
    fn panicking_int_methods_emit_obligation_method_form_not_silent() {
        let cfg = SubsetConfig::default_for_test();
        for path in [
            "core::num::<impl u32>::pow",
            "core::num::<impl i32>::abs",
            "core::num::<impl i32>::div_euclid",
        ] {
            let mut v = SubsetVisitor::new(&cfg);
            v.visit_body(&body_calling(path), false);
            let report = v.into_report();
            assert!(
                report.vc_obligations.iter().any(|o| matches!(
                    o.kind,
                    crate::vc::VcObligationKind::PanicReachability,
                )),
                "{path}: must emit a PanicReachability obligation; got {:?}",
                report.vc_obligations,
            );
        }
    }
    /// Negative: the non-panicking `wrapping_add` must NOT be flagged (it
    /// cannot panic) — guards against over-reach onto the safe families.
    #[test]
    fn wrapping_int_method_is_not_flagged() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&body_calling("core::num::<impl u32>::wrapping_add"), false);
        let report = v.into_report();
        assert!(
            !report.vc_obligations.iter().any(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::PanicReachability,
            )) && !report.errors.iter().any(|e| e.rule == rules::PB043),
            "wrapping_add must not be flagged; got errors {:?}, obligations {:?}",
            report.errors,
            report.vc_obligations,
        );
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
    /// M-1 (audit-cleanup 2026-05-26): a divergent body (no
    /// `TerminatorKind::Return`) that declares `#[pitbull::ensures]`
    /// must FAIL CLOSED: emit a (pending, undischarged) PB076
    /// obligation AND surface an explanatory audit note. The earlier
    /// M-1 fix only emitted the note (non-blocking → exit 0); the
    /// full-codebase sweep sharpened it to also emit the obligation
    /// so a divergent body with ensures is no less strict than a
    /// returning one. `empty_body()` has no blocks, hence no Return,
    /// modelling the diverging case (infinite loop / always-panics /
    /// `-> !`) — or an adapter that missed a return terminator.
    #[test]
    fn ensures_on_divergent_body_fails_closed_with_obligation_and_note() {
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 101".to_string()]);
        let body = empty_body(); // no blocks → no Return terminator
        v.visit_body(&body, false);
        let report = v.into_report();
        // Fail closed: the obligation IS emitted (at body span) so it
        // flows through the pending → undischarged → exit-1 path,
        // exactly like a returning body's ensures in the MVP.
        let pb076_count = report
            .vc_obligations
            .iter()
            .filter(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::EnsuresPostcondition { .. }
            ))
            .count();
        assert_eq!(
            pb076_count, 1,
            "divergent body with ensures must STILL emit a (pending) PB076 \
             obligation — fail closed, no exit-0 asymmetry vs returning bodies",
        );
        // And the gap must be explained as an audit note.
        let has_divergent_note = report
            .audit_notes
            .iter()
            .any(|n| n.message.contains("no return point"));
        assert!(
            has_divergent_note,
            "divergent body with ensures must surface a 'no return point' \
             audit note; got notes: {:?}",
            report.audit_notes,
        );
    }
    /// Task R (2026-05-28): div/rem/shift binops with same-type
    /// operands now emit a real `ArithmeticOverflow` obligation
    /// (PB049) — division-by-zero / signed MIN-/-1 / over-shift,
    /// encoded by `pitbull-vc`. This SUPERSEDES the earlier
    /// audit-note-only treatment from the full-codebase sweep.
    /// Pins: one obligation per op, kind = ArithmeticOverflow,
    /// op matches, id prefix `pb049-<tag>-`, no coverage-gap
    /// audit note.
    #[test]
    fn div_rem_shift_same_type_emit_arith_obligation() {
        use crate::mir_api::{BinOp, UintTy};
        let cfg = SubsetConfig::default_for_test();
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let cases = [
            (BinOp::Div, crate::vc::ArithOp::Div, "div"),
            (BinOp::Rem, crate::vc::ArithOp::Rem, "rem"),
            (BinOp::Shl, crate::vc::ArithOp::Shl, "shl"),
            (BinOp::Shr, crate::vc::ArithOp::Shr, "shr"),
        ];
        for (binop, expected_op, tag) in cases {
            let mut v = SubsetVisitor::new(&cfg);
            let body = Body {
                def_id: DefId(0),
                arg_tys: vec![u32_ty.clone(), u32_ty.clone()],
                arg_names: vec!["a".into(), "b".into()],
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
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::BinaryOp(
                                binop,
                                Operand::Copy(Place { local: Local(1), projection: vec![] }),
                                Operand::Copy(Place { local: Local(2), projection: vec![] }),
                            ),
                        ),
                        span: Span::default(),
                    }],
                    terminator: Terminator { kind: TerminatorKind::Return, span: Span::default() },
                }],
                span: Span::default(),
            };
            v.visit_body(&body, false);
            let report = v.into_report();
            assert_eq!(
                report.vc_obligations.len(), 1,
                "{binop:?} must emit exactly one obligation; got {:?}",
                report.vc_obligations,
            );
            let crate::vc::VcObligationKind::ArithmeticOverflow { op, ty_name } =
                &report.vc_obligations[0].kind
            else {
                panic!("{binop:?} must emit ArithmeticOverflow; got {:?}", report.vc_obligations[0].kind);
            };
            assert_eq!(*op, expected_op, "{binop:?} obligation op");
            assert_eq!(ty_name, "u32");
            assert!(
                report.vc_obligations[0].id.starts_with(&format!("pb049-{tag}-")),
                "{binop:?} id should be pb049-{tag}-N; got {:?}",
                report.vc_obligations[0].id,
            );
            // No coverage-gap audit note now that the op is encoded.
            assert!(
                !report.audit_notes.iter().any(|n| n.message.contains("does not yet emit")
                    || n.message.contains("coverage gap")),
                "{binop:?} must NOT carry a coverage-gap note now that it emits; \
                 got: {:?}",
                report.audit_notes,
            );
        }
    }
    /// #31 (2026-06-13): PB051 value-preserving-constant exemption.
    /// A cast of an integer CONSTANT whose value fits the target type is
    /// value-preserving (no truncation, no sign-change) and is ACCEPTED;
    /// every non-constant or value-changing cast still fails CLOSED. The
    /// headline case is `4_i32 as u32` — the synthetic cast rustc inserts
    /// for `x << 4`'s shift-overflow bounds check.
    #[test]
    fn pb051_const_cast_value_preservation_matrix() {
        use crate::mir_api::{CastKind, IntTy, UintTy};
        let cfg = SubsetConfig::default_for_test();
        let i32_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Int(IntTy::I32)) };
        let u8_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) };
        let u32_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let u64_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U64)) };
        let u128_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U128)) };
        let const_op = |value: i128, ty: Ty| {
            Operand::Constant(ConstOperand { ty, def_id: None, path: None, value: Some(value) })
        };
        // (operand, target_ty, accept?, label)
        let cases: Vec<(Operand, Ty, bool, &str)> = vec![
            (const_op(4, i32_ty()), u32_ty(), true, "4_i32 as u32 (the `x << 4` shift cast)"),
            (const_op(200, u32_ty()), u8_ty(), true, "200_u32 as u8 (value fits despite narrowing width)"),
            (const_op(300, i32_ty()), u8_ty(), false, "300_i32 as u8 (truncating)"),
            (const_op(-1, i32_ty()), u32_ty(), false, "-1_i32 as u32 (sign-flipping)"),
            (const_op(300, u32_ty()), u8_ty(), false, "300_u32 as u8 (truncating)"),
            (const_op(5, i32_ty()), u128_ty(), false, "5_i32 as u128 (unsupported target → fail closed)"),
            (
                Operand::Copy(Place { local: Local(1), projection: vec![] }),
                u32_ty(),
                false,
                "copy _1:u64 as u32 (non-constant → fail closed)",
            ),
        ];
        for (op, target_ty, accept, label) in cases {
            let mut v = SubsetVisitor::new(&cfg);
            let body = Body {
                def_id: DefId(0),
                arg_tys: vec![],
                arg_names: vec![],
                return_ty: target_ty.clone(),
                is_unsafe: false,
                is_async: false,
                locals: vec![
                    LocalDecl { ty: target_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                    LocalDecl { ty: u64_ty(), span: Span::default(), mutability: Mutability::Not },
                ],
                blocks: vec![BasicBlockData {
                    statements: vec![Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::Cast(CastKind::IntToInt, op, target_ty.clone()),
                        ),
                        span: Span::default(),
                    }],
                    terminator: Terminator { kind: TerminatorKind::Return, span: Span::default() },
                }],
                span: Span::default(),
            };
            v.visit_body(&body, false);
            let report = v.into_report();
            let fired = report.errors.iter().any(|e| e.rule == rules::PB051);
            if accept {
                assert!(!fired, "PB051 must NOT fire on {label}; errors: {:?}", report.errors);
                assert!(
                    report.audit_notes.iter().any(|n| n.message.contains("value-preserving")),
                    "{label} should carry a value-preserving transparency note; got: {:?}",
                    report.audit_notes,
                );
            } else {
                assert!(fired, "PB051 MUST fire (fail closed) on {label}; errors: {:?}", report.errors);
            }
        }
    }
    /// #31 (2026-06-13): the actual repro. A faithful shadow of rustc's
    /// `fn f(x: u32) -> u32 { x << 4 }` MIR — the untyped `4` defaults to
    /// i32 and is cast `const 4_i32 as u32` SOLELY for the shift-overflow
    /// bounds check (`Lt(_, 32_u32)` guarding the `Shl`). Pre-fix PB051
    /// fired on that cast and made all `x << N` code unverifiable. The
    /// success criterion: ZERO subset errors on this valid shift.
    #[test]
    fn pb051_does_not_fire_on_real_shift_amount_cast() {
        use crate::mir_api::{BinOp, CastKind, IntTy, UintTy};
        let cfg = SubsetConfig::default_for_test();
        let u32_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let i32_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Int(IntTy::I32)) };
        let bool_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Bool) };
        let const_i32 = |v: i128| {
            Operand::Constant(ConstOperand { ty: i32_ty(), def_id: None, path: None, value: Some(v) })
        };
        let const_u32 = |v: i128| {
            Operand::Constant(ConstOperand { ty: u32_ty(), def_id: None, path: None, value: Some(v) })
        };
        let mut v = SubsetVisitor::new(&cfg);
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty()],
            arg_names: vec!["x".into()],
            return_ty: u32_ty(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl { ty: u32_ty(), span: Span::default(), mutability: Mutability::Not }, // _0 ret
                LocalDecl { ty: u32_ty(), span: Span::default(), mutability: Mutability::Not }, // _1 x
                LocalDecl { ty: u32_ty(), span: Span::default(), mutability: Mutability::Not }, // _2 cast result
                LocalDecl { ty: bool_ty(), span: Span::default(), mutability: Mutability::Not }, // _3 cmp
            ],
            blocks: vec![
                BasicBlockData {
                    statements: vec![
                        Statement {
                            kind: StatementKind::Assign(
                                Place { local: Local(2), projection: vec![] },
                                Rvalue::Cast(CastKind::IntToInt, const_i32(4), u32_ty()),
                            ),
                            span: Span::default(),
                        },
                        Statement {
                            kind: StatementKind::Assign(
                                Place { local: Local(3), projection: vec![] },
                                Rvalue::BinaryOp(
                                    BinOp::Lt,
                                    Operand::Move(Place { local: Local(2), projection: vec![] }),
                                    const_u32(32),
                                ),
                            ),
                            span: Span::default(),
                        },
                    ],
                    terminator: Terminator {
                        kind: TerminatorKind::Assert {
                            cond: Operand::Move(Place { local: Local(3), projection: vec![] }),
                            expected: true,
                            msg: AssertMessage::Overflow,
                            target: BasicBlock(1),
                        },
                        span: Span::default(),
                    },
                },
                BasicBlockData {
                    statements: vec![Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place { local: Local(1), projection: vec![] }),
                                const_i32(4),
                            ),
                        ),
                        span: Span::default(),
                    }],
                    terminator: Terminator { kind: TerminatorKind::Return, span: Span::default() },
                },
            ],
            span: Span::default(),
        };
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(
            report.errors.len(),
            0,
            "#31: valid shift code `x << 4` must produce zero subset errors \
             (PB051 must not fire on the shift-amount cast); got: {:?}",
            report.errors,
        );
        assert!(
            report.audit_notes.iter().any(|n| n.message.contains("value-preserving")),
            "the accepted shift-amount cast should leave a transparency note; got: {:?}",
            report.audit_notes,
        );
    }
    /// Audit 2026-05-29 (CRITICAL fix): unary negation `-(a)` on a
    /// signed integer must emit a PB049 `ArithmeticOverflow` obligation
    /// (op = Neg) — previously the `Rvalue::UnaryOp(_, _)` wildcard
    /// swallowed it, so `-(i32::MIN)` (a runtime panic) was reported
    /// "safe". `!a` (bitwise Not) is total and must emit nothing.
    #[test]
    fn neg_signed_emits_arith_obligation_not_swallowed() {
        use crate::mir_api::{IntTy, UnOp};
        let cfg = SubsetConfig::default_for_test();
        let i32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Int(IntTy::I32)) };
        let make_body = |unop: UnOp| Body {
            def_id: DefId(0),
            arg_tys: vec![i32_ty.clone()],
            arg_names: vec!["a".into()],
            return_ty: i32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl { ty: i32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: i32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::UnaryOp(
                            unop,
                            Operand::Copy(Place { local: Local(1), projection: vec![] }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator { kind: TerminatorKind::Return, span: Span::default() },
            }],
            span: Span::default(),
        };
        // `-a` (Neg) on i32 → exactly one PB049 Neg obligation.
        let mut v = SubsetVisitor::new(&cfg);
        v.visit_body(&make_body(UnOp::Neg), false);
        let report = v.into_report();
        assert_eq!(
            report.vc_obligations.len(), 1,
            "`-a` must emit exactly one obligation; got {:?}", report.vc_obligations,
        );
        let crate::vc::VcObligationKind::ArithmeticOverflow { op, ty_name } =
            &report.vc_obligations[0].kind
        else {
            panic!("`-a` must emit ArithmeticOverflow; got {:?}", report.vc_obligations[0].kind);
        };
        assert_eq!(*op, crate::vc::ArithOp::Neg, "negation obligation op");
        assert_eq!(ty_name, "i32");
        assert!(
            report.vc_obligations[0].id.starts_with("pb049-neg-"),
            "id should be pb049-neg-N; got {:?}", report.vc_obligations[0].id,
        );
        // `!a` (bitwise Not) is total → no obligation.
        let mut v2 = SubsetVisitor::new(&cfg);
        v2.visit_body(&make_body(UnOp::Not), false);
        let report2 = v2.into_report();
        assert!(
            report2.vc_obligations.is_empty(),
            "`!a` (Not) must emit no obligation; got {:?}", report2.vc_obligations,
        );
    }
    /// #25 (2026-06-14): a VARIABLE mixed-width shift (`u32 << u8`) is no
    /// longer a silent pass. Pre-fix it emitted NO obligation + an audit
    /// note, so the over-shift went unchecked and the wrapper exited 0
    /// (fail-OPEN). Now it emits the over-shift obligation at the VALUE
    /// width (`u32`) with the amount LEFT FREE (no rhs-constraining
    /// assumption), so `(bvuge rhs bits_V)` is `sat` → the obligation does
    /// NOT discharge → fail CLOSED. (A constant amount fitting V discharges;
    /// see `mixed_width_const_shift_pins_only_when_value_fits`.)
    #[test]
    fn mixed_width_variable_shift_emits_freed_obligation_fail_closed() {
        use crate::mir_api::{BinOp, UintTy};
        let cfg = SubsetConfig::default_for_test();
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let u8_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) };
        let mut v = SubsetVisitor::new(&cfg);
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone(), u8_ty.clone()],
            arg_names: vec!["a".into(), "b".into()],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u32_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                LocalDecl { ty: u8_ty.clone(), span: Span::default(), mutability: Mutability::Not },
            ],
            blocks: vec![BasicBlockData {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place { local: Local(0), projection: vec![] },
                        Rvalue::BinaryOp(
                            BinOp::Shl,
                            Operand::Copy(Place { local: Local(1), projection: vec![] }),
                            Operand::Copy(Place { local: Local(2), projection: vec![] }),
                        ),
                    ),
                    span: Span::default(),
                }],
                terminator: Terminator { kind: TerminatorKind::Return, span: Span::default() },
            }],
            span: Span::default(),
        };
        v.visit_body(&body, false);
        let report = v.into_report();
        assert_eq!(
            report.vc_obligations.len(),
            1,
            "variable mixed-width shift must now emit one over-shift obligation \
             (fail-closed), not skip it; got {:?}",
            report.vc_obligations,
        );
        let crate::vc::VcObligationKind::ArithmeticOverflow { op, ty_name } =
            &report.vc_obligations[0].kind
        else {
            panic!("expected ArithmeticOverflow; got {:?}", report.vc_obligations[0].kind);
        };
        assert_eq!(*op, crate::vc::ArithOp::Shl);
        assert_eq!(ty_name, "u32", "obligation must be at the VALUE width");
        // The amount (rhs) is LEFT FREE — no rhs-constraining assumption —
        // so the obligation cannot vacuously discharge (fail closed).
        assert!(
            !report.vc_obligations[0]
                .assumptions
                .iter()
                .any(|a| a.contains("rhs")),
            "variable mixed-width amount must be left free (no rhs assumption); \
             got: {:?}",
            report.vc_obligations[0].assumptions,
        );
        // The old exit-0 "mixed-width shift skipped" audit note is gone.
        assert!(
            !report.audit_notes.iter().any(|n| n.message.contains("mixed-width shift")),
            "the old mixed-width-skip audit note must be gone; got: {:?}",
            report.audit_notes,
        );
    }
    /// #25: a mixed-width shift with a CONSTANT amount that FITS the value
    /// type pins the amount to `(amount as V)` at the VALUE width, so the
    /// over-shift obligation is Rust's exact check (`x: u32 << 4` → rhs
    /// pinned to 4 at u32 → discharges). A constant that does NOT fit V is
    /// left FREE (→ fail closed), never pinned to a truncated value.
    #[test]
    fn mixed_width_const_shift_pins_only_when_value_fits() {
        use crate::mir_api::{BinOp, IntTy, UintTy};
        let cfg = SubsetConfig::default_for_test();
        let u32_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let u8_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) };
        let i32_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Int(IntTy::I32)) };
        let const_op = |val: i128, ty: Ty| {
            Operand::Constant(ConstOperand { ty, def_id: None, path: None, value: Some(val) })
        };
        // (value_ty, amount, amount_ty, expected rhs pin literal or None)
        let cases: Vec<(Ty, i128, Ty, Option<&str>, &str)> = vec![
            (u32_ty(), 4, i32_ty(), Some("#x00000004"), "u32 << 4_i32 fits → pin (4 as u32)"),
            (u8_ty(), 4, i32_ty(), Some("#x04"), "u8 << 4_i32 fits → pin (4 as u8)"),
            (u8_ty(), 256, i32_ty(), None, "u8 << 256_i32 does NOT fit u8 → free (fail closed)"),
        ];
        for (value_ty, amount, amount_ty, expect_pin, label) in cases {
            let mut v = SubsetVisitor::new(&cfg);
            let body = Body {
                def_id: DefId(0),
                arg_tys: vec![value_ty.clone()],
                arg_names: vec!["x".into()],
                return_ty: value_ty.clone(),
                is_unsafe: false,
                is_async: false,
                locals: vec![
                    LocalDecl { ty: value_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                    LocalDecl { ty: value_ty.clone(), span: Span::default(), mutability: Mutability::Not },
                ],
                blocks: vec![BasicBlockData {
                    statements: vec![Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place { local: Local(1), projection: vec![] }),
                                const_op(amount, amount_ty.clone()),
                            ),
                        ),
                        span: Span::default(),
                    }],
                    terminator: Terminator { kind: TerminatorKind::Return, span: Span::default() },
                }],
                span: Span::default(),
            };
            v.visit_body(&body, false);
            let report = v.into_report();
            assert_eq!(
                report.vc_obligations.len(), 1,
                "{label}: must emit one obligation; got {:?}",
                report.vc_obligations,
            );
            let assumptions = &report.vc_obligations[0].assumptions;
            let rhs_pin = assumptions.iter().find(|a| a.contains("rhs"));
            match expect_pin {
                Some(lit) => assert!(
                    rhs_pin.is_some_and(|a| a.contains(lit)),
                    "{label}: expected rhs pinned to {lit} (= amount as V); got {assumptions:?}",
                ),
                None => assert!(
                    rhs_pin.is_none(),
                    "{label}: amount must be FREE (no rhs pin) — pinning a \
                     truncated value would hide a real over-shift; got {assumptions:?}",
                ),
            }
        }
    }
    /// Variable mixed-width discharge (safe subset, 2026-06-14): a precondition
    /// on the amount BINDS to `rhs` (modelled at the value width) ONLY when the
    /// amount is UNSIGNED and no wider than the value type — then
    /// `x: u32 << y: u8` + `requires(y < 32)` carries `(bvult rhs ...)` and
    /// (with a solver) discharges. A SIGNED amount (a negative value
    /// over-shifts but satisfies a signed bound) or a WIDER amount
    /// (truncation) is NOT bound → stays free → fail closed.
    #[test]
    fn mixed_width_variable_shift_binds_precondition_only_when_sound() {
        use crate::mir_api::{BinOp, IntTy, UintTy};
        let cfg = SubsetConfig::default_for_test();
        let u32_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let amount_ty = |t: &str| -> Ty {
            let kind = match t {
                "u8" => RigidTy::Uint(UintTy::U8),
                "i8" => RigidTy::Int(IntTy::I8),
                "u64" => RigidTy::Uint(UintTy::U64),
                _ => unreachable!("unmapped amount type in test"),
            };
            Ty { kind: TyKind::RigidTy(kind) }
        };
        // (amount type, expect the precondition bound to rhs?)
        let cases = [
            ("u8", true, "unsigned + narrower → bound (discharges with a solver)"),
            ("i8", false, "signed → unbound (a negative amount over-shifts → fail closed)"),
            ("u64", false, "wider than value → unbound (truncation unsound → fail closed)"),
        ];
        for (amt, expect_bound, label) in cases {
            let mut v = SubsetVisitor::new(&cfg);
            v.set_current_preconditions(vec!["y < 32".into()]);
            let body = Body {
                def_id: DefId(0),
                arg_tys: vec![u32_ty(), amount_ty(amt)],
                arg_names: vec!["x".into(), "y".into()],
                return_ty: u32_ty(),
                is_unsafe: false,
                is_async: false,
                locals: vec![
                    LocalDecl { ty: u32_ty(), span: Span::default(), mutability: Mutability::Not },
                    LocalDecl { ty: u32_ty(), span: Span::default(), mutability: Mutability::Not },
                    LocalDecl { ty: amount_ty(amt), span: Span::default(), mutability: Mutability::Not },
                ],
                blocks: vec![BasicBlockData {
                    statements: vec![Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place { local: Local(1), projection: vec![] }),
                                Operand::Copy(Place { local: Local(2), projection: vec![] }),
                            ),
                        ),
                        span: Span::default(),
                    }],
                    terminator: Terminator { kind: TerminatorKind::Return, span: Span::default() },
                }],
                span: Span::default(),
            };
            v.visit_body(&body, false);
            let report = v.into_report();
            assert_eq!(
                report.vc_obligations.len(),
                1,
                "{label}: must emit one obligation; got {:?}",
                report.vc_obligations,
            );
            let has_rhs_precond = report.vc_obligations[0]
                .assumptions
                .iter()
                .any(|a| a.contains("rhs"));
            assert_eq!(
                has_rhs_precond, expect_bound,
                "{label}: precondition-bound-to-rhs = {expect_bound}; got assumptions {:?}",
                report.vc_obligations[0].assumptions,
            );
        }
    }
    /// M-1 positive control: a body WITH a Return terminator and an
    /// ensures emits the PB076 obligation and does NOT surface the
    /// divergent-body audit note.
    #[test]
    fn ensures_on_returning_body_emits_obligation_no_divergent_note() {
        use crate::mir_api::UintTy;
        let cfg = SubsetConfig::default_for_test();
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![LocalDecl {
                ty: u32_ty,
                span: Span::default(),
                mutability: Mutability::Not,
            }],
            blocks: vec![BasicBlockData {
                statements: vec![],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 101".to_string()]);
        v.visit_body(&body, false);
        let report = v.into_report();
        let pb076_count = report
            .vc_obligations
            .iter()
            .filter(|o| matches!(
                o.kind,
                crate::vc::VcObligationKind::EnsuresPostcondition { .. }
            ))
            .count();
        assert_eq!(pb076_count, 1, "returning body with ensures emits one PB076");
        assert!(
            !report.audit_notes.iter().any(|n| n.message.contains("no return point")),
            "returning body must NOT trigger the divergent-body note",
        );
    }
    /// M-2 (audit-cleanup 2026-05-26): an ensures on a function with
    /// a NON-primitive return type (here `bool`, which is not an
    /// integer the BV encoder can size) emits the obligation with
    /// `ret_ty_name: None` AND surfaces an audit note. The `None`
    /// (not an empty-string sentinel) is what lets `pitbull-vc`
    /// fail closed by construction.
    #[test]
    fn ensures_on_non_primitive_return_carries_none_and_audits() {
        let cfg = SubsetConfig::default_for_test();
        // bool return type — not a primitive integer.
        let bool_ty = Ty { kind: TyKind::RigidTy(RigidTy::Bool) };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![],
            arg_names: vec![],
            return_ty: bool_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![LocalDecl {
                ty: bool_ty,
                span: Span::default(),
                mutability: Mutability::Not,
            }],
            blocks: vec![BasicBlockData {
                statements: vec![],
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        };
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result".to_string()]);
        v.visit_body(&body, false);
        let report = v.into_report();
        let kind = &report
            .vc_obligations
            .iter()
            .find_map(|o| match &o.kind {
                crate::vc::VcObligationKind::EnsuresPostcondition { ret_ty_name, .. } => {
                    Some(ret_ty_name.clone())
                }
                _ => None,
            })
            .expect("PB076 obligation emitted even for non-primitive return");
        assert_eq!(
            *kind, None,
            "M-2: non-primitive return type must carry ret_ty_name: None \
             (fail-closed), not an empty-string sentinel",
        );
        assert!(
            report.audit_notes.iter().any(|n| n.message.contains("not a primitive integer")),
            "M-2: non-primitive return must surface an audit note; got: {:?}",
            report.audit_notes,
        );
    }
    // === Q.4a: ensures SMT discharge (body-effect capture) ===
    //
    // These tests pin the SOUNDNESS-CRITICAL encoding deterministically
    // and solver-free: they assert the exact SMT the visitor builds. A
    // wrong body-effect or postcondition encoding (the cardinal sin —
    // falsely discharging a wrong postcondition) would change these
    // strings and fail loudly. The LIVE `unsat`/`sat` verdicts are
    // pinned separately by the Z3-gated wrapper e2e tests.
    /// A single-block `fn f(x: u32) -> u32 { <stmts>; return }` body.
    /// `_0` is the return slot, `_1` the parameter `x`, both `u32`.
    fn q4a_u32_body(statements: Vec<Statement>) -> Body {
        let u32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let local =
            |ty: Ty| LocalDecl { ty, span: Span::default(), mutability: Mutability::Not };
        Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty.clone()],
            arg_names: vec!["x".to_string()],
            return_ty: u32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![local(u32_ty.clone()), local(u32_ty)],
            blocks: vec![BasicBlockData {
                statements,
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        }
    }
    /// `_0 = move _1` — return the parameter `x` verbatim.
    fn q4a_return_x() -> Statement {
        Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::Use(Operand::Move(Place { local: Local(1), projection: vec![] })),
            ),
            span: Span::default(),
        }
    }
    /// Extract the (discharge_smt, consistency_smt) of the sole PB076
    /// obligation from a finished report.
    fn q4a_ensures_smt(report: &SubsetReport) -> (Option<String>, Option<String>) {
        report
            .vc_obligations
            .iter()
            .find_map(|o| match &o.kind {
                crate::vc::VcObligationKind::EnsuresPostcondition {
                    discharge_smt,
                    consistency_smt,
                    ..
                } => Some((discharge_smt.clone(), consistency_smt.clone())),
                _ => None,
            })
            .expect("a PB076 EnsuresPostcondition obligation must be emitted")
    }
    #[test]
    fn q4a_true_postcondition_builds_structurally_unsat_discharge() {
        // fn copy_arg(x: u32) -> u32 { x }  #[ensures("result == x")]
        // The discharge problem asserts BOTH `(= result x)` (the body
        // effect) and `(not (= result x))` (the negated goal) — a direct
        // contradiction, so any sound solver returns `unsat` ⇒ the
        // postcondition is discharged.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result == x".to_string()]);
        v.visit_body(&q4a_u32_body(vec![q4a_return_x()]), false);
        let (discharge, consistency) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("capturable body + translatable postcondition must discharge");
        assert!(smt.contains("(declare-const result (_ BitVec 32))"), "smt:\n{smt}");
        assert!(smt.contains("(declare-const x (_ BitVec 32))"), "smt:\n{smt}");
        assert!(smt.contains("(assert (= result x))"), "body effect missing:\n{smt}");
        assert!(smt.contains("(assert (not (= result x)))"), "negated goal missing:\n{smt}");
        assert!(smt.trim_end().ends_with("(check-sat)"), "smt:\n{smt}");
        assert!(consistency.is_none(), "no preconditions ⇒ no consistency check");
    }
    #[test]
    fn q4a_false_postcondition_builds_satisfiable_discharge() {
        // fn copy_arg(x: u32) -> u32 { x }  #[ensures("result < 5")]
        // `result == x` ∧ `not(result < 5)` is satisfiable (x = 5), so
        // the solver returns `sat` ⇒ NOT discharged — the honest verdict
        // since `copy_arg` can return a value ≥ 5. The body effect and
        // negated goal are independent terms (no structural contradiction).
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 5".to_string()]);
        v.visit_body(&q4a_u32_body(vec![q4a_return_x()]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("capturable body + translatable postcondition");
        assert!(smt.contains("(assert (= result x))"), "body effect missing:\n{smt}");
        assert!(
            smt.contains("(assert (not (bvult result #x00000005)))"),
            "negated `result < 5` goal missing:\n{smt}",
        );
        assert!(
            !smt.contains("(assert (not (= result x)))"),
            "must NOT be the structural contradiction of the TRUE case:\n{smt}",
        );
    }
    /// `+ 1` constant operand, reused by the arithmetic capture tests.
    fn q4b_const_u32(value: i128) -> Operand {
        Operand::Constant(ConstOperand {
            ty: Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) },
            def_id: None,
            path: None,
            value: Some(value),
        })
    }
    #[test]
    fn q4b_single_block_add_captures_wrapping_bvadd() {
        // fn add_one(x: u32) -> u32 { x + 1 } in the SCALAR form
        // (`_0 = Add(_1, const 1)`, single block). Q.4b captures the
        // wrapping sum as `(bvadd x #x00000001)`.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 101".to_string()]);
        let add = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4b_const_u32(1),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4a_u32_body(vec![add]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4b: a wrapping `x + 1` body effect must be captured");
        assert!(
            smt.contains("(assert (= result (bvadd x #x00000001)))"),
            "wrapping-add body effect missing:\n{smt}",
        );
    }
    #[test]
    fn q4b_two_block_checked_add_captures_via_field_zero() {
        // The REALISTIC analysis-MIR shape of `x + 1`:
        //   bb0: _2 = Add(_1, const 1);  assert(!_2.1) -> bb1
        //   bb1: _0 = move (_2.0);  return
        // Q.4b walks the linear chain through the overflow Assert and
        // resolves `_2.0` to the captured wrapping sum.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 101".to_string()]);
        let u32_ty = || Ty { kind: TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) };
        let local =
            |ty: Ty| LocalDecl { ty, span: Span::default(), mutability: Mutability::Not };
        let body = Body {
            def_id: DefId(0),
            arg_tys: vec![u32_ty()],
            arg_names: vec!["x".to_string()],
            return_ty: u32_ty(),
            is_unsafe: false,
            is_async: false,
            // _0 return, _1 = x, _2 = checked-add result (.0 is the sum).
            locals: vec![local(u32_ty()), local(u32_ty()), local(u32_ty())],
            blocks: vec![
                BasicBlockData {
                    statements: vec![Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(2), projection: vec![] },
                            Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Move(Place { local: Local(1), projection: vec![] }),
                                q4b_const_u32(1),
                            ),
                        ),
                        span: Span::default(),
                    }],
                    terminator: Terminator {
                        kind: TerminatorKind::Assert {
                            cond: Operand::Move(Place {
                                local: Local(2),
                                projection: vec![ProjectionElem::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow,
                            target: BasicBlock(1),
                        },
                        span: Span::default(),
                    },
                },
                BasicBlockData {
                    statements: vec![Statement {
                        kind: StatementKind::Assign(
                            Place { local: Local(0), projection: vec![] },
                            Rvalue::Use(Operand::Move(Place {
                                local: Local(2),
                                projection: vec![ProjectionElem::Field(0)],
                            })),
                        ),
                        span: Span::default(),
                    }],
                    terminator: Terminator {
                        kind: TerminatorKind::Return,
                        span: Span::default(),
                    },
                },
            ],
            span: Span::default(),
        };
        v.visit_body(&body, false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4b: checked-add tuple via `.0` must be captured");
        assert!(
            smt.contains("(assert (= result (bvadd x #x00000001)))"),
            "checked-add body effect (via _2.0) missing:\n{smt}",
        );
    }
    #[test]
    fn q4c_unsigned_div_captures_bvudiv() {
        // fn half(x: u32) -> u32 { x / 2 } → unsigned division `bvudiv`.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 101".to_string()]);
        let div = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4b_const_u32(2),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4a_u32_body(vec![div]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4c: unsigned `x / 2` must be captured");
        assert!(
            smt.contains("(assert (= result (bvudiv x #x00000002)))"),
            "unsigned-div body effect missing:\n{smt}",
        );
    }
    #[test]
    fn q4c_unsigned_rem_captures_bvurem() {
        // fn m(x: u32) -> u32 { x % 10 } → unsigned remainder `bvurem`.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 10".to_string()]);
        let rem = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::Rem,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4b_const_u32(10),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4a_u32_body(vec![rem]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4c: unsigned `x % 10` must be captured");
        assert!(
            // `format_bv_literal` emits UPPERCASE hex (10 → `#x0000000A`).
            smt.contains("(assert (= result (bvurem x #x0000000A)))"),
            "unsigned-rem body effect missing:\n{smt}",
        );
    }
    /// Build a single-block `fn f(x: i32) -> i32 { <stmts>; return }`.
    fn q4c_i32_body(statements: Vec<Statement>) -> Body {
        let i32_ty = Ty { kind: TyKind::RigidTy(RigidTy::Int(IntTy::I32)) };
        let local =
            |ty: Ty| LocalDecl { ty, span: Span::default(), mutability: Mutability::Not };
        Body {
            def_id: DefId(0),
            arg_tys: vec![i32_ty.clone()],
            arg_names: vec!["x".to_string()],
            return_ty: i32_ty.clone(),
            is_unsafe: false,
            is_async: false,
            locals: vec![local(i32_ty.clone()), local(i32_ty)],
            blocks: vec![BasicBlockData {
                statements,
                terminator: Terminator {
                    kind: TerminatorKind::Return,
                    span: Span::default(),
                },
            }],
            span: Span::default(),
        }
    }
    /// `i32` constant operand.
    fn q4c_const_i32(value: i128) -> Operand {
        Operand::Constant(ConstOperand {
            ty: Ty { kind: TyKind::RigidTy(RigidTy::Int(IntTy::I32)) },
            def_id: None,
            path: None,
            value: Some(value),
        })
    }
    #[test]
    fn q4c_signed_div_captures_bvsdiv() {
        // fn d(x: i32) -> i32 { x / 2 } → SIGNED division `bvsdiv`
        // (truncate toward zero), selected by the i32 return type.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result <= x".to_string()]);
        let div = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4c_const_i32(2),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4c_i32_body(vec![div]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4c: signed `x / 2` must be captured");
        assert!(
            smt.contains("(assert (= result (bvsdiv x #x00000002)))"),
            "signed-div body effect missing:\n{smt}",
        );
        assert!(!smt.contains("bvudiv"), "signed div must use bvsdiv, not bvudiv:\n{smt}");
    }
    #[test]
    fn q4c_signed_rem_uses_bvsrem_not_bvsmod() {
        // fn r(x: i32) -> i32 { x % 3 } → SIGNED remainder `bvsrem`
        // (sign of the DIVIDEND, matching Rust). MUST NOT be `bvsmod`
        // (sign of the divisor) — they differ (e.g. `7 % -2` is 1 vs -1).
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 3".to_string()]);
        let rem = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::Rem,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4c_const_i32(3),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4c_i32_body(vec![rem]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4c: signed `x % 3` must be captured");
        assert!(
            smt.contains("(assert (= result (bvsrem x #x00000003)))"),
            "signed-rem body effect must use bvsrem:\n{smt}",
        );
        assert!(!smt.contains("bvsmod"), "signed rem must be bvsrem, NOT bvsmod:\n{smt}");
    }
    #[test]
    fn q4d_shl_constant_captures_bvshl() {
        // fn f(x: u32) -> u32 { x << 1 } → `bvshl` with the amount
        // rendered at the value's width.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 101".to_string()]);
        let shl = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::Shl,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4b_const_u32(1),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4a_u32_body(vec![shl]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4d: `x << 1` must be captured");
        assert!(
            smt.contains("(assert (= result (bvshl x #x00000001)))"),
            "shl body effect missing:\n{smt}",
        );
    }
    #[test]
    fn q4d_unsigned_shr_captures_bvlshr() {
        // fn f(x: u32) -> u32 { x >> 4 } → LOGICAL right shift `bvlshr`.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result <= x".to_string()]);
        let shr = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::Shr,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4b_const_u32(4),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4a_u32_body(vec![shr]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4d: unsigned `x >> 4` must be captured");
        assert!(
            smt.contains("(assert (= result (bvlshr x #x00000004)))"),
            "unsigned-shr body effect must use bvlshr:\n{smt}",
        );
        assert!(!smt.contains("bvashr"), "unsigned >> must be bvlshr, not bvashr:\n{smt}");
    }
    #[test]
    fn q4d_signed_shr_captures_bvashr() {
        // fn f(x: i32) -> i32 { x >> 1 } → ARITHMETIC right shift `bvashr`
        // (sign-filling), selected by the i32 return type.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result <= x".to_string()]);
        let shr = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::Shr,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4c_const_i32(1),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4c_i32_body(vec![shr]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("Q.4d: signed `x >> 1` must be captured");
        assert!(
            smt.contains("(assert (= result (bvashr x #x00000001)))"),
            "signed-shr body effect must use bvashr:\n{smt}",
        );
        assert!(!smt.contains("bvlshr"), "signed >> must be bvashr, not bvlshr:\n{smt}");
    }
    #[test]
    fn q4d_bitwise_body_stays_pending() {
        // Bitwise ops (BitAnd/BitOr/BitXor) are deferred — `_0 = x ^ 1`
        // must stay pending (fail closed).
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_ensures(vec!["result < 101".to_string()]);
        let xor = Statement {
            kind: StatementKind::Assign(
                Place { local: Local(0), projection: vec![] },
                Rvalue::BinaryOp(
                    BinOp::BitXor,
                    Operand::Move(Place { local: Local(1), projection: vec![] }),
                    q4b_const_u32(1),
                ),
            ),
            span: Span::default(),
        };
        v.visit_body(&q4a_u32_body(vec![xor]), false);
        let (discharge, _c) = q4a_ensures_smt(&v.into_report());
        assert!(discharge.is_none(), "BitXor body effect must NOT be captured (fail closed)");
    }
    #[test]
    fn q4a_precondition_is_assumed_and_consistency_checked() {
        // fn copy_arg(x: u32) -> u32 { x }
        //   #[requires("x < 100")] #[ensures("result < 100")]
        // x<100 ∧ result==x ∧ not(result<100) is unsat ⇒ discharged. A
        // consistency check (assumptions only) is emitted for the F1
        // vacuous-precondition guard.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_preconditions(vec!["x < 100".to_string()]);
        v.set_current_ensures(vec!["result < 100".to_string()]);
        v.visit_body(&q4a_u32_body(vec![q4a_return_x()]), false);
        let (discharge, consistency) = q4a_ensures_smt(&v.into_report());
        let smt = discharge.expect("translatable precondition + postcondition");
        assert!(smt.contains("(assert (bvult x #x00000064))"), "assumed precondition missing:\n{smt}");
        assert!(smt.contains("(assert (= result x))"), "body effect missing:\n{smt}");
        assert!(
            smt.contains("(assert (not (bvult result #x00000064)))"),
            "negated goal missing:\n{smt}",
        );
        let cs = consistency.expect("preconditions present ⇒ a consistency check is emitted");
        assert!(cs.contains("(assert (bvult x #x00000064))"), "cs:\n{cs}");
        assert!(cs.trim_end().ends_with("(check-sat)"), "cs:\n{cs}");
        // F1 hardening (audit 2026-05-31): the consistency check carries the
        // FULL hypothesis set — the preconditions AND the body effect — so a
        // hypothesis contradicting the body effect is caught as vacuity. It
        // must include `(= result x)` but still NOT carry the negated goal.
        assert!(cs.contains("(= result x)"), "consistency check must include the body effect:\n{cs}");
        assert!(!cs.contains("(not "), "consistency check must omit the negated goal:\n{cs}");
    }
    #[test]
    fn q4a_untranslatable_precondition_fails_closed_to_pending() {
        // A raw-SMT precondition is deferred this increment. Rather than
        // silently DROP it (which could yield a spurious counterexample),
        // the whole obligation stays pending — fail closed.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_preconditions(vec!["(assert (bvult x #x00000064))".to_string()]);
        v.set_current_ensures(vec!["result < 100".to_string()]);
        v.visit_body(&q4a_u32_body(vec![q4a_return_x()]), false);
        let report = v.into_report();
        let (discharge, _c) = q4a_ensures_smt(&report);
        assert!(discharge.is_none(), "untranslatable precondition ⇒ pending (fail closed)");
        assert!(
            report.audit_notes.iter().any(|n| {
                n.message.contains("precondition") && n.message.contains("could not be translated")
            }),
            "pending must explain the untranslatable precondition; got: {:?}",
            report.audit_notes,
        );
    }
    #[test]
    fn q4a_precondition_referencing_result_fails_closed() {
        // SOUNDNESS regression (audit 2026-05-31, CRITICAL). A precondition
        // that references `result` (the OUTPUT) must NOT be usable as a
        // hypothesis — assuming a constraint on the output is circular and
        // would VACUOUSLY discharge a false postcondition. Trigger:
        //   #[requires("result < 100")] #[ensures("result < 100")]
        //   fn f(x: u32) -> u32 { x }
        // f can return >= 100, so `ensures(result < 100)` is FALSE; before
        // the fix the main check `result=x ∧ result<100 ∧ ¬(result<100)` was
        // unsat and wrongly "discharged". The precondition must now be
        // untranslatable (preconditions reference args only) ⇒ pending.
        let cfg = SubsetConfig::default_for_test();
        let mut v = SubsetVisitor::new(&cfg);
        v.set_current_preconditions(vec!["result < 100".to_string()]);
        v.set_current_ensures(vec!["result < 100".to_string()]);
        v.visit_body(&q4a_u32_body(vec![q4a_return_x()]), false);
        let report = v.into_report();
        let (discharge, _c) = q4a_ensures_smt(&report);
        assert!(
            discharge.is_none(),
            "a precondition referencing `result` must fail closed to pending, never \
             produce a (vacuously) dischargeable problem",
        );
        assert!(
            report.audit_notes.iter().any(|n| n.message.contains("precondition")),
            "pending must explain the rejected result-referencing precondition; got: {:?}",
            report.audit_notes,
        );
    }
}
