# Pitbull Subset Specification v0.1 — PSS-1
**Status:** Draft.
**Audience:** Pitbull implementors, auditors, qualification assessors.
**Normative.**
This is the canonical reference. The `pitbull-subset` crate's `RULES`
table is the machine-readable encoding; this document is the prose.
Where they disagree, this document wins.
## 0. Scope and conformance
PSS-1 defines the *Pitbull Verifiable Subset* of Rust as enforced by
Pitbull v0.1. A Rust crate **conforms to PSS-1** if and only if every
monomorphized item reachable from a `#[pitbull::verify]` entry point
satisfies every rule below. Non-conformance is a compile-time error;
v0.1 has no warning level.
## 1. Operational definitions
**MIR phase.** All subset checks run on `MirPhase::Runtime(PostCleanup)`
via `rustc_public` (StableMIR). This is post-monomorphization,
post-borrow-check, post-drop-elaboration MIR. Macros are expanded;
generics are instantiated; closures are desugared; trait calls are
resolved where statically possible.
**Reachability.** An item is reachable if it appears in the call graph
rooted at any `#[pitbull::verify]` function, transitively, after
monomorphization. Items not reachable are not checked.
**Trust surface.** Items annotated `#[pitbull::trusted]` are not checked
against PSS-1 bodies, but their signatures are. Trust is asymmetric: a
trusted function can promise anything, but its callers reason about it
through a clean spec interface.
**Severity.** PSS-1 v0.1 has one severity level: `Error`. Violations
abort the verification run and produce no report. The `Audit` level is
reserved for v0.2.
## 2. Categories
| ID range  | Category               |
|-----------|------------------------|
| PB001–010 | A. Unsafe operations   |
| PB011–020 | B. Heap allocation     |
| PB021–025 | C. Interior mutability |
| PB026–030 | D. Concurrency         |
| PB031–040 | E. Dispatch            |
| PB041–048 | F. Control flow        |
| PB049–055 | G. Numeric             |
| PB056–058 | H. FFI                 |
| PB059–063 | I. Macros, const, cfg  |
| PB064–070 | J. Spec mode           |
| PB071–075 | K. Project config      |
Each rule below documents: title, detection pattern, rationale, reject
example, accept example, and future plan.
## 3. Category A — Unsafe operations
### PB001 — `unsafe` block
**Detects.** Any HIR `ExprKind::Block` whose `BlockCheckMode` is
`UnsafeBlock(_)`, reachable from a verified entry point.
**Rationale.** Pitbull v0.1 has no separation-logic backend. Existing
modular unsafe verifiers are demonstrably unsound w.r.t. Rust's pointer
aliasing rules (Tas et al., 2026); we refuse to inherit that failure
mode.
**Reject.** `unsafe { std::ptr::read(p) }`
**Accept.** Any code path that does not transitively enter an `unsafe`
block.
**Future.** v0.3 admits `unsafe` only behind verified ghost-permission
types, gated on Pitbull shipping a Tree-Borrows-aware separation logic.
### PB002 — `unsafe fn` definition or call
**Detects.** `FnSig::unsafety == Unsafe` on either definition or
`TerminatorKind::Call` resolved callee. Includes intrinsics.
**Rationale.** Same as PB001.
**Future.** v0.3.
### PB003 — `unsafe trait` and `unsafe impl`
**Detects.** `TraitDef.unsafety == Unsafe` or `ImplPolarity` over an
unsafe trait.
**Rationale.** Soundness of trait methods relies on unverified
invariants.
**Future.** v0.3.
### PB004 — Raw pointer types
**Detects.** `RigidTy::RawPtr(_, _)` appearing in any reachable type,
function signature, or local. Also: `Rvalue::RawPtr`, `CastKind::PtrToInt`
/ `IntToPtr` / `PtrToPtr` / `FnPtrToPtr`, and `BinOp::Offset`.
**Rationale.** Raw pointers escape the borrow-check-based model on
which our prophecy reasoning depends. Provenance matters; v0.1 does
not model it.
**Reject.** `fn f(p: *const u8) {}`
**Accept.** `fn f(p: &u8) {}` or `fn f(p: &mut u8) {}`
**Future.** v0.3 admits raw pointers via a ghost-permission wrapper.
### PB005 — `union` types
**Detects.** `AdtKind::Union` in any reachable type.
**Rationale.** Active-variant invariant is not tracked by the type
system.
**Future.** v0.3.
### PB006 — Inline assembly
**Detects.** `TerminatorKind::InlineAsm` (post-mono) or `core::arch::asm!`
invocation.
**Rationale.** Out of scope of any logical model.
**Future.** v1.0 as `#[trusted]` boundary with explicit spec.
### PB007 — `transmute` and bit-casts
**Detects.** Call to `core::mem::transmute`, `transmute_copy`, or
`Rvalue::Cast(CastKind::Transmute, _, _)`.
**Rationale.** Bypasses the type system entirely.
**Future.** v0.3 with bit-precise specs.
### PB008 — `MaybeUninit`
**Detects.** Any use of `core::mem::MaybeUninit<_>` reachable from
verified code.
**Rationale.** Uninitialized memory is undefined behavior with no
first-class spec.
**Future.** v0.3 with ghost-permission-aware initialization tracking.
### PB009 — `Retag` statements
**Detects.** `StatementKind::Retag(_, _)` post-monomorphization,
regardless of `RetagKind`.
**Rationale.** `Retag` only appears when raw pointers or
`&UnsafeCell<_>` flow through code. Its presence post-mono in code that
nominally satisfies PB001/PB004 signals a subset escape via stdlib
internals or macro expansion. Fail closed.
**Future.** Informational once unsafe is admitted in later versions;
remains the canonical aliasing-relevance signal.
### PB010 — `Deinit` outside drop elaboration
**Detects.** `StatementKind::Deinit(_)` in a position not part of an
elaborated drop.
**Rationale.** `Deinit` is emitted by drop elaboration (acceptable) or
by raw-place assignment / intrinsics (not acceptable). The reachability
driver tags each statement with its origin phase; the visitor consults
the tag.
**Future.** v0.3.
## 4. Category B — Heap allocation
### PB011 — `Box<T>`
**Detects.** `RigidTy::Adt` resolving to `alloc::boxed::Box<_>`.
**Rationale.** Heap allocation requires modeling the allocator. v0.1
is stack-and-slice only.
**Future.** v0.2 admits `Box` with a global allocator axiom.
### PB012 — `Vec`, `String`, and `std::collections`
**Detects.** Any reachable `Adt` resolving to a path in
`{alloc::vec::Vec, alloc::string::String, alloc::collections::*, std::collections::*}`.
**Rationale.** Requires PB011 plus invariant-laden internal unsafe.
**Future.** v0.2 admits read-only `Vec` specs; v0.4 admits mutation.
### PB013 — `Rvalue::ShallowInitBox`
**Detects.** This MIR rvalue specifically.
**Rationale.** Distinct producer from PB011: can be emitted from macro
expansion bypassing source-level `Box::new`.
**Future.** v0.2 paired with PB011.
### PB014 — Custom allocators
**Detects.** Any type parameter satisfying `core::alloc::Allocator`.
**Rationale.** Allocator behavior is unbounded effectful computation.
**Future.** v0.4.
### PB015 — `Rc`, `Arc`, `Weak`
**Detects.** `alloc::rc::*` and `alloc::sync::Arc`/`Weak`.
**Rationale.** Reference-counted aliasing breaks unique ownership.
**Future.** v0.4 with ghost reference-count tracking.
### PB016 — Non-trivial `Drop`
**Detects.** Any reachable type implementing `Drop` whose impl body
contains operations beyond field-wise recursive drop.
**Rationale.** Implicit drop sites become hidden, potentially
panic-bearing function calls.
**Future.** v0.2 with explicit drop contracts.
### PB017 — Allocation-bearing macros
**Detects.** `format!`, `vec!`, `string!`, and similar expansions
reachable from verified code.
**Future.** v0.2.
### PB018 — `static mut` and interior-mutable statics
**Detects.** `static mut X: T` or `static X: T` where `T` contains a
`Cell`-family type.
**Future.** v0.4.
### PB019 — Thread-local storage
**Detects.** `#[thread_local]` and `thread_local!` macro expansions.
MIR signal: `Rvalue::ThreadLocalRef`.
**Future.** v0.4.
### PB020 — Implicit large stack allocation
**Detects.** A function-local or composite type whose layout exceeds
the configured `stack_allocation_limit_bytes` (default 64 KiB).
**Rationale.** Defense against accidental stack overflow on MCUs.
**Future.** Remains; threshold becomes per-target.
## 5. Category C — Interior mutability
### PB021 — `Cell` / `RefCell`
**Detects.** `RigidTy::Adt` for `core::cell::{Cell,RefCell,OnceCell,LazyCell}`.
**Future.** v0.3 admits `Cell` (Copy-only) with explicit aliasing contracts.
### PB022 — `UnsafeCell`
**Detects.** `RigidTy::Adt` for `core::cell::UnsafeCell` and
`#[repr(transparent)]` chains ending at `UnsafeCell`.
**Future.** v0.3.
### PB023 — Atomics
**Detects.** `core::sync::atomic::*`.
**Future.** v0.4 with a concurrency model.
### PB024 — `Mutex`, `RwLock`, `Once`
**Future.** v0.4.
### PB025 — Volatile reads/writes
**Detects.** Calls to `core::ptr::read_volatile`, `write_volatile`, and
the per-architecture volatile intrinsics.
**Future.** v1.0 via `#[trusted]` boundary specs for device drivers.
## 6. Category D — Concurrency
### PB026 — `async fn` / `async {}`
**Detects.** `FnSig.header.asyncness == Async`; in MIR, bodies that
lower to coroutines.
**Future.** v0.5+.
### PB027 — Coroutines, generators, `yield`
**Detects.** `TerminatorKind::Yield`, `TerminatorKind::CoroutineDrop`,
and `AggregateKind::Coroutine`.
**Future.** v0.5+.
### PB028 — `std::thread::spawn`
**Future.** v0.4.
### PB029 — `Send` / `Sync` bounds
**Future.** Lifted in v0.4.
### PB030 — Channels
**Detects.** `std::sync::mpsc::*`, `std::sync::mpmc::*`, and
well-known third-party channel types when present in dependencies.
**Future.** v0.5+.
## 7. Category E — Dispatch
### PB031 — Trait objects (`dyn Trait`)
**Detects.** Any `TyKind::Dynamic`.
**Future.** v0.2 with whole-crate impl enumeration; v0.4 modular vtables.
### PB032 — Function pointers
**Detects.** `RigidTy::FnPtr`.
**Future.** v0.2 with target-set annotations.
### PB033 — Escaping closures
**Detects.** A `RigidTy::Closure` or `AggregateKind::Closure` whose
value crosses a function boundary.
**Future.** v0.2 with closure-environment specs.
### PB034 — Higher-ranked trait bounds (`for<'a>`)
**Future.** v0.3.
### PB035 — Const generics of non-integer types
**Future.** v0.3.
### PB036 — Specialization
**Future.** Tied to upstream stabilization.
### PB037 — GATs in spec-relevant positions
**Future.** v0.3.
### PB038 — Virtual trait calls
**Detects.** `TerminatorKind::Call` whose resolved callee is
`InstanceKind::Virtual(_, _)`.
**Future.** v0.2.
### PB039 — Unresolvable `impl Trait`
**Future.** v0.2.
### PB040 — Recursive trait impls without termination certificate
**Future.** v0.2.
## 8. Category F — Control flow
### PB041 — Recursion without `#[decreases]`
**Detects.** Any function in a strongly-connected component of the
call graph lacking a `#[pitbull::decreases]` attribute.
**Rationale.** Non-terminating spec functions are unsoundness; for
executable functions, non-termination defeats AoRTE.
**Future.** Permanent; auto-inference for structural recursion in v0.2.
### PB042 — Loops without `#[variant]`
**Future.** Advisory at v0.2; inference for structurally bounded loops.
### PB043 — `panic!` without unreachability proof
**Detects.** Reachable call to `core::panicking::*` or any function
whose return type is `!` originating in panic infrastructure.
**Rationale.** The AoRTE goal.
**Future.** Permanent.
### PB044 — Non-terminating spec function
**Rationale.** Spec inconsistency makes every proof vacuous — the
worst failure mode.
**Future.** Permanent.
### PB045 — `TerminatorKind::TailCall` (`become`)
**Future.** v0.3.
### PB046 — `FalseEdge` / `FalseUnwind` post-cleanup
**Rationale.** Should not appear at the MIR phase we analyze; their
presence means our phase assumption is wrong. Fail closed.
**Future.** Permanent.
### PB047 — `?` over non-pure paths
**Future.** v0.2 with spec'd `Try` impls.
### PB048 — Unwinding panic strategy
**Detects.** Project compiled with `panic = "unwind"`, or any
`TerminatorKind::UnwindResume` / `UnwindTerminate` in reachable MIR.
**Future.** v0.4 with explicit unwind contracts.
## 9. Category G — Numeric
### PB049 — `overflow-checks` disabled
**Detects.** Project profile setting `overflow-checks = false`.
**Rationale.** Proofs and binary semantics must agree on overflow.
**Future.** Permanent.
### PB050 — Floating-point arithmetic
**Detects.** `f16`, `f32`, `f64`, `f128` in any reachable type or
operand; FP intrinsics.
**Future.** v0.3 via Why3's float theory and CVC5's FP support.
### PB051 — Narrowing or sign-changing `as` casts
**Detects.** `Rvalue::Cast(CastKind::IntToInt, _, _)` and
`FloatToInt` / `IntToFloat` / `PtrToInt` / `IntToPtr` / `PtrToPtr`.
**Future.** v0.2 with auto-generated cast obligations.
### PB052 — Unbounded `usize`/`isize` arithmetic
**Detects.** Any `usize`/`isize` arithmetic without a contract relating
it to a slice length or known bound. Stricter on 16- and 32-bit
targets.
**Future.** Permanent.
### PB053 — `char` in arithmetic position
**Future.** v0.3.
### PB054 — Slice indexing without bound
**Detects.** `Place::Projection(_, ProjectionElem::Index(_))` on a
slice/array where the index is not statically bounded by length.
**Future.** Permanent.
### PB055 — Drop glue in spec-bounded position
**Future.** Permanent.
## 10. Category H — FFI
### PB056 — `extern` blocks
**Detects.** Items inside `extern "..." { ... }` blocks reachable from
verified code.
**Future.** v1.0 via `#[pitbull::trusted]` C-function specs.
### PB057 — `#[no_mangle]` / `#[export_name]`
**Future.** v1.0 with explicit boundary contracts.
### PB058 — Non-Rust ABI
**Future.** v1.0.
## 11. Category I — Macros, const-eval, cfg
### PB059 — Non-allowlisted proc macros
**Detects.** Proc macros from a crate not on
`subset.allowed_proc_macros` in `pitbull.toml`.
**Future.** Permanent; allowlist grows with audit history.
### PB060 — Build scripts
**Detects.** Presence of `build.rs` in any reachable crate.
**Future.** Permanent; trusted scripts must declare SHA-256.
### PB061 — `const fn` outside the certified subset
**Detects.** `const fn` bodies that use constructs outside Ferrocene's
certified core subset (5,169 functions as of 26.02).
**Future.** Tracks Ferrocene certification expansion.
### PB062 — Unpinned `cfg` conditions
**Future.** Permanent.
### PB063 — `include!`, `include_str!`, `include_bytes!`
**Future.** Advisory at v0.2 if file hash is recorded.
## 12. Category J — Specification mode
### PB064 — Non-pure call in spec expression
**Detects.** A call from a `requires`/`ensures`/`invariant`/spec-`assert!`
expression to a function not marked `#[pitbull::pure]` or in the prelude's
pure set.
**Future.** Permanent.
### PB065 — Quantifiers over undecidable domains
**Detects.** `forall` / `exists` over types outside
`{Int, Bool, Seq<T>, Set<T>, Map<K,V>, bounded primitive integers}`.
**Future.** Permanent.
### PB066 — Spec function calling executable function
**Future.** Permanent.
### PB067 — `#[trusted]` without justification
**Detects.** `#[pitbull::trusted]` lacking a sibling
`#[pitbull::justification("...")]` or a `## Pitbull justification`
section in the doc comment.
**Future.** Permanent.
### PB068 — Trust budget exceeded
**Detects.** `trusted_lines / verified_lines >
config.subset.trust_budget_fraction` (default 0.05).
**Future.** Advisory at v0.2.
### PB069 — Spec depends on `unsafe` semantics
**Future.** v0.3.
### PB070 — Prophecy syntax (`^x`) used
**Detects.** Use of `^expr` in any spec expression.
**Rationale.** Reserved for v0.2 after tutorial and counterexample
UX are in place.
**Future.** v0.2.
## 13. Category K — Project configuration
### PB071 — Toolchain not on supported pair
**Detects.** `project.toolchain` not in `SUPPORTED_TOOLCHAINS`.
**Future.** Permanent.
### PB072 — Missing `Cargo.lock`
**Future.** Permanent.
### PB073 — Non-hermetic verification environment
**Future.** Permanent.
### PB074 — `pitbull-spec` version mismatch
**Future.** Permanent.
### PB075 — Unsigned cache entry under `--release`
**Future.** Permanent.
## 14. Audit methodology
Each rule is implemented in `pitbull-subset` as a single explicit arm
in the visitor's exhaustive dispatch. The dispatch table is over the
MIR enum surface (`TerminatorKind`, `StatementKind`, `Rvalue`,
`Operand`, `ProjectionElem`, `RigidTy`, `CastKind`, `AggregateKind`);
each variant has either an `accept` (with documented rationale) or a
`reject` (pointing to a PB rule). **No default arm exists.** Adding a
new MIR variant upstream causes a compile error in `pitbull-subset`;
the audit moves to the new variant.
The mutation-testing harness (`pitbull-subset::mutation`) is the
second line of defense: for every rule, perturbations of its predicate
must be detected by the test suite. Required score is 100%.
## 15. Test-corpus requirements
For PSS-1 v0.1 release:
- One representative reject and one accept example per category. *(v0.1
  release-blocker.)*
For full PSS-1 conformance:
- ≥10 rejecting examples per rule.
- ≥5 adjacent accepting examples per rule.
- Positive AoRTE proofs for: binary search, insertion sort, ring
  buffer, CRC-32, CRC-CCITT, IEEE 802.15.4 MAC frame parser, PID
  controller, voting reducer, fixed-point arithmetic primitives.
- Each positive example passes `MIRIFLAGS=-Zmiri-tree-borrows` with
  10,000 fuzzed inputs.
## 16. Stability and versioning
Rule numbers are **stable across releases**: a rule's PBnnn identifier
never changes once published. Retired rules remain in the registry
with `FuturePlan::Retired` rather than being renumbered. New rules
take the next available number, in any category.
Severity changes (e.g. from `Error` to `Audit`) are major-version
events.
## 17. Open issues for v0.2
The following are tracked but not in v0.1:
- Translation backend (MIR → Coma → Why3 → SMT).
- Proof certificate format and replay command.
- Counterexample rendering.
- Tree-Borrows-aware soundness cross-check protocol.
- Trusted-build-script hash verification.
- IDE integration (LSP, SARIF live updates).
### 17.1 Milestone 2 (rustc_public wiring) — in-progress sub-checklist
A working scaffold for Milestone 2 is in tree as of the post-v0.1 polish
checkpoint. The following items remain before the milestone can be
declared complete:
**Build infrastructure (DONE):**
- ✅ `crates/pitbull-subset/build.rs` opt-in env var `PITBULL_USE_RUSTC_PUBLIC=1`
- ✅ Custom rustc cfg `rustc_public_real` declared in workspace lints
- ✅ `extern crate rustc_public` + `feature(rustc_private)` in lib.rs (cfg-gated)
**Architectural correction (DONE):**
- ✅ Adapter pattern: shadow IR is the always-compiled internal type set;
  real rustc_public types are translated into shadow types by
  `mir_api::adapter` (cfg-gated). The visitor never sees real
  rustc_public types directly.
**Adapter translation surface (DONE):**
- ✅ `adapter::def_id` — stub via Debug-rendering hash
- ✅ `adapter::span` — placeholder (returns `Span::default()`; needs
  byte-offset extraction via `compiler_interface::with`)
- ✅ `adapter::ty` + `ty_kind` + `rigid_ty` — full RigidTy/TyKind
  dispatch over all 22 real RigidTy variants. Variants without a
  shadow analog (Foreign, Str, Pat, Coroutine*, CoroutineWitness,
  Dynamic, Never) are mapped to synthetic `__pitbull_*` ADT paths
  that the visitor walks past without firing rules — correct since
  PSS-1 has no specific rule on those types beyond the surrounding
  context (e.g. `Dynamic` triggers PB031 via TyKind::Dynamic at the
  TyKind level for safe references; this synthetic ADT path is the
  fallback for cases where Dynamic appears nested inside a RigidTy).
- ✅ `adapter::body` — fully populates `blocks` from real basic blocks
- ✅ `adapter::operand` — 4 real variants → 3 shadow variants
  (RuntimeChecks lossily mapped to a Bool constant)
- ✅ `adapter::place` + `adapter::projection` — full 7-variant surface
- ✅ `adapter::const_operand` — extracts the FnDef path for function
  calls (visitor-critical: enables PB011 alloc-call, PB023 atomic,
  PB025 volatile, PB028 thread, PB043 panic detection at call sites)
- ✅ `adapter::rvalue` — all 14 real variants (CheckedBinaryOp
  collapsed to BinaryOp, AddressOf mapped to RawPtr Rvalue)
- ✅ `adapter::statement` — all 12 real StatementKind variants
  (real lacks Deinit; shadow's Deinit is dead code in real-mode)
- ✅ `adapter::terminator` — all 10 real TerminatorKind variants
  (real lacks TailCall, Yield, CoroutineDrop, FalseEdge, FalseUnwind;
  shadow has them as dead code in real-mode; Resume/Abort renamed to
  UnwindResume/UnwindTerminate)
- ✅ `adapter::aggregate_kind`, `cast_kind`, `bin_op`, `un_op`,
  `assert_message`, `non_diverging_intrinsic`, `retag_kind` — full
  supporting-type translations
- ✅ `adapter::span` real line/col extraction (Task B, commit d581354)
  and filename URI side-channel (Task F, see Driver integration below).
  rustc_public does not expose byte offsets, so SARIF region encoding
  uses line/col only — adequate for IDE/CI consumers.
- ⏳ `adapter::def_id` should query the rustc bridge for a stable
  numeric ID rather than hashing Debug output (cosmetic; current
  hash IDs are stable within one compilation run, which is enough)
**End-to-end smoke confirmed (Box → PB011):**
A throwaway cargo project with `let b: Box<u32> = Box::new(42);`
under `cargo check` (with `RUSTC_WORKSPACE_WRAPPER` pointing at
pitbull-rustc) emits:
```
pitbull-rustc: PB011: `Box<T>` reachable — `Box<_>`
pitbull-rustc: PB048: panic strategy is `unwind` — ...
pitbull-rustc: crate analyzed: 1 items, 1 bodies walked, 14 subset violation(s)
```
The Box ADT triggers PB011; cargo init's default `panic = "unwind"`
profile triggers PB048; PB004/PB007 fire on the internal raw-pointer
machinery in `core::fmt::*` reachable from `println!`. This is the
end-to-end Milestone 2 success criterion.
**Visitor change (path normalization for std re-exports):**
rustc resolves item paths through whichever prelude brought them into
scope. For std-using crates, `Box` resolves as `std::boxed::Box` (via
the std re-export), not the canonical `alloc::boxed::Box`. The
visitor's `classify_adt` was broadened to accept both forms for PB011
(Box), PB012 (collections), PB015 (Rc/Arc). Shadow tests construct
the alloc form and continue to pass; real adapter typically produces
the std form and now also matches. No shadow type changes.
**Driver integration (PARTIAL):**
- ✅ `crates/pitbull-driver/build.rs` mirrors the subset crate's opt-in
- ✅ `pitbull-rustc` wrapper binary (`crates/pitbull-driver/src/bin/pitbull-rustc.rs`):
  on stable a stub that prints a diagnostic and exits 1; on nightly+opt-in
  uses `rustc_driver::run_compiler` with NoopCallbacks (passthrough)
- ✅ `cargo pitbull check` invokes `cargo check` with
  `RUSTC_WORKSPACE_WRAPPER` set to the wrapper's absolute path, so cargo
  calls our binary in place of rustc for every compile unit
- ✅ End-to-end smoke confirmed: nightly+opt-in wrapper compiles a Rust
  source file via rustc_driver, output binary runs correctly
- ✅ `PitbullCallbacks` implementing `rustc_driver::Callbacks`:
  `after_analysis` bridges to rustc_public via
  `rustc_internal::run(tcx, ...)`, walks `all_local_items()`, calls
  `adapter::body()` on each item with a body, runs `SubsetVisitor`,
  reports stats + violations on stderr.
- ✅ End-to-end via cargo confirmed: throwaway cargo project +
  `RUSTC_WORKSPACE_WRAPPER=path/to/pitbull-rustc cargo check`
  invokes the wrapper for each compile unit; PitbullCallbacks fires
  per-crate. (Reports 0 violations only because adapter::body still
  stubs the body interior — the pipeline is wired, the visitor sees
  empty bodies.)
- ✅ Reachability seeding via `pitbull.toml`'s `[reachability]
  verify_roots` (Task A). Path-based filtering — items whose
  fully-qualified name matches a root pattern get walked, others
  filtered out. `exclude` patterns also honored. Falls back to walk-all
  when no config / empty roots (over-approximating fail-safe). Driver
  forwards the user's `pitbull.toml` to dependency compiles via
  `PITBULL_TOML` env var.
  Note: `#[pitbull::verify]` attribute-based seeding remains a future
  option (requires `register_tool(pitbull)` in user crates AND
  proc-macro re-emission). Path-based filtering matches Creusot's
  approach and avoids both UX hurdles.
- ✅ Activate `corpus_runs_full_pipeline` integration test (Task C).
  Subprocess-based test that invokes the built `pitbull-rustc.exe`
  against each corpus file, gracefully skipping if prerequisites
  (wrapper binary, nightly toolchain) are missing. `PITBULL_REQUIRE_E2E=1`
  escalates missing-prerequisites to hard failure for CI.
  Documented unimplemented exceptions: PB041 (call-graph SCC analysis
  not implemented), PB054 (VC obligation, not visitor rule).
- ✅ Wrapper enumerates static + const items (Task E, corrected by
  Task H). `pitbull-rustc` matches on `CrateItem::kind()` and
  dispatches `ItemKind::Static` through `visit_static_item` (PB018
  fires end-to-end) and `ItemKind::Const` through `visit_const_item`.
  Mutability is resolved via the rustc_internal bridge —
  `TyCtxt::is_mutable_static` applied to the internal `DefId`
  returned by `rustc_internal::internal(tcx, item.def_id())`, since
  `rustc_public::ItemKind::Static` is a payload-less variant.
  Statics and consts are walked unconditionally regardless of
  `verify_roots` — those rules (PB018, PB021, PB022) are
  project-level and reject any such item in the local crate,
  independent of which (if any) function reads them. The `exclude`
  filter still applies for skipping specific item paths by name.
- ✅ Filename side-channel for SARIF artifactLocation URIs (Task F).
  Shadow `Span::file` is an opaque u32 hash (Copy-friendly, no
  owned strings); `adapter::span` populates a thread-local
  `FILENAME_TABLE` mapping each hash back to the rustc_public
  filename string. The wrapper drains it via
  `adapter::take_filename_table()` after `visitor.into_report()` and
  attaches it to the new optional `SubsetReport::filenames` field.
  `to_sarif_minimal` then emits `artifactLocation.uri` alongside the
  opaque `index`. Shadow tests stay unchanged (no adapter call,
  table empty, field stays `None`, only `index` is emitted).
  Wrapper now writes SARIF JSON to the path in `PITBULL_SARIF_OUT`
  when that env var is set; each invocation overwrites — multi-crate
  aggregation is a follow-up for the `cargo pitbull check` subcommand.
- ✅ Spec-context narrowing — predicate grammar (Task O.2).
  Replaces O.1's raw-SMT-LIB-only posture with an auditable
  Rust-like predicate language and a binding pass that maps
  predicate variables to MIR operand positions.

  Grammar accepted in `[verification.preconditions]`:
    "<ident> <cmp_op> <int_literal>"  e.g. "x < 100"
    "<int_literal> <cmp_op> <ident>"  e.g. "100 > x"  (normalized
                                                       to ident-first)
  where `<cmp_op>` is one of `<`, `<=`, `>`, `>=`, `==`, `!=`.

  Wiring:
    * `pitbull_subset::predicate::{Predicate, CmpOp, ParseError,
      TranslationError}` — typed IR plus a hand-rolled parser.
      `parse_predicate` accepts arbitrary whitespace, normalizes
      reversed form via `CmpOp::flip`, rejects malformed inputs
      with a `ParseError` that names the offender.
    * `pitbull_subset::predicate::predicate_to_smt_assertion`
      compiles to SMT-LIB. Signed types use `bvslt`/`bvsle`/etc.;
      unsigned use `bvult`/`bvule`/etc. Equality and inequality
      use SMT-LIB's `=` and `distinct`. Negative literals encode
      as two's-complement bit-vectors (e.g. `i8` -1 → `#xFF`).
      Out-of-range literals (e.g. `x < 1_000_000` for `u8`)
      produce `TranslationError::LiteralOutOfRange` rather than
      silent truncation.
    * `mir_api::Body` gains `arg_names: Vec<String>`; the adapter
      populates from `rustc_public::Body::var_debug_info`
      (1-based `argument_index` shifted to 0-based).
    * `SubsetVisitor.current_body_arg_names` is set per-body and
      consulted by a new `operand_arg_name` helper that resolves
      `Operand::Copy(Place(arg_local, no_projections))` to the
      source identifier.
    * `maybe_emit_overflow_obligation` now attempts the parse →
      bind → translate path per precondition. Any step's failure
      falls back to the O.1 raw-splice posture, so existing
      raw-SMT-LIB configs continue to work unchanged.

  Layered tests (24 new):
    * `predicate::tests::*` — 16 parser/translator tests covering
      every operator, signed/unsigned, reversed form, negative
      literals, two's-complement encoding, out-of-range rejection,
      unsupported types, malformed inputs, and operator-matched-
      but-operands-bad guarding against `<=`-as-`<` misparsing.
    * `visitor::tests::predicate_precondition_binds_lhs_operand`
      pins the parse → bind → translate path end-to-end on a
      synthetic body that mirrors MIR for `fn add_one(x) { x + 1 }`.
    * `visitor::tests::unbound_predicate_falls_back_to_raw_splice`
      pins the fallback when the predicate's variable doesn't
      match any operand.
    * `visitor::tests::raw_smt_lib_precondition_unchanged` pins
      the O.1 escape hatch: hand-written SMT-LIB strings flow
      through unchanged.

  Smoke (Z3 not on dev machine): wrapper invoked on
  `pub fn add_two(x: u32, y: u32) -> u32 { x + y }` with
  `"corpus_test::add_two" = ["x < 100", "y < 100"]` in pitbull.toml
  emits one obligation with both predicates translated and bound
  to `lhs`/`rhs`. Visible per-layer via the test suite:

      "x < 100" + arg x at local 1 + BinaryOp(_, Copy(_1), _)
        → (assert (bvult lhs #x00000064))

  Limitations to lift in O.3:
    * The binding fires ONLY for `BinaryOp` whose operand is a
      DIRECT `Operand::Copy(Place(arg_local, []))`. Intermediate
      `let`s (e.g. `let y = x; y + 1`) introduce temporaries that
      break the chain; the predicate falls back to raw splice.
      A future data-flow pass closes that gap.
    * Constant operands (e.g. the `1` in `x + 1`) are not yet
      constrained in the SMT problem — they're free BV vars from
      the solver's perspective, so `x + 1` with `x < 100` still
      returns sat (witness: rhs=u32::MAX). Constant-value
      extraction from `ConstOperand` lands in O.2.5 / O.3.
    * Multi-conjunct preconditions are arrays — each conjunct is
      one entry in the value array. Single-string `"x < 100 AND
      y > 0"` is not yet parsed.
- ✅ Spec-context narrowing — foundation (Task O.1). Threads
  spec-derived preconditions through the visitor → VC obligation →
  SMT-LIB pipeline. The first commit of three staged steps toward
  `#[pitbull::requires(...)]` end-to-end.
  Posture today: `[verification.preconditions]` in `pitbull.toml`
  accepts raw SMT-LIB `(assert ...)` directives per function path.
  Pieces wired:
    * `pitbull_subset::vc::VcObligation.assumptions: Vec<String>`
      with `#[serde(skip_serializing_if = "Vec::is_empty")]`.
    * `SubsetConfig.verification.preconditions: BTreeMap<String,
      Vec<String>>` deserialized from TOML.
    * `SubsetVisitor::set_current_preconditions` /
      `clear_current_preconditions`. `maybe_emit_overflow_obligation`
      attaches the current list to every obligation it emits.
    * `pitbull-rustc.rs`: per-item lookup by `CrateDef::name()` →
      `set_current_preconditions(...)` before each `visit_body`.
    * `pitbull_vc::compile` and `pitbull_vc::smt::emit_overflow_problem_with_assumptions`
      splice each assumption verbatim into the SMT-LIB problem
      *before* the safety predicate, so the solver gets them as
      hypotheses.

  Layered tests pin each handoff:
    * `config::tests::preconditions_table_round_trips_from_toml`
    * `config::tests::preconditions_table_optional` (backward compat)
    * `vc::tests::obligation_with_assumptions_round_trips`
    * `visitor::tests::preconditions_propagate_to_obligation_assumptions`
    * `visitor::tests::clearing_preconditions_makes_assumptions_empty`
    * `pitbull_vc::vc::tests::compile_incorporates_assumptions`

  Smoke (Z3 not installed on dev machine): `add_one(x: u32) -> u32 {
  x + 1 }` with `"corpus_test::add_one" = ["(assert (bvult lhs
  #x00000064))"]` in pitbull.toml produces one VC with the
  assumption attached; wrapper reports "undischarged (no solver)"
  cleanly. On a machine with Z3 in PATH the verdict flows through
  the normal match arms. The UX is intentionally crude in O.1
  (users hand-write SMT-LIB and track operand positions) — O.2
  introduces the Rust-like predicate grammar that fixes both.
- ✅ v0.2 deductive backend spine: end-to-end VC dispatch (Task N).
  Wires the visitor → `pitbull-vc` → external SMT solver loop that
  makes "deductive verifier" literally true for the first time:
    * `pitbull_subset::vc::VcObligation` is the typed-claim IR;
      `pitbull_vc::VcGoal` is the compiled form (obligation + SMT-LIB
      text). Split so the visitor and solver evolve independently.
    * `SubsetVisitor.visit_rvalue` now emits a
      `VcObligationKind::ArithmeticOverflow { op, ty_name }`
      for every `Rvalue::BinaryOp(Add | Sub | Mul, lhs, rhs)`
      where both operands resolve to the same primitive integer
      type. Other binops and mixed-type operands are no-ops.
      `SubsetReport.vc_obligations: Vec<VcObligation>` carries the
      results through the report (skip-serializing when empty).
    * `pitbull_vc::compile` turns each obligation into a
      QF_BV SMT-LIB problem using `bvuaddo` / `bvsaddo` / etc.
      `pitbull_vc::solver::invoke_z3` dispatches; verdicts map:
      `unsat` ⇒ discharged, `sat` ⇒ counterexample exists,
      `unknown` / timeout / error / not-installed ⇒ undischarged
      (each surfaced distinctly on stderr).
    * `pitbull-rustc` wrapper iterates `report.vc_obligations`
      after the MIR walk, dispatches each, and prints a summary
      line: `VC summary: N obligation(s), D discharged, U undischarged`.
    * Graceful degradation when Z3 isn't installed: the wrapper
      announces once and lists each obligation as "undischarged
      (no solver)" — the rest of the report still emits.

  Smoke test against `fn add_one(x: u32) -> u32 { x + 1 } fn
  multiply(a: u32, b: u32) -> u32 { a * b }` produces:
  ```
  pitbull-rustc: vc pb049-add-0: undischarged (no solver)
  pitbull-rustc: vc pb049-mul-1: undischarged (no solver)
  pitbull-rustc: VC summary: 2 obligation(s), 0 discharged, 2 undischarged
  ```
  (On a machine with z3 in PATH, both report `discharged (unsat)`
  for the trivial constraints today's scaffold emits — though
  reality is the inputs are unconstrained, so `sat` is the
  correct verdict; the scaffold lacks input-range narrowing, a
  follow-up task.)
- ✅ HIR pre-pass for PB001 `unsafe { ... }` block detection (Task G).
  rustc's MIR construction discards HIR-level block scopes, so PB001
  (the bare `unsafe` block, distinct from the rules that fire on
  operations *within* one — PB004/PB007/PB009) was previously
  undetectable in the wrapper. The wrapper now adds an `extern crate
  rustc_hir; extern crate rustc_span;` and an `UnsafeBlockVisitor`
  implementing `rustc_hir::intravisit::Visitor` with
  `NestedFilter = nested_filter::All`, driven by
  `tcx.hir_visit_all_item_likes_in_crate`. Each block whose
  `BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided)` matches
  emits PB001; `CompilerGenerated` (e.g. unsafe-trait method bodies
  rustc desugars) is ignored. Spans are converted from
  `rustc_span::Span` to shadow `Span` via `SourceMap::lookup_char_pos`
  and the same DefaultHasher-on-filename scheme adapter::span uses,
  so both walks share the SARIF filename table. PB001 violations are
  appended to the report alongside the MIR-derived ones; the
  per-crate summary now reports unsafe-block count separately.
**Known limitations of the current scaffold:**
- Nightly + opt-in `cargo test` fails to link (`rlib format` errors for
  rustc internals like `rustc_data_structures`, `rustc_index`). This is
  a known `rustc_private` mechanism limitation; tools like Kani and
  Creusot solve it by running tests inside `rustc_driver` callbacks
  rather than as standalone test binaries. The pitbull-subset crate's
  unit tests work fine on stable Rust (49 + 1 ignored, the v0.1
  baseline). The driver-side test harness is the right home for tests
  that exercise the adapter against real MIR.
**Verification today:**
```bash
# Stable: v0.1 baseline (49 + 1 ignored, 0 warnings)
cargo test --workspace --all-features
# Nightly + opt-in: adapter scaffold compiles
PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 check -p pitbull-subset
```
See `docs/ROADMAP.md` (forthcoming) for the milestone plan.
