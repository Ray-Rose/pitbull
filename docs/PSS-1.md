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
**Adapter translation surface (PARTIAL):**
- ✅ `adapter::def_id` — stub via Debug-rendering hash
- ✅ `adapter::span` — placeholder (returns `Span::default()`; needs
  byte-offset extraction via `compiler_interface::with`)
- ✅ `adapter::ty` — placeholder (returns `Ty::Bool`; needs full
  RigidTy/TyKind dispatch under compiler context)
- ✅ `adapter::body` — body shell with translated locals; statements
  and terminators not yet translated
- ⏳ `adapter::statement` — 13 StatementKind variants
- ⏳ `adapter::terminator` — 15 TerminatorKind variants
- ⏳ `adapter::rvalue` — 15 Rvalue variants
- ⏳ `adapter::operand`, `adapter::place`, `adapter::projection` — full surface
- ⏳ Real `Span` byte-offset extraction (requires rustc context)
- ⏳ Full `RigidTy` / `TyKind` translation (requires rustc context)
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
- ⏳ `PitbullCallbacks` implementing `rustc_driver::Callbacks` —
  currently `NoopCallbacks`, needs `after_analysis` hook that walks
  reachable MIR through the adapter and runs `SubsetVisitor`
- ⏳ `RustcPublicProvider` implementing `BodyProvider` against the adapter
- ⏳ Reachability seeding from `#[pitbull::verify]` annotated items
- ⏳ Activate `corpus_runs_full_pipeline` integration test
**Known limitations of the current scaffold:**
- Nightly + opt-in `cargo test` fails to link (`rlib format` errors for
  rustc internals like `rustc_data_structures`, `rustc_index`). This is
  a known `rustc_private` mechanism limitation; tools like Kani and
  Creusot solve it by running tests inside `rustc_driver` callbacks
  rather than as standalone test binaries. The pitbull-subset crate's
  unit tests work fine on stable Rust (49 + 1 ignored, the v0.1
  baseline). The driver-side test harness is the right home for tests
  that exercise the adapter against real MIR.
- Shadow `Span` carries `lo/hi/file` triple but `adapter::span` returns
  zeros; SARIF reports against real-rustc_public bodies will have
  placeholder source locations until byte-offset extraction lands.
**Verification today:**
```bash
# Stable: v0.1 baseline (49 + 1 ignored, 0 warnings)
cargo test --workspace --all-features
# Nightly + opt-in: adapter scaffold compiles
PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 check -p pitbull-subset
```
See `docs/ROADMAP.md` (forthcoming) for the milestone plan.
