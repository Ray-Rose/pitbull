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
**Exemption (2026-06-13).** An `IntToInt` cast of an integer
**constant** whose value is representable in the target type is
*value-preserving* — there is no truncation and no sign-change, so the
cast cannot alter the value and needs no obligation. Such casts are
ACCEPTED (with a transparency audit note). Everything else still fails
closed: every cast of a **non-constant** operand, and every
value-CHANGING constant cast (narrowing like `300 as u8`, sign-flipping
like `-1 as u32`, or an unsupported target width such as `u128` /
`usize`), is rejected. The gate is `value_fits_in_int_ty`
(`predicate.rs`) + `value_preserving_int_cast` (`visitor.rs`); the value
must round-trip through both the source and target types, so the one
lossy-extraction case (`u128` > `i128::MAX`) fails closed. This unblocks
shift code: rustc lowers `x << 4` with a synthetic `const 4_i32 as u32`
cast (the untyped `4` defaults to i32 and is cast to the value type for
the shift-overflow bounds check), which PB051 previously rejected,
making all `x << N` code unverifiable.
**Future.** v0.2 with auto-generated cast obligations for the
value-changing cases (so a `u64 as u32` narrowing emits a truncation VC
rather than a hard reject).
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
**Detects.** Derive/attribute proc-macros that expand into reachable
code from a crate not on `subset.allowed_proc_macros` in `pitbull.toml`.
**Status.** ENFORCED (2026-05-29). The wrapper's HIR pre-pass walks each
reachable item's span expansion chain (`SyntaxContext` → `ExpnData` →
`macro_def_id` → defining crate); a `Derive`/`Attr` expansion from a
crate that is not local, not a trusted toolchain crate
(core/std/alloc/proc_macro), and not on the allowlist emits a PB059
violation at the macro call-site. Derive/attribute macros cannot be
written with `macro_rules!`, so this is free of decl-macro false
positives. Function-like (`name!{…}`) proc-macros are a tracked
follow-up (distinguishing them from external `macro_rules!` needs a
proc-macro-crate check).
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
### PB076 — Postcondition unmet
Added in v0.2 alongside `#[pitbull::ensures("...")]` (Task Q.4).
Category: Control flow (registered as the 76th rule; `RULE_COUNT = 76`).
A spec-declared postcondition must hold at every function exit — every
`TerminatorKind::Return`, including the implicit return at end-of-body.
The visitor emits one `VcObligationKind::EnsuresPostcondition` per
return site (and, fail-closed, one at the body span when a body with
an `ensures` diverges / has no return terminator). The special binding
`result` denotes the return value.
**v0.2 status (Q.4a — 2026-05-29).** PB076 now DISCHARGES via SMT for
the straight-line shapes the visitor can capture *soundly*: a linear
chain of blocks (following `Goto` / overflow-`Assert` success to
`Return`) whose result is a (return-typed) argument, an integer
constant, a wrapping `Add`/`Sub`/`Mul` (`bvadd`/`bvsub`/`bvmul`,
bit-exact for Rust's wrapping), a `Div`/`Rem` (`bvsdiv`/`bvudiv`/
`bvsrem`/`bvurem` — Rust's truncating `/` and dividend-signed `%`), or a
shift (`bvshl`; `>>` is `bvashr`/`bvlshr` by the value's signedness —
arithmetic vs logical; constant or same-type amount) — all verified vs
Z3 — over captured operands. `result` and the
return-typed parameters are declared as
bit-vectors of the return width; the visitor asserts the captured body
effect (`(= result <expr>)`), assumes every translatable precondition
(with the F1 consistency guard), and negates the postcondition — so
`unsat` ⇒ discharged and `sat` ⇒ a genuine counterexample (NOT
discharged). The wrapping arithmetic is modelled over the FULL input
range rather than excluding the overflow-panic region the `Assert`
guards — a sound over-approximation (the modelled input set is a
superset of the returning set, so `unsat` still means "holds for every
returning input"; at worst it is conservative). Anything it cannot
capture with certainty — a bitwise body effect or a variable
narrower-width shift amount (Q.4b–Q.4d cover `Add`/`Sub`/`Mul`/`Div`/`Rem`
plus constant/same-type shifts), branches/loops, calls, casts, a
non-primitive-integer return, or an untranslatable spec — stays
*pending* (fail closed: never a false "verified"). A wrong body-effect
encoding would falsely discharge a wrong postcondition, so the capture
admits only shapes it can prove exactly and invalidates on any
projection write or uncapturable rvalue.
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
- Proof certificate format and replay command. **MVP shipped (Task T.1
  + T.2):** `pitbull-vc::cert` defines the replayable bundle and the
  wrapper emits it to `PITBULL_CERT_OUT`; `cargo pitbull replay` re-runs
  each recorded SMT and confirms the verdict reproduces (on stable Rust).
  Cryptographic signing of certificates is the remaining T.3 layer.
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
- ✅ `adapter::span` real line/col extraction (Task B, commit 722dc20)
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
- ✅ `#[pitbull::requires(...)]` attribute extraction (Task O.3).
  Closes the v0.2 spec-context-narrowing series (O.1 → O.2 →
  O.2.5 → O.3). Source-level annotations now work as a peer to
  the existing `pitbull.toml`-based mechanism: the user adds
  `#![feature(register_tool)]` + `#![register_tool(pitbull)]`
  to their crate root and writes
  `#[pitbull::requires("x < 100")]` on functions; the wrapper's
  HIR pre-pass extracts the string-literal argument and feeds
  it through the same predicate-translation pipeline as
  pitbull.toml preconditions.

  Pieces wired:
    * `pitbull-rustc.rs` adds `extern crate rustc_ast` for the
      `LitKind::Str` pattern match.
    * `collect_hir_unsafe_blocks` becomes `collect_hir_pre_pass`
      — now returns a third value, a
      `HashMap<String, Vec<String>>` of HIR-derived preconditions
      keyed by fully-qualified function path
      (`"{crate_name}::{def_path_str(def_id)}"`).
    * `UnsafeBlockVisitor` becomes `HirPreVisitor` with a new
      `preconditions` field; gains a `visit_item` method that
      filters `ItemKind::Fn { .. }`, reads `tcx.hir_attrs(hir_id)`,
      matches `attr.path_matches(&[Symbol::intern("pitbull"),
      Symbol::intern("requires")])`, and extracts each
      `LitKind::Str` argument as a precondition string.
    * Wrapper's `run_pitbull_subset_check` merges the
      HIR-derived map with `cfg.verification.preconditions`
      before calling `visitor.set_current_preconditions(...)`.
      Both sources flow through the same downstream layers —
      F2 lex validation, F1 consistency check, predicate
      grammar parsing — so the security and soundness
      guarantees are identical.
    * Verdict lines in the dispatch loop now include an
      `[N assumption(s)]` suffix that resolves the v0.2.5
      audit's L-3 finding (assumptions previously invisible to
      stderr).

  Tests:
    * `integration.rs::pitbull_requires_attribute_attaches_precondition`
      — writes a probe with `#![register_tool(pitbull)]` and
      `#[pitbull::requires("x < 100")]`, invokes the wrapper,
      asserts stderr contains `[2 assumptions]` (1 const-pin
      from O.2.5 + 1 attribute precondition from O.3).
    * `integration.rs::no_pitbull_requires_attribute_keeps_only_const_pin`
      — the control: same body without the attribute carries
      `[1 assumption]`. The differential is the signal that
      the attribute extraction fires.
    * New helper `run_one_corpus_file_preserving_attrs` opts
      out of the legacy `strip_pitbull_attrs` step so the
      attribute survives to the wrapper.

  Restrictions (deferred to v0.3+):
    * Only string-literal arguments accepted:
      `#[pitbull::requires("x < 100")]`. Rust-expression-form
      `#[pitbull::requires(x < 100)]` requires a real attribute
      parser; out of scope for this commit.
    * Non-string-literal arguments silently skipped (no audit
      note today — could be added if the format becomes
      common).
    * Only attributes on top-level `ItemKind::Fn` items
      extracted. Methods on impls / trait items / nested fns
      not yet covered.
- ✅ PB054 MVP — slice/array index sites emit IndexBound
  obligations (Task P). Visitor counterpart to the PB049
  overflow obligations; the next step in turning v0.2 from
  "deductive verifier with one obligation kind" into "verifier
  with one kind discharged and one kind plumbed end-to-end and
  visible". The wrapper now identifies every slice/array index
  in the MIR walk and emits a `VcObligationKind::IndexBound`
  obligation tagged with the source span.

  Pieces wired:
    * `SubsetVisitor::visit_projection` (visitor.rs) now calls
      `emit_index_bound_obligation` for `ProjectionElem::Index`,
      `ProjectionElem::ConstantIndex`, and `ProjectionElem::Subslice`.
      Previously all three were silent no-ops — the rule-meta
      registry advertised PB054 as "slice index without bound
      proof" but no visitor path emitted an obligation.
    * `emit_index_bound_obligation` is modeled on the existing
      `emit_panic_reachability_obligation`: pushes a
      `VcObligation { id: "pb054-idx-{seq}", kind: IndexBound,
      span, assumptions: current_body_preconditions.clone() }`.
      Preconditions are carried verbatim so the v0.3+ backend
      inherits spec context automatically when the encoding
      arm is written.
    * Distinct obligation-ID prefix (`pb054-idx-`) is mandatory:
      `rules::PB054` is also used by the projection-depth cap
      at `MAX_PROJECTION_DEPTH` (via `reject(PB054, ...)` in
      `visit_place`). The two PB054 sites are semantically
      adjacent (both about "projection sanity") but distinct in
      audit-trail terms — the syntactic depth-cap appears as a
      `SubsetError`; the index-bound check appears as a
      `VcObligation`. The ID prefix lets an auditor reading
      stderr / SARIF disambiguate at a glance.
    * `pitbull-vc::compile` still returns `None` for
      `IndexBound`, so the wrapper reports each as "pending
      (compilation not yet supported for IndexBound)". This is
      intentional — the audit posture is "no silent skips" and
      a "pending" line makes the gap visible. The SMT encoding
      arm (~`(declare-const idx ...) (declare-const len ...)
      (assert (bvult idx len))`) lands in a follow-up commit.
    * Doc-drift cleanup: stale `UnsafeBlockVisitor` references
      in `visitor.rs` and PSS-1.md updated to `HirPreVisitor`
      (the rename happened in Task O.3 but two doc comments
      were missed); HANDOFF.md Option A documents the rule-ID
      overlap explicitly.

  Tests:
    * `visitor::tests::projection_index_emits_index_bound_obligation`
      — Index(local) projection emits one IndexBound with the
      `pb054-idx-` prefix.
    * `visitor::tests::projection_constant_index_emits_index_bound_obligation`
      — ConstantIndex { offset } same shape.
    * `visitor::tests::projection_subslice_emits_index_bound_obligation`
      — Subslice { from, to } same shape.
    * `visitor::tests::non_index_projections_do_not_emit_index_bound`
      — negative-space pin: Deref / Field / Downcast must NOT
      emit. Future re-wiring can't silently start emitting
      bogus obligations on benign projections.
    * `visitor::tests::index_bound_carries_body_preconditions`
      — O.1 plumbing: assumptions field is populated from
      `current_body_preconditions` just like ArithmeticOverflow
      and PanicReachability do.
    * `visitor::tests::multiple_index_bounds_get_distinct_ids`
      — sequence numbering: two index sites in one body produce
      `pb054-idx-0` and `pb054-idx-1`, so an auditor can map
      each "pending" line back to a distinct location.

  E2e probe (real corpus file): the wrapper run against
  `crates/pitbull-subset/tests/corpus/reject/PB054_unbounded_index.rs`
  (a `fn first_byte_unsafe(s: &[u8], i: usize) -> u8 { s[i] }`)
  produces:
  ```
  pitbull-rustc: vc pb054-idx-0 (PB054): undischarged (no solver)
  pitbull-rustc: VC summary: 1 obligation(s), 0 discharged, 1 undischarged
  ```
  (Task P.1 superseded this with a real SMT problem; see below.
  The integration test now removes PB054 from
  `KNOWN_UNIMPLEMENTED_REJECT` because the wrapper surfaces the
  canonical `(PB054)` rule string in stderr.)
- ✅ PB054 SMT discharge — IndexBound compiles to QF_BV
  (Task P.1). Closes the loop on the "deductive verifier"
  claim for slice indices: the visitor emits an `IndexBound`
  obligation (Task P), `pitbull-vc::compile` now produces a
  real SMT-LIB problem, the wrapper dispatches it through Z3,
  and the verdict line surfaces the canonical PSS-1 rule ID
  on every kind via a new `rule_id()` method.

  Pieces wired:
    * `pitbull_subset::vc::VcObligationKind::rule_id()` returns
      `&'static str` — `"PB049"`, `"PB043"`, `"PB054"`,
      `"PB041"` — the printable uppercase form of the obligation's
      mapped PSS-1 rule. Pinned by the
      `rule_id_for_each_kind` unit test so adding a new kind
      without updating this method fails to compile (exhaustive
      match).
    * `pitbull_vc::smt::emit_index_bound_problem_with_assumptions`
      generates the QF_BV problem: declares `idx` and `len` as
      64-bit unsigned bit-vectors, splices assumptions in,
      asserts the negation of the safety predicate
      (`(assert (bvuge idx len))`), `(check-sat)`. The 64-bit
      width is hardcoded in `INDEX_SMT_BITS` pending the
      target-pointer-width threading from `[verification]`
      config — the wider default is sound for both 32-bit and
      64-bit targets (a 64-bit problem dominates the 32-bit
      one).
    * `emit_index_bound_consistency_check` mirrors
      `emit_consistency_check` for the F1 audit guard: same
      declarations + assumptions, no safety predicate; the
      dispatcher runs it first to refuse vacuous discharges
      from contradictory preconditions.
    * `pitbull_vc::vc::compile` IndexBound arm calls both
      emitters. Obligations with assumptions populate
      `consistency_check`; obligations without skip the extra
      solver call (matches the ArithmeticOverflow contract).
    * Wrapper verdict format (`pitbull-rustc.rs`): each
      verdict line now includes `(PB054)` / `(PB049)` / etc.
      via `obligation.kind.rule_id()`. Applied to all six
      dispatch branches (discharged / NOT DISCHARGED / no
      solver / unknown / timeout / error) AND the
      consistency-check branches (REFUSED / timeout / error)
      AND the "pending" line (when compile returns None).
      Two purposes: integration tests can match the canonical
      rule string, and auditors don't have to mentally map
      `pb054-idx-0` → PB054.
    * `integration.rs::KNOWN_UNIMPLEMENTED_REJECT` drops PB054
      — the wrapper now surfaces `PB054` uppercase on the
      verdict line, so the contains-check matches. A new
      `KNOWN_UNDISCHARGED_ACCEPT = &[54]` constant skips the
      ACCEPT corpus file (`PB054_bounded_index.rs`) because
      the verifier can detect the index site but cannot yet
      discharge the obligation without operand bindings —
      until Task P.2+ wires the bindings, even
      `#[pitbull::requires(i < s.len())]` doesn't constrain
      the SMT `idx`/`len` variables.

  Tests added:
    * `pitbull_subset::vc::tests::rule_id_for_each_kind` —
      pins the kind → rule mapping.
    * `pitbull_vc::smt::tests::index_bound_problem_basic` —
      pins the SMT shape (logic, declarations, predicate).
    * `pitbull_vc::smt::tests::index_bound_uses_unsigned_predicate`
      — pins `bvuge` (slice indices are usize, never
      negative; signed predicate would admit impossible
      counterexamples).
    * `pitbull_vc::smt::tests::index_bound_with_assumptions_orders_correctly`
      — assumptions come before the safety predicate (same
      contract as overflow encoding).
    * `pitbull_vc::smt::tests::index_bound_consistency_check_omits_safety_predicate`
      — F1 guard test for the IndexBound side.
    * `pitbull_vc::vc::tests::compile_index_bound_produces_smt`
      — compile no longer returns None for IndexBound.
    * `pitbull_vc::vc::tests::compile_index_bound_with_assumptions_includes_consistency_check`
      — F1 wiring is symmetric to ArithmeticOverflow.
    * `pitbull_vc::vc::tests::compile_panic_and_recursion_still_return_none`
      — negative-space pin so adding IndexBound to compile
      didn't accidentally enable the other unhandled kinds.

  E2e probe (real corpus file, no Z3 installed):
  ```
  pitbull-rustc: vc pb054-idx-0 (PB054): undischarged (no solver)
  pitbull-rustc: VC summary: 1 obligation(s), 0 discharged, 1 undischarged
  ```
  With Z3 installed but without operand bindings the verdict
  becomes `NOT DISCHARGED (sat — counterexample exists)` — the
  honest answer for an obligation whose `idx` and `len` are
  unconstrained. Test totals after this commit: 1 + 104 + 15 +
  24 = 144 (up from 136; +8 SMT-discharge tests). Task P.2 (next
  entry) wires the operand binding that lets `i < len`-style
  preconditions actually constrain the SMT problem.
- ✅ PB054 P.2 — operand binding (idx → source identifier).
  Closes the PB054 deductive chain end-to-end. `fn at(s: &[u8],
  i: usize) -> u8 { s[i] }` with a precondition `(assert (bvult
  i len))` in `pitbull.toml` now reports `discharged (unsat
  — safety property holds) [1 assumption]` under Z3.

  Pieces wired:
    * `VcObligationKind::IndexBound` becomes a struct variant:
      `IndexBound { idx_source_name: Option<String> }`. The
      visitor populates it from the MIR local that the
      `ProjectionElem::Index(Local)` references. When the index
      local IS a function-argument slot whose source name is
      known (e.g. `i` in `fn at(s, i) { s[i] }`), the name flows
      into the obligation. Conservative posture: indices
      derived from local computations (intermediate `let`
      bindings, arithmetic results) emit `None` because the
      visitor doesn't do data-flow analysis — the SMT problem
      then has no source-name alias, the precondition silently
      doesn't bind, and the obligation reports as undischarged.
      That's the audit-safe direction: missing-bind ⇒ over-
      approximate "could fail", not under-approximate
      "vacuously holds".
    * New visitor helper `local_arg_name(Local) -> Option<String>`:
      sibling to the existing `operand_arg_name(Operand)`,
      reusing the same arg-slot-lookup logic (`_1..=_arg_count`
      → `current_body_arg_names[0..arg_count)`, skipping empty
      names from anonymous patterns).
    * `emit_index_bound_obligation` now takes
      `idx_source_name: Option<String>` and applies F2 lex
      validation (`validate_assertion_form`) to each
      precondition before attaching, with a PB054-specific
      audit note on rejection. Mirrors the audit posture of the
      PB049 path — no silent skips when a user precondition is
      malformed. The v0.2 grammar's `<ident> <cmp> <int>` form
      doesn't apply to IndexBound (whose natural shape is `i <
      len`, two idents), so only raw SMT-LIB strings flow
      through today; the predicate-grammar extension to ident-
      vs-ident lands in a follow-up.
    * `smt::emit_index_bound_problem_with_assumptions` now
      takes `idx_alias: Option<&str>`. When `Some(name)`, the
      SMT problem emits `(define-fun <name> () (_ BitVec 64)
      idx)` between the variable declarations and the
      assumptions. A user precondition `(assert (bvult i len))`
      then reaches `idx` via the alias; combined with the
      safety negation `(assert (bvuge idx len))`, the
      conjunction is unsat under any sound precondition.
      Collision guard: an alias name equal to `idx` or `len`
      is silently dropped (no-op for `idx`, would collide with
      `len`'s declaration).
    * `emit_index_bound_consistency_check` takes the SAME
      alias for the F1 guard — running the consistency check
      against a different model than the main problem would
      let the F1 guard miss-fire on alias-dependent
      assumptions.
    * `pitbull-vc::vc::compile` threads `idx_source_name.as_deref()`
      through to both SMT emitters.
    * Integration test infrastructure now passes
      `--crate-name=corpus_test` explicitly. CARGO_PKG_NAME is
      a cargo env var that rustc doesn't read; without `--
      crate-name` rustc derived the crate name from the temp
      filename, silently breaking pitbull.toml-keyed
      precondition lookups for e2e tests. The fix landed
      alongside Task P.2 because the new bounded-index
      capstone exposed it (the existing add_one capstone was
      Z3-gated and skip-passed on dev machines without Z3).

  Tests added:
    * `visitor::tests::index_projection_binds_arg_source_name`
      — pins that an arg-slot index (`_2` in a body with
      `arg_names = ["s", "i"]`) resolves to `Some("i")` via
      `local_arg_name`.
    * `visitor::tests::index_projection_with_non_arg_local_has_no_binding`
      — pins the conservative-fail direction for non-arg
      locals.
    * `visitor::tests::constant_index_and_subslice_have_no_idx_source_name`
      — pins that ConstantIndex / Subslice carry `None` (no
      MIR local to look up).
    * `pitbull_vc::smt::tests::index_bound_with_alias_emits_define_fun`
      — SMT-shape pin for the alias path.
    * `pitbull_vc::smt::tests::index_bound_alias_collision_with_canonical_names_dropped`
      — collision-guard pin.
    * `pitbull_vc::smt::tests::index_bound_alias_lets_assumption_reference_source_name`
      — assumption-after-alias ordering pin.
    * `pitbull_vc::vc::tests::compile_index_bound_with_source_name_emits_alias`
      — `compile()` threading pin (both main SMT and
      consistency check carry the alias).
    * `integration::tests::wrapper_proves_bounded_index_safe_under_precondition`
      — full e2e capstone: writes a probe with `fn at(s, i) {
      s[i] }`, a `pitbull.toml` with `(assert (bvult i len))`,
      invokes the wrapper, asserts `discharged (unsat)` and
      exit code 0 when Z3 is on PATH. Skips gracefully without
      Z3.

  E2e capstone output (Z3 4.13.0 via GNATprove bundle):
  ```
  pitbull-rustc: vc pb054-idx-0 (PB054): discharged (unsat — safety property holds) [1 assumption]
  pitbull-rustc: VC summary: 1 obligation(s), 1 discharged, 0 undischarged
  ```

  Restrictions (deferred to v0.3+):
    * `KNOWN_UNDISCHARGED_ACCEPT = &[54]` stays in place for
      the corpus accept file (`PB054_bounded_index.rs`) — that
      file uses `#[pitbull::requires(i < s.len())]` in
      expression form, which the O.3 attribute parser (string-
      literal only) can't extract. Use pitbull.toml-based
      preconditions for now; the attribute-expression parser
      extension lands separately.
    * `len` doesn't have a source-level alias yet; users still
      write `len` (the canonical SMT name) in raw-SMT
      preconditions. Synthesizing `s_len`-style aliases for
      the slice place would require threading the base local's
      source name through the projection visit — natural
      follow-up.
    * The predicate grammar doesn't yet support
      `<ident> <cmp> <ident>` form, so users can't write
      `"i < len"` and have it desugar to SMT — they write the
      raw `(assert (bvult i len))` form via pitbull.toml.

  Test totals after this commit: 1 + 107 + 16 + 28 = 152 (up
  from 144; +8 tests covering visitor binding, SMT alias
  emission, compile threading, and e2e discharge).
- ✅ Constant-operand value extraction — the headline-demo
  unlocker (Task O.2.5). Before this commit, the SMT problem
  treated `Operand::Constant` as a free `BitVec N` variable —
  even with `requires(x < 100)` as a precondition for
  `fn add_one(x: u32) -> u32 { x + 1 }`, the obligation
  returned `sat` (witness: rhs = u32::MAX) because the
  constant `1` wasn't constrained. After O.2.5 the wrapper
  produces SMT containing `(assert (= rhs #x00000001))`
  alongside the precondition translation
  `(assert (bvult lhs #x00000064))`, which Z3 returns `unsat`
  on — the obligation discharges.

  Pieces wired:
    * Shadow `mir_api::ConstOperand` gains
      `value: Option<i128>`. Stored as `i128` to cover every
      supported primitive integer (u8..u128, i8..i128); u128
      values above i128::MAX wrap via two's complement,
      producing the same bit pattern in the SMT encoding.
    * `adapter::const_operand` populates the value via a new
      `try_extract_integer_value` helper. Path:
      `c.const_.kind()` → `ConstantKind::Allocated(alloc)` →
      `alloc.read_int()` / `alloc.read_uint()` depending on
      the constant's RigidTy. Non-integer / unevaluated
      constants return `None` (silent — caller distinguishes).
    * `predicate::operand_pin_assertion` emits the SMT
      directive `(assert (= <pos> <bv-lit>))` for a known
      operand value. Reuses the two's-complement bit-vector
      encoder. No range check — values come from real MIR
      constants whose type is already that of the operand.
    * `SubsetVisitor::maybe_emit_overflow_obligation` walks
      the two operands; for each `Constant` with a known
      value, synthesizes a pinning assertion and pushes it to
      `obligation.assumptions` BEFORE the user preconditions.
      The pins appear first in the SMT problem (reading
      "the operand IS 1, AND x < 100, AND the negation of
      no-overflow"); this ordering is cosmetic for the
      solver but reads naturally for an auditor.

  Layered tests (5 new in commit 0d52ae1, plus 1 e2e test
  in the audit follow-up at integration.rs::wrapper_proves_add_one_safe_under_precondition):
    * `predicate::tests::operand_pin_assertion_basic` —
      pins the bv-literal encoding for u32/i64/i32 with
      positive and negative values, including two's-complement.
    * `predicate::tests::operand_pin_assertion_rejects_unsupported_types`
      — Bool, f32, usize/isize, gibberish all return None.
    * `visitor::tests::constant_operand_value_pinned_in_assumptions`
      — synthetic body for `fn add_one(x: u32) { x + 1u32 }`
      produces an obligation whose assumptions include
      `(assert (= rhs #x00000001))` but NOT `(= lhs ...)`
      (because lhs is `Copy(x)`, not a constant).
    * `visitor::tests::constant_operand_without_value_emits_no_pin`
      — synthetic body where both constants have
      `value: None` produces an obligation with no pinning
      assertions (negative space pinned so the adapter's
      extraction code can't silently regress).
    * `pitbull_vc::vc::tests::compile_with_const_pin_plus_precondition_combines_both`
      — the headline composition: an obligation with both a
      const-pin (`rhs=1`) AND a user precondition (`lhs<100`)
      compiles to SMT with both assertions appearing before
      the safety predicate. Z3 returns `unsat` on this text;
      the wrapper would report "discharged (unsat)".

  Z3 not installed on the developer's machine prevents an
  e2e smoke that confirms the actual `unsat` verdict
  end-to-end. The compose test pins the SMT text shape that
  Z3 will see; the path from there to a verdict is
  exercised by the existing `solver::tests::pinned_inputs_proves_no_overflow`
  (gracefully skips when Z3 absent).

  Remaining limitations:
    * The pinning fires ONLY for `Operand::Constant` with a
      successfully-extracted value. `Operand::Copy/Move` of
      a place that happens to come from a literal (`let y =
      1; x + y`) still won't pin — needs data-flow analysis
      to track the chain. Documented for v0.3.
    * `usize` and `isize` remain unsupported in
      `int_type_info` (pending the pitbull.toml
      target-pointer-width threading from PB052).
    * `u128` values that wrap to negative `i128` round-trip
      bit-exactly in the SMT encoding but the test coverage
      doesn't include u128 specifically.
- ✅ Audit cleanup #6 (final residuals). Closes M-4/M-5/M-6/M-7/M-8
  from a third audit pass: PSS-1.md entries for the four
  follow-up cleanup commits, stale "49 + 1 ignored" baseline
  updated to current "120 passing, 0 ignored",
  `pitbull.toml.example` documents F1/F2/F3 behavior changes,
  visitor module-doc updated to reflect that PB001's HIR
  pre-pass and PB043's VC obligation emission are live (not
  future). Removed dead `pub fn vc_obligation` method
  (replaced by direct field push within the visitor since the
  emission helpers were inlined). Added two new regression
  tests: `dispatch_refuses_contradictory_preconditions` (F1
  REFUSED path) and `wrapper_exits_nonzero_on_violation` (F10
  exit code policy). The F7 macro-filter regression test is
  documented as remaining work (requires a real-nightly e2e
  fixture).
- ✅ Audit cleanup #5: F7 + F8 + F10 (red-team finding cluster).
  HIR pre-pass now skips macro-expanded `unsafe` blocks via
  `Span::from_expansion()` — `vec![1,2,3]`, `format!()`,
  `println!()` no longer trigger PB001 false positives.
  `pitbull-driver` (both `main.rs` and `bin/pitbull-rustc.rs`)
  gets `#![forbid(unsafe_code)]` for defense in depth — every
  TCB crate root now refuses unsafe at the language level.
  Wrapper exit code now reflects Pitbull's findings: `rustc_exit_code.max(pitbull_exit_code)`
  where pitbull_exit_code is 1 if violations > 0 OR
  undischarged obligations > 0. `dispatch_vc_obligations` now
  returns the undischarged count for the caller to fold.
- ✅ Audit cleanup #4: F3 + H-1/H-2/H-3 + specific audit
  messages for translation failures. `legal_range_i128`
  special-cases `(true, 128)` to return `(i128::MIN, i128::MAX)`
  — the off-by-one overflow on `1i128.checked_shl(127)` is
  closed. The classifier `is_panic_call_path` adds
  `core::panic_any` and `std::panic_any` (top-level panic API
  that isn't under `panicking::*`). PB007 transmute arm adds
  `core::intrinsics::transmute_unchecked` and the `std::*`
  re-export. PB011 alloc arm adds `core::alloc::Allocator::*`
  and `std::alloc::Allocator::*` prefixes for trait-method
  allocator calls. The visitor's precondition processing
  restructured into three explicit outcomes with
  path-specific audit messages (predicate-parsed + bound +
  translated; predicate parsed + bound + translation failed
  with translator's error; predicate doesn't parse or doesn't
  bind, then raw-splice with lex validation).
- ✅ Audit cleanup #3: F1 (consistency-check guard against
  contradictory preconditions). CRITICAL soundness fix. A
  pitbull.toml precondition like `"(assert false)"` would
  otherwise make Z3 return `unsat` for any safety property,
  which the wrapper interprets as "discharged" — silently
  "verifying" unsafe code under vacuous truth. The fix runs a
  sat-check-only SMT problem (declarations + assumptions +
  `check-sat`, no safety predicate) BEFORE the main check.
  If the consistency check returns `Unsat`, the wrapper logs
  "REFUSED — preconditions are contradictory" and treats the
  obligation as undischarged. `VcGoal` gains
  `consistency_check: Option<String>` (None when no
  assumptions — trivially consistent, skip the extra solver
  call). Cost: one extra solver call per obligation with
  assumptions.
- ✅ Audit cleanup #2: F2 + F9 (assumption lex-validation +
  verdict-parser hardening). Both are CRITICAL soundness
  fixes from the second-pass red-team. F2: a maliciously
  crafted assumption could carry multiple SMT-LIB directives
  (`"(check-sat) (assert false)"`) that subvert the wrapper's
  verdict interpretation. The new `predicate::validate_assertion_form`
  function requires every raw assumption to be exactly one
  `(assert ...)` form with balanced parens, no string
  literals, no comments. Anything else is refused with an
  audit note rather than spliced verbatim. F9: defense in
  depth at the solver layer — the verdict parser now
  collects ALL verdict lines and refuses output with more
  than one verdict (returns `SolverResult::Error`). The
  wrapper's dispatch already maps `Error` to "undischarged",
  so a multi-verdict response cannot be silently misread.
- ✅ Audit cleanup after O.2 (Task O.2-cleanup). Three findings
  from a deep audit landed as a single commit:

  (1) PSS-1.md doc-drift — Tasks I, J, K, L, M had no §17.1 entries
      despite the code being live. Added.

  (2) PB043 silent-skip in default mode — `classify_called_function`
      did NOTHING when a panic call was found in default-acceptance
      mode (only acted in strict mode). The same anti-pattern Task I
      fixed for unclassifiable callees. Fix: default mode now emits
      a `VcObligationKind::PanicReachability` obligation; the
      wrapper's dispatch loop reports each as "pending" so the gap
      is visible in the VC summary rather than silently accepted.
      `pitbull_vc::compile` returns `None` for the kind today (the
      backend encoding lands later); once it arrives the visitor
      change requires no further code change.

  (3) Classifier path-match coverage — the call classifier matched
      `core::*` paths but not the `std::*` re-export forms rustc
      actually emits for std-using crates. Discovered during O.2
      audit smoke: `panic!("...")` resolves to `std::rt::panic_fmt`,
      not `core::panicking::*`. Fixed:
        - Panic: a new `is_panic_call_path` helper covers
          `core::panicking::*`, `std::panicking::*`, `core::panic`,
          `std::panic`, and the four std-runtime entry points
          (`std::rt::panic_fmt`, `std::rt::panic_display`,
          `std::rt::begin_panic`, `std::rt::begin_panic_fmt`).
        - Alloc (PB011): also matches `std::alloc::*`.
        - Transmute (PB007): also matches `std::mem::transmute`,
          `std::intrinsics::transmute`.
        - Volatile (PB025): also matches `std::ptr::*_volatile`.
        - Atomic (PB023): also matches `std::sync::atomic::*`.

      Same fix shape as the Box ADT path-normalization that landed
      in f8d4ed5. Now PB043 default obligations fire on real
      panicking code: `panic!("boom")` produces
      `pitbull-rustc: vc pb043-panic-0: pending (compilation not
      yet supported for PanicReachability)` rather than silently
      registering no diagnostic.

  (4) `clear_current_preconditions` was a dead-API: it was added
      in O.1 but only the test used it (the wrapper always passes
      a fresh `Vec` via `set_current_preconditions(unwrap_or_default())`).
      Removed; the test now uses `set_current_preconditions(vec![])`
      to express the empty-state intent.

  4 new tests pin these fixes: `is_panic_call_path_recognizes_known_entry_points`,
  `std_rt_panic_fmt_emits_panic_reachability_obligation`,
  `default_panic_call_via_std_re_export_emits_obligation`,
  `std_re_exports_match_for_all_classifier_rules`.
- ✅ Audit finding C2 fixed (Task I). The visitor's
  `classify_called_function` previously bundled `Some(_)` and
  `None` under the same fall-through arm — `None` (an unclassifiable
  callee, e.g. a non-FnDef const operand) was silently elided. The
  fix splits the arms; the `None` branch now records a new
  `AuditNote` (`pitbull_subset::diagnostic::AuditNote`) so the
  audit trail is visible without raising a violation. The wrapper
  prints notes alongside errors. Regression test:
  `visitor::tests::unclassifiable_callee_records_audit_note`.
- ✅ Audit finding H1 fixed (Task J). `pitbull-rustc` no longer
  silently falls back to `SubsetConfig::default_for_test()` when
  `PITBULL_TOML` is set but the file is missing or malformed; it
  exits 2 with a clear `config error: ...` message. Empty-config
  fallback (PITBULL_TOML unset AND `./pitbull.toml` absent) is
  preserved for ad-hoc smoke tests. Regression tests:
  `integration::malformed_pitbull_toml_hard_errors`,
  `integration::nonexistent_pitbull_toml_path_hard_errors`.
- ✅ Audit finding H3 fixed (Task K). Defense-in-depth path
  validation for env-supplied paths (`PITBULL_TOML`,
  `PITBULL_SARIF_OUT`). The new `check_env_path` helper refuses
  `..`-containing paths and paths whose extension isn't in the
  whitelist for that variable. Defeats build-script env injection
  (`cargo:rustc-env=PITBULL_TOML=$HOME/.ssh/id_rsa` leaking
  content via TOML parse errors;
  `cargo:rustc-env=PITBULL_SARIF_OUT=$HOME/.bashrc` overwriting a
  config file). `PITBULL_ALLOW_UNSAFE_PATHS=1` is the explicit
  opt-out for legitimate unconventional paths. Regression tests:
  `integration::pitbull_toml_with_nontoml_extension_refused` (the
  most important — asserts file content does NOT leak to stderr),
  `pitbull_toml_with_traversal_refused`,
  `pitbull_sarif_out_with_nonjson_extension_refused`.
- ✅ CI workflow (Task L). `.github/workflows/ci.yml` with two
  jobs matrix'd across Linux and Windows: `stable` runs
  `cargo +stable test --workspace --all-features` (corpus e2e
  tests gracefully skip without the nightly wrapper); `nightly-e2e`
  installs `nightly-2026-01-29` with `rustc-dev` + `rust-src`,
  builds the wrapper, then runs the suite with
  `PITBULL_REQUIRE_E2E=1` so the e2e corpus tests are forced
  rather than skipped. Concurrency group cancels in-progress runs
  on the same ref. Intentionally NOT gated (today): `cargo fmt
  --check` (source style is intentionally compact), `cargo clippy
  -D warnings` (60+ pre-existing warnings), and the mutation-testing
  harness (pending `cargo-mutants` integration).
- ✅ `pitbull-vc` crate scaffold (Task M). New workspace member
  holding the v0.2 deductive surface:
    * `vc::VcGoal { obligation, smt }` — compiled VC (typed
      obligation + SMT-LIB text).
    * `vc::compile` — turns a `VcObligation` into a `VcGoal`.
    * `smt::emit_overflow_problem_with_assumptions` — bit-vector
      QF_BV problem for the seven `bvXaddo`/`bvXsubo`/`bvXmulo`
      overflow predicates (signed + unsigned, u8..u128 + i8..i128).
    * `solver::invoke_z3` — pipes SMT-LIB to `z3 -in`, returns
      `SolverResult { Sat, Unsat, Unknown, NotInstalled, Timeout,
      Error(String) }`. `NotInstalled` is observably distinct so
      the wrapper degrades gracefully on developer machines
      without Z3.
    * Includes per-VC timeout via SMT-LIB `(set-option :timeout)`.
    * 13 unit tests covering parser, translator, and a live Z3
      round-trip that skips cleanly when Z3 isn't installed.
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
  rustc_hir; extern crate rustc_span;` and a `HirPreVisitor`
  (renamed from `UnsafeBlockVisitor` in Task O.3 to reflect that it
  now also extracts `#[pitbull::requires]` attributes)
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
- ✅ Predicate grammar `<ident> <cmp> <ident>` (Phase B). The v0.2
  grammar was `<ident> <cmp> <int>` only, forcing raw-SMT for
  `i < len`-shaped index preconditions. Phase B adds the
  ident-vs-ident form so `#[pitbull::requires("i < len")]` (PB054)
  parses and translates without raw SMT-LIB.
- ✅ `#[pitbull::trusted]` (Task Q.1). Marks a body so the visitor
  checks its signature but skips the MIR walk (FFI shims / opaque
  bodies). Trust does NOT admit `unsafe`: PB002/PB026 are
  signature-level and still fire. Q.1 also fixed a latent adapter
  soundness gap — `body()` hardcoded `is_unsafe`/`is_async = false`;
  the wrapper now extracts the real flags via `tcx.fn_sig().safety`
  and `tcx.asyncness()`, so PB002/PB026 fire on real MIR.
- ✅ Impl-method attribute extraction (Task Q.2). `visit_impl_item`
  extracts `requires`/`ensures`/`trusted` from `impl` methods, with
  a `visit_nested_impl_item` no-op override to prevent the
  nested-visit double-fire.
- ✅ Expression-form attributes (Task Q.3). `#[pitbull::requires(x < 100)]`
  (no quotes) is accepted by pretty-printing the attribute token
  tree via `rustc_ast_pretty::pprust::tts_to_string` and feeding it
  through the same predicate pipeline as the string-literal form.
- ✅ `#[pitbull::ensures("...")]` (Tasks Q.4 + Q.4a, rule PB076). The
  visitor emits a `VcObligationKind::EnsuresPostcondition` at every
  return (and fail-closed at the body span for divergent bodies);
  `result` binds the return value. **Q.4a DISCHARGES it via SMT** for
  single-block bodies returning a return-typed argument or an integer
  constant — asserting the captured body effect, the translatable
  preconditions (F1-guarded), and the negated postcondition (`unsat` ⇒
  holds; `sat` ⇒ counterexample). **Q.4b–Q.4d** add `Add`/`Sub`/`Mul`
  (wrapping `bvadd`/`bvsub`/`bvmul`, via the checked-add MIR), `Div`/`Rem`
  (`bvsdiv`/`bvudiv`/`bvsrem`/`bvurem`), and shifts (`bvshl`/`bvlshr`/
  `bvashr`), so `add_one`, `safe_div`, and `halve` discharge; bitwise ops
  and variable narrower-width shift amounts stay deferred. Anything
  uncapturable fails closed to "pending", never a false "verified".
  Verified adversarially: TRUE postconditions discharge (unsat), FALSE
  ones do not (sat), uncapturable stays pending — unit (exact-SMT) +
  Z3-gated e2e tests, plus an independent soundness review.
- ✅ Full-codebase audit sweep cleanup (post-Q). Closed three
  "no silent skip" gaps the foundational-code audit found:
  (a) Div/Rem/Shl/Shr produced no obligation AND no audit note;
  (b) the divergent-`ensures` exit-0 asymmetry (now fail-closed);
  (c) `[reachability] exclude` dropped items with no surfaced count
  when `verify_roots` was empty (now printed with a warning).
- ✅ Division / over-shift obligation encoding (Task R, 2026-05-28).
  Closes the (a) gap above: Div/Rem/Shl/Shr now emit real PB049
  `ArithmeticOverflow` obligations that discharge under Z3. The
  `pitbull-vc` violation predicate is per-op: Div/Rem assert
  division-by-zero `(= rhs 0)` plus (signed only) the `MIN / -1`
  overflow; Shl/Shr assert over-shift `(bvuge rhs <bit-width>)`.
  `fn d(a,b){a/b}` with `requires("b > 0")` reports `discharged
  (unsat)`; without it, `NOT DISCHARGED (sat — b = 0 witness)`.
  Mixed-width shifts (`u32 << u8`) cannot form a same-sort BV
  problem and surface an explicit "mixed-width shift" audit note
  (the over-shift encoding for those, via zero-extending the shift
  amount, is a tracked follow-up). e2e capstones:
  `wrapper_proves_division_safe_under_precondition` and
  `wrapper_division_without_precondition_not_discharged`.
- ✅ Multi-solver agreement gate (Task S, 2026-05-28). Discharge no
  longer trusts a single solver: `pitbull-vc::solver` gained a generic
  `Solver` descriptor (Z3 / CVC5 / Alt-Ergo, each with its own timeout
  convention), `run_solvers` (parallel pool), and a PURE
  `vote(results, threshold)` policy — any `sat` blocks discharge, a
  `sat`+`unsat` split is a loud `Disagreement` (fail closed),
  `threshold`+ `unsat` with zero `sat` discharges, else `Inconclusive`.
  `dispatch_vc_obligations` maps the verdict to diagnostics + exit code,
  and the consistency-check guard now refuses if ANY solver proves the
  preconditions contradictory. Default pool `[z3, cvc5]`, threshold 2;
  **Alt-Ergo is recognized but excluded by default** — Alt-Ergo ≤ 2.4.0
  has no bit-vector theory, so it can never discharge QF_BV. The policy
  is pinned by `vote()` unit tests; the e2e capstone
  `wrapper_two_solver_agreement_discharges_division` proves 2-of-2
  agreement (gated on both z3 and cvc5).
- ✅ Task S red-team hardening (2026-05-29). A 4-agent audit of the
  gate found and closed two CRITICAL soundness holes: (a) a
  consistency-check *fail-open* — `Timeout`/`Error`/`Unknown` on the
  precondition consistency check fell through to the main check, so a
  contradictory precondition that timed out could be discharged
  *vacuously*; now the wrapper requires `threshold` independent solvers
  to confirm the assumptions satisfiable (positive `sat` evidence)
  before trusting the main `unsat`, else it fails closed. (b)
  duplicate-solver *vote inflation* — `solvers=["z3","z3"]` ran one
  binary twice and counted its single `unsat` as two votes; now `vote`
  counts DISTINCT solver names and the driver dedups the pool (with a
  warning). Both verified closed across 7 fake-solver scenarios;
  regression-guarded by `vote_duplicate_solver_name_counts_once` and
  `vote_empty_results_is_inconclusive`.
- ✅ Unary-negation overflow obligation (program-wide audit,
  2026-05-29, CRITICAL fix). The visitor's `Rvalue::UnaryOp(_, _)` arm
  matched the operator with a `_` wildcard, silently swallowing
  `UnOp::Neg` — so `-(x)` on a signed integer emitted NO obligation,
  NO violation, and NO audit note, and `-(iN::MIN)` (a runtime panic)
  was reported "safe". Closed by: an exhaustive `UnOp` match in the
  visitor; a new `ArithOp::Neg` carried through the PB049
  `ArithmeticOverflow` machinery (single operand in the `lhs`
  position, precondition-bindable like the binary ops); and a
  `pitbull-vc` violation predicate `(= lhs iN::MIN)` (signed only —
  Rust has no unsigned unary `-`; unsigned fails closed to `None`).
  Verified e2e against fake solvers (`-x` discharges under `unsat`,
  refutes under `sat` with the MIN counterexample); pinned by
  `visitor::neg_signed_emits_arith_obligation_not_swallowed` and
  `smt::neg_emits_signed_min_overflow`. The other panic/UB-capable MIR
  operations (Add/Sub/Mul/Div/Rem/Shl/Shr, slice index, casts, panic
  calls) were re-audited and confirmed obligated or justifiably
  skipped; the SMT encodings (signed/unsigned overflow predicates,
  div MIN/-1, over-shift width, index bound) were confirmed sound.
- ✅ PB051 value-preserving-constant cast exemption (PB051-on-shift,
  2026-06-13). PB051 rejected EVERY `IntToInt` cast, which made shift
  code unverifiable: rustc lowers `x << 4` with a synthetic
  `const 4_i32 as u32` cast — the untyped `4` defaults to i32 and is
  cast to the value type SOLELY for the shift-overflow bounds check
  (the real `Shl` uses the original operand). The fix accepts an
  `IntToInt` cast of an integer CONSTANT whose value is representable in
  the target type: such a cast is value-preserving (no truncation, no
  sign-change), so PB051's "truncation needs an obligation" rationale
  does not apply and accepting it is sound. Gate:
  `predicate::value_fits_in_int_ty` (the value must round-trip through
  BOTH the source and target types, so the lone lossy-extraction case
  `u128` > `i128::MAX` fails closed) + `visitor::value_preserving_int_cast`.
  Every NON-constant cast (a variable read — including `let s = 4; x << s`)
  and every value-CHANGING constant cast (narrowing `300 as u8`, sign-flip
  `-1 as u32`, unsupported target `u128`/`usize`) still fails CLOSED.
  Accepted casts leave a transparency audit note — never a silent
  relaxation. Verified end-to-end on the real nightly wrapper: `x << 4` /
  `x >> 4` (signed + unsigned) / `x <<= 4` / `x << y` analyze with 0
  subset violations, while a genuine `x as u32` (u64→u32) narrowing still
  emits PB051. Pinned by
  `predicate::value_fits_in_int_ty_matches_two_complement_ranges`,
  `visitor::pb051_const_cast_value_preservation_matrix`, and
  `visitor::pb051_does_not_fire_on_real_shift_amount_cast`. SCOPE: this
  closes the subset REJECTION only. The over-shift DISCHARGE for a
  mixed-width `u32 << i32`-literal shift still routes to the pre-existing
  "mixed-width shift" audit note (tracked separately under Task R);
  same-type shifts (`i32 >> 4`, `u32 << y`) emit their PB049 over-shift
  obligation as before.
- ✅ CRITICAL fail-open fixed — a bridge failure could exit 0 "verified"
  (full-codebase audit 2026-06-14). In `pitbull-rustc`'s `after_analysis`,
  if `rustc_public::rustc_internal::run` returned `Err`, the error was
  only printed: the subset check never ran, the finding counters stayed
  at their `Default` 0, and a clean rustc compile then yielded
  `rustc_exit.max(0) == 0` — the process reported "verified" having
  performed NO analysis. Fix: a `bridge_failed` flag set in the `Err`
  arm forces a fail-closed exit 2 (analysis-could-not-run ranks above
  "verification failed"). The exit-code decision was extracted into a
  pure, lane-agnostic `decide_pitbull_exit_code` and pinned by four
  stable unit tests, incl. `bridge_failure_never_reports_verified`. The
  same 4-agent audit confirmed (and I re-verified) that the adapter
  type-mapping is compile-error-on-unknown (the `_ =>` arms forward to
  exhaustive sub-matches, never a silent benign map), the wrapper's
  `is_unsafe`/`is_async` override makes PB002/PB026 fire on real MIR,
  and the pitbull-vc discharge / agreement-gate / certificate paths are
  fail-closed — no other fail-open found. Doc-honesty cleanups: PB049
  overflow-checks config policy is now documented as NOT yet enforced
  (was mislabeled "checked by the driver"); the PB053 `char` comment no
  longer claims a char-arithmetic check that does not exist (and is not
  expressible in safe Rust).
- ✅ #27 reachability fail-open hardened — `verify_roots` narrowing no
  longer silently skips in-crate callees (2026-06-14). The wrapper walks
  `all_local_items()` filtered by `verify_roots`; on its own that skips a
  root's in-crate callees, so a root could be reported "verified" while a
  function it calls (holding, say, a `Box`) went unchecked — a fail-open
  under explicit narrowing. Now FAIL-CLOSED: the wrapper records every
  walked (non-trusted) body's direct callees (`reachability::callee_paths`)
  and, after the walk, flags any in-crate fn reachable from a verified root
  that was neither walked, `#[pitbull::trusted]`, nor `exclude`d
  (`reachability::unverified_reachable_callees`) — each forces exit 1.
  Applied every run, this transitively requires the whole reachable
  in-crate closure to be covered before a "verified" verdict is possible;
  the user resolves a flag by widening `verify_roots`, leaving it empty
  (full-crate coverage), or trusting the callee. The pure helpers live in
  `pitbull-subset::reachability` (stable unit tests for callee extraction +
  the flag set); the exit-code fold is pinned by
  `unverified_reachable_callee_fails_closed`; the end-to-end behavior by
  `verify_roots_fails_closed_on_unverified_in_crate_callee` (root calls a
  non-root Box-holding helper → `PB-reachability` diagnostic + exit 1).
  Honest-docs: `reachability.rs` now states the `ReachabilityDriver` BFS is
  a tested reference NOT yet wired to production; auto-walking the closure
  (vs. flagging) plus trait-dispatch / drop-glue edges remain the tracked
  follow-up.
- ✅ Coverage-gap audit + PB003 enforcement (2026-06-14). A
  defined-vs-enforced sweep of all 76 PSS-1 rules — each candidate probed
  empirically through the real wrapper — confirmed the CARDINAL AoRTE
  soundness is intact (no rule gap enables a false discharge in the
  verifiable subset) but found several rules SILENTLY accepted: the
  verifier reported "verified" for constructs the README lists as rejected
  — PB003 (`unsafe impl`/`unsafe trait`), PB016 (`Drop` impl), and
  PB056–PB058 (FFI: `extern` block / `#[no_mangle]` / non-Rust-ABI fn).
  The remaining unenforced rules are sound deferrals: TRANSITIVELY COVERED
  (PB014/PB017 heap-macros → PB011/PB012, verified via `format!`/`vec!`
  probes; PB038 virtual call → PB031 `dyn`), DOCUMENTED-DEFERRED
  (PB041/PB042 termination — already a known gap), ARCHITECTURALLY
  OUT-OF-SCOPE for the v0.2 MIR scaffold (spec-mode PB044/PB055/PB064–070,
  type-system PB034–037/PB040, build/const/cfg PB061–063, project-config),
  or NOT EXPRESSIBLE in safe Rust (PB053 char arithmetic).
  **PB003 is now ENFORCED:** the HIR pre-pass (which already finds PB001
  unsafe blocks) detects `unsafe trait` (`ItemKind::Trait` safety) and
  `unsafe impl` (`Impl::of_trait`→`TraitImplHeader::safety`), emits PB003,
  and fails closed (exit 1). Macro-expansion spans are skipped (same F7
  posture as PB001; a non-allowlisted macro emitting an unsafe impl is
  caught by PB059); safe traits/impls do not fire. The "N unsafe blocks"
  summary now counts PB001 only (PB003 joins the violation total). Pinned
  e2e by `unsafe_impl_and_trait_fire_pb003`. REMAINING (now tracked here,
  no longer silent): PB016 drop-site modeling and PB056–058 FFI surface —
  each carries a far-future `FuturePlan`, and none is an AoRTE
  false-discharge (a bad `unsafe Send` needs concurrency → PB028; a drop
  panic → the walked drop body → PB043; FFI calls are `unsafe` →
  PB001/PB002).
- ✅ FFI surface enforced (PB056/PB057/PB058) + PB016 reclassified
  (2026-06-14, follow-up to the coverage-gap audit). The HIR pre-pass now
  flags `extern` blocks (PB056, `ItemKind::ForeignMod`), non-Rust-ABI fn
  definitions (PB058, `FnHeader::abi.is_rustic_abi()` is false), and
  `#[no_mangle]`/`#[export_name]` (PB057, via `codegen_fn_attrs` — the
  `NO_MANGLE` flag or a `symbol_name`), each failing closed (exit 1).
  Macro-expansion spans are skipped (F7 posture); a normal Rust fn does not
  fire. Pinned e2e by `ffi_constructs_fire_pb056_pb057_pb058`. This closes
  the last expressible silent subset-membership gaps the coverage-gap audit
  found. PB016 (`Drop` impl) is deliberately NOT enforced as a syntactic
  reject — that would wrongly reject safe RAII; it is TRANSITIVELY COVERED
  for AoRTE: the drop method body is walked, so a panicking drop fires
  PB043 (verified: `impl Drop { fn drop(&mut self){ panic!() } }` → pending
  PB043 → exit 1) and a panic-free drop is genuinely safe. The only
  residual is a panicking drop reached ONLY via implicit drop-glue under
  `verify_roots` narrowing — the #27 drop-glue follow-up (`callee_paths`
  tracks `Call`, not `Drop`, terminators); with the default empty
  `verify_roots` (full-crate walk) every drop body is walked.
- ✅ #25 mixed-width over-shift discharge + fail-open fix (2026-06-14). A
  shift whose amount type differs from the value type (`x: u32 << 4` — the
  literal `4` is i32; or `x: u32 << y: u8`) previously emitted ONLY an audit
  note and NO obligation, so the over-shift went unchecked and the wrapper
  exited 0 ("verified") even for an over-shifting amount — a latent
  FAIL-OPEN (verified empirically). Now a mixed-width shift emits the
  over-shift obligation at the VALUE width. Rust's over-shift check is
  `(amount as V) >= bits_of(V)` (unsigned, value width — confirmed against
  real MIR), so the amount is constrained ONLY when modelling it at V is
  exact: a CONSTANT amount whose value FITS V is pinned to `(amount as V)`
  (so `x << 4` DISCHARGES with a solver; an over-shifting constant stays
  `sat`); otherwise (variable amount, or a constant that does NOT fit V and
  would truncate under the pin — e.g. `u8 << 256` → 0 — hiding a real
  over-shift) the amount is left FREE → `(bvuge rhs bits_V)` is `sat` → the
  obligation does NOT discharge → FAIL CLOSED (exit 1). This both closes the
  fail-open and adds discharge for the headline `x << N`. The soundness
  pivot — never pin a truncated value — reuses `predicate::value_fits_in_int_ty`
  (the PB051 gate). Pinned by
  `visitor::mixed_width_const_shift_pins_only_when_value_fits`,
  `visitor::mixed_width_variable_shift_emits_freed_obligation_fail_closed`,
  and e2e `mixed_width_const_shift_emits_obligation_not_silent_pass`.
  REMAINING (tracked): fully DISCHARGING a VARIABLE mixed-width amount under
  a precondition needs modelling the amount at its own width
  (zero/sign-extend) — today such a shift fails closed (undischarged)
  rather than discharging. Supersedes the Task R "mixed-width shift audit
  note" follow-up.
- ✅ Variable mixed-width shift discharge — safe subset (2026-06-14,
  follow-up to #25). The amount is modelled at the VALUE width V; a
  precondition now BINDS to it, but ONLY when that modelling is sound: the
  amount type must be UNSIGNED and no wider than V. Then the amount
  zero-extends into a free V-wide `rhs`, the precondition and the over-shift
  `(bvuge rhs bits_V)` both compare UNSIGNED at V, and zero-extension
  preserves unsigned comparisons against a fits-in-amount literal — so
  proving `precond ⟹ rhs < bits_V` for ALL V-wide `rhs` implies it for the
  narrower real amount. Hence `x: u32 << y: u8` + `requires(y < 32)` now
  DISCHARGES (verified e2e: the obligation gains `[1 assumption]`). A SIGNED
  amount (a negative value over-shifts yet satisfies a signed `< bits_V`
  bound) or a WIDER amount (truncating to V hides high bits) is NOT bound →
  free `rhs` → fail closed (verified: `u32 << y: i8` carries no assumption).
  No SMT-encoder change — the soundness lives entirely in the visitor's
  bind-only-when-sound gate (`int_type_info`-checked). Pinned by
  `visitor::mixed_width_variable_shift_binds_precondition_only_when_sound`
  and e2e `mixed_width_unsigned_amount_binds_precondition`. REMAINING: the
  signed / wider-amount cases need modelling the amount at its OWN width
  (zero/sign-extend + its own declaration); today they fail closed.
- ✅ #27 drop-glue residual closed (2026-06-14). The #27 reachability check
  tracked `Call` terminators only, so a `Drop::drop` reached via IMPLICIT
  drop-glue (a `Drop` terminator) under `verify_roots` narrowing could go
  unwalked AND unflagged — a (possibly panicking) drop slipping through to
  exit 0. Now every LOCAL `Drop` impl method (identified via its parent
  impl's trait ref == the `Drop` lang item — `trait_of_assoc` does NOT
  resolve impl methods, so the impl's `impl_opt_trait_ref` is used, guarded
  by a `DefKind::Impl { of_trait: true }` check) is added to the
  reachable-callee set, so narrowing that leaves it unwalked is flagged
  fail-closed (exit 1). Conservative (a local Drop impl is treated as
  reachable even if no walked root provably drops that type) but sound, and
  Drop impls are rare; the default empty-`verify_roots` (full-crate) walk
  verifies every drop body unchanged. Verified e2e: a root dropping a
  custom-`Drop` value under `verify_roots=[root]` flags
  `<D as Drop>::drop` and exits 1 (was exit 0). Pinned by
  `drop_glue_under_narrowing_fails_closed`. This was the last
  fail-closed-under-narrowing residual from #27.
- ✅ Adapter accept-on-unknown closed (2026-06-14). The rustc_public adapter
  maps real `RigidTy` variants with no shadow analog (`Foreign`,
  `CoroutineWitness`, a `Dynamic` reaching `rigid_ty`, `Never`, and the
  non-rigid inner of a pattern type via `rigid_ty_of`) to synthetic
  `__pitbull_*` placeholder ADTs. `classify_adt`'s final arm ACCEPTS any
  unclassified path (correct for real user/stdlib ADTs), so these synthetics
  were silently accepted — a latent fail-OPEN: an unanalyzable or
  already-forbidden construct reported "verified" because the visitor didn't
  recognize it. `classify_adt` now classifies the `__pitbull_*` namespace
  EXPLICITLY and fails closed by default: `__pitbull_never` (the uninhabited
  `!`) stays accepted (rejecting would false-positive on safe diverging code);
  `dyn_trait_fallback`→PB031, `coroutine_witness`→PB027, `foreign`→PB056,
  `unrigid`→PB039; and an UNKNOWN future synthetic also rejects (PB039) via the
  catch-all, so a new adapter placeholder can never silently reopen the hole.
  The bare single-segment `__pitbull_*` path is unconstructable from Rust
  source (a real type path is always `crate::…`), so no real type is affected.
  Pinned by 7 stable visitor tests (`synthetic_*`); the same audit restored the
  clippy-error-clean invariant (a drifted collapsible-`if let` in
  `reachability.rs::callee_paths`).
- ✅ Panic-bearing library calls caught (2026-06-14, reachability-integrity —
  a CRITICAL false-discharge on ubiquitous code). `Option`/`Result`'s
  `unwrap` / `expect` / `unwrap_err` / `expect_err` panic on the wrong
  variant, but that panic lives INSIDE the library fn (in `core`), which the
  v0.2 wrapper does not walk (only `all_local_items()`) and has no prelude
  model for. So the call lowered to `Call(core::option::Option::<T>::unwrap,
  …)` fell through `classify_called_function`'s `Some(_)` "assume the callee
  is walked elsewhere" arm — but the reachability driver that *would* have
  walked it transitively is the dead `#[cfg(test)]` reference, never the
  production path. Net effect: `fn f(x: Option<u32>) -> u32 { x.unwrap() }`
  was reported **verified** (exit 0) despite panicking on `None`, directly
  violating the README's "No reachable `panic!`, `unwrap`, `expect`"
  guarantee. Fix: `is_panicking_library_call` recognizes these combinators
  at the call site (anchored on the `option::Option` / `result::Result` type
  qualifier + panicking method name, robust to post-mono generic args and the
  `std::` re-export form; the non-panicking `unwrap_or*` family is excluded),
  and routes them through the SAME PB043 handling as `panic!` — strict mode
  rejects, default mode emits a pending `PanicReachability` obligation (the
  honest "cannot prove this won't panic", undischarged → fail closed). Verified
  end-to-end: 4 stable unit tests (classification, default-obligation,
  strict-reject, the `unwrap_or` negative) plus a new corpus reject file
  `reject/PB043_unwrap_panic.rs` that the nightly wrapper surfaces as `(PB043)`
  on REAL rustc MIR. The `Some(_)` arm comment and `callee_paths` doc were
  corrected to state the real analyzed-vs-trusted boundary (now in
  `SAFETY-MANUAL.md` §3.6) instead of the stale "reachability driver walks the
  callee" claim. RESIDUAL (documented, not closed): other panicking stdlib
  functions remain on the trusted side pending the prelude; cross-crate
  closure coverage is now aggregated (next entry).
- ✅ Cross-crate reachability aggregation (2026-06-14). The per-crate `#27`
  gate's universe is the LOCAL crate only, so a verified root in crate A
  calling into workspace crate B — whose own `verify_roots` narrowing
  skipped that entry — slipped past both crates' local gates (a cross-crate
  false-"verified"). Closed by a whole-workspace gate: each `pitbull-rustc`
  run emits a reachability manifest (its walked / referenced / trusted
  paths) into `PITBULL_REACH_DIR`, and `cargo pitbull check` aggregates them
  after the build — `reachability::cross_crate_unverified` flags any
  workspace-member callee referenced from a verified root that NO crate's
  run walked or trusted (exit 1). The pure aggregation is stable-unit-tested
  (6 tests incl. the trusted opt-out, the external-callee trusted boundary,
  and a warm-cache INDETERMINATE case that avoids false positives when cargo
  serves a crate from cache); manifest emission is smoke-verified on real
  MIR (walked/referenced path formats match — the gate's key invariant).
  Workspace membership comes from `cargo metadata`; registry/non-workspace
  deps stay trusted. RESIDUAL: a full multi-crate-narrowing e2e fixture, and
  forcing complete re-analysis on warm caches (today: INDETERMINATE note +
  "run a clean build").
- ✅ Coverage-gap audit notes folded into the exit code (M1, 2026-06-14).
  `decide_pitbull_exit_code` ignored audit notes, so a safety check the
  visitor could not run with NO compensating obligation — an unmodelable
  `p.0 + p.1`, a unary-negation skip, an unclassifiable callee — emitted a
  stderr note but exited 0 ("verified"). That is a silent skip *w.r.t. the
  CI gate*, against the project's "no silent skips" posture. Fixed by typing
  each note: `AuditNoteKind::{CoverageGap, Transparency}` (serde-defaulting
  to CoverageGap — fail closed on legacy notes). The visitor's `audit_note`
  helper now defaults to CoverageGap; the 8 sites where an obligation is
  emitted alongside (so the exit code already reflects it) or the check ran
  safe (value-preserving cast, trusted/divergent/pending ensures, refused
  preconditions) were moved to a new `audit_transparency`. The wrapper folds
  `report.coverage_gap_count()` into the exit code (exit 1) gated on
  `[verification] fail_on_coverage_gaps` (default true; set false to keep
  gaps as non-blocking notes). 4 visitor sites stay CoverageGap (callee
  unclassified, two PB049 binop skips, neg skip). Pinned by +5 subset tests
  (kind filter, fail-closed serde default, gap-site tagged CoverageGap,
  divergent-ensures tagged Transparency, clean-body zero gaps) and +2
  exit-code tests (gap fails closed by default; opt-out doesn't fail);
  corpus accept files still pass under the fail-closed default.
- ✅ Deep-audit self-review fixes (2026-06-14) — a 3-agent adversarial review
  of this session's own commits, each finding verified against the source
  before acting. Two issues fixed:
  (1) **Cross-crate gate false-positive (a regression in 4861ebf)** — the
  aggregation keyed on rendered path STRINGS, but `item.name()` renders a
  trait-impl method as `<crate::S as crate::T>::m` (walked) while the CALL
  references the trait path `crate::T::m` (referenced) — verified empirically
  against real MIR. So ANY crate using trait methods would have its trait
  call false-flagged as an unverified workspace callee → spurious exit 1
  breaking clean builds. Fixed by mirroring the proven `#27` gate: the
  manifest now carries `universe` (the in-crate fn items), and a callee is
  hard-flagged only if it is a member of SOME crate's universe (an actual
  walkable item) — a trait-path call, never a walkable item, is correctly
  ignored. `crate_of_path` is now robust to the `<.. as ..>` form (a naive
  first-`::` split yielded `<crate`, a separate fail-open the agent found).
  Pinned by a `cross_crate_unverified_ignores_trait_method_call_path`
  regression test built from the empirically-observed manifest shape, and
  e2e-reconfirmed.
  (2) **Method-form integer overflow silently accepted** — the agent noted
  the unwrap fix's same un-walked-`core` mechanism left `x.pow(y)` (and
  `abs`/`div_euclid`/…) reporting `verified` with NO obligation, while the
  operator form `x * y` is PB049 and the README claimed "no overflow"
  unconditionally. `is_panicking_int_method` now catches the panicking
  primitive-int inherent methods (`pow`/`abs`/`div_euclid`/`rem_euclid`/
  `next_power_of_two`/`ilog*`, excluding the `checked_/wrapping_/
  overflowing_/saturating_/unsigned_` families) and routes them through the
  same fail-closed PB043 handling; verified e2e (`x.pow(y)` now emits
  `pb043-panic-0 (PB043): pending` → exit 1). README + SAFETY-MANUAL §3.6
  updated to scope the AoRTE claim honestly and list the remaining trusted
  library-panic residual (`str` range/byte index, `<[T]>::split_at`) as a
  documented gap, not a silent pass.
- ✅ Library-panic residual closed: range-index + split_at/chunks
  (tracked-residual closure, 2026-06-14). The deep audit's documented
  residual — `str`/slice RANGE indexing and the panicking slice split/chunk
  methods — is now caught at the call site (no longer trusted). Verified
  empirically: `&s[a..b]` / `&v[a..b]` does NOT lower to a
  `ProjectionElem::Index` (only element `v[i]` does, which is PB054); it
  lowers to a `Call` to `core::ops::Index::index`, whose out-of-bounds panic
  lives in un-walked `core`. `is_panicking_index_or_slice_call` now matches
  `ops::Index::index` / `ops::IndexMut::index_mut` plus the panicking
  `core::slice::<impl [T]>` methods (`split_at`/`split_at_mut`/`chunks`/
  `chunks_exact`/`rchunks`/`windows`), routing them through the same
  fail-closed PB043 handling. Element-projection indexing (`a[i]`, PB054)
  and the non-panicking slice methods (`len`/`iter`/`first`/…) are correctly
  NOT matched (verified e2e + 2 unit tests; the `bytes[i]` accept-corpus
  file is unaffected since it is a projection). README + SAFETY-MANUAL §3.6
  updated to move these from "trusted residual" to "caught". Remaining
  residual is now just less-common panicking library methods not yet
  enumerated.
- ✅ Empirical AoRTE soundness net — property-test harness (2026-06-14,
  first increment of the Safety Manual §3.2 "fuzzed-inputs" promise).
  `tests/aorte_proofs.rs` is a stable, dependency-free (deterministic
  xorshift PRNG, reproducible) net that hammers AoRTE-relevant functions
  with 200k fuzzed inputs each and asserts none ever panics — the empirical
  counterpart to the static discharge logic (it catches the exact
  false-discharge class the deep audit found in `unwrap`/`pow` by *reasoning*).
  Two kinds of proof: (1) UNCONDITIONAL AoRTE proofs safe on every input —
  bitwise CRC-32 and CRC-16/CCITT-FALSE (with the canonical `0xCBF43926` /
  `0x29B1` known-answers), in-place insertion sort (oracle: matches `std`'s
  sort ⇒ sorted + a permutation), a fixed-point Q16.16 PID step (all-total
  saturating / wrapping / clamp / shift ops; oracle: zero gains ⇒ 0),
  branchless median-of-three (oracle: the middle of the sorted triple), a
  guarded binary search (oracle: agrees with linear scan), and power-of-two
  ring-buffer addressing (oracle: always in capacity) — the positive proofs
  PSS-1 §15 names; (2) PRECONDITION-RESPECTING proofs that
  fuzz ONLY the admitted domain of Pitbull's discharged shapes — `at(s,i)`
  under `i < len` (PB054) and `add_one(x)` under `x < 100` (PB049) — a
  direct empirical check that each discharged precondition is SUFFICIENT for
  safety. A control test confirms the net has teeth: `add_one(u32::MAX)`
  (the precondition dropped) DOES overflow-panic under `overflow-checks`, so
  a discharge resting on an insufficient precondition would be caught. 10
  tests.
- ✅ End-to-end AoRTE differential wired (2026-06-14). Closes the loop: the
  `pitbull-rustc` wrapper's STATIC verdict (its exit code — 0 only with zero
  violations / undischarged / coverage-gaps) now gates the EMPIRICAL fuzz
  programmatically in `integration.rs`, so a false discharge fails the suite.
  Four probes: (1) the STRONG claim exercisable WITHOUT a solver — `mix`
  (wrapping ops, no indexing) emits ZERO obligations so the wrapper exits 0
  on its own, and 100k fuzzed `(a,b)` pairs must be panic-free (`verified ⟹
  fuzz-clean`, asserted directly); (2) a NEGATIVE control — unconstrained
  `x + 1` must NOT be verified (it can overflow) AND the full-range fuzz
  finds the overflow, pinning that Pitbull doesn't falsely-discharge a
  genuinely-unsafe fn; (3) solver-gated — `add_one` under
  `#[pitbull::requires("x < 100")]` discharges with a solver (then the
  admitted-domain fuzz must be clean), and on a solverless host confirms the
  empirical side + notes the SMT claim couldn't be exercised; (4) a SECOND
  zero-obligation witness in a DIFFERENT trusted-total call family —
  `median3` (only `Ord::min`/`max`; no arithmetic, indexing, `as` casts, or
  loops) verifies on its own (exit 0, empirically confirmed), then 100k
  fuzzed triples must be panic-free AND equal the sorted middle (a
  correctness oracle `mix` lacks). 4 tests (gated on the nightly wrapper like
  the corpus e2e). NEXT: the remaining §15 proof (the MAC-frame parser); and
  the Miri / Tree-Borrows pass for UB (not just panics).
- ✅ CRITICAL false-discharge fix: panicking slice/str methods (deep audit,
  2026-06-14). A 4-agent adversarial re-audit of the whole codebase
  (verified against real MIR) PROVED a false discharge: `<[T]>::swap`,
  `rotate_left`/`rotate_right`, `copy_from_slice`/`clone_from_slice`,
  `copy_within`, `swap_with_slice`, `select_nth_unstable*` panic at runtime
  (OOB / `mid > len` / length mismatch) but the wrapper reported exit 0
  ("verified") with ZERO obligations — `is_panicking_index_or_slice_call`'s
  suffix list was under-inclusive (`split_at`/`chunks`/`windows` were caught,
  their siblings were not), and the `slice::<impl` anchor missed `str`
  methods entirely. Fixed: the matcher now enumerates the COMPLETE stable
  panicking `[T]`/`str` inherent API and anchors on `::slice::<impl` /
  `::str::<impl` (the leading `::` excludes `c_str::<impl`/CStr). The same
  audit added the iterator-fold overflow `Iterator::{sum, product}` (same
  class as `pow`) and hardened `crate_of_path` to peel ALL leading `<`
  (`<<A as T1>::Assoc as T2>::m` → `A`'s crate, not the fail-open `<crate`).
  Verified e2e: `dst.copy_from_slice(src)` now emits PB043 → exit 1 (was
  exit 0). Pinned by extended classification + obligation-emission unit
  tests and a new corpus reject file `reject/PB043_slice_panic.rs`. The
  re-audit ALSO disproved a flagged "cross-crate generic fail-open" — the
  manifest's `referenced` and `universe` use the SAME generic-item path
  format (empirically `corpus_test::generic_fn`, no `::<u32>` args), so the
  universe-filter does not miss generic cross-crate callees.
- ✅ CRITICAL false-discharge fix #2: panicking integer methods + iterator
  adapters (deep audit 2026-06-14 **#2**). Adding the `median3` §15 proof
  (which verifies via the trusted `Ord::min`/`max` boundary) prompted a
  follow-on sweep of that boundary, which PROVED a whole CLASS of false
  discharges `is_panicking_int_method` had missed — every one confirmed
  panic-bearing AND stable on the pinned nightly, every one reported
  `verified` (exit 0): SIGNED `isqrt` (`self < 0`), `next_multiple_of` and
  `div_ceil` (zero rhs / overflow), the ALWAYS-panicking `strict_*` family
  (`strict_add`/`sub`/`mul`/`div`/`rem`/`neg`/`pow`/`shl`/`shr`/… — panic on
  overflow regardless of the `overflow-checks` profile), and
  `Iterator::step_by(0)` (panics at construction). The prior revision of the
  matcher's own doc-comment even rationalised `isqrt` as "correctly excluded"
  — true only for the UNSIGNED impls, since signed `isqrt` panics on a
  negative receiver. The matcher now enumerates these and discriminates
  `isqrt` by signedness (matched only for `<impl i…>`, so total `u32::isqrt`
  is not a false REJECT), routing each through the same fail-closed PB043
  handling. Verified e2e: each panicking form emits PB043 → exit 1 (was exit
  0), while `u32::isqrt`/`midpoint`/`wrapping_add`/`median3` stay verified
  (exit 0). Pinned by extended classification + obligation-emission unit
  tests, a ground-truth panic control in `tests/aorte_proofs.rs`, and new
  corpus files `reject/PB043_int_method_panic.rs` +
  `accept/PB043_int_method_total.rs`. The SAME sweep also caught
  `i*::from_str_radix` (panics on `radix ∉ 2..=36`; folded into
  `is_panicking_int_method`) and the `char` radix methods `to_digit` /
  `is_digit` / `from_digit` (same radix panic — the check precedes the
  `Option` return), which get a fourth call-site matcher
  `is_panicking_char_method` wired into `classify_called_function` alongside
  the unwrap/int/slice families; verified e2e (exit 1), with safe radix-free
  `char` methods staying verified, and pinned by `reject/PB043_char_radix_
  panic.rs` + `accept/PB043_char_radix_total.rs`. **Process note:** these two
  false-discharge classes were found by *exercising the trusted-library
  boundary* (the `median3` proof routed through `Ord::min`/`max`), which is
  why the soundness posture must treat that boundary as fail-OPEN until a
  prelude allow-list inverts it (§3.4) — each newly-reached panicking method
  is a latent false discharge until enumerated.
**Known limitations of the current scaffold:**
- Nightly + opt-in `cargo test` fails to link (`rlib format` errors for
  rustc internals like `rustc_data_structures`, `rustc_index`). This is
  a known `rustc_private` mechanism limitation; tools like Kani and
  Creusot solve it by running tests inside `rustc_driver` callbacks
  rather than as standalone test binaries. The pitbull-subset crate's
  unit tests work fine on stable Rust (post-audit-cleanup baseline:
  323 passing, 0 ignored — was 49 + 1 ignored in the v0.1
  baseline; the surge tracks the v0.2 deductive-backend, HIR
  pre-pass, PB054 P / P.1 / P.2 work, the N3 + H-RT post-interruption
  red-team cleanup, the Q-series Option C expansion (Phase B
  ident-vs-ident predicate grammar, Q.1 `#[pitbull::trusted]` +
  adapter is_unsafe/is_async fix, Q.2 impl-method attribute
  extraction, Q.3 expression-form attributes, Q.4 `#[pitbull::ensures]`
  MVP), and the full-codebase-sweep cleanup closing div/rem/shift
  silent-skips, the divergent-ensures fail-closed asymmetry, and
  exclude-count visibility). The driver-side test harness is the
  right home for tests that exercise the adapter against real MIR.
**Verification today:**
```bash
# Stable: 323 passing, 0 warnings, clippy clean
cargo +stable test --workspace --all-features
cargo +stable clippy --workspace --all-features --all-targets
# Nightly + opt-in: wrapper builds + lints, end-to-end PB049/PB054
# discharge through the multi-solver gate (graceful skip when no
# solver is on PATH).
PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 clippy -p pitbull-driver --bin pitbull-rustc
PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc
PITBULL_REQUIRE_E2E=1 cargo +stable test --workspace --all-features -- --test-threads=1
```
Future-roadmap detail lives in `docs/HANDOFF.md`; multi-solver
agreement shipped (Task S) and **proof certificates + `replay`** have a
working MVP (Task T.1 + T.2 — emission to `PITBULL_CERT_OUT` and
`cargo pitbull replay`). The next strategic directions are
certificate **signing** (T.3) and the v0.3 path-sensitive
panic-reachability backend.
