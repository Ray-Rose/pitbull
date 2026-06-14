# Pitbull v0.1 Safety Manual (Draft)
**Status:** Draft for v0.1; companion to PSS-1.
**Audience:** Users deploying Pitbull, safety assessors, qualification reviewers.
This document is the *contract* between Pitbull and its users. It
states, in normative terms, what Pitbull v0.1 guarantees, what it does
not, what the Trusted Computing Base is, and what obligations a user
must meet for the guarantees to hold.
A safety manual is not a marketing document. Where the manual seems
under-promising relative to what a marketing summary would say,
believe the manual.
## 1. The guarantee
For any function annotated `#[pitbull::verify]` whose body and
transitive reachable callees:
1. satisfy the Pitbull Verifiable Subset (PSS-1, see `docs/PSS-1.md`);
2. were compiled by a Pitbull-pinned toolchain pair
   (`SUPPORTED_TOOLCHAINS` constant in `pitbull-subset/src/config.rs`);
3. contain no unsound `#[pitbull::trusted]` annotations relative to
   their actual implementations;
Pitbull guarantees, with respect to the **Absence of Runtime Errors
(AoRTE)**, that the resulting binary will not, on any input,
exhibit:
- A reachable panic from `panic!`, `unwrap`, `expect`,
  `unreachable!`, or any function in `core::panicking::*`.
- An integer arithmetic overflow under `overflow-checks = true`
  semantics.
- An out-of-bounds slice or array index.
- A division or modulo by zero.
- A construction of an invalid primitive value (e.g. `bool` from
  arbitrary bits).
The guarantee covers every machine state the program enters under
the verified semantics of safe Rust.
## 2. What Pitbull v0.1 does NOT guarantee
Pitbull v0.1 is intentionally narrow. The following are out of scope:
- **Functional correctness** beyond AoRTE: that the program produces
  the *intended* output (only that no failure mode listed in §1
  occurs). For functional correctness, users write postconditions
  via `#[pitbull::ensures]`, which are checked but are not part of
  the AoRTE guarantee.
- **Timing properties.** Pitbull says nothing about WCET, deadlines,
  or interrupt latencies.
- **Side-channel resistance.** Timing channels, power channels,
  cache channels are out of scope.
- **Non-interference and information flow.** No taint analysis is
  performed.
- **Hardware fault tolerance.** Bit flips, voltage glitches, and
  similar physical faults are not modeled.
- **Compiler correctness.** Pitbull does not re-verify the compiler
  beneath it. The compiler's correctness is asserted by Ferrocene
  qualification, which is a separate artifact.
- **`unsafe` code.** Pitbull v0.1 refuses to verify code containing
  `unsafe`. There is no claim about `unsafe` code's behavior.
## 3. Trusted Computing Base
A bug in any of the following invalidates Pitbull's guarantee. Each
item names the responsible upstream party.
### 3.1 The compiler
- **Ferrocene** (compiler distribution and qualification).
- **LLVM** (code generation).
- **rustc** (source-to-MIR lowering, monomorphization,
  borrow-checking, drop elaboration).
Pitbull does not validate the compiler's correctness. Users running
Pitbull outside the Ferrocene-pinned configuration void the
guarantee.
### 3.2 The Pitbull pipeline
- **`pitbull-subset`** (this crate): the PSS-1 enforcer.
- **`pitbull-translate`** (v0.2+): the MIR→Coma translator (forked
  from Creusot).
- **`pitbull-vc`** (v0.2+): VC generation.
- **`pitbull-driver`**: orchestration.
A bug in any of these is a soundness bug. Defenses:
- Mutation testing at 100% kill rate (CI gate).
- Multi-solver agreement (2-of-3 default; configurable).
- Proof-certificate replay against current solver binaries
  (catches solver-bug-dependent proofs).
- Miri cross-validation under Tree Borrows on fuzzed inputs (v0.2+).
- Differential testing against Kani (v0.2+).
### 3.3 The proof tooling
- **Why3** (verification platform).
- **Z3, CVC5, Alt-Ergo** (SMT solvers).
A solver soundness bug can produce a false "verified" result. The
2-of-3 agreement requirement, combined with proof-certificate replay,
substantially mitigates this. As of May 2026, cumulative testing
campaigns have found 1,500+ unique bugs in Z3 and CVC5, including 400+
soundness bugs. Users requiring the highest assurance should:
- Set `verification.solver_agreement = 3`.
- Set `reporting.strict_replay = true`.
- Enable the (future) Coq/Lean back-check for prelude axioms.
### 3.4 The prelude
The Pitbull prelude axiomatizes a small subset of `core` (integer
operations, `Option`, `Result`, slice indexing). The prelude's
axioms are part of the TCB; their consistency is checked offline
against Coq/Lean (v0.2+).
### 3.5 The user-supplied spec
- `#[pitbull::trusted]` items are user assertions. The justification
  attribute is required (PB067) and the trust budget is bounded
  (PB068), but neither makes a wrong trusted spec correct.
- `#[pitbull::requires]` clauses bind callers. A wrong precondition
  silently weakens the proof's claim.
### 3.6 The reachability / analyzed-vs-trusted boundary
The AoRTE guarantee (§1) covers every item **reachable from a verified
entry point**. What the v0.2 scaffold actually *analyzes* versus what it
*trusts* is a TCB boundary users must understand:
- **Analyzed.** Every item of the **crate currently being compiled**
  through the `pitbull-rustc` wrapper. With an empty
  `[reachability] verify_roots` the whole crate is walked
  (over-approximating, fail-safe). With a non-empty `verify_roots`, the
  walk is narrowed to the roots, and the fail-closed `#27` gate then
  forces the entire **in-crate direct-call closure** of those roots to be
  covered or the run exits non-zero. Indirect dispatch
  (`dyn`/fn-ptr/closure) inside any walked body is a hard subset
  rejection (PB031/PB032/PB033), so it cannot route reachable code around
  the walk (see `reachability.rs::callee_paths` for the soundness
  argument). Local `Drop::drop` impls are injected into the gate so
  implicit drop glue is covered too.
- **Trusted, NOT analyzed.** Code in **other crates** —
  `core`/`std`/`alloc`, registry dependencies, and any crate not compiled
  through the wrapper (`RUSTC_WORKSPACE_WRAPPER` wraps workspace members,
  not registry deps). These are assumed **total** (panic-free, AoRTE-safe)
  exactly as SPARK trusts its runtime. Precisely modelling the standard
  library is the **prelude's** job (§3.4), which is future work.
  - **Exception — common panic-bearing stdlib calls are caught, not
    trusted.** Calls whose panic is invisible at the call site (the panic
    lives in un-walked `core`) are recognized by the visitor and produce a
    PB043 obligation (or a hard reject under `strict_panic_acceptance`), so
    they are reported as an unproven panic, never silently "verified"
    (reachability-integrity audit, 2026-06-14). Caught today:
    - `Option`/`Result::{unwrap, expect, unwrap_err, expect_err}`;
    - the panicking primitive-int inherent methods `pow` / `abs` /
      `div_euclid` / `rem_euclid` / `next_power_of_two` / `ilog`/`ilog2`/
      `ilog10` (the METHOD form of overflow — the OPERATOR form `x * y` is
      already PB049); and
    - `str`/slice RANGE indexing `&s[a..b]` / `&v[a..b]` (which lowers to a
      `core::ops::Index::index` `Call`, NOT a `ProjectionElem::Index`, so
      PB054 does not see it — only element `v[i]` is a projection) plus the
      panicking slice methods `<[T]>::split_at`/`split_at_mut`/`chunks`/
      `chunks_exact`/`rchunks`/`windows`.
  - **Documented residual — less-common library panics remain trusted (a
    known gap, NOT a silent pass).** The catch-list above is the common-and-
    dangerous subset, not exhaustive. Other library functions whose panic is
    in un-walked `core` and that are NOT yet enumerated remain on the trusted
    side until the prelude models them. **Operator-form arithmetic
    (`+ - * / % << >>`) and element-projection indexing (`a[i]`) ARE fully
    covered** (PB049 / PB054). Until the prelude lands, treat a `verified`
    function that uses a not-yet-enumerated panicking library method as
    covering everything EXCEPT that specific library panic, and prefer the
    caught forms.
- **Cross-crate aggregation (whole-workspace gate).** Each crate's
  per-crate `#27` gate only sees its own items, so on its own it cannot
  tell whether a callee in *another* workspace crate was verified. To close
  that, `cargo pitbull check` now has every wrapper run emit a reachability
  manifest (its walked / referenced / trusted paths) into a shared dir and,
  after the build, runs the **whole-workspace** gate
  (`reachability::cross_crate_unverified`): a workspace-member function
  referenced from a verified root anywhere in the build that NO crate's run
  walked or trusted fails the check (exit 1). A verified root in crate A
  calling workspace crate B's `foo` therefore requires *some* crate's run to
  have verified `foo`, or the build fails closed — the per-crate boundary no
  longer hides it. **Warm-cache caveat:** if cargo serves a crate from cache
  (no recompile), that crate emits no manifest this run and its callees are
  reported as INDETERMINATE rather than failed (so incremental builds don't
  false-positive); run a clean build (`cargo clean`) for a complete
  cross-crate verdict. Registry/non-workspace deps stay on the trusted side
  (they are not workspace members, so the gate never demands their
  coverage).
## 4. User obligations
For the guarantee to hold:
1. **Pin the toolchain** to one of `SUPPORTED_TOOLCHAINS`.
2. **Commit `Cargo.lock`** (PB072) and `pitbull.toml`.
3. **Run in a hermetic environment** (PB073): no network, no
   filesystem writes outside the build directory, no environment
   variables affecting compilation.
4. **Audit every `#[pitbull::trusted]` annotation** in your crate and
   its dependencies. The trust budget (PB068) is a guideline, not
   a substitute for review.
5. **Commit proof certificates** under `.pitbull-cache/certs/` and
   sign them with a key restricted to the verification team
   (PB075).
6. **Run `pitbull replay` in CI** so that stale proofs disagreeing
   with current solver versions block merges.
7. **Cross-validate with Miri under Tree Borrows** for any code
   path your spec touches: `MIRIFLAGS=-Zmiri-tree-borrows cargo
   miri test`. (Available now as a soft gate; required for full
   conformance.)
8. **Do not modify the Pitbull pipeline.** If you must (e.g. for
   downstream integration), document the change and re-run the
   qualification kit.
## 5. Known limitations of v0.1
- **No support for `unsafe`.** This is deliberate; see PB001–PB010
  in PSS-1.
- **No support for heap allocation or collections.** See PB011–PB020.
  Workaround: use stack-allocated buffers with explicit capacity.
- **No support for floating-point arithmetic.** See PB050. Workaround:
  fixed-point representations (Q-format).
- **No support for `async` or concurrency.** See PB026–PB030. Pitbull
  v0.1 verifies single-threaded synchronous code only.
- **`overflow-checks = true` required.** v0.1 cannot verify code with
  wrapping arithmetic enabled.
- **`panic = "abort"` required.** No unwinding semantics in v0.1.
These restrictions are itemized so users can decide before adoption
whether their code shape fits.
## 6. Reporting bugs and security issues
Pitbull soundness bugs are treated as security issues. Suspected
unsoundness — Pitbull reporting `verified` on a program that
violates the guarantee — should be reported under embargo via the
process described in `SECURITY.md` (forthcoming).
A counterexample-by-construction is the gold standard for a
soundness report: produce a verified function `f` and an input on
which `f` exhibits one of the §1 failure modes.
## 7. Versioning and compatibility
PSS-1 rules are stable: a rule's PBnnn identifier never changes
once published. Severity changes (e.g. error → audit) are major
version events. The Pitbull-supported toolchain pairs may add
entries in minor versions; entries are not removed without a major
version bump (with a documented migration path).
## 8. Acknowledgements and references
Pitbull stands on:
- **SPARK / Ada and GNATprove** for the deductive verification
  paradigm.
- **Creusot** for the prophecy-based modular semantics of safe Rust
  and for the MIR→Why3 translation infrastructure.
- **Verus** for linear ghost permissions and the mode discipline
  separating spec, proof, and executable code.
- **Kani** for the rustc_public migration path and for the
  differential-testing protocol.
- **Ferrocene** for the qualified compiler distribution and the
  certified core subset of `core`.
- **Miri** for the Tree Borrows aliasing model implementation.
- **Why3, Z3, CVC5, Alt-Ergo** for the SMT layer.
The shoulders are well-established.
