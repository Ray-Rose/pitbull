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
