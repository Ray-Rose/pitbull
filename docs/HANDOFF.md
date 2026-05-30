# Pitbull Hand-off — fresh-session instructions

This file is the entry point for a fresh Claude Code session
(or a human contributor) picking up the Pitbull deductive
verifier where the previous session left off. Read top to
bottom on first sit-down; refer back to individual sections
during work.

Last known-good commit at hand-off: the latest on `main` — run
`git log -1`. The most recent milestone is **Task S** (multi-solver
2-of-N agreement gate); the prior one is **`11aed4c`** (Task R,
division/over-shift obligation encoding). The v0.2 state ships the
deductive backend, full PB054 end-to-end discharge (P / P.1 / P.2),
the Option-C attribute suite (Phase B grammar, Q.1 trusted, Q.2
impl-methods, Q.3 expression-form, Q.4 ensures-MVP), the full
arithmetic AoRTE family (Task R), the **multi-solver agreement gate**
(Task S), and several deep-audit cleanup passes. Branch `main`, local
repo only (no remote).

## TL;DR

- **What it is:** Pitbull is a SPARK-style deductive verifier for Rust.
  v0.1 ships a PSS-1 subset enforcer; v0.2 adds the VC-generation
  spine and SMT dispatch through a **multi-solver agreement gate**
  (Z3 + CVC5 by default). See `docs/PSS-1.md` for the specification.
- **State:** 204 tests passing (1 + 124 subset-lib + 30 integration
  + 49 vc), both lanes warning-clean, clippy error-clean. Done:
  the v0.2 deductive backend (Tasks M + N), spec-context narrowing
  (O.1 → O.2 → O.2.5 → O.3), full PB054 discharge (P / P.1 / P.2),
  and **Option C complete** — the predicate-grammar
  `<ident> <cmp> <ident>` extension (Phase B), `#[pitbull::trusted]`
  (Q.1, with the adapter fix for real `is_unsafe`/`is_async`),
  impl-method attribute extraction (Q.2), expression-form
  attributes (Q.3), and `#[pitbull::ensures]` emission (Q.4 MVP —
  obligation emitted, discharge pending Q.4a). Plus deep-audit
  cleanups F1/F2/F7/H3/N1/N2/N3/F3/F4/F8/F11/H-RT1–3/M-RT3/
  M-RT-Q.A–D/M-1/M-2/L-1/L-2 and the latest silent-skip closures
  (div/rem/shift coverage notes, divergent-ensures fail-closed,
  exclude-count visibility).
- **Rules that DISCHARGE end-to-end under Z3:** PB049 (arithmetic
  AoRTE) and PB054 (slice index bound), both with
  `pitbull.toml`/attribute preconditions. PB049 now covers the full
  arithmetic family — Add/Sub/Mul overflow PLUS Div/Rem
  division-by-zero + signed `MIN/-1` and Shl/Shr over-shift (Task R,
  2026-05-28) PLUS unary negation `-(iN::MIN)` overflow (audit
  2026-05-29; a CRITICAL fix — `-x` was silently unobligated before).
  PB043 / PB041 / PB076 emit obligations that `compile`
  returns `None` for (reported "pending"). The other ~71 rules are
  syntactic visitor rejects.
- **Next task (recommended):** Task R closed the division/over-shift
  AoRTE hole; **Task S closed the loudest TCB hole** — a single
  hostile/buggy `z3` on PATH can no longer rubber-stamp unsafe code,
  because discharge now requires `threshold` independent solvers to
  agree `unsat` with zero `sat` votes (default `[z3, cvc5]`,
  threshold 2; a sat/unsat split is a loud `DISAGREEMENT` that fails
  closed). The remaining highest-leverage moves:
  1. **Proof certificates + `replay`** — replayable per-obligation
     artifacts; the differentiator no competing Rust verifier ships.
     Recommended next.
  2. **Q.4a ensures SMT discharge** + **mixed-width over-shift
     encoding** (Task R deferred the `u32 << u8` case to a
     zero-extend follow-up; same-type shifts discharge today).
  See Section 5 for the full menu.
- **First commands to run in a fresh session:** see
  [Section 4: Smoke test in a fresh session](#4-smoke-test-in-a-fresh-session).

---

## Table of contents

1. [Repository state](#1-repository-state)
2. [Architecture overview](#2-architecture-overview)
3. [Toolchain + system requirements](#3-toolchain--system-requirements)
4. [Smoke test in a fresh session](#4-smoke-test-in-a-fresh-session)
5. [Next: verify the v0.2 demo, then pick a strategic direction](#5-next-verify-the-v02-demo-then-pick-a-strategic-direction)
6. [Common commands cheat sheet](#6-common-commands-cheat-sheet)
7. [Known limitations + remaining work](#7-known-limitations--remaining-work)
8. [Common pitfalls + Windows quirks](#8-common-pitfalls--windows-quirks)
9. [Editor identity + commit conventions](#9-editor-identity--commit-conventions)

---

## 1. Repository state

### Recent commit log (newest first)

```
b080d1a Audit-cleanup: close silent-skip soundness gaps (div/rem/shift notes, divergent-ensures fail-closed, exclude-count)
49fbf09 Audit-cleanup post-Q: close M-1/M-2/L-1/L-2 (divergent-ensures note, ret_ty_name Option, ascii assert)
dfef08b Milestone 2 Task Q.4 MVP: #[pitbull::ensures(...)] postcondition obligations (PB076)
1ba425e Audit-cleanup pass after Q.1-Q.3 (M-RT-Q.A–D)
4ba79ba Milestone 2 Task Q.3: expression-form #[pitbull::requires(x < 100)] without quotes
39ab294 Milestone 2 Task Q.2: #[pitbull::requires]/#[trusted] on impl methods
99c7b28 Milestone 2 Task Q.1: #[pitbull::trusted] + adapter is_unsafe/is_async fix
73a5568 Phase B: predicate grammar <ident> <cmp> <ident> form
c43f051 chore: remove orphan deps (sha2/trybuild/insta/syn/quote/proc-macro2)
0767285 N3 + H-RT1/H-RT2/H-RT3/M-RT3 (post-interruption red-team cleanup)
e6f9154 Audit-cleanup pass after P/P.1/P.2 (N1/N2/F3/F4/F5–F13 closed)
c05bd13 Milestone 2 Task P.2: PB054 operand binding — IndexBound discharges end-to-end
f0b7dc7 Milestone 2 Task P.1: PB054 SMT discharge — IndexBound compiles to QF_BV
9e15116 Milestone 2 Task P: PB054 MVP — detect index sites and emit IndexBound obligations
de0054e docs: HANDOFF.md refresh for post-O.3 state
a66a1a4 Milestone 2 Task O.3: #[pitbull::requires(...)] attribute extraction via HIR
808f5dd Audit O.2.5-followup: sign-extend narrow signed values + capstone test + doc fixes
f18a3fa Milestone 2 Task O.2.5: constant-operand value extraction (headline demo unlocker)
c535fe4 docs: HANDOFF.md — fresh-session instructions for the next contributor
7f6bdc2 Audit O.2-cleanup #6: final residuals (doc drift, dead method, F1/F10 regression tests, integration-test race fix)
99f975c Audit O.2-cleanup #5: F7 + F8 + F10 (defense-in-depth + UX correctness)
9f6ce90 Audit O.2-cleanup #4: F3 + H-1/H-2/H-3 + specific audit messages for translation failures
01c001b Audit O.2-cleanup #3: F1 (consistency-check guard against contradictory preconditions)
db34fb7 Audit O.2-cleanup #2: F2 + F9 (assumption lex-validation + verdict-parser hardening)
dc5ed6d Milestone 2 Task O.2-cleanup: audit findings after O.2
102aeca Milestone 2 Task O.2: spec-context narrowing — predicate grammar + parameter binding
bc2bd46 Milestone 2 Task O.1: spec-context narrowing — foundation (raw SMT-LIB preconditions)
3c477e2 Milestone 2 Task N: visitor → pitbull-vc → Z3 end-to-end (v0.2 spine working)
6a4c3ec Milestone 2 Task M: pitbull-vc scaffold (VC types + SMT-LIB + Z3 dispatch)
79a87c7 Milestone 2 Task L: add CI workflow (stable + nightly-e2e gates)
7b6d5a6 Milestone 2 Task K: fix audit finding H3 (env-path injection guards)
8950d55 Milestone 2 Task J: fix audit finding H1 (silent default-config fallback)
d362094 Milestone 2 Task I: fix audit finding C2 (silent path=None fallthrough)
931a90a Milestone 2 Task H: fix audit finding C1 (verify_roots skipped statics)
7b7de36 Milestone 2 Task G: HIR pre-pass for PB001 unsafe-block detection
b383707 Milestone 2 Task F: filename side-channel for SARIF artifactLocation URIs
3d4f2d7 Milestone 2 Task E: wrapper enumerates static/const items (PB018 e2e)
50ec60d Milestone 2 Task C: activate corpus_runs_full_pipeline e2e test
40a0511 Milestone 2 Task D: cleaner def_id via DefId::name()
d581354 Milestone 2 Task B: real Span line/col from rustc_public
13b2b8b Milestone 2 Task A: verify_roots filtering via pitbull.toml
781b906 Milestone 2: full adapter — Box example emits PB011 end-to-end
7a54f52 Milestone 2: PitbullCallbacks fires end-to-end through cargo check
c601831 Milestone 2: pitbull-rustc wrapper binary + cargo check integration
ab4cde1 Milestone 2 scaffold: rustc_public adapter wiring
f10970d Initial v0.1.0-dev skeleton: PSS-1 subset enforcer
```

### Test invariant

| Lane | Status |
|---|---|
| `cargo +stable test --workspace --all-features` | **204 passing**, 0 failed, 0 ignored, 0 warnings |
| `cargo +stable check --workspace --all-features` | warning-clean |
| `cargo +stable clippy --workspace --all-features --all-targets` | clippy-clean (no `error:` lines) |
| `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 clippy -p pitbull-driver --bin pitbull-rustc` | clippy-clean (lints the `cfg(rustc_public_real)` dispatch path) |
| `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc` | warning-clean |

The 204 breaks down: 1 (cargo-pitbull bin) + 124 (subset lib) + 30 (integration) + 49 (vc) = 204. The +11 over the 191 Task-R baseline are Task S (multi-solver agreement gate) plus its post-commit red-team hardening: vc gains 10 `vote()` unit tests — the 8 agreement-policy cases (two-unsat-meets-threshold, single-unsat-inconclusive, unsat+sat-disagreement, all-sat-refuted, sat+unknown-refuted, threshold-1-discharges, no-decisions-inconclusive, known-solver-resolves) plus two soundness regression guards (duplicate-solver-name-counts-once, empty-results-inconclusive) — and integration gains the 2-of-N agreement discharge capstone (gated on both z3 and cvc5 present). A 4-agent red-team of the gate (2026-05-29) found and fixed **two CRITICALs**: a consistency-check fail-open (Timeout/Error/Unknown on the precondition consistency check used to fall through to the main check, risking a *vacuous* discharge of contradictory preconditions) and duplicate-solver vote inflation (`solvers=["z3","z3"]` counted one binary as two independent votes). Both are verified closed; the six dispatch branches plus the two fixes were exercised across 7 fake-solver scenarios end-to-end. A follow-on program-wide audit (2026-05-29) additionally found and fixed a CRITICAL missed obligation: unary negation `-x` was completely unobligated (the `Rvalue::UnaryOp` arm swallowed `UnOp::Neg`), so `-(iN::MIN)` was reported safe. PB049 now emits a `neg` obligation encoding `(= lhs iN::MIN)`, guarded by +1 visitor and +1 smt test (the +2 that take vc 48→49 and subset 123→124).

---

## 2. Architecture overview

### Workspace crates

| Crate | Role |
|---|---|
| `pitbull-spec` | Attribute proc-macros (`#[pitbull::requires]`, `#[pitbull::ensures]`, etc.). v0.1 they're no-ops; v0.3 wires real extraction. |
| `pitbull-subset` | PSS-1 subset enforcer. Visitor + adapter + reachability + VC-obligation types. **The TCB core.** |
| `pitbull-vc` | v0.2 scaffold: VC compilation (`compile`) and SMT solver dispatch (`solver::invoke_z3`). Depends on `pitbull-subset` for typed obligations. |
| `pitbull-driver` | Two binaries: `cargo-pitbull` (subcommand) and `pitbull-rustc` (rustc-replacement wrapper invoked by cargo). |

### Key types

| Type | Where | Purpose |
|---|---|---|
| `mir_api::Body` | `pitbull-subset/src/mir_api.rs` | Shadow MIR body. Carries `arg_names: Vec<String>` for spec-binding. |
| `mir_api::Span` | same | Shadow Span. `lo`/`hi` pack line/col; `file` is a u32 hash of the filename. |
| `vc::VcObligation` | `pitbull-subset/src/vc.rs` | Typed obligation (id, span, kind, **assumptions**). Visitor produces these. |
| `vc::VcGoal` | `pitbull-vc/src/vc.rs` | Compiled obligation: typed claim + SMT-LIB text + optional consistency-check problem. |
| `diagnostic::SubsetReport` | `pitbull-subset/src/diagnostic.rs` | Visitor output: `errors`, `audit_notes`, `vc_obligations`, `filenames` table, `phase_completed`. |
| `predicate::Predicate` | `pitbull-subset/src/predicate.rs` | Tiny IR for spec preconditions: `<ident> <cmp> <int>`. |
| `SolverResult` | `pitbull-vc/src/solver.rs` | Six variants — Sat, Unsat, Unknown, NotInstalled, Timeout, Error(String). |

### Data flow

```
                       ┌──────────────────────────────────────────────────────────┐
                       │              `cargo pitbull check` command               │
                       │   (crates/pitbull-driver/src/main.rs — subcommand UI)    │
                       └────────────────────────────┬─────────────────────────────┘
                                                    │  invokes `cargo check`
                                                    │  with RUSTC_WORKSPACE_WRAPPER
                                                    ▼
                       ┌──────────────────────────────────────────────────────────┐
                       │                    `pitbull-rustc` wrapper               │
                       │     (crates/pitbull-driver/src/bin/pitbull-rustc.rs)     │
                       │                                                          │
                       │   For each crate cargo compiles:                         │
                       │   1. Load pitbull.toml (PITBULL_TOML env or ./)          │
                       │   2. HIR pre-pass: collect PB001 unsafe blocks           │
                       │      (filters macro-expanded spans)                      │
                       │   3. Enter `rustc_public::rustc_internal::run`           │
                       │   4. Walk every item via `all_local_items()`:            │
                       │      - Fn: adapter::body → SubsetVisitor::visit_body     │
                       │      - Static: visit_static_item (incl. PB018)           │
                       │      - Const: visit_const_item                           │
                       │   5. Take filename table from adapter                    │
                       │   6. Dispatch VC obligations via pitbull-vc              │
                       │   7. Optional: write SARIF to PITBULL_SARIF_OUT          │
                       │   8. Exit with rustc_exit.max(pitbull_exit)              │
                       └────────────────────────────┬─────────────────────────────┘
                                                    │
                                                    ▼
                       ┌──────────────────────────────────────────────────────────┐
                       │                       SubsetVisitor                      │
                       │              (crates/pitbull-subset/src/visitor.rs)      │
                       │                                                          │
                       │  Exhaustive match over MIR variants. Two outputs:        │
                       │  - errors: subset violations (SubsetError)               │
                       │  - vc_obligations: VC obligations the backend discharges │
                       │  - audit_notes: non-violation diagnostic gaps            │
                       └────────────────────────────┬─────────────────────────────┘
                                                    │   for each obligation
                                                    ▼
                       ┌──────────────────────────────────────────────────────────┐
                       │                        pitbull-vc                        │
                       │             (crates/pitbull-vc/src/{vc,smt,solver}.rs)   │
                       │                                                          │
                       │  compile(obligation) → Option<VcGoal>:                   │
                       │    - emit overflow SMT problem (with assumptions)        │
                       │    - emit consistency-check SMT (if assumptions)         │
                       │                                                          │
                       │  Wrapper dispatch:                                       │
                       │    - run consistency-check first (refuse if Unsat)       │
                       │    - then main check                                     │
                       │    - map verdict → "discharged"/"NOT DISCHARGED"/etc.    │
                       └──────────────────────────────────────────────────────────┘
```

### Soundness defenses (post-audit-cleanup posture)

1. **Lex-validation of raw assumptions** (`predicate::validate_assertion_form`). Multi-directive SMT injection is refused with an audit note.
2. **Consistency-check guard** (`pitbull-vc::compile` + dispatch). Contradictory preconditions can no longer make Z3 vacuously "verify" unsafe code.
3. **Verdict-parser hardening** (`solver::invoke_z3`). Multiple verdict lines → `Error`, never silently misread.
4. **Specific audit messages** for every rejection path. The "no silent skips" posture is enforced at every layer.
5. **Exit code reflects findings** (`pitbull-rustc.rs`). `rustc_exit.max(pitbull_exit)` where Pitbull contributes 1 if violations > 0 OR undischarged > 0.
6. **`#![forbid(unsafe_code)]`** on every TCB crate root.

---

## 3. Toolchain + system requirements

| Component | Version | Notes |
|---|---|---|
| Stable Rust | 1.78+ | For the shadow build and tests. `rustup toolchain install stable`. |
| Nightly Rust | **`nightly-2026-01-29`** exactly | Required for the rustc-replacement wrapper. `rustup toolchain install nightly-2026-01-29 --component rustc-dev rust-src`. |
| Z3 SMT solver | Any 4.x | Optional but recommended. Used by the VC dispatch loop. Without it, the wrapper reports VC obligations as "undischarged (no solver)" — pipeline still works. Install: `winget install Microsoft.Z3` on Windows, `apt install z3` on Debian/Ubuntu. |
| Git Bash | Bundled with Git for Windows | All shell commands assume Git Bash on Windows; equivalent on Linux/macOS. |
| Python 3 | Any 3.x | Used by one smoke-test script (inspecting SARIF JSON). Not required for the regular test suite. |

### Environment variables the wrapper consults

| Variable | Purpose | Default |
|---|---|---|
| `PITBULL_USE_RUSTC_PUBLIC` | Build cfg flag. Set to `1` to enable the nightly+opt-in lane. | unset (stable stub) |
| `PITBULL_TOML` | Absolute path to the user's pitbull.toml. Cargo-subcommand sets this so dependency compiles see the user's config. | unset (falls back to `./pitbull.toml`) |
| `PITBULL_SARIF_OUT` | Absolute path. When set, the wrapper writes SARIF JSON to it after each compile unit. | unset (no SARIF output) |
| `PITBULL_REQUIRE_E2E` | Test gate. When set, `corpus_runs_full_pipeline` and other e2e tests escalate "wrapper missing" to a hard test failure instead of graceful skip. | unset |
| `PITBULL_ALLOW_UNSAFE_PATHS` | Escape hatch for the H3 path-traversal/extension guards. Set to bypass the safety checks on `PITBULL_TOML` / `PITBULL_SARIF_OUT`. | unset (guards active) |

---

## 4. Smoke test in a fresh session

Run these commands in order. Each line should produce the indicated output. If any step fails, stop and investigate before continuing.

### Step 4.1 — Confirm you're in the right directory

```bash
cd /path/to/PLAYGROUND_pitbull/pitbull_official
pwd
# Expected: .../PLAYGROUND_pitbull/pitbull_official

git log --oneline -1
# Expected: a66a1a4 Milestone 2 Task O.3: #[pitbull::requires(...)] attribute extraction via HIR
```

### Step 4.2 — Stable test suite (the 204-test baseline)

```bash
cargo +stable test --workspace --all-features 2>&1 | grep "^test result"
# Expected: "test result: ok" lines totaling 204 passing, 0 failed, 0 ignored
```

If you see `Application Control policy has blocked this file` on Windows: that's Smart App Control quarantining a fresh test binary. Run again — usually clears on the second try. If persistent, run `cargo +stable test --workspace --all-features` (without the -p flag) to use the workspace-mode binary path which SAC tends to accept.

### Step 4.3 — Stable warning check

```bash
cargo +stable check --workspace --all-features 2>&1 | grep -iE "warning|error"
# Expected: empty output
```

### Step 4.4 — Build the nightly wrapper

```bash
PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc
# Expected: "Finished `dev` profile [unoptimized + debuginfo] target(s) in N.NNs"
# (no warnings, no errors)
```

### Step 4.5 — End-to-end smoke on a real Rust file

```bash
SYSROOT=$(rustup run nightly-2026-01-29 rustc --print sysroot)
TMPDIR=$(cygpath -m $(mktemp -d))   # On Linux: TMPDIR=$(mktemp -d)
cat > "$TMPDIR/probe.rs" <<'RUST'
pub fn add_one(x: u32) -> u32 {
    x + 1
}
RUST

PATH="$SYSROOT/bin:$PATH" \
  ./target/debug/pitbull-rustc.exe --sysroot "$SYSROOT" \
  --edition=2021 --crate-type=lib --emit=metadata "$TMPDIR/probe.rs" \
  -o "$TMPDIR/probe.rmeta"
```

Expected stderr (Z3 not installed):
```
pitbull-rustc: z3 not installed; VC obligations cannot be discharged. ...
pitbull-rustc: vc pb049-add-0 (PB049): undischarged (no solver) [1 assumption]
pitbull-rustc: VC summary: 1 obligation(s), 0 discharged, 1 undischarged
pitbull-rustc: crate analyzed: 1 items, 1 bodies walked, 0 non-fn items, 0 unsafe blocks, 0 subset violation(s)
```

Each verdict line carries `(PBxxx)` (the canonical PSS-1 rule id, added in Task P.1) alongside the obligation id, so an auditor reading stderr sees both the rule and the per-obligation tag at a glance.

If Z3 IS installed:
```
pitbull-rustc: vc pb049-add-0 (PB049): NOT DISCHARGED (sat — counterexample exists) [1 assumption]
pitbull-rustc: VC summary: 1 obligation(s), 0 discharged, 1 undischarged
```
(The lone obligation reports sat because there's no precondition constraining `x`; `x = u32::MAX` is a witness. The `[1 assumption]` is the O.2.5 const-pin for `rhs = 1`.

With a `#[pitbull::requires("x < 100")]` attribute on the same function — and `#![feature(register_tool)]` + `#![register_tool(pitbull)]` at the crate root — the verdict flips:
```
pitbull-rustc: vc pb049-add-0 (PB049): discharged (unsat — safety property holds) [2 assumptions]
pitbull-rustc: VC summary: 1 obligation(s), 1 discharged, 0 undischarged
```

A second discharge demo, PB054 (added in Tasks P / P.1 / P.2):
`fn at(s: &[u8], i: usize) -> u8 { s[i] }` with
`"corpus_test::at" = ["(assert (bvult i len))"]` in pitbull.toml
produces (Z3 on PATH):
```
pitbull-rustc: vc pb054-idx-0 (PB054): discharged (unsat — safety property holds) [1 assumption]
pitbull-rustc: VC summary: 1 obligation(s), 1 discharged, 0 undischarged
```
Both demos route through the same compile + dispatch pipeline.
See Section 5 for verification details.)

### Step 4.6 — Optional: full e2e with PITBULL_REQUIRE_E2E

```bash
PITBULL_REQUIRE_E2E=1 cargo +stable test --workspace --all-features -- --test-threads=1
# Expected: all integration tests run (none gracefully skipped). Still 204 passing.
# Note: the 2-of-N agreement capstone additionally requires BOTH z3 and
# cvc5 on PATH; with PITBULL_REQUIRE_E2E set it panics if either is missing.
```

If any of these steps fail, the project state is degraded. Don't proceed to new tasks until baseline is green.

---

## 5. Next: verify the v0.2 demo, then pick a strategic direction

The v0.2 spec-context-narrowing arc — O.1 (raw SMT) → O.2
(predicate grammar) → O.2.5 (constant-pin) → O.3
(`#[pitbull::requires]` attributes) — is complete. The natural
first thing a fresh session should do is **verify the demo
works end-to-end**, then choose from a menu of follow-ups.

### Step 5.1 — Install Z3 (5 minutes)

Z3 isn't required to build/test, but it IS required to
observe the actual `unsat` discharge verdict on the headline
demo. Without it, the wrapper reports "undischarged (no
solver)" everywhere.

```bash
# Windows
winget install Microsoft.Z3

# macOS
brew install z3

# Debian/Ubuntu
sudo apt install z3

# Verify
z3 --version  # any 4.x version is fine
```

### Step 5.2 — Run the headline demo end-to-end

With Z3 installed, the existing tests
`solver::tests::pinned_inputs_proves_no_overflow` and
`integration::wrapper_proves_add_one_safe_under_precondition`
should exercise the actual solver path:

```bash
cargo +stable test --workspace --all-features
# Expected: 204 passing (same as without Z3 — the new tests
# also pass via graceful-skip if no solver is present, but with
# z3 they exercise the real `unsat` verdict path).
```

Additionally, run the direct smoke:

```bash
SYSROOT=$(rustup run nightly-2026-01-29 rustc --print sysroot)
TMPDIR=$(mktemp -d)
cat > "$TMPDIR/probe.rs" <<'RUST'
#![feature(register_tool)]
#![register_tool(pitbull)]

#[pitbull::requires("x < 100")]
pub fn add_one(x: u32) -> u32 { x + 1 }
RUST
PATH="$SYSROOT/bin:$PATH" \
  ./target/debug/pitbull-rustc.exe --sysroot "$SYSROOT" \
  --edition=2021 --crate-type=lib --emit=metadata "$TMPDIR/probe.rs" \
  -o "$TMPDIR/probe.rmeta"
```

Expected stderr line with Z3 installed:
```
pitbull-rustc: vc pb049-add-0: discharged (unsat — safety property holds) [2 assumptions]
pitbull-rustc: VC summary: 1 obligation(s), 1 discharged, 0 undischarged
```

If you see "discharged" here, the entire v0.2
spec-context-narrowing pipeline works end-to-end. Pat
yourself on the back.

### Step 5.3 — Pick a strategic direction

Several reasonable next steps. Listed in approximate
impact-to-effort order:

#### Option A — PB054 bound checks (**DONE** in Tasks P / P.1 / P.2)
~~The next obligation kind after PB049 overflow.~~ Shipped.
PB054 now emits via the visitor's `visit_projection` (Task P),
compiles to a real QF_BV SMT problem (Task P.1), and discharges
end-to-end under Z3 with operand-bound preconditions (Task P.2).
See `tests/integration.rs::wrapper_proves_bounded_index_safe_under_precondition`
for the e2e capstone. Limitations that remain are tracked in
Section 7 below — chiefly that the predicate grammar doesn't yet
support `<ident> <cmp> <ident>` form, so users write raw SMT in
`pitbull.toml` rather than `#[pitbull::requires("i < len")]`.

#### Option A' — PB043 panic reachability (~3 days, high impact)
The next obligation kind. Different shape than PB049/PB054: needs
path-sensitive symbolic execution rather than bit-vector arithmetic
alone. The visitor already emits `VcObligationKind::PanicReachability`
at every reachable `core::panicking::*` / `std::panicking::*` call
site; `pitbull-vc::compile` returns `None` for the kind today
(reported as "pending" in the verdict). A real backend would track
SMT-encoded path conditions through the MIR (post-monomorphization)
and prove the panic call is unreachable under the precondition set.

Sketch:
1. Add a new `pitbull-vc` module for path-condition tracking
   (CFG → SMT bool assertions per basic block).
2. Encode the call site's path condition; ask the solver "is
   this path condition satisfiable under the user preconditions?"
3. unsat ⇒ discharged (panic unreachable); sat ⇒ undischarged
   with the satisfying assignment as counterexample.
4. Connect to `strict_panic_acceptance` in pitbull.toml (current
   posture: visitor-level reject when strict; obligation when
   non-strict).

#### Option B — Multi-solver agreement ✅ DONE (Task S, 2026-05-28)
The SAFETY-MANUAL flagged solver bugs as a real TCB hole; the
defense is N-of-M agreement. Shipped:
1. ✅ A generic `Solver` descriptor + `invoke_solver_with_timeout`
   replaces the Z3-only path — Z3 (`z3 -in`), CVC5 (`cvc5
   --lang=smt2`), and Alt-Ergo (`alt-ergo -i smtlib2`) each carry
   their own timeout convention. `invoke_z3` is now a thin wrapper.
   The N3 subprocess hardening (writer thread, capped readers,
   OS-kill deadline, single-verdict parse) is preserved for all.
2. ✅ `run_solvers` runs the configured pool in parallel; the PURE
   `vote(results, threshold)` applies the policy: any `sat` blocks
   discharge; a `sat`+`unsat` split is a `Disagreement` (fail
   closed, loud); `threshold`+ `unsat` votes with zero `sat`
   discharges; otherwise `Inconclusive`. `dispatch_vc_obligations`
   maps the verdict to diagnostics + exit code.
3. ✅ Default pool is `[z3, cvc5]` with threshold 2. **Alt-Ergo is
   recognized but NOT default** — Alt-Ergo ≤ 2.4.0 has no
   bit-vector theory ("Bitvector not yet supported"), so it can
   never discharge a QF_BV obligation and would only dilute the
   pool. Verified empirically 2026-05-28.

Remaining hardening follow-up (not blocking): cache per-solver
versions against `cfg.verification.solver_versions` so a binary
swap is loud (the config field exists; the check is not yet wired).

#### Option C — Extend O.3 attribute coverage ✅ DONE (Phase B + Q.1–Q.4)
All four sub-items shipped:
1. ✅ `#[pitbull::ensures("...")]` postconditions — Q.4 MVP emits the
   PB076 obligation at every return (and fail-closed for divergent
   bodies); the SMT discharge (modelling `result` as a BV variable)
   is the remaining Q.4a slice.
2. ✅ `#[pitbull::trusted]` opt-out — Q.1, with the adapter fix that
   makes real `is_unsafe`/`is_async` flow so PB002/PB026 still fire
   on trusted signatures (trust never admits unsafe).
3. ✅ Methods on impl blocks — Q.2 (`visit_impl_item`, with the
   double-fire fix for nested-visit).
4. ✅ Rust-expression-form arguments — Q.3 (token-tree pretty-print
   via `rustc_ast_pretty`).
Plus Phase B added the `<ident> <cmp> <ident>` predicate grammar so
`i < len`-style preconditions no longer need raw-SMT.

#### Option D — Corpus expansion (~half day per rule, mechanical)
The `tests/corpus/` directory should have ≥10 reject + ≥5
accept files per rule per PSS-1 §15. Currently most rules
have 1 each. Hand-writing the examples is the bottleneck;
this is the kind of task that scales with calendar time.

#### Option E — `cargo pitbull check` subcommand wires verdict aggregation (~1 day)
The cargo subcommand currently uses `status.success()` and
loses per-crate Pitbull output. Should parse stderr / SARIF
across all compile units and produce a unified report.

### Step 5.4 — Update PSS-1.md and HANDOFF.md when done

Whatever you pick, end the work with a §17.1 entry in
`docs/PSS-1.md` and update this HANDOFF.md's commit pointer
to the new tip.

---

## 6. Common commands cheat sheet

### Test + verify
```bash
# Quick: just the stable test suite
cargo +stable test --workspace --all-features

# Just one package
cargo +stable test -p pitbull-subset --all-features

# Just one test
cargo +stable test --workspace --all-features <test_name>

# Force serial (debugging races)
cargo +stable test --workspace --all-features -- --test-threads=1

# Hard-fail if e2e prerequisites missing
PITBULL_REQUIRE_E2E=1 cargo +stable test --workspace --all-features

# Stable warning check
cargo +stable check --workspace --all-features

# Nightly+opt-in wrapper build
PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc

# Nightly check (faster than build)
PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 check -p pitbull-driver
```

### Direct smoke testing
```bash
SYSROOT=$(rustup run nightly-2026-01-29 rustc --print sysroot)
TMPDIR=$(cygpath -m $(mktemp -d))   # Windows
# TMPDIR=$(mktemp -d)               # Linux/Mac

# Write a probe Rust file
cat > "$TMPDIR/probe.rs" <<'RUST'
pub fn example() -> u32 { 42 }
RUST

# Run the wrapper
PATH="$SYSROOT/bin:$PATH" \
  ./target/debug/pitbull-rustc.exe --sysroot "$SYSROOT" \
  --edition=2021 --crate-type=lib --emit=metadata "$TMPDIR/probe.rs" \
  -o "$TMPDIR/probe.rmeta"

# With a custom pitbull.toml
cat > "$TMPDIR/pitbull.toml" <<'TOML'
[project]
name = "corpus_test"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"

[verification.preconditions]
"corpus_test::example" = ["x < 100"]
TOML
PITBULL_TOML="$TMPDIR/pitbull.toml" \
PATH="$SYSROOT/bin:$PATH" \
  ./target/debug/pitbull-rustc.exe --sysroot "$SYSROOT" \
  --edition=2021 --crate-type=lib --emit=metadata "$TMPDIR/probe.rs" \
  -o "$TMPDIR/probe.rmeta"

# With SARIF output
PITBULL_SARIF_OUT="$TMPDIR/out.sarif.json" \
PATH="$SYSROOT/bin:$PATH" \
  ./target/debug/pitbull-rustc.exe --sysroot "$SYSROOT" \
  --edition=2021 --crate-type=lib --emit=metadata "$TMPDIR/probe.rs" \
  -o "$TMPDIR/probe.rmeta"
python -c "import json; print(json.dumps(json.load(open(r'$TMPDIR/out.sarif.json')), indent=2))"
```

### Git
```bash
# Commit as Ray Rose (the project author)
git -c user.name="Ray Rose" -c user.email="RayRose-dev@outlook.com" commit -m "..."

# Or set globally first
git config user.name "Ray Rose"
git config user.email "RayRose-dev@outlook.com"
git commit -m "..."
```

---

## 7. Known limitations + remaining work

### Soundness gaps (acknowledged, deferred)

| ID | What | Where | Why deferred |
|---|---|---|---|
| solver PATH trust | A solver binary on PATH could be a hostile substitute always returning `unsat`. | `pitbull-vc/src/solver.rs::{run_solvers,vote}` | **Mitigated (Task S + 2026-05-29 audit):** discharge requires `threshold` *distinct* solvers (default `[z3, cvc5]`, threshold 2) to agree `unsat` with zero `sat`; one corrupt solver yields at most `Inconclusive`, and a `sat`/`unsat` split is a loud `DISAGREEMENT`. `vote` counts distinct solver names and the driver dedups the pool, so a duplicate config entry (`["z3","z3"]`) cannot inflate the vote. The precondition consistency check fails closed unless `threshold` solvers confirm satisfiability, so a timed-out/errored consistency check cannot yield a vacuous discharge. Residual: a coordinated swap of ALL distinct solvers, and the per-solver version pin (`solver_versions`) is not yet enforced. |
| u32 file-hash collisions | `Span::file` is a u32 hash. At ~65K files, 50% collision probability. | `pitbull-subset/src/mir_api/adapter.rs` (and `mir_api.rs::Span`) | Bumping to u64 ripples through the shadow IR. Tracked. |
| Constant operand extraction (O.2.5) | ✅ DONE in `f18a3fa`. Adapter now extracts integer values via `try_extract_integer_value`; visitor synthesizes `(assert (= rhs #x...))` pinning assertions. Sign-extension fix in `808f5dd`. | — | Closed. |
| `#[pitbull::requires]` attribute extraction (O.3) | ✅ DONE in `a66a1a4`. HIR pre-pass extracts string-literal arguments from `#[pitbull::requires("...")]`; merged with `pitbull.toml`-based preconditions. Verdict lines now include `[N assumption(s)]` suffix. | — | Closed. |
| Path-sensitive symbolic exec | PB043 PanicReachability obligations are emitted but `pitbull-vc::compile` returns None for the kind. | `pitbull-vc/src/vc.rs::compile` | The SMT encoding for "panic site is unreachable" requires path-sensitive analysis — multi-week task. |
| Termination measures (PB041) | Recursion-decreasing obligations not yet emitted. | visitor + vc | Needs call-graph SCC analysis, currently a documented gap. |
| Bounds checks (PB054) | ✅ DONE in Tasks P / P.1 / P.2 + audit-cleanup. Visitor emits `IndexBound { idx_source_name: Option<String> }`; compile emits QF_BV with `__pb_idx`/`__pb_len` canonical names + `idx`/`len` aliases + optional source-name alias in quoted-symbol syntax for raw-ident safety. End-to-end discharge under Z3 verified by `wrapper_proves_bounded_index_safe_under_precondition`. | — | Closed. |
| Z3 subprocess timeout / output cap | Z3 invocation can hang indefinitely on a pathological SMT problem; no captured-output size cap. | `pitbull-vc/src/solver.rs` | DoS vector flagged in audit finding N3 (2026-05-26). Mitigation requires spawning + try_wait + size-cap; bigger change than the audit-cleanup pass absorbed. |
| PB049 silent skip on projected operands | ✅ DONE in audit-cleanup. `maybe_emit_overflow_obligation` now emits a `PB049: ... skipped` audit note when operand types can't be resolved (projected operands like `p.0 + p.1`, mismatched types). Pre-fix the obligation was silently dropped — auditors reading "0 obligations" would falsely conclude verified. | — | Closed (audit finding N1, 2026-05-26). |
| SARIF / TOML symlink follow | ✅ DONE in audit-cleanup. `check_env_path` now refuses symlink leaf paths via `symlink_metadata().file_type().is_symlink()`. Pre-fix a build.rs could create a `.json`-extension symlink to overwrite `~/.config/.../settings.json` via `PITBULL_SARIF_OUT`. | — | Closed (audit finding N2, 2026-05-26). |

### UX / quality work

| What | Where | Priority |
|---|---|---|
| F7 regression corpus test | `crates/pitbull-subset/tests/corpus/accept/PB001_macro_expansion.rs` | MEDIUM. Smoke-verified manually; pinning requires a corpus file walked through the nightly wrapper. |
| Clippy cleanup | workspace-wide | ✅ DONE in audit-cleanup. `cargo +stable clippy --workspace --all-features --tests` is now error-clean. Remaining are non-deny warnings (~100). |
| Mutation testing harness wiring | `pitbull-subset/src/mutation.rs` | MEDIUM. Module exists; cargo-mutants integration is the missing piece. |
| Corpus expansion | `tests/corpus/{accept,reject}/` | LOW (ongoing). Want ≥10 reject + ≥5 accept per rule per PSS-1 §15. |
| `cargo pitbull check` subcommand wires verdict aggregation | `pitbull-driver/src/main.rs` | MEDIUM. Subcommand exists but uses status.success() rather than per-crate Pitbull output. |
| Documentation: per-rule rationale | `docs/PSS-1.md` | LOW. Each of the 76 rules has a description; some lack the "why" explanation. |

### Test infrastructure

| What | Where | Severity |
|---|---|---|
| Application Control blocks on Windows | Smart App Control quarantines fresh test binaries | LOW. Re-run usually clears. Workaround documented in Section 8. |
| `cargo +nightly-2026-01-29 test` rustc-private linking fails | nightly+opt-in lane | DOCUMENTED LIMITATION. The integration tests subprocess-invoke the built wrapper to bypass; PSS-1.md §17.1 has the technical detail. |

---

## 8. Common pitfalls + Windows quirks

### Smart App Control / WDAC blocks on fresh test binaries

Symptom: `An Application Control policy has blocked this file. (os error 4551)` on a newly-built test binary at `target/debug/deps/<crate>-<hash>.exe`.

Workaround: re-run the same `cargo test` command. SAC typically allows the binary on the second invocation (after a reputation cache update). If still blocked, the binary path produced by `--workspace` mode differs from `-p <crate>` mode; the workspace path is usually unblocked first. So prefer:
```bash
cargo +stable test --workspace --all-features  # workspace mode (preferred)
```
over:
```bash
cargo +stable test -p pitbull-subset --all-features  # crate-only mode
```

### Cargo test parallel races on shared temp files

Fixed in `7f6bdc2`. If you write new integration tests in `crates/pitbull-subset/tests/integration.rs`, the helper `run_one_corpus_file_full` now uses `TEMP_FILE_COUNTER` to uniquify temp filenames. Don't reintroduce pid-only filenames.

### Nightly wrapper not rebuilt after code changes

Symptom: `cargo +stable test` integration tests show stale wrapper output (your code edit doesn't appear in stderr).

Fix: rebuild the wrapper after editing pitbull-driver or pitbull-subset:
```bash
PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc
```
`cargo test` doesn't auto-rebuild the wrapper because tests subprocess-invoke the binary; cargo only rebuilds when it's a `cargo` dependency.

### Wrapper exits without producing expected output

If the wrapper outputs only `"pitbull-rustc: crate analyzed: ... 0 violation(s)"` and nothing else for a body you expect to violate, possibilities:
1. The body wasn't walked. Check `crate analyzed: N items, M bodies walked` — if M is 0, reachability filter excluded it. Check `pitbull.toml` `verify_roots`.
2. Path classifier missed the call. The audit notes will show "TEMP DIAG: unmatched callee path = ..." IF you re-enable diagnostic. The current code doesn't print these by default.
3. rustc lowered the construct differently than expected. Read the actual rustc_public MIR via toolchain source under `~/.rustup/toolchains/nightly-2026-01-29-x86_64-pc-windows-msvc/lib/rustlib/rustc-src/rust/compiler/rustc_public/`.

### `.claude/settings.local.json` accidentally committed

This happens when you use `git add -A`. The `.claude/` directory is now in `.gitignore` (since commit `d362094`), so it won't happen automatically. If it does, `git rm --cached .claude/settings.local.json` and commit.

---

## 9. Editor identity + commit conventions

### Author identity

Use Ray Rose as the author. Either set globally:
```bash
git config user.name "Ray Rose"
git config user.email "RayRose-dev@outlook.com"
```

or per-commit:
```bash
git -c user.name="Ray Rose" -c user.email="RayRose-dev@outlook.com" commit -m "..."
```

### Commit message format

Single-line title (under 72 chars), blank line, body in markdown-ish style with section headers underlined with `---`. End with the Claude co-author footer:
```
Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
```

Example commit titles:
- `Milestone 2 Task O.2.5: constant-operand value extraction`
- `Audit O.2-cleanup #7: ...` (if more audit work)
- `Milestone 3 Task A: ...` (when starting next milestone)

### Code conventions

- **No `_` wildcard match arms** in subset/dispatch code. Use explicit variants with `todo!()` for unimplemented cases that should fail closed.
- **Doc-comments on every public item** (`#![warn(missing_docs)]` is active on pitbull-subset/pitbull-vc/pitbull-spec).
- **Forbid unsafe everywhere** (`#![forbid(unsafe_code)]` on every crate root).
- **`unwrap_used` and `expect_used`** are clippy::warn. Justify each `.expect()` with a comment.
- **Source style is compact** — DO NOT run `cargo fmt --all` or auto-format. The file structure is intentionally dense.

---

## Appendix: Where to find specific things

| Looking for... | Look in... |
|---|---|
| The 76 PSS-1 rule definitions | `crates/pitbull-subset/src/rules.rs` |
| Per-rule rationale + status | `docs/PSS-1.md` (long) |
| The exhaustive MIR visitor dispatch | `crates/pitbull-subset/src/visitor.rs` |
| Shadow IR types (Body, Span, Operand, etc.) | `crates/pitbull-subset/src/mir_api.rs` |
| The rustc_public adapter | `crates/pitbull-subset/src/mir_api/adapter.rs` |
| The HIR pre-pass for PB001 | bottom of `crates/pitbull-driver/src/bin/pitbull-rustc.rs` |
| Spec-language parser + translator | `crates/pitbull-subset/src/predicate.rs` |
| Audit-note channel | `crates/pitbull-subset/src/diagnostic.rs::AuditNote` |
| VC compile + dispatch | `crates/pitbull-vc/src/{vc,smt,solver}.rs` |
| Wrapper main logic | `crates/pitbull-driver/src/bin/pitbull-rustc.rs` |
| Cargo subcommand entry | `crates/pitbull-driver/src/main.rs` |
| Integration test corpus | `crates/pitbull-subset/tests/corpus/{accept,reject}/` |
| Integration test driver | `crates/pitbull-subset/tests/integration.rs` |
| CI workflow | `.github/workflows/ci.yml` |
| Example pitbull.toml | `pitbull.toml.example` (root) |

Good luck. The repo is in a clean, well-tested state. The audit work that just landed (six cleanup commits) closed every CRITICAL/HIGH finding from two red-team passes. Build forward with confidence — but always run the smoke test in Section 4 first.
