# Pitbull Hand-off — fresh-session instructions

This file is the entry point for a fresh Claude Code session
(or a human contributor) picking up the Pitbull deductive
verifier where the previous session left off. Read top to
bottom on first sit-down; refer back to individual sections
during work.

Last known-good commit at hand-off: **`7f6bdc2`** ("Audit
O.2-cleanup #6"). Branch `main`, local repo only (no remote).

## TL;DR

- **What it is:** Pitbull is a SPARK-style deductive verifier for Rust.
  v0.1 ships a PSS-1 subset enforcer; v0.2 adds the VC-generation
  spine and SMT dispatch (Z3 today). See `docs/PSS-1.md` for the
  specification.
- **State:** 122 tests passing, both lanes warning-clean. The
  Milestone-2 work (Tasks E through O.2 plus six audit-cleanup
  commits) is done.
- **Next task:** **O.2.5** — extract numeric values from
  `ConstOperand` so `fn add_one(x: u32) -> u32 { x + 1 }` with
  `requires(x < 100)` proves `unsat`.
- **First commands to run in a fresh session:** see
  [Section 4: Smoke test in a fresh session](#4-smoke-test-in-a-fresh-session).

---

## Table of contents

1. [Repository state](#1-repository-state)
2. [Architecture overview](#2-architecture-overview)
3. [Toolchain + system requirements](#3-toolchain--system-requirements)
4. [Smoke test in a fresh session](#4-smoke-test-in-a-fresh-session)
5. [Next task: O.2.5 — micro-step instructions](#5-next-task-o25--micro-step-instructions)
6. [Common commands cheat sheet](#6-common-commands-cheat-sheet)
7. [Known limitations + remaining work](#7-known-limitations--remaining-work)
8. [Common pitfalls + Windows quirks](#8-common-pitfalls--windows-quirks)
9. [Editor identity + commit conventions](#9-editor-identity--commit-conventions)

---

## 1. Repository state

### Recent commit log (newest first)

```
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
| `cargo +stable test --workspace --all-features` | **122 passing**, 0 failed, 0 ignored, 0 warnings |
| `cargo +stable check --workspace --all-features` | warning-clean |
| `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc` | warning-clean |

The 122 breaks down: 1 (spec) + 93 (subset lib) + 12 (integration) + 16 (vc) = 122.

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
# Expected: 7f6bdc2 Audit O.2-cleanup #6: final residuals...
```

### Step 4.2 — Stable test suite (the 122-test baseline)

```bash
cargo +stable test --workspace --all-features 2>&1 | grep "^test result"
# Expected: five lines all "test result: ok. N passed" totaling 122
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
pitbull-rustc: vc pb049-add-0: undischarged (no solver)
pitbull-rustc: VC summary: 1 obligation(s), 0 discharged, 1 undischarged
pitbull-rustc: crate analyzed: 1 items, 1 bodies walked, 0 non-fn items, 0 unsafe blocks, 0 subset violation(s)
```

If Z3 IS installed:
```
pitbull-rustc: vc pb049-add-0: NOT DISCHARGED (sat — counterexample exists)
pitbull-rustc: VC summary: 1 obligation(s), 0 discharged, 1 undischarged
```
(The lone obligation reports sat because there's no precondition constraining `x`; `x = u32::MAX` is a witness.)

### Step 4.6 — Optional: full e2e with PITBULL_REQUIRE_E2E

```bash
PITBULL_REQUIRE_E2E=1 cargo +stable test --workspace --all-features -- --test-threads=1
# Expected: all integration tests run (none gracefully skipped). Still 122 passing.
```

If any of these steps fail, the project state is degraded. Don't proceed to new tasks until baseline is green.

---

## 5. Next task: O.2.5 — micro-step instructions

**Goal:** Extract numeric values from `ConstOperand` so the SMT problem can constrain constant operands. Today, `fn add_one(x: u32) -> u32 { x + 1 }` with `requires(x < 100)` returns `sat` because `rhs` is unconstrained (the constant `1`'s value isn't pinned in SMT). After O.2.5, `rhs` will be pinned to `1` and the obligation discharges as `unsat`.

**Why this matters:** This is the headline demo of the v0.2 spec-context-narrowing work. Without O.2.5, even properly-annotated code can't be proven safe by the verifier.

### Step 5.1 — Read the current adapter behavior

Read `crates/pitbull-subset/src/mir_api/adapter.rs` lines 411-432 — the `const_operand` function. Today it:
- Extracts `path` and `def_id` for `FnDef`-typed constants
- Sets `def_id = None`, `path = None` for everything else

The integer value of `1u32` (or any literal const) is NOT extracted into the shadow `ConstOperand`.

### Step 5.2 — Decide on the shadow field

Add `pub value: Option<i128>` to `mir_api::ConstOperand`. Rationale:
- `i128` covers every supported primitive integer (u8..u128, i8..i128) with one slot, similar to how `predicate::Predicate.lit` works.
- `Option` makes "not a known integer constant" explicit (e.g. a `FnDef` constant, a struct constant, etc.).
- Don't try to support floats / non-primitive constants yet — the SMT encoder doesn't support them.

Open `crates/pitbull-subset/src/mir_api.rs` and add the field to `pub struct ConstOperand`. Update doc comment.

### Step 5.3 — Update every `ConstOperand` construction site

Search for `ConstOperand {` in the workspace:
```bash
grep -rn "ConstOperand {" crates/ --include='*.rs' | grep -v target
```

Expected sites:
- `crates/pitbull-subset/src/mir_api.rs` (the struct definition; add the field there).
- `crates/pitbull-subset/src/mir_api/adapter.rs` (the `const_operand` function; populate from rustc_public).
- All test bodies in `crates/pitbull-subset/src/visitor.rs` (~12 sites that construct synthetic ConstOperands).
- `crates/pitbull-subset/src/reachability.rs` (helper construction sites).

For each test site, default `value: None`. For the adapter, extract the value.

### Step 5.4 — Implement value extraction in the adapter

In `adapter::const_operand`, after the existing `(def_id_opt, path_opt)` match, add a new extraction block:

```rust
let value = extract_integer_value(c);
```

Where `extract_integer_value` does:
1. Check `c.const_.ty()` is an integer primitive type.
2. Use `c.const_.try_eval_target_usize(...)` or the appropriate const-eval API to get the value.
3. Return `Some(i128)` if a value was extracted, else `None`.

Look at rustc_public's `MirConst` API for the exact function — likely `try_to_uint()` returning `Option<u128>` or similar. The right path needs investigation; spawn an Explore agent to find the exact API.

### Step 5.5 — Constrain constant operands in the SMT problem

In `pitbull-vc/src/smt.rs::emit_overflow_problem_with_assumptions`, after the variable declarations, accept a new parameter `operand_values: &[(OperandPos, i128)]` (or similar) that pins constant operand values:

```rust
for (pos, value) in operand_values {
    let label = pos.smt_label();  // "lhs" or "rhs"
    let bv = format_bv_literal(*value, bits);
    smt.push_str(&format!("(assert (= {label} {bv}))\n"));
}
```

This is structurally the same as how user assumptions get spliced — just a new internally-generated set.

### Step 5.6 — Plumb the values from the visitor

The visitor's `maybe_emit_overflow_obligation` knows the operands. For each `Operand::Constant(c)` with `c.value.is_some()`, record `(position, value)`. Pass to `VcObligation` (new field? or fold into compile-time encoding via a method on the obligation).

Two design options:
- **A**: Add `pub operand_values: Vec<(OperandPos, i128)>` to `VcObligation`. Visitor populates. `compile()` uses.
- **B**: Encode operand values DIRECTLY into the `assumptions` field as SMT-LIB strings. No new field. Visitor synthesizes the assertions.

Option B is simpler (no new field, no new types) but mixes spec assumptions with operand pinning. Option A is cleaner architecturally but bigger surface area.

**Recommendation: option B.** The `assumptions` field is already a Vec<String> of SMT-LIB assertions; adding operand-pinning assertions to it is the path of least friction. The visitor adds entries like `"(assert (= rhs #x00000001))"` alongside any spec-derived ones.

### Step 5.7 — Tests

Add at least:

1. **Adapter unit test (or shadow test)**: a synthetic body with `Operand::Constant(ConstOperand { value: Some(1), ... })` flows through `maybe_emit_overflow_obligation` producing an obligation whose assumptions include `(assert (= rhs ...))`.
2. **End-to-end smoke**: `fn add_one(x: u32) -> u32 { x + 1 }` with `[verification.preconditions] "corpus_test::add_one" = ["x < 100"]` produces a VC that — when Z3 is installed — returns `unsat`. The wrapper's stderr should contain "discharged (unsat — safety property holds)".

### Step 5.8 — Verify

```bash
cargo +stable test --workspace --all-features 2>&1 | grep "^test result"
# Expected: ~125 passing (was 122; adding ~3 new tests)
```

### Step 5.9 — Commit

Use the standard pattern (see Section 9). Suggested message: `"Milestone 2 Task O.2.5: constant-operand value extraction (proves add_one safe under preconditions)"`.

### Step 5.10 — Update PSS-1.md

Add a §17.1 entry for O.2.5. Mirror the existing audit-cleanup entry format.

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
| z3 PATH trust | Z3 binary on PATH could be a hostile substitute always returning `unsat`. | `pitbull-vc/src/solver.rs::invoke_z3` | Mitigation is the planned multi-solver agreement gate (CVC5 + Alt-Ergo). v0.2 posture is "research-grade." |
| u32 file-hash collisions | `Span::file` is a u32 hash. At ~65K files, 50% collision probability. | `pitbull-subset/src/mir_api/adapter.rs` (and `mir_api.rs::Span`) | Bumping to u64 ripples through the shadow IR. Tracked. |
| Constant operand extraction (O.2.5) | The `1` in `x + 1` isn't constrained in SMT. | adapter::const_operand | **This is the next task** — see Section 5. |
| Path-sensitive symbolic exec | PB043 PanicReachability obligations are emitted but `pitbull-vc::compile` returns None for the kind. | `pitbull-vc/src/vc.rs::compile` | The SMT encoding for "panic site is unreachable" requires path-sensitive analysis — multi-week task. |
| Termination measures (PB041) | Recursion-decreasing obligations not yet emitted. | visitor + vc | Needs call-graph SCC analysis, currently a documented gap. |
| Bounds checks (PB054) | Index obligations emitted but not compiled. | vc compile | Needs `idx < len` reasoning over MIR local state. |

### UX / quality work

| What | Where | Priority |
|---|---|---|
| F7 regression corpus test | `crates/pitbull-subset/tests/corpus/accept/PB001_macro_expansion.rs` | MEDIUM. Smoke-verified manually; pinning requires a corpus file walked through the nightly wrapper. |
| Clippy cleanup | workspace-wide | LOW. 60+ pre-existing warnings; not gated in CI. |
| Mutation testing harness wiring | `pitbull-subset/src/mutation.rs` | MEDIUM. Module exists; cargo-mutants integration is the missing piece. |
| Corpus expansion | `tests/corpus/{accept,reject}/` | LOW (ongoing). Want ≥10 reject + ≥5 accept per rule per PSS-1 §15. |
| `cargo pitbull check` subcommand wires verdict aggregation | `pitbull-driver/src/main.rs` | MEDIUM. Subcommand exists but uses status.success() rather than per-crate Pitbull output. |
| Documentation: per-rule rationale | `docs/PSS-1.md` | LOW. Each of the 75 rules has a description; some lack the "why" explanation. |

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
| The 75 PSS-1 rule definitions | `crates/pitbull-subset/src/rules.rs` |
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
