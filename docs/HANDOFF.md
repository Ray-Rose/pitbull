# Pitbull Hand-off — fresh-session instructions

This file is the entry point for a fresh Claude Code session
(or a human contributor) picking up the Pitbull deductive
verifier where the previous session left off. Read top to
bottom on first sit-down; refer back to individual sections
during work.

Last known-good commit at hand-off: the latest on `main` — run
`git log -1`. The most recent milestone is **Task S** (multi-solver
2-of-N agreement gate); the prior one is **`51c99e5`** (Task R,
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
- **State:** 343 tests passing (190 subset-lib + 77 vc + 54 integration + 11 aorte_proofs + 11 driver-bin),
  both lanes warning-clean, clippy error-clean. Done:
  the v0.2 deductive backend (Tasks M + N), spec-context narrowing
  (O.1 → O.2 → O.2.5 → O.3), full PB054 discharge (P / P.1 / P.2),
  and **Option C complete** — the predicate-grammar
  `<ident> <cmp> <ident>` extension (Phase B), `#[pitbull::trusted]`
  (Q.1, with the adapter fix for real `is_unsafe`/`is_async`),
  impl-method attribute extraction (Q.2), expression-form
  attributes (Q.3), and `#[pitbull::ensures]` (Q.4 emission + **Q.4a
  SMT discharge** of copy/constant straight-line bodies). Plus deep-audit
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
  PB076 (ensures postcondition) now DISCHARGES too — Q.4a (copy/constant
  bodies) + Q.4b (wrapping `Add`/`Sub`/`Mul`) + Q.4c (`Div`/`Rem` via
  bvsdiv/bvudiv/bvsrem/bvurem) + Q.4d (shifts `bvshl`/`bvlshr`/`bvashr`),
  so `add_one`, `safe_div`, `halve` discharge; bitwise ops + variable
  narrower-width shift amounts remain. PB043 / PB041 still emit obligations that `compile` returns
  `None` for (reported "pending"). The other ~71 rules are syntactic
  visitor rejects.
- **Next task (recommended):** Task R closed the division/over-shift
  AoRTE hole; **Task S closed the loudest TCB hole** — a single
  hostile/buggy `z3` on PATH can no longer rubber-stamp unsafe code,
  because discharge now requires `threshold` independent solvers to
  agree `unsat` with zero `sat` votes (default `[z3, cvc5]`,
  threshold 2; a sat/unsat split is a loud `DISAGREEMENT` that fails
  closed). **Task T (proof certificates + `replay`) now has a working
  MVP** (T.1 data model + T.2 emission + `cargo pitbull replay`): the
  wrapper writes a replayable certificate bundle (one entry per
  main-check obligation) to `PITBULL_CERT_OUT`, and `cargo pitbull
  replay <cert.json>` re-runs each recorded SMT through the solver pool
  and confirms the agreement verdict reproduces — on STABLE Rust (no
  nightly needed). This is the differentiator no competing Rust
  verifier ships. The remaining highest-leverage moves:
  1. **Task T.3 — cryptographic signing** of certificates (the
     "signed solver outputs" provenance layer; deliberately deferred —
     no crypto dep today), plus certifying the consistency-refused /
     pending obligations (currently only main-check decisions get a
     cert).
  2. ✅ **Q.4a–Q.4d ensures SMT discharge** — DONE (2026-05-29 →
     2026-05-31): PB076 discharges copy/constant bodies (Q.4a), wrapping
     `Add`/`Sub`/`Mul` through the checked-add MIR (Q.4b), and `Div`/`Rem`
     (Q.4c — `bvsdiv`/`bvudiv`/`bvsrem`/`bvurem`; signed `%` is `bvsrem`
     NOT `bvsmod`, verified vs Z3); `add_one` and `safe_div` discharge
     end-to-end. Verified adversarially (TRUE→unsat, FALSE→sat,
     uncapturable→pending) via unit (exact-SMT) + Z3-gated e2e tests, plus
     an independent soundness review (Q.4d shifts added 2026-05-31:
     `bvshl`/`bvlshr`/`bvashr`, constant + same-type amounts). Remaining:
     variable narrower-width shift amounts (zero-extend + their own
     declaration), bitwise ops, and the **mixed-width over-shift PB049
     encoding** (Task R deferred `u32 << u8`; same-type shifts today).
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
d439bbe Wire end-to-end AoRTE differential (wrapper verdict gates the fuzz)
d801178 Fix CRITICAL false discharge: panicking slice/str methods silently accepted
09aecbc Empirical AoRTE soundness net: property-test harness (first increment)
b4297f4 Close library-panic residual: range-index + split_at/chunks
3d26d72 docs: refresh commit-hash references after history identity rewrite
d791197 Deep-audit self-review: fix cross-crate false-positive + catch method-form overflow
7f20f26 M1: fold coverage-gap audit notes into the exit code (no silent skips)
4861ebf Cross-crate reachability aggregation (whole-workspace gate)
19ad8b9 Audit: catch unwrap/expect false-discharge + adapter accept-on-unknown
06e86a9 #27 drop-glue: fail closed on Drop reached via drop-glue under narrowing
bef6478 Discharge variable mixed-width shifts (safe subset) under preconditions
73c24b5 #25: discharge mixed-width over-shift + close its fail-open
927e628 Enforce FFI surface (PB056/057/058); reclassify PB016 as covered
69644ab Close coverage-gap audit: enforce PB003 (unsafe impl/trait)
7bfda25 Harden #27: fail closed on in-crate callees skipped by verify_roots
b9739e9 Fix CRITICAL fail-open: rustc_public bridge failure could exit 0
f646492 Fix PB051-on-shift: exempt value-preserving constant int casts
4a424d0 Fix CI nightly-e2e: run the REAL wrapper + don't panic without cvc5
bf51a7b Harden corpus accept-check; fix mislabeled accept files (audit 2026-05-31)
e4fa2cb Fix HIGH fail-open: config policy violations ignored by the exit code
772ce36 Fix CRITICAL false-discharge: precondition referencing `result` (PB076)
0bdd6de Milestone 2 Task Q.4d: discharge #[pitbull::ensures] over shifts
8969ac6 Milestone 2 Task Q.4c: discharge #[pitbull::ensures] over Div/Rem
01ad538 Milestone 2 Task Q.4b: discharge #[pitbull::ensures] over wrapping arithmetic
ac787c0 Milestone 2 Task Q.4a: discharge #[pitbull::ensures] (PB076) via SMT
ae8a29b Unit-test + DRY the solver-version-pin and unmatched-precondition checks
6d81891 PB059: enforce the proc-macro allowlist (reject non-allowlisted reachable derives/attrs)
ca2eccf Red-team T.3/hardening fixes: from_hex panic (HIGH), probe_version timeout, +Lows
9b9afc4 docs: refresh test count to 219 + record T.3 signing / red-team / hardening
01e41ed Hardening: enforce solver_versions pins + warn on unmatched precondition keys
d0d3062 Task T.3: HMAC-SHA256 certificate signing (closes swapped-SMT + threshold tamper)
6b3a7f4 Red-team Task T fixes: empty-bundle exit-0, internal consistency, timeout, size cap
cac9cf6 Task T.2: emit proof certificates from the wrapper + `cargo pitbull replay`
29f7bd7 Task T.1: proof-certificate data model + replay logic (pitbull-vc)
a8e700a Audit fix (CRITICAL): unary negation overflow was silently unobligated
19c7aa8 Task S audit: fix consistency-check fail-open + duplicate-solver vote inflation
bc38c42 Task S: multi-solver N-of-M agreement gate (closes single-solver TCB hole)
51c99e5 Task R: division-by-zero / over-shift obligation encoding (closes AoRTE gap)
12e8c82 docs: refresh drift flagged by full-codebase audit (counts, Q-series, PB076)
55a80fe Audit-cleanup: close silent-skip soundness gaps in foundational code
c80ae81 Audit-cleanup post-Q: close M-1, M-2, L-1, L-2 from 4-agent deep audit
b31f3c8 Task Q.4 MVP: #[pitbull::ensures("...")] postcondition obligations
11496fc Audit-cleanup pass after Q.1-Q.3: close M-RT-Q.A through M-RT-Q.D + doc refresh
f3556d9 Task Q.3: expression-form #[pitbull::requires(x < 100)] without quotes
d3682f6 Task Q.2: extract #[pitbull::requires] and #[pitbull::trusted] from impl methods
```

### Test invariant

| Lane | Status |
|---|---|
| `cargo +stable test --workspace --all-features` | **343 passing**, 0 failed, 0 ignored, 0 warnings |
| `cargo +stable check --workspace --all-features` | warning-clean |
| `cargo +stable clippy --workspace --all-features --all-targets` | clippy-clean (no `error:` lines) |
| `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 clippy -p pitbull-driver --bin pitbull-rustc` | clippy-clean (lints the `cfg(rustc_public_real)` dispatch path) |
| `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc` | warning-clean |

The **343** breaks down: 4 (cargo-pitbull bin) + 7 (pitbull-rustc bin) + 190
(subset lib) + 54 (integration) + 11 (aorte_proofs) + 77 (vc) = 343 (the
2026-06-15 re-audit added +10 over the prior 332; see the dated subsection at
the end of §1). This supersedes the long
Task-S-era narration that previously lived here (which still said "226" while
the table said 277 — a drift caught and corrected in the 2026-06-14 deep
audit). The lineage to today's number: the multi-solver agreement gate (Task
S) and its red-team hardening (the `vote()` policy cases + the
duplicate-solver / consistency-check CRITICAL fixes), the unary-negation
missed-obligation CRITICAL (`-(iN::MIN)` now obligated), the proof-certificate
arc (Task T.1/T.2/T.3 incl. HMAC-SHA256 signing and the `from_hex` HIGH),
PB059 proc-macro allowlisting, the mixed-width-shift discharge (#25), and the
drop-glue fail-closed reachability gate (#27). The most recent **+22 subset
tests** (154→176) are the 2026-06-14 deep audit, which landed four soundness
fixes (plus the cross-crate aggregation and the M1 exit-code work below).
(1) The adapter **accept-on-unknown** hole (+7): `classify_adt` now
classifies the rustc_public adapter's synthetic `__pitbull_*` placeholder ADTs
explicitly and fails closed on unknown synthetics (`__pitbull_never` stays
benign; the dyn/coroutine/foreign/unrigid placeholders reject), rather than
letting them reach the user-ADT accept fall-through. (2) The
**reachability-integrity / panic-bearing-library-call** fix (+4, plus the new
`reject/PB043_unwrap_panic.rs` corpus file): `Option`/`Result::unwrap`/`expect`
were SILENTLY ACCEPTED — a CRITICAL false-discharge on `x.unwrap()` — because
the panic lives in un-walked `core` and the call fell through
`classify_called_function`'s "assume walked elsewhere" arm (whose reachability
driver is the dead `#[cfg(test)]` reference). They are now caught at the call
site (`is_panicking_library_call`) and routed through PB043 (strict reject /
default pending obligation); verified e2e on real MIR via the corpus file. The
analyzed-vs-trusted boundary this exposed is now documented in
`SAFETY-MANUAL.md` §3.6. That same audit also restored the clippy-error-clean
invariant (a pre-existing collapsible-`if let` in
`reachability.rs::callee_paths` had drifted to an `error:` under the current
toolchain). (3) **Cross-crate reachability aggregation** (+6): `ReachManifest`
+ `cross_crate_unverified` (the whole-workspace companion to the per-crate
`#27` gate) — each wrapper run emits a manifest into `PITBULL_REACH_DIR`,
`cargo pitbull check` aggregates them via `cargo metadata` and fails closed on
a workspace-member callee no crate verified (warm-cache-safe via an
INDETERMINATE bucket). (4) **M1 coverage-gap exit-code** (+5 subset, +2
driver): `AuditNoteKind::{CoverageGap,Transparency}` — a safety check that
could not run with no compensating obligation now folds into the exit code
(fail closed, gated on `verification.fail_on_coverage_gaps`, default true), so
exit 0 can't mean "verified except the parts I couldn't model". See
`docs/PSS-1.md` §17.1 for the per-fix detail.

### 2026-06-15 deep re-audit + Track A hardening (this session)

A fresh whole-codebase audit (five independent fronts: a line-by-line read of
the VC→SMT→`vote`→exit-code path plus four parallel agents over visitor,
adapter+reachability, predicate+config, and cert+subcommand) **re-confirmed the
core soundness claim** — no false-discharge path in the proof core; SMT polarity
exact; `vote` / consistency-gate / wrapper exit-code all fail-closed. The prior
capstone's "zero findings" framing did NOT survive, though: a real cluster of
gaps sat in the **artifact + aggregation + provenance layer** (not the proof
core). Fixed this session, all fail-closed, none changing what discharges:

- **Certificate is now a COMPLETE coverage ledger** (was: silently only the
  discharged subset — the F3 finding, the one place exit-0 could outrun proof at
  the artifact level). `CertificateBundle` gained `total_obligations` +
  `uncertified[]` (`CERT_FORMAT_VERSION` → **2**); the wrapper records every
  pending / consistency-refused / consistency-unconfirmed obligation;
  `from_json` rejects a ledger that doesn't add up; `cargo pitbull replay`
  exit-0 now requires `attests_full_verification`, so a clean replay of a
  partial bundle no longer implies "crate verified".
- **`ReachabilityDriver` de-trapped.** Its `None`-body arm records a CoverageGap
  (was a silent `continue`); the doc no longer mis-advertises it as a
  production-ready "COMPLETE" walk (it is a test-only reference still missing the
  drop-glue + cross-crate gates the wrapper has).
- **`cargo pitbull replay` strict signing** (`PITBULL_REQUIRE_SIGNED`): an
  unsigned / unverifiable certificate fails closed (exit 2).
- **`cargo pitbull check --strict`** fails closed on warm-cache INDETERMINATE
  cross-crate coverage (was a note); **exit-2 fidelity** now distinguishes
  "could-not-run" (exit 2) from "found problems" (exit 1).
- **F7 (a build.rs overriding `PITBULL_TOML`) was already mitigated** —
  `load_config` applies `check_env_path` (traversal/extension/symlink) to the
  env value; the residual (a well-formed absolute permissive `.toml`) is
  inherent to env-config and is covered by the PB073 hermetic-build obligation.
  No code change (the audit agent overstated this one — verified against source).

Pure soundness-decision helpers added (mirroring `decide_pitbull_exit_code`):
`replay_exit_code`, `signing_policy_ok`, `check_exit_code` — all unit-tested.

**Red-team follow-up (same day, separate commit).** Two adversarial agents
re-attacked the two commits above. The soundness agent found NO new
false-discharge path (every partial/legacy/mismatched/unsigned bundle fails
closed behind two gates; the producer ledger is provably exact); the security
agent confirmed the HMAC/ledger crypto is sound (the new fields ARE under the
MAC). Four findings were then closed (+1 test → 343):
- `attests_full_verification` returns false for a zero-obligation bundle —
  defense-in-depth vs a future caller lacking `replay`'s empty-guard.
- The reachability-manifest temp dir is created **EXCLUSIVELY** (unpredictable
  name + `create_dir`, never reusing a pre-existing dir): closes a shared-host
  manifest-injection lever where a co-tenant could pre-create
  `pitbull-reach-<pid>` and suppress a real cross-crate gap (verdict-flip).
- `PITBULL_REACH_DIR` now passes `check_env_path` (traversal/symlink) like the
  other env paths (`check_env_path` gained an empty-extension "directory" mode).
- The cert-written log reports the full ledger (total / certified / uncertified).

Residuals accepted as covered by the PB073 hermetic-build obligation:
`PITBULL_TOML` / `PITBULL_CERT_KEY` env injection (the cert-key path is
read-amplification, not a leak — the key is never echoed). Remaining (P2, LOW):
the `Rvalue::Repeat` inert-count comment; a `capture_shift_amount`
constant-mask pin test; intermediate-symlink / Windows-junction path notes.

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
| Z3 + CVC5 SMT solvers | Z3 4.x, CVC5 1.x | Needed for discharge — the default gate is 2-of-2 over `[z3, cvc5]`. Without them, obligations report "undischarged (no solver)" (still sound, fail closed). **Installed on this machine 2026-06-15** (Z3 4.16.0 + CVC5 1.3.4 under `%USERPROFILE%\smt-tools`, on user PATH). Install via the official GitHub release zips (`Z3Prover/z3`, `cvc5/cvc5`) — NOTE `winget install Microsoft.Z3` does NOT exist; macOS `brew install z3 cvc5`; Debian `apt install z3` (+cvc5 from releases). See §5.1. |
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
# Expected: the latest commit on `main` (the tip moves every session; do
# not pin a specific hash here). See the recent-commit-log block in §1.
```

### Step 4.2 — Stable test suite (the 332-test baseline)

```bash
cargo +stable test --workspace --all-features 2>&1 | grep "^test result"
# Expected: "test result: ok" lines totaling 332 passing, 0 failed, 0 ignored
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
# Expected: all integration tests run (none gracefully skipped). Still 332 passing.
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

### Step 5.1 — Install Z3 + CVC5

The default agreement gate is **2-of-2 over `[z3, cvc5]`**, so BOTH are needed
to observe an actual `unsat`→discharged verdict (without them the wrapper
reports "undischarged (no solver)" everywhere — still sound, fail closed).

**Already installed on this machine (2026-06-15):** Z3 **4.16.0** + CVC5
**1.3.4**, unzipped under `%USERPROFILE%\smt-tools\` and added to the user
PATH — new shells get `z3` / `cvc5` directly.

Reinstall (Windows): **`winget install Microsoft.Z3` does NOT work** (no such
winget package as of 2026-06). Use the official GitHub release zips —
`z3-<ver>-x64-win.zip` from `Z3Prover/z3/releases` and
`cvc5-Win64-x86_64-static.zip` from `cvc5/cvc5/releases` — unzip each and put
its `bin/` on PATH (the release-asset URLs are resolvable via
`https://api.github.com/repos/{Z3Prover/z3,cvc5/cvc5}/releases/latest`).
macOS: `brew install z3 cvc5`. Debian/Ubuntu: `apt install z3` (+ cvc5 from
the cvc5 releases). Verify: `z3 --version && cvc5 --version`.

**VERIFIED 2026-06-15 (Track B — first real discharge on this machine):** with
both solvers on PATH the headline demo discharges for real — `add_one` under
`#[pitbull::requires("x < 100")]` →
`discharged (unsat — safety property holds; 2-solver agreement) [z3=unsat
cvc5=unsat]`, exit 0; the SAME fn with NO precondition is correctly REFUSED
(`NOT DISCHARGED (sat — counterexample exists)`, exit 1). The full e2e + aorte
suite passes WITH solvers under `PITBULL_REQUIRE_E2E=1` (so nothing skips). One
test was fixed in the process — `mixed_width_const_shift_emits_obligation_not_silent_pass`:
its exit-code guard matched the substring `"undischarged"` inside the
`"0 undischarged"` summary and wrongly demanded exit 1 when the safe `x << 4`
(4 < 32) legitimately discharges; it now branches on the per-obligation verdict.

### Step 5.2 — Run the headline demo end-to-end

With Z3 installed, the existing tests
`solver::tests::pinned_inputs_proves_no_overflow` and
`integration::wrapper_proves_add_one_safe_under_precondition`
should exercise the actual solver path:

```bash
cargo +stable test --workspace --all-features
# Expected: 332 passing (same as without Z3 — the new tests
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
| solver PATH trust | A solver binary on PATH could be a hostile substitute always returning `unsat`. | `pitbull-vc/src/solver.rs::{run_solvers,vote}` | **Mitigated (Task S + 2026-05-29 audit):** discharge requires `threshold` *distinct* solvers (default `[z3, cvc5]`, threshold 2) to agree `unsat` with zero `sat`; one corrupt solver yields at most `Inconclusive`, and a `sat`/`unsat` split is a loud `DISAGREEMENT`. `vote` counts distinct solver names and the driver dedups the pool, so a duplicate config entry (`["z3","z3"]`) cannot inflate the vote. The precondition consistency check fails closed unless `threshold` solvers confirm satisfiability, so a timed-out/errored consistency check cannot yield a vacuous discharge. `[verification.solver_versions]` pins are now enforced — a solver whose `--version` doesn't match its pin is dropped from the pool (fail-closed). Residual: a coordinated swap of ALL distinct solvers to the pinned versions. |
| u32 file-hash collisions | `Span::file` is a u32 hash. At ~65K files, 50% collision probability. | `pitbull-subset/src/mir_api/adapter.rs` (and `mir_api.rs::Span`) | Bumping to u64 ripples through the shadow IR. Tracked. |
| Constant operand extraction (O.2.5) | ✅ DONE in `0d52ae1`. Adapter now extracts integer values via `try_extract_integer_value`; visitor synthesizes `(assert (= rhs #x...))` pinning assertions. Sign-extension fix in `a930691`. | — | Closed. |
| `#[pitbull::requires]` attribute extraction (O.3) | ✅ DONE in `719dba8`. HIR pre-pass extracts string-literal arguments from `#[pitbull::requires("...")]`; merged with `pitbull.toml`-based preconditions. Verdict lines now include `[N assumption(s)]` suffix. | — | Closed. |
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

Fixed in `506563a`. If you write new integration tests in `crates/pitbull-subset/tests/integration.rs`, the helper `run_one_corpus_file_full` now uses `TEMP_FILE_COUNTER` to uniquify temp filenames. Don't reintroduce pid-only filenames.

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

This happens when you use `git add -A`. The `.claude/` directory is now in `.gitignore` (since commit `5862f34`), so it won't happen automatically. If it does, `git rm --cached .claude/settings.local.json` and commit.

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
