# Pitbull Hand-off — fresh-session instructions

This file is the entry point for a fresh Claude Code session
(or a human contributor) picking up the Pitbull deductive
verifier where the previous session left off. Read top to
bottom on first sit-down; refer back to individual sections
during work.

Last known-good commit at hand-off: the latest on `main` — run
`git log -1`. The most recent milestone is **call-site precondition discharge,
Increment 3** (2026-08-08, rule PB077 still — see the dated subsection at the
end of §1): extends Increment 2 to a call site whose actual is a COMPUTED
EXPRESSION (`v + 1`) over constants and/or the caller's own parameters,
traced back through the caller's own straight-line statements —
`fn caller(v: u32) { let t = v + 1; safe_div(10, t) }` under a caller
contract bounding `v` now DISCHARGES too. **The design needed a real
mid-course correction**: the first draft only walked the call's own basic
block and gapped the very first real-wrapper probe, because real MIR lowers
`v + 1` to `AddWithOverflow` (a `(u32, bool)` tuple) in ONE block with the
sum read back out via a SEPARATE `_2 = move (_3.0)` statement in the block
the overflow-check `Assert` jumps to — confirmed by dumping real MIR with
`rustc -Z unpretty=mir` before touching the code again. Fixed by reusing
`capture_body_effect`'s exact `Goto`/`Assert`-chain traversal (the same
machinery `#[pitbull::ensures]` already uses) instead of a bespoke
same-block walk, and by writing every capture into BOTH the `env` AND
`checked` maps (not just `env`) so a later `.0`-of-tuple read resolves too.
A value behind an actual BRANCH is still correctly refused — the boundary
`capture_body_effect` itself already draws. Same F1 vacuity guard as before,
re-confirmed through the new expression path. **This session also
independently audited, then committed, Increment 1, then designed and
shipped Increment 2** — the prior session had shipped Increment 1 in code
(391→411 tests) but left it uncommitted for three days; this one
re-verified it by hand before committing as `5cfd10a`, then built and
shipped Increment 2 (`8fb9df2`, 411→424 tests), then Increment 3 (424→437
tests), all in one continuous session at the user's repeated "keep moving
forward". The prior milestone is **call-site precondition discharge,
Increment 2** (2026-08-07): extends Increment 1 to a call site whose actual
is a BARE read of the CALLER's own parameter (no computation), linked to
the callee's parameter and constrained by whatever the caller's own
precondition set establishes about it. The milestone before that is
**call-site precondition discharge, Increment 1** itself (2026-08-03): the
first completeness increment since WS-3, closing the open half of the
2026-07-09 modular-verification finding — a call whose CONSTANT actuals
satisfy the callee's contract discharges (`safe_div(10, 5)` verifies) and one
that violates it is refuted with a counterexample (`safe_div(10, 0)`), where
both were previously the same fail-closed coverage gap. **That session also
found the local e2e lane silently dead** — the pinned nightly had been
uninstalled and the wrapper binary was absent, so all 58 wrapper tests were
taking their graceful-skip path and the suite was green on shadow IR alone.
Check §4 first in any fresh session for exactly this reason. The prior
milestone before that is the **2026-07-18 trait-dispatch soundness pass**, a
four-front
adversarial audit that found and closed **three more confirmed false discharges
— all previously-documented §7 residuals, now reproduced end-to-end and fixed**:
(A) a statically-dispatched trait-method CALL escaping the #27 reachability gate
under `verify_roots` narrowing (CRITICAL — an unproven trait-impl body reachable
from a verified root exited 0); (B) `#[pitbull::ensures]` on a trait-IMPL method
silently binding nothing (no PB076 emitted → exit 0 on a false postcondition,
because the HIR key `def_path_str` and the lookup key `name()` render trait
impls differently); (C) the same for a trait-DEFAULT method (no
`visit_trait_item` extractor existed at all). The prior milestone was the
**2026-07-15 four-front deep audit** (see its dated subsection), which found and
closed three false discharges outside the allow-list — the `verify_roots`
trait-impl matcher blindness (CRITICAL), fn-items passed as arguments escaping
the reachability gate (CRITICAL under narrowing), and the type-level rules being
dead on real std code (HIGH) — plus a solver-verdict hole where z3 reports an
error, drops the offending directive, and answers the REST of the problem. The prior milestone was the **2026-07-12 allow-list
div/rem false-discharge fix** (the `wrapping_`/`overflowing_`/`saturating_`
div/rem methods were trusted-as-total but panic on a zero divisor — evicted,
now PB043 pending; the sibling of the 2026-07-09 `clamp`/`sort` class), and
before that the **2026-07-09 deep-audit second pass** (`Ord::clamp` / sort-family false
discharges closed, call-site preconditions fail closed, `vote` threshold-0 +
forged-replay hole closed, warm-cache `check` fail-open closed). The v0.2 state ships the
deductive backend, full PB054 end-to-end discharge (P / P.1 / P.2),
the Option-C attribute suite (Phase B grammar, Q.1 trusted, Q.2
impl-methods, Q.3 expression-form, Q.4 ensures-MVP), the full
arithmetic AoRTE family (Task R), the **multi-solver agreement gate**
(Task S), proof certificates + replay + signing (Task T), and several
deep-audit cleanup passes. Branch `main`, with `origin` remote on GitHub.

## TL;DR

- **What it is:** Pitbull is a SPARK-style deductive verifier for Rust.
  v0.1 ships a PSS-1 subset enforcer; v0.2 adds the VC-generation
  spine and SMT dispatch through a **multi-solver agreement gate**
  (Z3 + CVC5 by default). See `docs/PSS-1.md` for the specification.
- **State:** 437 tests passing (226 subset-lib + 100 vc + 76 integration + 12 aorte_proofs + 5 allowlist-exhaustiveness + 18 driver-bin),
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
  narrower-width shift amounts remain. PB043 (panic reachability) and PB041
  (**direct self-recursion**, callee `DefId` == body `DefId`, as of Frontier
  #3 / 2026-06-16) emit obligations that `compile` returns `None` for
  (reported "pending"; never falsely discharged). Frontier #4 (2026-06-16)
  landed the PB043 *backend* SMT encoding — `smt::emit_panic_unreachability_problem`
  plus its mandatory vacuity guard, proven under z3 (reachable -> sat,
  unreachable -> unsat, contradictory-precondition -> unsat) — but it stays
  out of the live `compile` arm until the visitor captures the per-site path
  condition (the deferred path-sensitive core), so PB043 remains pending
  end-to-end with no false-discharge risk. **PB077 (call-site precondition)
  DISCHARGES too**, now over three increments: Increment 1 (2026-08-03)
  proves a call whose CONSTANT integer actuals satisfy the callee's
  `requires` clauses (`safe_div(10, 5)` verifies); Increment 2 (2026-08-07)
  extends this to a call whose actual is a bare read of the CALLER's own
  parameter, linked to the callee's parameter and constrained by whatever
  the caller's own precondition set establishes about it (`fn caller(v:
  u32) { safe_div(10, v) }` under `requires("v > 0")` — the forwarding-code
  shape); Increment 3 (2026-08-08) extends it again to a call whose actual
  is a COMPUTED EXPRESSION over constants and/or caller parameters, traced
  back through the caller's own straight-line (`Goto`/`Assert`-chained)
  statements — `fn caller(v: u32) { let t = v + 1; safe_div(10, t) }` under
  a caller contract bounding `v` now verifies too (the encoder had to
  follow the SAME block-splitting the overflow-check `Assert` already
  causes for `#[pitbull::ensures]`, or it would gap essentially every
  checked arithmetic expression — i.e. most real code — confirmed the hard
  way against the real wrapper before landing). Any violation is refuted
  with a counterexample; anything the encoder cannot bind soundly — a value
  behind an actual branch, raw-SMT clauses, `usize`, mixed widths, a
  bitwise op — keeps the pre-existing fail-closed coverage gap. A caller
  whose OWN preconditions are mutually contradictory does not get a free
  pass: the same F1 consistency-check dispatch every other obligation kind
  already used refuses the claim as vacuous, regardless of which increment
  reached it. The other ~72 rules are syntactic visitor rejects.
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
  1. ✅ **Task T.3 — cryptographic signing** of certificates — DONE.
     HMAC-SHA256 (`d0d3062`, symmetric, tamper-resistant within a
     trust domain holding the key) plus **Ed25519** (`2711f67`,
     frontier #2, asymmetric — a third party verifies with only the
     PUBLIC key, the "don't-trust-the-verifier" story), and
     `PITBULL_REQUIRE_SIGNED` makes an unsigned/unverifiable
     certificate fail closed at replay. (This bullet claimed
     "deliberately deferred — no crypto dep today" long after both
     landed; corrected 2026-07-15. The deps are real: `sha2`, `hmac`,
     `ed25519-dalek` in `pitbull-vc/Cargo.toml`.) **Still open:**
     certifying the consistency-refused / pending obligations —
     today only main-check decisions get a per-obligation cert, and
     the certificate records neither the consistency-check problem
     nor its verdicts, so replay cannot re-validate the vacuity
     guard (a bundle whose F1 check was wrongly answered `sat` at
     certification time replays as MATCH forever). LOW: it needs a
     threshold-wide sat-side solver bug, but it is the honest gap in
     "the certificate is a complete coverage ledger".
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
| `cargo +stable test --workspace --all-features` | **437 passing**, 0 failed, 0 ignored, 0 warnings |
| `cargo +stable check --workspace --all-features` | warning-clean |
| `cargo +stable clippy --workspace --all-features --all-targets` | clippy-clean (no `error:` lines) |
| `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 clippy -p pitbull-driver --bin pitbull-rustc` | clippy-clean (lints the `cfg(rustc_public_real)` dispatch path) |
| `PITBULL_USE_RUSTC_PUBLIC=1 cargo +nightly-2026-01-29 build -p pitbull-driver --bin pitbull-rustc` | warning-clean |

The **437** breaks down: 4 (cargo-pitbull bin) + 14 (pitbull-rustc bin) + 226
(subset lib) + 76 (integration) + 12 (aorte_proofs) + 5 (allowlist_exhaustiveness)
+ 100 (vc) = 437 (the 2026-08-08 call-site precondition Increment 3 added +13
over 424: 7 visitor unit tests for the expression-capture encoding —
single-hop, chained, two-caller-params, the Goto-chain traversal, the
branch boundary, and the contradictory-preconditions-via-expression
vacuity pin — and 6 e2e integration tests pinning discharge / an
insufficient / a chained / a branch-gapped / a two-parameter expression
and the contradictory-caller F1 refusal reached through an expression; the
2026-08-07 call-site precondition Increment 2 added +13
over 411: 8 visitor unit tests for the caller-parameter link/hypothesis/
consistency encoding — including the contradictory-caller-preconditions
vacuity pin — and 5 e2e integration tests pinning discharge / an
insufficient / an unconstrained caller contract, the contradictory-caller
F1 refusal, and self-offset method dispatch through a caller-linked actual;
the 2026-08-03 call-site precondition Increment 1 added +20 over
391: 10 PB077 encoder unit tests, 1 `int_type_info` decode test, 3
`callee_spec_preconditions` merge tests, 2 vc routing/serde tests, and 4 e2e
integration tests pinning discharge / refutation / argument binding / gap
fallback; the 2026-07-18 trait-dispatch soundness pass added +10 over
381: 3 reachability-gate tests for the trait-method-form augmentation, 4
`canonical_spec_key` tests, and 3 e2e integration tests pinning the trait-impl /
trait-default `ensures` binding and the trait-call reachability gate; the
2026-07-15 four-front audit added +13 over 368: 5 subset
soundness pins, 5 vc proof-core pins, 3 exhaustiveness-gate tests for the
non-integer surfaces; the 2026-07-13 exhaustiveness gate added +2 over 366; the
2026-07-09 deep audit added +4 soundness-pinning tests over the interim 362,
which itself grew from 343 via the red-team suite + trusted-total broadening
commits; see the dated subsections at the end of §1). This supersedes the long
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
**CAVEAT (2026-07-09): the PB073 hermetic-build obligation named above as the
compensating control is NOT implemented** (the config.rs comment claiming the
driver checks PB072/073/074 was corrected this session) — those env-injection
residuals are currently guarded only by `check_env_path` hygiene. See §7.

### 2026-07-09 deep audit, second pass (this session)

Four parallel adversarial audits (proof core; visitor + allow-lists;
adapter + reachability; driver + config + predicate) over the whole codebase;
every finding re-verified against source before fixing. Full detail in
`docs/PSS-1.md` §17.1 (dated entry). Fixed, all fail-closed (+4 tests → 366):

- **`Ord::clamp` false discharge (CRITICAL)** — trusted-as-total but panics on
  `min > max`; confirmed exit-0 end-to-end on real MIR pre-fix. Evicted from
  the allow-list; now a precise PB043 (pending). `sort`/`sort_unstable`
  likewise de-trusted (panic on non-total `Ord`, Rust 1.81+); `min`/`max`/
  `cmp`/`binary_search` stay trusted with negative controls pinned.
- **Call-site preconditions unproven (HIGH)** — `#[pitbull::requires]` was
  assumed in the callee but no call site ever proved it
  (`oops(){safe_div(10,0)}` verified). Every call to a precondition-carrying
  fn now records a fail-closed CoverageGap (`set_known_precondition_fns`),
  verified e2e. Real call-site SMT discharge is the tracked follow-up.
- **`vote(_, 0)` vacuous discharge + forged-certificate replay (HIGH)** —
  `vote` now clamps `threshold.max(1)`; `from_json` refuses `threshold == 0`
  at bundle and obligation level. A hand-forged unsigned `threshold:0` bundle
  could previously replay to exit 0.
- **Warm-cache `cargo pitbull check` fail-open (CRITICAL class)** — zero
  manifests (nothing recompiled ⇒ no analysis ran) exited 0 even under
  `--strict`, and a `pitbull.toml` change is never applied to cached crates.
  `--strict` now exits 2 (could-not-confirm); default warns loudly;
  `cargo pitbull verify` now runs strict.
- **Empty solver-version pin fail-open (LOW)** — `version_matches("...", "")`
  matched punctuation tokens; empty pins now refuse.
- **Honesty pass** — corrected overclaiming comments/docs: PB072/073/074
  "checked by the driver" (unimplemented), PB060 sha256 format-only,
  mutation.rs "CI ground truth" (unwired), visitor `Unreachable` "obligation
  emitted" (none exists), stale adapter is_unsafe contract note, README/
  SAFETY-MANUAL allow-list examples naming `clamp`.

### 2026-07-12 allow-list div/rem false-discharge fix (this session)

A follow-up per-method adversarial sweep of the `is_trusted_total_library_call`
allow-list — the same TCB surface the 2026-07-09 second pass evicted
`clamp`/`sort` from — found a **CRITICAL false discharge that pass missed**.
Full detail in `docs/PSS-1.md` §17.1 (dated entry). Fixed, fail-closed (test
count unchanged at 366; the two classification unit tests were extended and a
reject/accept corpus pair added):

- **Integer `wrapping_`/`overflowing_`/`saturating_` div & rem trusted-as-total
  (CRITICAL)** — `wrapping_div`, `wrapping_rem`, `overflowing_div`,
  `overflowing_rem`, `saturating_div`, and the `_euclid` kin all PANIC on a
  zero divisor (the wrap/saturate/overflow only tames `iN::MIN / -1`), but the
  broad `contains("::wrapping_")` / `::saturating_` / `::overflowing_` family
  globs swallowed them, so `x.wrapping_div(y)` verified (exit 0) while the
  operator form `x / y` was correctly obligated by PB049. The deny matcher
  `is_panicking_int_method` missed them (it enumerated only the plain
  `::div_euclid`/`::div_ceil`/… suffixes + `::strict_`). Now: deny matcher
  catches any of these three families ending in `_div`/`_rem`/`_div_euclid`/
  `_rem_euclid` → precise PB043 pending. That is the whole fix: the trust
  matcher already opens with a deny guard (`return false` for anything the four
  `is_panicking_*` matchers flag), so it stops trusting these automatically —
  no trust-matcher logic change needed. Total `checked_div`/`checked_rem` stay
  trusted (negative controls pinned).
- **Verified end-to-end on real MIR** with the rebuilt nightly wrapper:
  `x.wrapping_div(y)` → `pb043-panic-0 (PB043): pending` → exit 1;
  `x.checked_div(y).unwrap_or(0)` → zero obligations. Corpus pair
  `reject/PB043_div_rem_method_panic.rs` + `accept/PB043_div_rem_method_total.rs`
  pins both on the (SAC-free) CI Linux e2e lane.
- **Method note (Windows dev env):** the stable e2e integration lane (55
  wrapper-spawning tests) is blocked by Smart App Control (`os error 4551`) in
  this session and did not clear on re-run; the 308 non-e2e tests + the direct
  wrapper smoke above are the local evidence, with the corpus files carrying
  the CI e2e proof.

### 2026-07-13 integer allow-list exhaustiveness gate (this session)

The 2026-07-12 div/rem fix was the **second consecutive** audit to evict a
CRITICAL false discharge of one shape from `is_trusted_total_library_call`
(after 2026-07-09 `clamp`/`sort`): a broad allow-list glob trusting a panicking
member of a family it globs. Rather than wait for a third to surface live, this
session added a **structural regression gate** that ends the class for the
integer surface. New file `crates/pitbull-subset/tests/allowlist_exhaustiveness.rs`
(+2 tests → **368**):

- Enumerates **every member of each trust-granting integer family glob**
  (`::wrapping_`/`::checked_`/`::saturating_`/`::overflowing_`/`::unbounded_`/
  `::from_`/`::to_`, reviewed against the Rust 1.94 stdlib) plus the panicking
  plain-method families (`pow`/`abs`/`div_euclid`/`ilog*`/signed-`isqrt`/…).
- For each, asserts the classifier's verdict against a **runtime-anchored ground
  truth** — a probe that calls the method on an adversarial witness and observes
  whether it panics (`black_box`-ing the panic driver so it is a runtime event,
  not a const-eval one the deny-by-default `unconditional_panic` lint rejects).
  28 witnessed panics fire per run, so a *mislabel* (the exact misconception
  that plants these bugs) cannot pass silently.
- Per-entry invariant: `Panics ⟹ is_panicking_int_method` true AND
  `is_trusted_total_library_call` false (the soundness guard); `Total ⟹` the
  converse (no false reject). A future stdlib member added to a globbed family,
  or a widened glob, now fails this test instead of shipping as a false
  discharge.

Scope/limitation: the gate covers the **integer** allow-list families only. The
slice / `char` / `Option` / `Result` surfaces are enumerated by exact
`ends_with` (lower glob-risk) and are the natural follow-up to fold into the
same runtime-anchored harness. Stable suite green (368), clippy error-clean.
**(That follow-up landed 2026-07-15 — see below.)**

### 2026-07-15 four-front deep audit (this session)

Four parallel adversarial audits (proof core; visitor + allow-lists; adapter +
reachability; driver + config + predicate). Every finding was re-verified
against source AND, where the claim concerned real MIR, **reproduced end-to-end
with the nightly wrapper before any fix** — several agent claims died on that
check (see "Refuted"). Fixed, all fail-closed (+13 tests → **381**).

**The headline: the allow-list was clean; the false discharges were elsewhere.**
Two consecutive prior audits had evicted CRITICALs from
`is_trusted_total_library_call`, so that surface got a structural gate and this
session's sweep of it (both an agent's and my own independent probing of every
trusted entry against adversarial witnesses) found **no third instance**. The
three confirmed false discharges were all in the *reachability / rendering*
layer — the path-string plumbing around the proof core, not the proof core:

- **`verify_roots` glob never matched trait impls (CRITICAL).** `item.name()`
  renders a trait-impl method as `<demo::Calc as demo::Div2>::div2` — a leading
  `<` — so `starts_with("demo::")` matched none. `verify_roots = ["demo::*"]`,
  which reads as "verify my whole crate", walked NOTHING and **exited 0** on
  `fn div2(&self, a: u32, b: u32) -> u32 { a / b }`. The #27 gate cannot
  backstop it: a public trait impl with no in-crate caller is never
  `referenced`. `crate_of_path` already understood this rendering *with tests*;
  the matcher never did — the Drop-glue special case was the tell (the one
  trait the authors tripped over got patched, not the matcher under it).
  Fixed by normalizing `<Self as Trait>::m` → `Self::m` (generics + `&`/`*`
  sigils stripped); the driver's hand-copied mirror now DELEGATES to the subset
  copy so the two cannot drift again.
- **Fn ITEMS passed as arguments escaped the reachability gate (CRITICAL under
  narrowing).** `o.map(panicky)` coerces nothing (no fn-ptr local ⇒ PB032 never
  fires), rides in the ARGUMENT list not `func` (⇒ the direct-call scan missed
  it), and `Option::map` is correctly trusted-total (⇒ no gap). The invocation
  happens inside un-walked `core`. `callee_paths`'s soundness argument
  enumerated three ways to name a callable and missed the fourth. **The bug was
  never that `map` is wrongly trusted** — it is that "this function is total"
  was read as "this call site is safe", which holds only if everything the
  callee *invokes* is separately verified.
- **Type rules dead on real std code (HIGH).** rustc renders a type by the path
  it was REACHED through, so `Cell` arrives as `std::cell::Cell` **even when the
  source writes `core::cell::Cell`**. PB011/PB012/PB015 carried dual
  `alloc::`+`std::` spellings; PB008/PB021/PB022/PB023 were `core::`-only and
  thus dead on every std-linked crate. Confirmed with a clean control under the
  documented `strict_library_acceptance = false` opt-out: `Box` rejected,
  `Cell` exit 0. All arms now match the root-stripped suffix. Corpus:
  `reject/PB021_std_cell_reexport.rs` — the coverage that was missing, since
  every prior test for these rules hand-built the `core::` path the adapter
  never emits.

**Proof-core hardening** (no CRITICAL found there; these are defense-in-depth):

- **A verdict alongside an SMT-LIB `(error ...)` or a non-zero exit is now
  REFUSED.** Z3 does not treat a malformed directive as fatal — it reports the
  error, DROPS it, and answers the REST. Verified on z3 4.16.0: a problem whose
  middle `(assert ...)` (a *hypothesis*) is malformed prints `(error "…")` then
  `unsat` and exits 1, and the parser counted that as a full discharge vote.
  Not live-exploitable in the default pool (cvc5 is stricter, emitting no
  verdict, so 2-of-2 degraded to Inconclusive) — **but safety must not rest on
  one vendor being more conservative than the other**: at `threshold = 1` or
  with two z3-like solvers the same input falsely discharges. Also retires the
  structural assumption that a dropped directive always weakens toward `sat`.
- Vacuity guard's all-not-installed exemption is now **enforced** at the main
  check, not assumed (it was a temporal claim: "no solver now ⇒ none in 3ms").
- `compile` fails closed when assumptions exist but consistency emission fails.
- Version pins must be SHAPED like a version (`z3 = "Z3"`/`"64"`/`"bit"` each
  matched a constant token of every Z3 banner — configured-looking, pinning
  nothing; a digit test alone is insufficient, "Z3" contains one).
- `from_json` pins the bundle header threshold to each cert's, so the gate an
  auditor reads is the gate replay enforces.
- `crate_of_path` strips `&`/`*`/`[` sigils (`impl Add for &Matrix` yielded the
  crate `"&crate_b"`, which no manifest carries).

**Structural backstops** (close the class, not the instance):

- A `verify_roots` pattern matching **zero** functions now fails closed —
  whether from a typo or a silent matcher gap, which is exactly how the
  trait-impl bug hid. (It earned its keep immediately: it caught a wrong crate
  name in one of my own probes.)
- `exclude` is counted apart from root-narrowing, and its warning is
  unconditional (it was an `else if` on the verify-roots branch, so setting BOTH
  silenced it — the config where it matters most, since an excluded item is
  dropped *before* the universe and is invisible to the #27 gate).
- **Exhaustiveness gate extended to the non-integer surfaces** (+~90 entries,
  62 witnessed panics/run, up from 28). **Mutation-tested**: re-introducing the
  2026-07-09 `sort` eviction makes it fail, so it demonstrably catches the class
  it exists for.
  - *The sort witness is subtle and worth reading before touching:* 1.81+
    order-violation detection is **opportunistic**. An "always return Less"
    comparator makes the input look already-sorted and does **not** panic
    (verified n = 8…5000); a **stateful** comparator panics deterministically
    from n ≈ 50. The naive witness would have "proven" `sort` total and argued
    to un-evict it — a mislabel that reads as evidence. Both facts are pinned by
    `sort_order_violation_witness_is_genuine`.

**Refuted by verification (claims NOT acted on).** The adapter agent's
`std::`-vs-`core::` finding was real in *mechanism* but its proposed repro was
wrong: BOTH spellings render `std::`, so its "control" case failed identically
and proved nothing — the Box-vs-Cell control is what establishes it. Its
"`covered_analyzed_universe` mis-parse" and the visitor agent's float-glob and
`From::from` items were confirmed non-exploitable (PB050 / type-level rejects
already dominate) and left alone rather than churned.

**Method note:** unlike 2026-07-12, the stable e2e lane ran clean on Windows
this session — all 58 wrapper-spawning tests executed under
`PITBULL_REQUIRE_E2E=1` with z3 4.16.0 + cvc5 1.3.4 on PATH (no Smart App
Control block), so the local evidence is complete rather than corpus-deferred.

### 2026-07-18 trait-dispatch soundness pass (this session)

A fresh four-front adversarial audit (proof core; visitor + allow-lists;
adapter + reachability; driver + config + predicate), each front tasked to find
a false discharge and NOT to trust the soundness claims in comments. Two fronts
came back clean and CORROBORATED the core: the **proof core** (`pitbull-vc`)
re-confirmed SMT polarity empirically on both solvers with no new hole, and the
**visitor + allow-list** front found no trusted-but-panicking method and
independently pointed at "the `verify_roots`-narrowed reachability gate" as the
place to hunt. The other two fronts each reproduced a CONFIRMED false discharge
end-to-end on the real wrapper — all three were §7 "STILL OPEN" residuals that
had been *theorized* but never demonstrated or fixed. Every finding was
reproduced on the clean wrapper before any fix (per the project rule that a
proposed repro is often wrong even when the underlying finding is real). Fixed,
all fail-closed (+10 tests → **391**):

- **(A) Trait-method CALL escaped the #27 reachability gate under `verify_roots`
  narrowing (CRITICAL).** A statically-dispatched `c.div2(a, b)` is referenced
  by its bare TRAIT path (`demo::Div2::div2`), while the walkable impl item is
  `<demo::Calc as demo::Div2>::div2` — `referenced ∩ universe` never matched the
  two, so `fn caller(c){ c.div2(10, 0) }` with the impl body `a / b` unwalked
  exited 0 despite a reachable division-by-zero (walk-all correctly exits 1).
  Fixed in `reachability.rs` by augmenting the `walked`/`universe`/`trusted`
  sets (per-crate `unverified_reachable_callees` AND cross-crate
  `covered_analyzed_universe`) with the new `trait_method_form` of every
  trait-impl path (`<Type as Trait>::m` → `Trait::m`) — a WALKED impl clears the
  gate, an UNWALKED-but-in-universe impl is flagged. Trait-PRESERVING, so it does
  NOT reuse the trait-DROPPING `normalize_impl_path`. The gate now treats a
  trait-impl callee identically to a regular callee under narrowing (verified:
  a regular `helper()` is flagged the same way). Pinned by 3 unit tests + the e2e
  `wrapper_trait_method_call_gated_under_verify_roots`.
- **(B) `#[pitbull::ensures]` on a trait-IMPL method silently bound nothing
  (false discharge).** The HIR pre-pass keyed specs by `tcx.def_path_str`'s
  `demo::<Calc as Doubler>::m`, but the item-walk looked them up by `name()`'s
  `<demo::Calc as demo::Doubler>::m` — they differ only for trait impls, so a
  false `ensures("result < x")` on `fn m(x){ x }` emitted NO PB076 and exited 0
  (the inherent-method control correctly exited 1). `requires`/`trusted` share
  the mismatch but fail SAFE (fewer assumptions / the body is still walked); only
  `ensures` is fail-OPEN. Fixed with a trait-PRESERVING `canonical_spec_key`
  applied to the `ensures` map store + lookup (leaving `requires`/`trusted` on
  their raw keys, so the fragile `set_known_precondition_fns` call-site gate is
  untouched — a collision on the ensures key is fail-safe: EXTRA obligations,
  never fewer). Now the false ensures is refuted (sat, exit 1) and a TRUE one
  DISCHARGES. Pinned by 4 `canonical_spec_key` unit tests + the e2e
  `wrapper_ensures_on_trait_impl_method_binds` (both directions).
- **(C) `#[pitbull::ensures]` on a trait-DEFAULT method silently bound nothing
  (false discharge).** Distinct mechanism: there was NO `visit_trait_item`
  extractor at all (only a `visit_nested_trait_item` no-op), so trait-item
  attributes were never read. Added `visit_trait_item` (keys already align for
  default methods — no `<.. as ..>` rendering). Pinned by the e2e
  `wrapper_ensures_on_trait_default_method_binds`.
- **Fail-closed backstop for the whole `ensures`-binding class.** An
  `#[pitbull::ensures]` key that binds to NO walked function is now folded into
  the coverage-gap exit code (`unmatched_ensures_keys`), governed by
  `fail_on_coverage_gaps` (default true) like every other gap. So even an exotic
  rendering the canonicalization misses, or an ensures on a function `verify_roots`
  narrowed out, fails closed instead of silently attesting an unchecked
  postcondition (verified: an ensures on a narrowed-out fn now exits 1).

**Honesty / drift pass** (same session): the `pitbull-spec` `ensures` rustdoc
said PB076 was "reported pending" (stale since Q.4a–d — it discharges, and now
binds on trait methods); the CI header comment claimed the "61-test invariant"
(now the count moves each session, pointed at §1); `docs/PSS-1.md` §17.1's
closing example still said "366 passing". All corrected.

**Not changed (verified sound this session):** the proof core, the `is_*`
allow/deny classifier (empirically re-probed across int widths / char / slice /
Option-Result), the `vote`/agreement gate, the exit-code decider, and the
`build.rs` stub (fails closed, exit 1). The `requires`/`trusted` binding on
trait-impl methods remains on raw keys — it is fail-SAFE today, and canonicalizing
it would risk desyncing the call-site precondition gate; the UX improvement (so a
`requires` on a trait-impl method enables its discharge) is a tracked follow-up,
NOT a soundness gap. Method note: the full 58→61-test e2e lane ran clean on
Windows under `PITBULL_REQUIRE_E2E=1` with z3 4.16.0 + cvc5 1.3.4.

### 2026-08-03 call-site precondition discharge, Increment 1 (this session)

**Environment first — the e2e lane was silently dead and had to be restored.**
On sit-down the stable suite reported 391/391 green in **0.01 s of integration
time**: `nightly-2026-01-29` was no longer installed on this machine (only a
2026-05-28 nightly) and `target/debug/pitbull-rustc.exe` did not exist, so all
58 wrapper-spawning tests took their graceful-skip path. Green, and proving
nothing about real MIR. Reinstalled the pinned nightly (`--component rustc-dev
--component llvm-tools`) and rebuilt the wrapper; integration went 0.01 s →
~4 s and the whole suite now runs under `PITBULL_REQUIRE_E2E=1`. **Check this
first in any fresh session** — the skip-net is deliberate and correct for
contributors without nightly, but it means a green local run is not by itself
evidence.

**The feature (the first COMPLETENESS increment since WS-3).** Closes the
open half of the 2026-07-09 modular-verification finding. That audit made
calls to precondition-carrying functions *honest* (a fail-closed CoverageGap);
this makes them *provable*. New rule **PB077** ("precondition unmet at call
site", `RULE_COUNT` 76 → 77) + `VcObligationKind::CallSitePrecondition`,
routed through `pitbull-vc::compile` verbatim like `EnsuresPostcondition`.
`safe_div(10, 5)` now verifies; `safe_div(10, 0)` is refuted with a
counterexample instead of merely gapped. Tests **391 → 411**; both clippy
lanes error-clean; zero warnings.

- **Wrapper:** a callee-spec pre-pass (a separate loop, because item order is
  not caller-before-callee) records `arg_names` + primitive-int `arg_ty_names`
  for every in-crate fn whose path carries preconditions.
- **Visitor:** `build_callsite_precondition_smt` maps each precondition ident
  → parameter → the constant actual, pins it, and negates the conjunction.
- **The invariant that makes it sound:** the precondition list discharged at
  the call site must equal the one the callee's body ASSUMES. Both now come
  from one helper (`callee_spec_preconditions`); proving a subset would close
  the callee's obligations with clauses nothing established.

**This is the one direction where a bug is a false discharge, so it was
red-teamed before the tests were written** — 20 adversarial probes on the real
wrapper (z3 4.16.0 + cvc5 1.3.4, 2-of-2). Parameter binding is right at the
first, middle, and `self`-offset positions (`s.div(10, 0)`, where `b` is
argument index 2, is refuted); the boundary is sharp (`b8(200)` refuted vs
`b8(201)` discharged under `x > 200`); signed comparisons use `bvsgt`
(`s(10, -1)` refuted); `usize`, mixed widths, raw-SMT clauses, unknown idents
and caller-variable actuals all fall back to the gap; and a
`verify_roots`-narrowed callee still trips the #27 gate even when its call
site discharges. The 34-probe independent red-team suite was **re-run after
the change — still 0 false discharges.**

**Incidental (toolchain drift, not the feature):** clippy 1.97 promoted
`question_mark` to an `error:` on the if-let-chain prefix dispatch in
`predicate::int_type_info` and `smt::IntInfo::from_name`, breaking the
error-clean invariant on code nobody had touched (same class as the
2026-06-14 `callee_paths` drift). Both rewritten to `match` + `?`,
behaviour-identical; `int_type_info` — which decides the signedness and width
of every literal the project emits — had no direct test and now has one.

**Windows note:** Smart App Control intermittently blocked freshly-relinked
*test* binaries (os error 4551) this session, including targets whose source
was untouched. Re-running the same command clears it, usually on the first
retry; `--no-fail-fast` lets the other targets report meanwhile. The already-
built `pitbull-rustc.exe` was never blocked.

### 2026-08-07 call-site precondition discharge, Increment 2 (this session)

**A fresh session first audited, then committed, the Increment 1 work the
2026-08-03/04 session had left uncommitted for three days** (13 files,
+1445/-66) — full manual trace of the parameter-binding path, the existing
411-test suite re-run under `PITBULL_REQUIRE_E2E=1` (integration took 3.04s,
confirming the wrapper actually ran rather than gracefully skipping), and 4
fresh hands-on adversarial probes against the real wrapper not drawn from
the existing suite (method-call `&self`-offset binding, a generic function
with an unrelated type parameter, two preconditions on the same parameter).
All matched the sound design; committed as `5cfd10a`, no code changes. The
user then chose to continue the PB077 feature line with Increment 2.

**The feature.** Closes the next slice of the 2026-07-09 modular-verification
finding: Increment 1 could only bind a call-site actual that was a CONSTANT
integer, so the common forwarding shape — `fn caller(v: u32) { safe_div(10,
v) }` under `requires("v > 0")` on `caller` — stayed a fail-closed coverage
gap even though the caller's own contract obviously establishes what
`safe_div` needs. Increment 2 recognizes a bare (unprojected) read of one of
the CALLER's own parameters as a second binding shape, links the callee's
parameter symbol to a canonical caller-argument symbol
(`__pb_caller_arg{index}`, never derived from user-chosen identifier text —
so it cannot collide with a callee parameter sharing a caller parameter's
name, e.g. `fn caller(b: u32) { safe_div(10, b) }`), and folds the caller's
OWN precondition set in as hypotheses over those same canonical symbols.
`fn caller(v: u32) { safe_div(10, v) }` under `requires("v > 0")` now
verifies; the same call under a caller contract that doesn't actually
establish `v > 0` (`v >= 0`, or no contract at all) is refuted with a
counterexample, not silently gapped.

**Why this is the delicate direction (more than Increment 1 was).**
Increment 1 only ever pinned symbols to LITERAL constants, which can never
be mutually contradictory. Increment 2 assumes the CALLER's own
preconditions as hypotheses, and a caller's own contract CAN be
self-contradictory (`requires("v > 10")` and `requires("v < 5")` on the same
`v`) — under contradictory hypotheses, any goal is trivially "unsat", so a
naive implementation would vacuously discharge every call `caller` makes,
regardless of whether it's actually safe. The defense is the SAME F1
consistency-check dispatch every other obligation kind (`ArithmeticOverflow`,
`IndexBound`, `EnsuresPostcondition`, and Increment 1's own
`CallSitePrecondition`) already used — `pitbull-rustc.rs`'s dispatch loop
runs `goal.consistency_check` first and refuses to trust the main check's
`unsat` if that comes back anything but `sat`, entirely independent of
`VcObligationKind`. Confirmed by reading the dispatch code (no
`CallSitePrecondition`-specific branch exists anywhere in it) BEFORE writing
any Increment 2 code, then re-confirmed by running the contradictory-caller
probe on the real wrapper: `pitbull-rustc: vc pb077-callsite-1 (PB077):
REFUSED — preconditions are contradictory (a solver's consistency check
returned unsat: [z3=unsat cvc5=unsat]); a discharge claim here would be
vacuously true`, exit 1. Zero wrapper/driver changes were needed for this —
the whole feature lives in `pitbull-subset/src/visitor.rs` (`CallsiteBinding`,
`operand_as_caller_arg`, `caller_param_lookup`, `caller_arg_symbol`,
`caller_precondition_hypotheses`, and the extended `bind_callsite_param`/
`build_callsite_precondition_smt`).

**Asymmetric translation is intentional.** The callee's own precondition set
(the GOAL) keeps Increment 1's all-or-nothing contract: any untranslatable
clause abandons the whole obligation, because discharging a subset would
prove a WEAKER contract than the callee assumed. The caller's own
precondition set (the HYPOTHESES) is deliberately best-effort:
`caller_precondition_hypotheses` drops whatever it cannot translate (a
raw-SMT-LIB clause, an ident not naming exactly one caller parameter) rather
than aborting, because using a SUBSET of what's actually true only makes the
discharge goal HARDER to prove, never easier — dropping a hypothesis cannot
manufacture a false discharge. A pure-Increment-1 (all-constant) call site's
SMT text is untouched byte-for-byte — the caller-hypothesis machinery only
runs at all when a `CallerArg` binding is actually present.

**Verified, not assumed.** 8 adversarial probes on the real wrapper (z3
4.16.0 + cvc5 1.3.4, 2-of-2), constructed BEFORE the permanent test suite:
the contradictory-caller-preconditions case above; a satisfying caller
contract discharges; a subtly-insufficient one (`v >= 0` vs the needed
`v > 0` — `v == 0` is a genuine counterexample) refutes; NO caller
precondition at all is still ATTEMPTED (not silently gapped) and correctly
refutes via an unconstrained symbol; a shape-1 (ident-vs-ident) caller
precondition chain that doesn't jointly establish the goal refutes; mixed
constant + caller-linked actuals across two independent call sites in one
file get independent, correct verdicts; and self-offset method dispatch
(`c.div(10, v)`) combined with caller-linking binds `v` to the right MIR
argument slot, not the receiver. Zero false discharges. The existing
34-probe independent red-team suite and all four Increment 1 e2e tests were
re-run after the change — all still pass; one Increment 1 e2e test
(`wrapper_callsite_precondition_falls_back_to_the_gap`) needed its
"non-constant actual" fixture changed from a bare caller parameter (now a
valid Increment 2 link, so it's attempted-and-refuted rather than gapped —
same exit code, different diagnostic) to a genuinely still-uncapturable
arbitrary expression (`v + 1`), which is exactly Increment 3's scope, not a
regression.

Tests **411 → 424** (8 visitor unit tests + 5 e2e integration tests). Both
clippy lanes error-clean; zero warnings; `pitbull-driver` untouched (the
whole feature is `pitbull-subset`-only — confirmed via `git diff --stat`).

**Next open (all completeness):** Increment 3 = arbitrary expression actuals
(`safe_div(10, v + 1)`, or any actual that isn't a bare constant or a bare
caller-parameter read) — the shape `wrapper_callsite_precondition_falls_back_
to_the_gap`'s remaining case now pins as still-gapped. After that: loops/
PB042, PB043 path-condition capture, PB041 SCC+measure.

### 2026-08-08 call-site precondition discharge, Increment 3 (this session)

**Same continuous session as Increments 1 (audit+commit) and 2 above** —
the user asked to "keep moving forward" after Increment 2 landed, choosing
to continue the PB077 line rather than switch to a different roadmap item.

**The feature.** Closes Increment 2's remaining residual: a call-site
actual that is a COMPUTED EXPRESSION (`v + 1`), not just a bare constant or
a bare caller-parameter read. `fn caller(v: u32) { let t = v + 1;
safe_div(10, t) }` under a caller contract that bounds `v` now DISCHARGES —
previously a fail-closed coverage gap. New `bind_callsite_param` branch:
when an actual is neither a constant (Increment 1) nor a bare
caller-parameter read (Increment 2), try `capture_call_arg_expr`, which
reuses `capture_rvalue`/`capture_operand` — the SAME machinery
`#[pitbull::ensures]` (Q.4a–Q.4d) already uses to capture a function's
return-typed effect — verbatim. Those two functions were confirmed generic
over their target-type parameter (nothing return-slot-specific baked in)
by reading them BEFORE reuse, not assumed. `capture_call_arg_expr` seeds
their `env` with the caller's OWN parameters (mapped to canonical
`__pb_caller_arg{index}` symbols, Increment 2's naming) instead of
`capture_body_effect`'s return-typed-parameters-only seed, and stops at the
call's block instead of at `Return`.

**The design needed a real mid-course correction — the honest kind.** The
FIRST draft walked only the call's own basic block's statements (an
architecturally smaller, more contained change — no need to thread the
full block list + a block index through the dispatch chain). It compiled
clean, passed its own hand-built shadow-IR unit tests, and then GAPPED THE
VERY FIRST real-wrapper probe: `let t = v + 1; safe_div(10, t)` reported
the coverage-gap note, not a PB077 obligation. Rather than assume the
probe was wrong, dumped the real MIR (`rustc -Z unpretty=mir`, no
rustc_public needed) for exactly that function:
```
bb0: { _3 = AddWithOverflow(copy _1, const 1_u32);
       assert(!move (_3.1: bool), "...") -> [success: bb1, unwind continue]; }
bb1: { _2 = move (_3.0: u32);
       _0 = safe_div(const 10_u32, copy _2) -> [return: bb2, unwind continue]; }
```
`v + 1` lowers to `AddWithOverflow` — a `(u32, bool)` TUPLE — in `bb0`,
with the actual sum read back out via a `.0`-projected statement `_2 = move
(_3.0)` in `bb1`, the block the overflow-check `Assert`'s success edge
jumps to. A same-block-only walk can never see across that split — which
means it would have gapped essentially every checked-arithmetic
expression, i.e. most real code, making the whole increment far less
useful than it looked from the shadow-IR tests alone (the exact trap
`docs/HANDOFF.md`'s own 2026-06-13 lesson warns about: hand-built MIR
fixtures bypass real rustc lowering). Fixed in two parts: (1) reused
`capture_body_effect`'s existing `Goto`/`Assert`-chain traversal (walk from
bb0, follow only `Goto`/`Assert`-success edges, fail closed — never
guess — on anything else, including a real branch) instead of a bespoke
same-block walk; (2) wrote every successful capture into BOTH the `env`
map (whole-local reads) AND the `checked` map (`.0`-of-tuple reads) —
exactly mirroring `capture_body_effect`'s own dual-insert, which the first
draft had dropped as "narrower on purpose," a scope cut that turned out to
be wrong rather than conservative. Re-ran the SAME probe after the fix:
`pb077-callsite-2 (PB077): discharged`.

**Verified, not assumed — 8 adversarial probes on the real wrapper** (z3
4.16.0 + cvc5 1.3.4, 2-of-2), the failing one above plus: a satisfying
single-hop capture (after the fix); a genuinely insufficient caller
contract refutes; the CONTRADICTORY-caller-preconditions case reached
through a captured expression is still `REFUSED` by the (unchanged) F1
guard — the cardinal check, since this increment is the third to assume
caller hypotheses that could be self-contradictory; a two-statement CHAINED
expression (`let a = v+1; let b = a*2;`) discharges, proving the walk
accumulates across statements and across each one's OWN checked-arithmetic
block split; a value behind an actual `if`/`else` BRANCH still falls back
to the gap, never guessing which arm ran; and an expression combining TWO
DISTINCT caller parameters (`v + w`) — first left unbounded (correctly
REFUTED: `v`,`w` both `>= 1` does not prevent `bvadd` wraparound to 0 in
machine arithmetic, a genuine counterexample, not a bug) then properly
bounded (cleanly discharges end-to-end, exit 0) — confirming
`referenced_caller_arg_indices` correctly attributes and declares BOTH
symbols from one expression. Zero false discharges. The full existing
suite (all Increment 1 + 2 tests, the 34-probe red-team suite) was re-run
after — all still pass; one Increment 2 e2e test needed its "still gapped"
fixture changed again — `v + 1` (chosen specifically because Increment 2
couldn't capture it) is now capturable by design, so it was swapped for
`v & 1` (a bitwise op, `capture_rvalue`'s own separately-documented
deferred boundary) to keep pinning a real residual.

Tests **424 → 437** (7 visitor unit tests + 6 e2e integration tests). Both
clippy lanes error-clean; zero warnings; nightly build+clippy lanes clean.

**Next open (all completeness):** a value behind a branch, a bitwise op, a
cast, a field/call-result read — everything `capture_rvalue` itself already
declines — remain gapped, matching `#[pitbull::ensures]`'s own boundary
exactly (extending either would extend both, and both would need the same
red-team discipline). Beyond PB077 itself: loops/PB042, PB043
path-condition capture, PB041 SCC+measure remain the untouched
multi-week items.

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

### Step 4.2 — Stable test suite (the 437-test baseline)

```bash
cargo +stable test --workspace --all-features 2>&1 | grep "^test result"
# Expected: "test result: ok" lines totaling 437 passing, 0 failed, 0 ignored
```

**A green run here is NOT by itself evidence the verifier works** (learned the
hard way, 2026-08-03). The ~65 wrapper-spawning integration tests gracefully
skip when the pinned nightly or the built wrapper is missing — deliberately, so
contributors without a nightly toolchain still get a useful suite — and the
suite reports the same "ok" either way. The tell is the clock: the integration
target takes **seconds** when the wrapper is present and **~0.01 s** when every
e2e test skipped. If it is the latter, do §4.4 and §4.6 before trusting
anything, and re-verify that `rustup toolchain list` still has
`nightly-2026-01-29` (a rustup cleanup can remove it, and then only the shadow
IR is being exercised).

If you see `Application Control policy has blocked this file` on Windows: that's Smart App Control quarantining a freshly-relinked test binary — it can hit targets whose source you never touched. Run the same command again; it usually clears on the first or second retry. Add `--no-fail-fast` so the other targets still report while one is blocked. The already-built `pitbull-rustc.exe` is not affected.

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
# Expected: all integration tests run (none gracefully skipped). Still 437 passing.
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
# Expected: 437 passing (same as without Z3 — the new tests
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
| Path-sensitive symbolic exec | **Partial (Frontier #4, 2026-06-16):** the SMT *encoding* for "panic site is unreachable" now exists and is z3-verified — `smt::emit_panic_unreachability_problem` asserts `(assumptions AND path_condition)` (unsat => unreachable) with a mandatory vacuity guard so contradictory preconditions cannot vacuously discharge a reachable panic. `compile` still returns None for `PanicReachability`; the remaining (deferred) core is the visitor-side capture of the per-site path condition from the MIR CFG. | `pitbull-subset` visitor + `pitbull-vc/src/{smt,vc}.rs` | Path-condition capture is the multi-week part; the encoding + vacuity reasoning are done and tested. |
| Termination measures (PB041) | **Partial (Frontier #3, 2026-06-16):** direct self-recursion (callee `DefId` == body `DefId`) now emits a `RecursionDecreases` obligation, surfaced as *pending* (`compile` returns `None`, never a false discharge). Remaining: mutual-recursion SCC detection + SMT discharge of a `#[decreases]` measure. | visitor + vc | Whole-call-graph SCC + measure-decrease encoding deferred. |
| Self-verification / dogfood (Frontier #6) | Pitbull cannot yet verify its own TCB: that code uses heap + collections (`Vec`/`String`/`HashMap`), serde, and `rustc_private` internals — all outside PSS-1, so the subset enforcer would (correctly) reject it. End-to-end verification of *real* code is instead demonstrated by the accept corpus + the fixed-point `scale_q` proof (Frontier #1, `aorte_proofs.rs`), now exercised on the Linux nightly-e2e lane. This is the honest scope: a "partial dogfood" via real external targets, not self-hosting. | whole TCB | True self-hosting awaits the subset covering heap/collections (v0.2+); the alternative (carving out a tiny pure subset of the TCB to verify) would be a contrived demo, not a real soundness signal. |
| Bounds checks (PB054) | ✅ DONE in Tasks P / P.1 / P.2 + audit-cleanup. Visitor emits `IndexBound { idx_source_name: Option<String> }`; compile emits QF_BV with `__pb_idx`/`__pb_len` canonical names + `idx`/`len` aliases + optional source-name alias in quoted-symbol syntax for raw-ident safety. End-to-end discharge under Z3 verified by `wrapper_proves_bounded_index_safe_under_precondition`. | — | Closed. |
| Z3 subprocess timeout / output cap | Z3 invocation can hang indefinitely on a pathological SMT problem; no captured-output size cap. | `pitbull-vc/src/solver.rs` | DoS vector flagged in audit finding N3 (2026-05-26). Mitigation requires spawning + try_wait + size-cap; bigger change than the audit-cleanup pass absorbed. |
| Reachability path-matching cluster (2026-07-09 audit; partly closed 2026-07-15; **trait-CALL side closed 2026-07-18**) | Under `verify_roots` NARROWING, the per-crate/#27 and cross-crate gates ignore referenced paths they can't match to a universe entry ("unmatched ⇒ ignore"). **CLOSED 2026-07-15:** the `<Self as Trait>::method` rendering is matched by `pattern_matches`, fn-item arguments are referenced callees, `crate_of_path` handles sigiled Self types, a zero-match root pattern fails closed. **CLOSED 2026-07-18 (was a live CRITICAL false discharge, reproduced e2e):** the statically-dispatched trait-method CALL recorded under the trait path (`demo::Div2::div2`) vs. the walkable impl `<demo::Calc as demo::Div2>::div2` — the gate sets are now augmented with each impl's `trait_method_form`, so `referenced ∩ universe` matches (see §1). **STILL OPEN (LOW, not reproduced):** visible-vs-canonical re-export renderings; `covered_analyzed_universe` inferring "analyzed" from an impl-for-foreign-type path. NOT exploitable with default walk-all (`verify_roots = []`). | `pitbull-subset/src/reachability.rs` (gates), `pitbull-driver/src/main.rs` (aggregation) | The `trait_method_form` augmentation over-approximates in the multi-impl case (flags a trait call if ANY impl of that trait-method is unwalked, even when the resolved one was walked) — fail-closed / a false REJECT, the acceptable side. The precise fix (resolve a trait-path call to its exact impl) needs the trait-impl map, not a string rewrite. |
| Certificates omit the consistency (vacuity) evidence (2026-07-15 audit) | An `ObligationCertificate` records the main-check SMT + verdicts but neither the consistency-check problem nor its verdicts, so `replay` cannot re-validate the F1 vacuity guard: if `threshold` solvers wrongly answered `sat` on a contradictory assumption set at certification time, the resulting vacuous "discharged" cert replays as MATCH forever. | `pitbull-vc/src/cert.rs`, `pitbull-rustc.rs` dispatch | LOW (needs a threshold-wide sat-side solver bug), but it is the honest gap in the "complete coverage ledger" claim. Recording `consistency_check` + its verdicts is a `CERT_FORMAT_VERSION` → 3 change. |
| Trait-impl `#[pitbull::requires/trusted]` binding (2026-07-15 audit; **`ensures` closed 2026-07-18**) | The HIR pre-pass keys specs as `crate::<Foo as Trait>::bar` (`tcx.def_path_str`) but the lookup uses `item.name()`'s `<crate::Foo as crate::Trait>::bar` — they differ for TRAIT-impl methods. **`ensures` CLOSED 2026-07-18** (it was fail-OPEN — a non-binding one emitted no PB076, a silently unchecked postcondition = false discharge): the `ensures` map now keys store+lookup through `canonical_spec_key` (trait-preserving), a `visit_trait_item` extractor covers trait-DEFAULT methods, and an unmatched `ensures` key is a fail-closed coverage gap. **`requires`/`trusted` STILL don't bind on trait-impl methods — deliberately:** both are fail-SAFE (fewer assumptions / the body is walked), and `set_known_precondition_fns` shares the raw HIR keys so the call-site gap fails together with it (the `oops(){safe_div(10,0)}` hole stays closed). Canonicalizing them would be a UX win (a `requires` on a trait-impl method would enable its discharge) but risks desyncing the call-site gate. | `pitbull-driver/src/bin/pitbull-rustc.rs` (HIR pre-pass keys) | Follow-up (UX, NOT soundness): canonicalize `requires`/`trusted` too, threading the same canonical key through `set_known_precondition_fns` AND the call-site matcher so they stay in sync. |
| ADT generic args dropped by adapter (2026-07-09 audit) | The shadow `AdtDef` carries only `{path, is_union}`; `RigidTy::Adt(_, generic_args)` discards args, so `static S: Option<Cell<u32>>` (or a user struct with a `Cell` field) passes PB018/PB021's item-type check — the `Cell` is invisible at the item level. In-body USES still fire PB021 (materializing `&Cell` in a local); transport-only flows do not. | `pitbull-subset/src/mir_api/adapter.rs`, `mir_api.rs` | Threading args through the shadow IR ripples every AdtDef consumer; needs a deliberate design (render-into-path vs. structured args). |
| PB060 build-script hash recorded, not verified (2026-07-09 audit) | `trusted_build_scripts[].sha256` is format-validated (64 hex chars) only; no code hashes the referenced build.rs and compares, so a changed build script stays trusted. | `pitbull-subset/src/config.rs::validate` | Requires resolving the build.rs path per crate + hashing at wrapper start; disclosed inline in config.rs. |
| PB072/PB073/PB074 unimplemented (2026-07-09 audit) | Cargo.lock presence, hermetic-environment, and pitbull-spec version checks do not exist (a config.rs comment previously claimed the driver performs them — corrected). PB073 is the named compensating control for the `PITBULL_*` env-injection residuals (`PITBULL_TOML` redirect, `PITBULL_ALLOW_UNSAFE_PATHS` from a hostile build.rs), so those residuals are currently guarded only by `check_env_path` hygiene. | driver | Implementing PB073 (refuse or fingerprint suspicious `PITBULL_*` provenance, e.g. a sentinel set by the subcommand) is the highest-leverage of the three. |
| Bang-macro `unsafe {}` HIR skip (2026-07-09 audit) | The PB001 HIR pre-pass skips blocks whose span `from_expansion()`, and PB059 provenance-checks only Derive/Attr macros — a local `macro_rules!` expanding to `unsafe { … }` evades both. MIR-level operation rules (PB004/PB007/PB009…) still fire on the operations INSIDE, so this is a PB001-reporting gap more than a free pass, but it is untested. | `pitbull-driver/src/bin/pitbull-rustc.rs` (HIR pre-pass), config PB059 | Needs a Bang-macro provenance policy (allowlist local macros?) without false-flagging std macros like `assert!`. |
| Call-site precondition SMT discharge (2026-07-09 audit; **Increment 1 DONE 2026-08-03, Increment 2 DONE 2026-08-07, Increment 3 DONE 2026-08-08 — rule PB077**) | Was: the fail-closed CoverageGap (`maybe_gap_callsite_preconditions`) made calls to precondition-carrying fns honest but CONSERVATIVE — `safe_div(10, 5)` gapped even though `5 > 0`. **Increment 1 PROVES constant actuals**; `unsat` ⇒ discharged (`safe_div(10, 5)` verifies), `sat` ⇒ refuted (`safe_div(10, 0)`). **Increment 2 additionally PROVES a bare caller-parameter actual** (`fn caller(v: u32) { safe_div(10, v) }` under `requires("v > 0")`): `operand_as_caller_arg` links the callee's parameter symbol to a canonical `__pb_caller_arg{index}` symbol (never derived from user identifier text, so it can't collide with a same-named callee parameter), and `caller_precondition_hypotheses` folds the caller's OWN precondition set in as hypotheses (best-effort — an untranslatable caller clause is dropped, not fatal). **Increment 3 additionally PROVES a computed EXPRESSION actual** (`let t = v + 1; safe_div(10, t)`): `capture_call_arg_expr` reuses `capture_rvalue`/`capture_operand` verbatim (the SAME machinery `#[pitbull::ensures]` uses for its return-effect capture — verified generic over target type before reuse, not copied) to trace the actual back through the caller's own statements. Its first draft walked only the call's own block and gapped nearly every real checked-arithmetic expression — confirmed by dumping real MIR (`rustc -Z unpretty=mir`) after the first red-team probe failed: `v + 1` lowers to `AddWithOverflow` (a tuple) in one block, read back via a `.0`-projected statement in the block the overflow `Assert` jumps to. Fixed by reusing `capture_body_effect`'s Goto/Assert-chain traversal and writing every capture into BOTH the `env` and `checked` maps; a value behind an actual branch (`SwitchInt`) is still correctly refused (the same boundary `capture_body_effect` itself draws — never guess which arm ran). All three increments route through `pitbull-vc::compile` verbatim like `EnsuresPostcondition`, and the pins/links/expressions are hypotheses, so the pre-existing, obligation-kind-agnostic F1 consistency guard runs over them regardless of which increment produced them — confirmed on the real wrapper for all three: a caller with mutually-contradictory preconditions gets `REFUSED — preconditions are contradictory`, never a vacuous discharge. | visitor + `pitbull-vc` + wrapper | **STILL OPEN (completeness, not soundness):** a raw-SMT-LIB clause anywhere in either contract, a `usize`/`isize`/non-int parameter, a mixed-width two-ident comparison, an ident naming no parameter, a value behind a branch, and a bitwise/cast/field-read/call-result operand (`capture_rvalue`'s own documented boundary) all keep the fail-closed CoverageGap. **Read before extending:** this is the one place in the codebase where a change *broadens what is accepted*, so every relaxation must be re-run against the 34-probe red-team suite (`red_team_no_false_discharge`) AND the full PB077 e2e set (now 15 tests across three increments). |
| `extract_arg_names` index-only binding (2026-07-09 audit) | Arg names bind by `argument_index` alone without checking the debug-info place; a destructured pattern arg could attach a binding's name to the tuple local. Neutralized TODAY by the VC layer's primitive-int filter, but becomes a wrong-variable-binding vector when multi-width support widens that filter. | `pitbull-subset/src/mir_api/adapter.rs::extract_arg_names` | Require `info.value` to be a projection-free place on exactly local `i+1` before trusting the name. |
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
| Documentation: per-rule rationale | `docs/PSS-1.md` | LOW. Each of the 77 rules has a description; some lack the "why" explanation. |

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
| The 77 PSS-1 rule definitions | `crates/pitbull-subset/src/rules.rs` |
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
