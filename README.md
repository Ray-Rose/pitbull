# Pitbull
A deductive verifier for Rust, in the lineage of GNATprove for SPARK.
Pitbull proves that Rust code in its verifiable subset cannot panic, overflow,
or index out of bounds. It is intentionally narrow in scope: it is a
soundness-bearing tool, and its first commitment is to tell the truth about
what it has and has not proven.
## What v0.1 guarantees
For any function annotated `#[pitbull::verify]` whose body and transitive
reachable callees satisfy the **Pitbull Verifiable Subset (PSS-1)**, Pitbull
proves the **Absence of Runtime Errors (AoRTE)**:
- No reachable `panic!`, `unwrap`, `expect`, or `unreachable!` call site
- No integer arithmetic overflow under `overflow-checks = true` semantics
- No out-of-bounds slice indexing
- No division or modulo by zero
- No construction of invalid primitive values (e.g. `bool` from arbitrary bits)
If Pitbull reports `verified`, and the verified crate is compiled with the
Pitbull-pinned toolchain, and the user has not introduced unsound
`#[pitbull::trusted]` annotations, then the resulting binary will not exhibit
any of the failure modes above on any input.
## What v0.1 deliberately refuses to handle
PSS-1 forbids the following constructs in any code reachable from a verified
entry point. Pitbull rejects them at compile time; this is not a warning:
- `unsafe` in any form: blocks, `fn`, `trait`, `impl`
- Raw pointers, `UnsafeCell`, `MaybeUninit`, `transmute`, inline assembly
- Heap allocation: `Box`, `Vec`, `String`, all `std::collections`
- Reference counting: `Rc`, `Arc`, `Weak`
- Interior mutability: `Cell`, `RefCell`, `OnceCell`, atomics
- Concurrency: `thread::spawn`, `Mutex`, channels, `Send`/`Sync` requirements
- `async`/`await`, coroutines, generators
- Trait objects (`dyn Trait`), function pointers, escaping closures
- Float arithmetic (deferred to v0.3)
- FFI (`extern` blocks)
- Build scripts, non-allowlisted proc macros, `include!`-family macros
- Recursion or loops without explicit `#[decreases]` / `#[variant]` clauses
See `docs/PSS-1.md` for the normative specification.

**Enforcement status (v0.2 scaffold).** The core memory-safety rules above
are enforced today: unsafe blocks/`fn`/`trait`/`impl`, FFI (`extern`
blocks / `#[no_mangle]` / `#[export_name]` / non-Rust ABI), heap &
collections, interior mutability, concurrency primitives, trait objects /
fn-pointers / closures, floats, `as` casts, slice bounds, and overflow. A
few constructs are specified but **not yet fully enforced** by the v0.2
scaffold — loop/recursion termination (PB041/PB042) and implicit drop-glue
under `verify_roots` narrowing — each tracked per-rule in `docs/PSS-1.md`
§17.1. The panic of a *library method* lives inside un-walked `core`, so it
is caught at the call site. As of the **prelude flip** this boundary is
**fail-closed by default** (`verification.strict_library_acceptance`): a call
into `core`/`std`/`alloc` is accepted only if it is on the explicit
*trusted-total* allow-list (`is_trusted_total_library_call` — the
`wrapping_*`/`checked_*`/`saturating_*` int methods, `Ord::min`/`max`/`clamp`,
`From`/`TryFrom`, the total `char`/slice/`Option`/`Result` methods, …);
**any other stdlib call fails closed as a coverage gap (exit 1)**, whether or
not we have separately enumerated it as panicking. The enumerated panicking
families — `unwrap`/`expect`; the panicking int methods
`pow`/`abs`/`div_euclid`/`div_ceil`/`next_multiple_of`/`from_str_radix`/signed
`isqrt`/the `strict_*` family; `Iterator::sum`/`product`/`step_by`; the `char`
radix/encode methods; `str`/slice range indexing and
`split_at`/`swap`/`copy_from_slice`/`chunks`/`as_chunks`/… — still produce a
precise `(PB043)` diagnostic, but they are now an *optimization over* the
fail-closed default, not the safety boundary itself: an un-modelled panicking
stdlib method can no longer be silently trusted. Operator-form arithmetic
(`x * y`) and element-projection indexing (`a[i]`) are covered by PB049/PB054
regardless. The residual is now the *inverse* and far smaller: a genuinely
*total* stdlib method the allow-list does not yet enumerate is **conservatively
rejected** (a false *reject*, never a false discharge) until it is added — see
`docs/SAFETY-MANUAL.md` §3.6.
Pitbull will not claim to have proven what it has not: an unimplemented
rule is a documented gap, never a silent pass.
## Why this list looks brutal
It is the same list SPARK started with. The deal SPARK has kept with its users
for forty years is: tell us what we are not allowed to do, and in exchange we
tell you the truth about what you have done. Pitbull makes the same deal.
The constructs we forbid are not forbidden because they are bad — they are
forbidden because v0.1 does not have a sound model for them yet. Each rule has
a tracked `Future` plan in `docs/PSS-1.md`.
## Toolchain
Pitbull pins to a specific nightly that matches pur fork of Creusot's translator. Use `rust-toolchain.toml` in your project root:
```toml
[toolchain]
channel = "nightly-2026-01-29"
components = ["rustc-dev", "llvm-tools-preview"]
```
For ISO 26262 / IEC 61508 / DO-178C qualified deployment, Pitbull layers on
top of Ferrocene. The Pitbull qualification kit is in `qualification/`
(separately versioned, separately maintained).
## Not in scope
Pitbull does not prove timing, side-channel resistance, or non-interference.
It does not re-verify the compiler beneath it. It does not detect hardware
faults. For those concerns, use the appropriate tool — and combine results,
do not substitute.
## License
Dual MIT / Apache-2.0.
