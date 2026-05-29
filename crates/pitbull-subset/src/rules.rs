//! The PSS-1 rule registry.
//!
//! Each rule is a single immutable record describing one prohibited
//! construct: its identifier, its category, its rationale, and the milestone
//! at which the prohibition is expected to relax. The visitor never
//! constructs a `Rule` value — it references entries by [`RuleId`].
//!
//! The full normative text of every rule lives in `docs/PSS-1.md`. The
//! `rationale` field here is a single-sentence summary intended for
//! diagnostic output; auditors should refer to PSS-1 itself.
use serde::{Deserialize, Serialize};
use std::fmt;
/// Identifier for a PSS-1 rule.
///
/// Rules are numbered `PB001` through `PB076` (PB076 — "postcondition
/// unmet" — was added in v0.2 alongside `#[pitbull::ensures]`). The
/// numeric value is
/// stable across releases: a rule's number never changes once published, and
/// retired rules are kept in the registry as `FuturePlan::Retired` rather
/// than renumbered.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RuleId(pub u16);
impl fmt::Display for RuleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PB{:03}", self.0)
    }
}
/// PSS-1 category. Used for grouping rules in reports.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Category {
    /// A: PB001..=PB010 — unsafe operations and raw pointers.
    UnsafeOps,
    /// B: PB011..=PB020 — heap allocation, collections, drop.
    HeapAllocation,
    /// C: PB021..=PB025 — interior mutability, atomics.
    InteriorMut,
    /// D: PB026..=PB030 — concurrency, async, coroutines.
    Concurrency,
    /// E: PB031..=PB040 — dynamic dispatch, function pointers, closures.
    Dispatch,
    /// F: PB041..=PB048 — control flow, termination, panics, unwinding.
    ControlFlow,
    /// G: PB049..=PB055 — numeric primitives, overflow, floats, casts.
    Numeric,
    /// H: PB056..=PB058 — FFI and non-Rust ABI.
    Ffi,
    /// I: PB059..=PB063 — proc macros, build scripts, const-eval, cfg.
    MacroConst,
    /// J: PB064..=PB070 — specification mode hygiene.
    SpecMode,
    /// K: PB071..=PB075 — project-level configuration.
    ProjectConfig,
}
/// Disposition of a rule in a future Pitbull release.
///
/// Encoded as data because qualification assessors will ask, for every
/// restriction, "when does this relax?" The answer must be machine-readable.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FuturePlan {
    /// Planned for the named Pitbull version (e.g. `"0.2"`, `"0.3"`).
    PlannedFor(&'static str),
    /// Restriction will remain in place indefinitely.
    Permanent,
    /// Restriction will become advisory (warning-level) at the named version.
    AdvisoryAt(&'static str),
    /// The rule has been retired; preserved here for numbering stability.
    Retired,
}
/// Severity of a rule violation.
///
/// In PSS-1 v0.1 every rule is `Severity::Error` — there are no warnings.
/// The `Severity::Audit` level is reserved for v0.2 where some rules become
/// advisory (e.g. trust-budget exceedance).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Severity {
    /// Rejected; verification halts and no report is produced.
    Error,
    /// Reported but does not block verification. Reserved for v0.2+.
    Audit,
}
/// A single PSS-1 rule.
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub struct Rule {
    /// The rule's identifier (`PBnnn`).
    pub id: RuleId,
    /// Short title (≤ 60 chars), used in compiler-style headlines.
    pub title: &'static str,
    /// PSS-1 category.
    pub category: Category,
    /// Severity of a violation.
    pub severity: Severity,
    /// One-sentence rationale for the rule. Full text in `docs/PSS-1.md`.
    pub rationale: &'static str,
    /// Future disposition.
    pub future: FuturePlan,
}
// -----------------------------------------------------------------------------
// Rule ID constants.
//
// Defining each ID as a `const RuleId` rather than chasing numeric literals
// through the codebase makes greppability ironclad: every reference to PB004
// in the visitor reads as `rules::PB004`, and `cargo grep PB004` finds every
// site instantly.
// -----------------------------------------------------------------------------
// Category A: Unsafe operations.
/// Unsafe blocks.
pub const PB001: RuleId = RuleId(1);
/// Unsafe fn definition or call.
pub const PB002: RuleId = RuleId(2);
/// Unsafe trait / unsafe impl.
pub const PB003: RuleId = RuleId(3);
/// Raw pointer types.
pub const PB004: RuleId = RuleId(4);
/// Union types.
pub const PB005: RuleId = RuleId(5);
/// Inline assembly.
pub const PB006: RuleId = RuleId(6);
/// Transmute / bit-cast.
pub const PB007: RuleId = RuleId(7);
/// MaybeUninit.
pub const PB008: RuleId = RuleId(8);
/// Retag statements.
pub const PB009: RuleId = RuleId(9);
/// Deinit outside drop elaboration.
pub const PB010: RuleId = RuleId(10);
// Category B: Heap allocation.
/// Box types.
pub const PB011: RuleId = RuleId(11);
/// Vec / String / collections.
pub const PB012: RuleId = RuleId(12);
/// ShallowInitBox.
pub const PB013: RuleId = RuleId(13);
/// Custom allocators.
pub const PB014: RuleId = RuleId(14);
/// Rc / Arc / Weak.
pub const PB015: RuleId = RuleId(15);
/// Drop with non-trivial body.
pub const PB016: RuleId = RuleId(16);
/// Allocation-bearing literals.
pub const PB017: RuleId = RuleId(17);
/// Static mut / interior-mut statics.
pub const PB018: RuleId = RuleId(18);
/// Thread-local storage.
pub const PB019: RuleId = RuleId(19);
/// Implicit large stack allocation.
pub const PB020: RuleId = RuleId(20);
// Category C: Interior mutability.
/// Cell / RefCell / OnceCell.
pub const PB021: RuleId = RuleId(21);
/// UnsafeCell derivatives.
pub const PB022: RuleId = RuleId(22);
/// Atomics.
pub const PB023: RuleId = RuleId(23);
/// Mutex / RwLock / Once.
pub const PB024: RuleId = RuleId(24);
/// Volatile reads/writes.
pub const PB025: RuleId = RuleId(25);
// Category D: Concurrency.
/// Async fn / async blocks.
pub const PB026: RuleId = RuleId(26);
/// Coroutines / generators / yield.
pub const PB027: RuleId = RuleId(27);
/// Thread::spawn.
pub const PB028: RuleId = RuleId(28);
/// Send / Sync bounds.
pub const PB029: RuleId = RuleId(29);
/// Channels.
pub const PB030: RuleId = RuleId(30);
// Category E: Dispatch and higher-order.
/// Trait objects (dyn Trait).
pub const PB031: RuleId = RuleId(31);
/// Function pointers.
pub const PB032: RuleId = RuleId(32);
/// Escaping closures.
pub const PB033: RuleId = RuleId(33);
/// Higher-ranked trait bounds.
pub const PB034: RuleId = RuleId(34);
/// Const generics beyond integers.
pub const PB035: RuleId = RuleId(35);
/// Specialization.
pub const PB036: RuleId = RuleId(36);
/// GATs in spec-relevant positions.
pub const PB037: RuleId = RuleId(37);
/// Virtual trait calls (InstanceKind::Virtual).
pub const PB038: RuleId = RuleId(38);
/// Unresolvable impl Trait.
pub const PB039: RuleId = RuleId(39);
/// Recursive trait impls.
pub const PB040: RuleId = RuleId(40);
// Category F: Control flow.
/// Recursion without decreases.
pub const PB041: RuleId = RuleId(41);
/// Loops without variant.
pub const PB042: RuleId = RuleId(42);
/// Panic without unreachability proof.
pub const PB043: RuleId = RuleId(43);
/// Spec-mode non-termination.
pub const PB044: RuleId = RuleId(44);
/// TerminatorKind::TailCall.
pub const PB045: RuleId = RuleId(45);
/// FalseEdge / FalseUnwind post-cleanup.
pub const PB046: RuleId = RuleId(46);
/// `?` over non-pure paths.
pub const PB047: RuleId = RuleId(47);
/// Unwinding panic strategy.
pub const PB048: RuleId = RuleId(48);
// Category G: Numeric.
/// Overflow-checks must be on.
pub const PB049: RuleId = RuleId(49);
/// Floats.
pub const PB050: RuleId = RuleId(50);
/// Narrowing or sign-changing `as` casts.
pub const PB051: RuleId = RuleId(51);
/// Unbounded usize/isize arithmetic.
pub const PB052: RuleId = RuleId(52);
/// Char in arithmetic position.
pub const PB053: RuleId = RuleId(53);
/// Slice indexing without bound.
pub const PB054: RuleId = RuleId(54);
/// Drop glue in spec-bounded position.
pub const PB055: RuleId = RuleId(55);
// Category H: FFI.
/// Extern blocks.
pub const PB056: RuleId = RuleId(56);
/// #[no_mangle] / #[export_name].
pub const PB057: RuleId = RuleId(57);
/// Non-Rust ABI fn.
pub const PB058: RuleId = RuleId(58);
// Category I: Macros, const-eval, cfg.
/// Non-allowlisted proc macros.
pub const PB059: RuleId = RuleId(59);
/// Build scripts.
pub const PB060: RuleId = RuleId(60);
/// Const fn outside certified subset.
pub const PB061: RuleId = RuleId(61);
/// Unpinned cfg conditions.
pub const PB062: RuleId = RuleId(62);
/// Include! / include_str! / include_bytes!.
pub const PB063: RuleId = RuleId(63);
// Category J: Spec-mode hygiene.
/// Spec exprs must be pure.
pub const PB064: RuleId = RuleId(64);
/// Quantifiers over decidable domains.
pub const PB065: RuleId = RuleId(65);
/// Spec functions cannot call executable.
pub const PB066: RuleId = RuleId(66);
/// #[trusted] requires justification.
pub const PB067: RuleId = RuleId(67);
/// Trust budget threshold.
pub const PB068: RuleId = RuleId(68);
/// Spec depending on unsafe semantics.
pub const PB069: RuleId = RuleId(69);
/// Prophecies disabled in v0.1.
pub const PB070: RuleId = RuleId(70);
// Category K: Project configuration.
/// Toolchain pinning.
pub const PB071: RuleId = RuleId(71);
/// Cargo.lock required.
pub const PB072: RuleId = RuleId(72);
/// Hermetic verification.
pub const PB073: RuleId = RuleId(73);
/// Pitbull-spec version.
pub const PB074: RuleId = RuleId(74);
/// Cache signature verification.
pub const PB075: RuleId = RuleId(75);
/// Postcondition unmet. Task Q.4 (2026-05-26): added when
/// `#[pitbull::ensures("...")]` attribute coverage landed.
/// Category F (Control flow) — the postcondition's truth value
/// at every function exit (every `return`, including the
/// implicit return at end-of-body) must be provable from the
/// body's effects and the precondition set.
pub const PB076: RuleId = RuleId(76);
// -----------------------------------------------------------------------------
// The rule registry. Order is significant for reporting: rules appear in
// numeric order, grouped by category, mirroring `docs/PSS-1.md`.
// -----------------------------------------------------------------------------
/// All PSS-1 rules.
pub const RULES: &[Rule] = &[
    // --- Category A: Unsafe operations --------------------------------------
    Rule {
        id: PB001, title: "`unsafe` block", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "v0.1 lacks a separation-logic backend; existing modular \
                    verifiers that admit unsafe are unsound w.r.t. aliasing rules.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB002, title: "`unsafe fn` definition or call", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Same as PB001; includes intrinsics.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB003, title: "`unsafe trait` or `unsafe impl`", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Soundness of trait methods relies on unverified invariants.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB004, title: "raw pointer type", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Raw pointers escape the prophecy-based model for safe references.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB005, title: "`union` type", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Active-variant invariant is not tracked by the type system.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB006, title: "inline assembly", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Out of scope of any logical model.",
        future: FuturePlan::PlannedFor("1.0"),
    },
    Rule {
        id: PB007, title: "`transmute` or bit-cast", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Bypasses the type system.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB008, title: "`MaybeUninit`", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Uninitialized memory has no first-class spec in v0.1.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB009, title: "`Retag` statement in reachable MIR", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Retag indicates raw-pointer or UnsafeCell-touching MIR; \
                    its appearance post-mono is a subset-escape signal.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB010, title: "`Deinit` outside drop elaboration", category: Category::UnsafeOps,
        severity: Severity::Error,
        rationale: "Spurious Deinit indicates an unmodeled effectful operation.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    // --- Category B: Heap allocation ----------------------------------------
    Rule {
        id: PB011, title: "`Box<T>` reachable", category: Category::HeapAllocation,
        severity: Severity::Error,
        rationale: "Heap allocation requires modeling the allocator.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB012, title: "`Vec`, `String`, or `std::collections` type",
        category: Category::HeapAllocation, severity: Severity::Error,
        rationale: "Requires PB011 + invariant-laden internal unsafe.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB013, title: "`Rvalue::ShallowInitBox`", category: Category::HeapAllocation,
        severity: Severity::Error,
        rationale: "Shallow-init Box can appear from macro expansion bypassing PB011.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB014, title: "custom allocator type parameter",
        category: Category::HeapAllocation, severity: Severity::Error,
        rationale: "Allocator behavior is unbounded effectful computation.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    Rule {
        id: PB015, title: "`Rc`, `Arc`, or `Weak`",
        category: Category::HeapAllocation, severity: Severity::Error,
        rationale: "Reference-counted aliasing breaks unique ownership.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    Rule {
        id: PB016, title: "non-trivial `Drop` impl",
        category: Category::HeapAllocation, severity: Severity::Error,
        rationale: "Implicit drop sites become hidden potentially-panicking calls.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB017, title: "allocation-bearing macro (`format!`, `vec!`)",
        category: Category::HeapAllocation, severity: Severity::Error,
        rationale: "Closes PB011/PB012 from the macro-expansion side.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB018, title: "`static mut` or interior-mutable static",
        category: Category::HeapAllocation, severity: Severity::Error,
        rationale: "Concurrent mutation and aliasing without scope.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    Rule {
        id: PB019, title: "thread-local storage",
        category: Category::HeapAllocation, severity: Severity::Error,
        rationale: "Aliasing across implicit reentry.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    Rule {
        id: PB020, title: "implicit large stack allocation",
        category: Category::HeapAllocation, severity: Severity::Error,
        rationale: "Defense against stack overflow on constrained targets.",
        future: FuturePlan::Permanent,
    },
    // --- Category C: Interior mutability ------------------------------------
    Rule {
        id: PB021, title: "`Cell` or `RefCell` family",
        category: Category::InteriorMut, severity: Severity::Error,
        rationale: "Shared mutability breaks prophecy-based reasoning.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB022, title: "`UnsafeCell` or transparent wrapper",
        category: Category::InteriorMut, severity: Severity::Error,
        rationale: "The shared-mutability primitive itself.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB023, title: "atomic type or operation",
        category: Category::InteriorMut, severity: Severity::Error,
        rationale: "v0.1 has no memory-ordering reasoning.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    Rule {
        id: PB024, title: "`Mutex`, `RwLock`, or `Once`",
        category: Category::InteriorMut, severity: Severity::Error,
        rationale: "Concurrent synchronization primitives.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    Rule {
        id: PB025, title: "volatile read or write",
        category: Category::InteriorMut, severity: Severity::Error,
        rationale: "Memory-mapped I/O escapes our model.",
        future: FuturePlan::PlannedFor("1.0"),
    },
    // --- Category D: Concurrency --------------------------------------------
    Rule {
        id: PB026, title: "`async fn` or `async {}` block",
        category: Category::Concurrency, severity: Severity::Error,
        rationale: "Future poll semantics are an open research area.",
        future: FuturePlan::PlannedFor("0.5"),
    },
    Rule {
        id: PB027, title: "coroutine or generator yield",
        category: Category::Concurrency, severity: Severity::Error,
        rationale: "State-machine lowering with no verification semantics.",
        future: FuturePlan::PlannedFor("0.5"),
    },
    Rule {
        id: PB028, title: "`std::thread::spawn`",
        category: Category::Concurrency, severity: Severity::Error,
        rationale: "No concurrent semantics in v0.1.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    Rule {
        id: PB029, title: "`Send` or `Sync` bound",
        category: Category::Concurrency, severity: Severity::Error,
        rationale: "Signals concurrent intent we cannot honor in v0.1.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    Rule {
        id: PB030, title: "channel type",
        category: Category::Concurrency, severity: Severity::Error,
        rationale: "Concurrent communication.",
        future: FuturePlan::PlannedFor("0.5"),
    },
    // --- Category E: Dispatch -----------------------------------------------
    Rule {
        id: PB031, title: "trait object (`dyn Trait`)",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "v0.1 does not model vtables.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB032, title: "function pointer",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Target is data, not a known item.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB033, title: "escaping closure",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Captured-environment specs are not in v0.1.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB034, title: "higher-ranked trait bound (`for<'a>`)",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Interaction with prophecies unspecified.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB035, title: "const generic of non-integer type",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Encoding open.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB036, title: "specialization feature",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Specialization soundness is open in upstream Rust.",
        future: FuturePlan::Permanent, // until upstream stabilizes
    },
    Rule {
        id: PB037, title: "GAT in reachable signature",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Interaction with prophecies unresolved.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB038, title: "virtual trait call (`InstanceKind::Virtual`)",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Vtable indirection at the MIR level.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB039, title: "unresolvable `impl Trait`",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Existential the verifier cannot pin at call site.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB040, title: "recursive trait impl without certificate",
        category: Category::Dispatch, severity: Severity::Error,
        rationale: "Non-terminating trait resolution.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    // --- Category F: Control flow -------------------------------------------
    Rule {
        id: PB041, title: "recursion without `#[decreases]`",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "Non-termination defeats AoRTE and breaks spec consistency.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB042, title: "loop without `#[variant]`",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "Termination measure required.",
        future: FuturePlan::AdvisoryAt("0.2"),
    },
    Rule {
        id: PB043, title: "panic without unreachability proof",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "The AoRTE goal itself.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB044, title: "non-terminating spec function",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "Spec inconsistency makes every proof vacuous.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB045, title: "`TerminatorKind::TailCall` (`become` keyword)",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "Stack-frame collapse not modeled.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB046, title: "`FalseEdge` or `FalseUnwind` post-cleanup",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "Should not appear at the MIR phase we analyze; fail-closed signal.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB047, title: "`?` operator over non-pure path",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "Implicit early return through unspecified trait method.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB048, title: "panic strategy is `unwind`",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "v0.1 assumes panic-abort.",
        future: FuturePlan::PlannedFor("0.4"),
    },
    // --- Category G: Numeric ------------------------------------------------
    Rule {
        id: PB049, title: "`overflow-checks` disabled",
        category: Category::Numeric, severity: Severity::Error,
        rationale: "Proofs and binary semantics must agree on overflow handling.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB050, title: "floating-point type or operation",
        category: Category::Numeric, severity: Severity::Error,
        rationale: "No FP prelude in v0.1.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB051, title: "narrowing or sign-changing `as` cast",
        category: Category::Numeric, severity: Severity::Error,
        rationale: "Truncation needs explicit obligation.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    Rule {
        id: PB052, title: "unbounded `usize`/`isize` arithmetic",
        category: Category::Numeric, severity: Severity::Error,
        rationale: "Platform-width-dependent overflow on small MCUs.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB053, title: "`char` in arithmetic position",
        category: Category::Numeric, severity: Severity::Error,
        rationale: "21-bit value with surrogate gaps requires a dedicated theory.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB054, title: "slice index without bound proof",
        category: Category::Numeric, severity: Severity::Error,
        rationale: "Dominant AoRTE obligation; called out for diagnostic clarity.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB055, title: "non-trivial Drop in spec-bounded position",
        category: Category::Numeric, severity: Severity::Error,
        rationale: "Spec mode is pure; drop is effectful.",
        future: FuturePlan::Permanent,
    },
    // --- Category H: FFI ----------------------------------------------------
    Rule {
        id: PB056, title: "`extern` block",
        category: Category::Ffi, severity: Severity::Error,
        rationale: "Foreign code is outside any model.",
        future: FuturePlan::PlannedFor("1.0"),
    },
    Rule {
        id: PB057, title: "`#[no_mangle]` or `#[export_name]`",
        category: Category::Ffi, severity: Severity::Error,
        rationale: "Caller's contract obligations are out of our control.",
        future: FuturePlan::PlannedFor("1.0"),
    },
    Rule {
        id: PB058, title: "non-Rust ABI",
        category: Category::Ffi, severity: Severity::Error,
        rationale: "Closes loop on PB056/PB057.",
        future: FuturePlan::PlannedFor("1.0"),
    },
    // --- Category I: Macros, const-eval, cfg --------------------------------
    Rule {
        id: PB059, title: "non-allowlisted proc macro",
        category: Category::MacroConst, severity: Severity::Error,
        rationale: "Proc macros run arbitrary compile-time code; we pin a vetted set.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB060, title: "`build.rs` in reachable crate",
        category: Category::MacroConst, severity: Severity::Error,
        rationale: "Build scripts generate code outside our view.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB061, title: "`const fn` outside certified subset",
        category: Category::MacroConst, severity: Severity::Error,
        rationale: "Const-eval is tracked against Ferrocene's certified subset.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB062, title: "unpinned `cfg` condition",
        category: Category::MacroConst, severity: Severity::Error,
        rationale: "Verified build must equal deployed build.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB063, title: "`include!` / `include_str!` / `include_bytes!`",
        category: Category::MacroConst, severity: Severity::Error,
        rationale: "Source comes from outside the verified crate root.",
        future: FuturePlan::AdvisoryAt("0.2"),
    },
    // --- Category J: Spec-mode hygiene --------------------------------------
    Rule {
        id: PB064, title: "non-pure call in spec expression",
        category: Category::SpecMode, severity: Severity::Error,
        rationale: "Spec language must be effect-free.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB065, title: "quantifier over undecidable domain",
        category: Category::SpecMode, severity: Severity::Error,
        rationale: "Unbounded quantifiers over user ADTs are not decidable.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB066, title: "pure function calling executable function",
        category: Category::SpecMode, severity: Severity::Error,
        rationale: "Mode separation.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB067, title: "`#[trusted]` without justification",
        category: Category::SpecMode, severity: Severity::Error,
        rationale: "Trust is the soundest pathway to lies; every assumption gets a paper trail.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB068, title: "trust budget exceeded",
        category: Category::SpecMode, severity: Severity::Error,
        rationale: "Defense against trust creep.",
        future: FuturePlan::AdvisoryAt("0.2"),
    },
    Rule {
        id: PB069, title: "spec depends on `unsafe` semantics",
        category: Category::SpecMode, severity: Severity::Error,
        rationale: "Even safe-bodied functions inherit unsafe obligations through spec.",
        future: FuturePlan::PlannedFor("0.3"),
    },
    Rule {
        id: PB070, title: "prophecy syntax (`^x`) used",
        category: Category::SpecMode, severity: Severity::Error,
        rationale: "Reserved for v0.2 once tutorial and UX are in place.",
        future: FuturePlan::PlannedFor("0.2"),
    },
    // --- Category K: Project configuration ----------------------------------
    Rule {
        id: PB071, title: "toolchain not pinned to Pitbull-supported pair",
        category: Category::ProjectConfig, severity: Severity::Error,
        rationale: "Verification is per-compiler.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB072, title: "missing `Cargo.lock`",
        category: Category::ProjectConfig, severity: Severity::Error,
        rationale: "Verification is per-version.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB073, title: "verification environment not hermetic",
        category: Category::ProjectConfig, severity: Severity::Error,
        rationale: "Side effects taint the result.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB074, title: "`pitbull-spec` version mismatch",
        category: Category::ProjectConfig, severity: Severity::Error,
        rationale: "Spec macros and verifier must agree on attribute encoding.",
        future: FuturePlan::Permanent,
    },
    Rule {
        id: PB075, title: "unsigned cache entry under `--release`",
        category: Category::ProjectConfig, severity: Severity::Error,
        rationale: "Defense against cache poisoning.",
        future: FuturePlan::Permanent,
    },
    // --- Category L (extends F): Postconditions -----------------------------
    // Task Q.4 (2026-05-26): added when `#[pitbull::ensures(...)]`
    // attribute coverage landed. v0.2 MVP emits the obligation;
    // `pitbull-vc::compile` returns None (pending) until the
    // body-effect encoder lands in Q.4a.
    Rule {
        id: PB076, title: "postcondition unmet",
        category: Category::ControlFlow, severity: Severity::Error,
        rationale: "Spec-declared exit condition must hold at every return.",
        future: FuturePlan::Permanent,
    },
];
/// Look up a rule by id. Panics in debug, returns `None` in release if the id
/// is unknown — callers should refer to rules through the `PB001`-style
/// constants above, which makes this lookup mostly redundant outside of
/// diagnostic rendering.
#[must_use]
pub fn lookup(id: RuleId) -> Option<&'static Rule> {
    RULES.iter().find(|r| r.id == id)
}
#[cfg(test)]
mod tests {
    use super::*;
    /// Invariant: the registry contains exactly `RULE_COUNT` rules and they
    /// are numbered contiguously from 1.
    #[test]
    fn registry_is_contiguous() {
        assert_eq!(RULES.len(), crate::RULE_COUNT);
        for (i, rule) in RULES.iter().enumerate() {
            assert_eq!(
                rule.id.0 as usize,
                i + 1,
                "rule at index {i} has non-contiguous id {}",
                rule.id
            );
        }
    }
    /// Invariant: every rule constant matches the corresponding registry entry.
    #[test]
    fn constants_align_with_registry() {
        let constants = [
            PB001, PB002, PB003, PB004, PB005, PB006, PB007, PB008, PB009, PB010,
            PB011, PB012, PB013, PB014, PB015, PB016, PB017, PB018, PB019, PB020,
            PB021, PB022, PB023, PB024, PB025,
            PB026, PB027, PB028, PB029, PB030,
            PB031, PB032, PB033, PB034, PB035, PB036, PB037, PB038, PB039, PB040,
            PB041, PB042, PB043, PB044, PB045, PB046, PB047, PB048,
            PB049, PB050, PB051, PB052, PB053, PB054, PB055,
            PB056, PB057, PB058,
            PB059, PB060, PB061, PB062, PB063,
            PB064, PB065, PB066, PB067, PB068, PB069, PB070,
            PB071, PB072, PB073, PB074, PB075,
            PB076,
        ];
        assert_eq!(constants.len(), RULES.len());
        for (k, c) in constants.iter().enumerate() {
            assert_eq!(*c, RULES[k].id);
        }
    }
    /// Every rule has non-empty title and rationale.
    #[test]
    fn rules_have_metadata() {
        for rule in RULES {
            assert!(!rule.title.is_empty(), "{} has empty title", rule.id);
            assert!(!rule.rationale.is_empty(), "{} has empty rationale", rule.id);
            assert!(rule.title.len() <= 80, "{} title too long for diagnostics", rule.id);
        }
    }
}
