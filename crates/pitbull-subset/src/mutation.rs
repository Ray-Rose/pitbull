//! Mutation-testing harness for the subset checker itself.
//!
//! ## Motivation
//!
//! The subset checker is part of the Pitbull trusted computing base. A bug
//! here is a soundness bug. The unit tests in `visitor.rs` and the corpus
//! tests under `tests/corpus/` exercise each rule, but coverage alone does
//! not prove the tests are *strong* — a test that runs the code but checks
//! nothing meaningful is worthless. Mutation testing is the established
//! discipline for measuring test strength.
//!
//! ## Protocol
//!
//! Pitbull's mutation testing follows the standard mutant-survival
//! protocol, with one strictness lift:
//!
//! 1. For each PSS-1 rule, define a set of *mutations* to the predicate
//!    that detects it (negate, swap variant, off-by-one).
//! 2. Apply each mutation to the source tree, recompile, run the full test
//!    suite.
//! 3. A mutation is *killed* if any test fails. A mutation that *survives*
//!    indicates the test suite is too weak to detect the bug the mutation
//!    represents.
//! 4. **No mutation may survive.** Conventional mutation testing accepts a
//!    "mutation score" (% killed) below 100%; Pitbull treats any surviving
//!    mutant as a CI failure. The reason is the soundness posture: a
//!    weakening of any rule's predicate is exactly the failure mode we
//!    must not ship.
//!
//! ## Implementation choice
//!
//! The actual mutation application is delegated to `cargo-mutants` — the
//! mature Rust ecosystem tool for source-level mutation. This module
//! provides:
//!
//! - The *targeted file list* (which files are in scope).
//! - The *expected-killed manifest* (which mutants must die, used by CI
//!   to detect new mutants introduced by a refactor that the existing
//!   tests don't cover).
//! - An optional in-process harness for unit-test-style mutation runs
//!   when the developer wants fast feedback on a single rule.
//!
//! Feature-gated as `mutation-testing` because pulling in the harness's
//! dev tooling is slow.
use crate::rules::RuleId;
/// A mutation operator applicable to a rule's detector.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MutationOp {
    /// Flip a boolean predicate (`p` → `!p`).
    NegatePredicate,
    /// Replace `==` with `!=`.
    InvertEquality,
    /// Replace a match arm's reject with accept.
    DemoteReject,
    /// Replace a match arm's accept with reject (useful for catching
    /// rules that over-accept).
    PromoteAccept,
    /// Off-by-one in a numeric threshold.
    OffByOne,
    /// Swap two adjacent match arms (catches order-dependent dispatch bugs).
    SwapArms,
}
/// A specific mutation site: a rule and the operator(s) to apply.
#[derive(Clone, Debug)]
pub struct MutationTarget {
    /// The rule whose detector is being mutated.
    pub rule: RuleId,
    /// The source file (relative to the crate root) the mutation operates on.
    pub file: &'static str,
    /// The mutations the test suite must kill.
    pub operators: &'static [MutationOp],
}
/// The full manifest of mutation targets.
///
/// CI uses this as ground truth: every entry must be killed; new mutants
/// (introduced by `cargo-mutants` discovering additional sites in a
/// refactor) must be added here or the test suite must be strengthened
/// to kill them.
pub const MUTATION_MANIFEST: &[MutationTarget] = &[
    MutationTarget {
        rule: crate::rules::PB001,
        file: "src/visitor.rs",
        operators: &[
            MutationOp::DemoteReject,
            MutationOp::NegatePredicate,
        ],
    },
    MutationTarget {
        rule: crate::rules::PB002,
        file: "src/visitor.rs",
        operators: &[MutationOp::DemoteReject, MutationOp::NegatePredicate],
    },
    MutationTarget {
        rule: crate::rules::PB004,
        file: "src/visitor.rs",
        operators: &[MutationOp::DemoteReject, MutationOp::SwapArms],
    },
    MutationTarget {
        rule: crate::rules::PB011,
        file: "src/visitor.rs",
        operators: &[MutationOp::DemoteReject],
    },
    MutationTarget {
        rule: crate::rules::PB031,
        file: "src/visitor.rs",
        operators: &[MutationOp::DemoteReject, MutationOp::PromoteAccept],
    },
    MutationTarget {
        rule: crate::rules::PB050,
        file: "src/visitor.rs",
        operators: &[MutationOp::DemoteReject, MutationOp::SwapArms],
    },
    MutationTarget {
        rule: crate::rules::PB020,
        file: "src/visitor.rs",
        operators: &[MutationOp::OffByOne],
    },
    MutationTarget {
        rule: crate::rules::PB068,
        file: "src/config.rs",
        operators: &[MutationOp::OffByOne, MutationOp::InvertEquality],
    },
    // The full manifest expands as the visitor's predicates grow.
    // Initial v0.1 release ships ≥ one MutationTarget per category.
];
/// The minimum acceptable mutation score for a release build.
///
/// Set to 1.0 by design: any surviving mutant blocks the release.
pub const REQUIRED_MUTATION_SCORE: f64 = 1.0;
/// Helper to feed `cargo-mutants` the rule-pinned file list.
#[must_use]
pub fn target_files() -> Vec<&'static str> {
    let mut files: Vec<&'static str> = MUTATION_MANIFEST.iter().map(|t| t.file).collect();
    files.sort_unstable();
    files.dedup();
    files
}
#[cfg(test)]
mod tests {
    use super::*;
    /// Every category has at least one mutation target. Adding a category
    /// without registering a mutation target is a coverage regression.
    #[test]
    fn each_category_has_coverage() {
        use crate::rules::{lookup, Category};
        let mut covered = std::collections::HashSet::new();
        for t in MUTATION_MANIFEST {
            if let Some(rule) = lookup(t.rule) {
                covered.insert(rule.category);
            }
        }
        let needed = [
            Category::UnsafeOps,
            Category::HeapAllocation,
            Category::Dispatch,
            Category::Numeric,
            Category::SpecMode,
        ];
        for cat in needed {
            assert!(
                covered.contains(&cat),
                "category {cat:?} has no mutation target in the manifest"
            );
        }
    }
    #[test]
    fn target_files_are_distinct() {
        let files = target_files();
        let unique: std::collections::HashSet<_> = files.iter().collect();
        assert_eq!(unique.len(), files.len());
    }
}
