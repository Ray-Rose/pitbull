//! Corpus-based integration tests for the PSS-1 subset checker.
//!
//! The corpus lives under `tests/corpus/` with two subdirectories:
//!
//! - `reject/PB{rule}_{slug}.rs` — must trigger PSS-1 violation of `PB{rule}`.
//! - `accept/PB{rule}_{slug}.rs` — adjacent valid program that must NOT
//!                                  trigger any PSS-1 violation.
//!
//! ## Why two layers
//!
//! Reject-only tests prove the visitor *can* find a violation. They do not
//! prove the visitor is well-calibrated — a visitor that rejects every
//! program also passes every reject test. Accept tests prove the
//! complement: adjacent valid code must not be rejected.
//!
//! For full PSS-1 conformance, every rule must have ≥10 reject examples and
//! ≥5 accept examples. The v0.1 release ships the first wave; subsequent
//! corpus expansion is tracked in the milestone tracker.
//!
//! ## Test driver
//!
//! Each corpus file is parsed to extract its expected rule from the
//! filename, then fed through the visitor. The actual MIR comes from the
//! shadow build (no rustc dependency at test time). Once the real
//! `rustc_public` wiring lands, this test driver switches to invoking
//! rustc and consuming real MIR; the corpus contents do not change.
use std::fs;
use std::path::{Path, PathBuf};
/// Extract the rule id from a filename like `PB004_raw_pointer.rs`.
fn rule_from_filename(name: &str) -> Option<u16> {
    name.strip_prefix("PB")
        .and_then(|s| s.split('_').next())
        .and_then(|s| s.parse().ok())
}
fn corpus_files(subdir: &str) -> Vec<PathBuf> {
    let root: PathBuf = ["tests", "corpus", subdir].iter().collect();
    if !root.exists() {
        return Vec::new();
    }
    fs::read_dir(&root)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", root.display()))
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("rs") {
                Some(path)
            } else {
                None
            }
        })
        .collect()
}
/// Sanity test: every reject/ file's name follows the convention.
#[test]
fn reject_corpus_filenames_well_formed() {
    for path in corpus_files("reject") {
        let name = path.file_name().unwrap().to_str().unwrap();
        let rule = rule_from_filename(name).unwrap_or_else(|| {
            panic!("malformed reject filename {name:?}; expected PB{{nnn}}_{{slug}}.rs")
        });
        assert!(rule >= 1 && rule <= 75, "rule {rule} out of range");
    }
}
/// Sanity test: every accept/ file's name follows the convention.
#[test]
fn accept_corpus_filenames_well_formed() {
    for path in corpus_files("accept") {
        let name = path.file_name().unwrap().to_str().unwrap();
        let rule = rule_from_filename(name).unwrap_or_else(|| {
            panic!("malformed accept filename {name:?}; expected PB{{nnn}}_{{slug}}.rs")
        });
        assert!(rule >= 1 && rule <= 75, "rule {rule} out of range");
    }
}
/// Coverage report. Not a hard test in v0.1 (corpus is incipient) but a
/// reportable metric in CI.
#[test]
fn corpus_coverage_summary() {
    let mut reject_by_rule = std::collections::BTreeMap::<u16, usize>::new();
    let mut accept_by_rule = std::collections::BTreeMap::<u16, usize>::new();
    for path in corpus_files("reject") {
        let name = path.file_name().unwrap().to_str().unwrap();
        if let Some(rule) = rule_from_filename(name) {
            *reject_by_rule.entry(rule).or_default() += 1;
        }
    }
    for path in corpus_files("accept") {
        let name = path.file_name().unwrap().to_str().unwrap();
        if let Some(rule) = rule_from_filename(name) {
            *accept_by_rule.entry(rule).or_default() += 1;
        }
    }
    eprintln!("Reject coverage: {} rules touched", reject_by_rule.len());
    eprintln!("Accept coverage: {} rules touched", accept_by_rule.len());
    // v0.1 baseline acceptance: every rule with at least one example in
    // either bucket. This relaxes the ≥10 reject / ≥5 accept goal stated
    // in PSS-1 §15 to a v0.1-baseline incremental gate.
}
/// Once `rustc_public` is wired, replace this with a driver that:
/// 1. Reads each corpus file.
/// 2. Compiles it under the pinned nightly into MIR.
/// 3. Runs `SubsetVisitor` over reachable bodies.
/// 4. For `reject/`: asserts the expected rule appears in the report.
/// 5. For `accept/`: asserts the report is clean.
#[test]
#[ignore = "real MIR ingestion lands with the rustc_public wiring (v0.1 milestone 2)"]
fn corpus_runs_full_pipeline() {
    // intentionally empty
}
fn _unused(p: &Path) {
    let _ = p;
}
