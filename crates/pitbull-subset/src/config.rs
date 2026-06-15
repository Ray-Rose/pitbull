//! Project-level configuration for the subset checker.
//!
//! The `pitbull.toml` file at the verified crate root is the single source of
//! truth for project-wide verification policy: stack-allocation limit, trust
//! budget, allowed proc macros, trusted build scripts, target pointer width,
//! panic strategy, and the set of `#[pitbull::verify]` root paths.
//!
//! ## Why a separate file from `Cargo.toml`?
//!
//! - Cargo's `[package.metadata]` is per-package; Pitbull configures the
//!   whole verification surface (roots may span workspace members).
//! - We want the verification policy under explicit version control and
//!   reviewable as a unit — diffs to `pitbull.toml` should jump out in code
//!   review.
//! - It mirrors Creusot's design: the upstream tool uses a separate field
//!   `default-members` under `[package.metadata.creusot]` to designate
//!   verification targets distinct from `cargo build` targets. We borrow the
//!   same separation but lift it out of `Cargo.toml` for the reasons above.
//!
//! ## Validation
//!
//! Loading a config also validates it. Many PSS-1 rules are config-level
//! (PB048 panic strategy, PB049 overflow-checks, PB068 trust budget,
//! PB071–PB075 project hygiene), so failed validation produces
//! `SubsetError`s rather than panics or `io::Error`s — they belong in the
//! same diagnostic stream as MIR-level violations.
use crate::diagnostic::SubsetError;
use crate::mir_api::Span;
use crate::rules::{
    self, PB048, PB049, PB060, PB068, PB071, PB072, PB073, PB074, PB075,
};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
/// Project-level configuration loaded from `pitbull.toml`.
///
/// Every field maps one-to-one with a documented entry in the example config.
/// Adding a field here without updating `pitbull.toml.example` is a
/// documentation regression that CI catches.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SubsetConfig {
    /// `[project]` section.
    pub project: ProjectSection,
    /// `[verification]` section.
    #[serde(default)]
    pub verification: VerificationSection,
    /// `[subset]` section.
    #[serde(default)]
    pub subset: SubsetSection,
    /// `[reachability]` section.
    #[serde(default)]
    pub reachability: ReachabilitySection,
    /// `[reporting]` section.
    #[serde(default)]
    pub reporting: ReportingSection,
    /// `[cache]` section.
    #[serde(default)]
    pub cache: CacheSection,
}
/// `[project]` — identity and toolchain pinning.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProjectSection {
    /// Crate name. Must match the verified `Cargo.toml`.
    pub name: String,
    /// PSS-1 PB071 / PB074: pinned Pitbull-toolchain identifier.
    pub toolchain: String,
}
/// `[verification]` — solver policy.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerificationSection {
    /// Per-VC timeout, seconds.
    #[serde(default = "default_vc_timeout")]
    pub vc_timeout_seconds: u64,
    /// 2-of-3 solver agreement threshold.
    #[serde(default = "default_solver_agreement")]
    pub solver_agreement: u8,
    /// Solver names in the pool.
    #[serde(default = "default_solvers")]
    pub solvers: Vec<String>,
    /// Pinned solver versions. The map's keys are solver names.
    #[serde(default)]
    pub solver_versions: std::collections::BTreeMap<String, String>,
    /// If true, the subset checker rejects reachable panic calls during
    /// `pitbull check` instead of tagging them as VC obligations. This is
    /// the conservative posture for the v0.1 demo, before the VC backend
    /// can discharge unreachability proofs. Default `false` to align with
    /// the v0.2 design where panics become proof obligations; set to `true`
    /// in v0.1 if you want subset-level panic rejection.
    #[serde(default)]
    pub strict_panic_acceptance: bool,
    /// If true (the default), COVERAGE-GAP audit notes — safety checks the
    /// visitor could not run, with no compensating VC obligation — are
    /// folded into the wrapper's exit code (exit 1), so a CI gate keyed on
    /// the exit status cannot mistake "verified except the parts I could
    /// not model" for a clean verification (the "no silent skips" posture).
    /// Set to `false` to keep coverage gaps as stderr-only notes that do
    /// not affect the verdict (the pre-2026-06-14 behavior). Transparency
    /// notes never affect the exit code regardless.
    #[serde(default = "default_fail_on_coverage_gaps")]
    pub fail_on_coverage_gaps: bool,
    /// If true (the default), the **prelude allow-list** is enforced: a call
    /// into the standard library (`core::` / `std::` / `alloc::`) that is
    /// NOT on the trusted-total allow-list
    /// ([`crate::visitor::is_trusted_total_library_call`]) and is not already
    /// caught as a known panicking method emits a COVERAGE-GAP note (so it
    /// fails closed via `fail_on_coverage_gaps`). This INVERTS the historic
    /// fail-OPEN posture where any un-enumerated stdlib call was trusted as
    /// total — under which an un-modelled panicking method was a silent false
    /// discharge. In-crate calls and user trait-impls are unaffected (they are
    /// not in a stdlib namespace and are owned by the reachability gates).
    /// Set to `false` to restore the pre-prelude trust-all-stdlib behavior
    /// (e.g. while migrating a crate whose total stdlib surface the prelude
    /// does not yet enumerate). See `docs/SAFETY-MANUAL.md` §3.6.
    #[serde(default = "default_strict_library_acceptance")]
    pub strict_library_acceptance: bool,
    /// Per-function precondition lists. Keys are fully-qualified
    /// function paths (matched against `CrateDef::name()` for each
    /// item the wrapper walks). Values are arrays of SMT-LIB 2
    /// assertion forms that the wrapper attaches as VC-obligation
    /// assumptions for every obligation emitted while walking the
    /// matching body.
    ///
    /// v0.2 O.1 posture: assumptions are raw SMT-LIB strings — the
    /// user is responsible for matching operand positions
    /// (`lhs` / `rhs`) to the function's parameters. O.2 (the next
    /// commit) introduces a small predicate grammar
    /// (`<ident> <cmp> <int>`); O.3 wires
    /// `#[pitbull::requires(...)]` extraction.
    ///
    /// Example:
    /// ```toml
    /// [verification.preconditions]
    /// "my_crate::add_one" = ["(assert (bvult lhs #x00000064))"]
    /// ```
    #[serde(default)]
    pub preconditions: std::collections::BTreeMap<String, Vec<String>>,
}
impl Default for VerificationSection {
    fn default() -> Self {
        Self {
            vc_timeout_seconds: default_vc_timeout(),
            solver_agreement: default_solver_agreement(),
            solvers: default_solvers(),
            solver_versions: std::collections::BTreeMap::new(),
            strict_panic_acceptance: false,
            fail_on_coverage_gaps: default_fail_on_coverage_gaps(),
            strict_library_acceptance: default_strict_library_acceptance(),
            preconditions: std::collections::BTreeMap::new(),
        }
    }
}
/// Default for `verification.fail_on_coverage_gaps`: `true` (fail closed —
/// a coverage gap drives the exit code so it cannot be mistaken for a clean
/// verification by a CI gate).
fn default_fail_on_coverage_gaps() -> bool {
    true
}
/// Default for `verification.strict_library_acceptance`: `true` (fail closed —
/// the prelude allow-list is enforced, so an un-modelled stdlib call is a
/// visible coverage gap rather than a silent trust-as-total false discharge).
fn default_strict_library_acceptance() -> bool {
    true
}
fn default_vc_timeout() -> u64 { 60 }
fn default_solver_agreement() -> u8 { 2 }
fn default_solvers() -> Vec<String> {
    // Default agreement pool: z3 + cvc5. Both fully support the
    // QF_BV bit-vector logic Pitbull emits (verified empirically
    // 2026-05-28: both decide `bvuaddo`/`bvsdiv`/`bvshl` problems).
    // Alt-Ergo is intentionally NOT in the default set — Alt-Ergo
    // 2.4.0 has no bit-vector theory ("Bitvector not yet supported",
    // "Undefined sort BitVec"), so it can never discharge an
    // overflow/index obligation and would only ever dilute the
    // agreement pool. Users targeting a future BV-capable Alt-Ergo
    // can add it explicitly via `[verification] solvers`.
    vec!["z3".into(), "cvc5".into()]
}
/// `[subset]` — PSS-1 enforcement knobs.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SubsetSection {
    /// PSS-1 PB020: per-local stack allocation limit, bytes.
    #[serde(default = "default_stack_limit")]
    pub stack_allocation_limit_bytes: u64,
    /// PSS-1 PB052: target pointer width, bits. Must be 16, 32, or 64.
    ///
    /// SCOPE (audit M, 2026-06-14): this width drives PB020 stack-size
    /// estimation. The PB054 **index-bound** SMT encoding, however, currently
    /// models indices/lengths at a fixed 64-bit width regardless of this
    /// setting — a SOUND over-approximation (a 64-bit `unsat` implies `unsat`
    /// at any narrower true width, since the narrower domain is a subset), so
    /// no false discharge, but on a 16/32-bit target it may fail to discharge
    /// a bound that is only provable using the narrower `usize` range. Native
    /// per-width index modeling is tracked completeness work; see
    /// `pitbull-vc/src/smt.rs::INDEX_SMT_BITS` and `docs/SAFETY-MANUAL.md` §3.
    #[serde(default = "default_pointer_width")]
    pub target_pointer_width: u8,
    /// PSS-1 PB048: panic strategy, must be `"abort"` in v0.1.
    #[serde(default = "default_panic_strategy")]
    pub panic_strategy: String,
    /// PSS-1 PB068: trust budget as a fraction of total verified lines.
    #[serde(default = "default_trust_budget")]
    pub trust_budget_fraction: f64,
    /// PSS-1 PB059: proc-macro allowlist.
    #[serde(default = "default_allowed_proc_macros")]
    pub allowed_proc_macros: Vec<String>,
    /// PSS-1 PB060: explicitly trusted build scripts with content hashes.
    #[serde(default)]
    pub trusted_build_scripts: Vec<TrustedBuildScript>,
}
impl Default for SubsetSection {
    fn default() -> Self {
        Self {
            stack_allocation_limit_bytes: default_stack_limit(),
            target_pointer_width: default_pointer_width(),
            panic_strategy: default_panic_strategy(),
            trust_budget_fraction: default_trust_budget(),
            allowed_proc_macros: default_allowed_proc_macros(),
            trusted_build_scripts: Vec::new(),
        }
    }
}
fn default_stack_limit() -> u64 { 65_536 }
fn default_pointer_width() -> u8 { 64 }
fn default_panic_strategy() -> String { "abort".into() }
fn default_trust_budget() -> f64 { 0.05 }
fn default_allowed_proc_macros() -> Vec<String> {
    vec!["pitbull-spec".into()]
}
/// Toolchain crates whose macros are part of the trusted base and are
/// never subject to the PB059 proc-macro allowlist (built-in derives
/// like `Debug`/`Clone`, and std macros like `vec!`/`format!`, are
/// defined in these crates).
const PB059_TRUSTED_MACRO_CRATES: &[&str] = &["core", "std", "alloc", "proc_macro"];
/// PB059 decision (PURE, no rustc types — unit-testable on stable):
/// should an item generated by a derive/attribute macro DEFINED in
/// `macro_crate` be rejected, given the `allowed` proc-macro allowlist?
///
/// `is_local` is true when the macro is defined in the crate under
/// verification (the user's own macro — never rejected). A macro from
/// a trusted toolchain crate ([`PB059_TRUSTED_MACRO_CRATES`]) is never
/// rejected. Otherwise the macro's crate must appear on the allowlist.
///
/// Crate-name normalization: rustc reports crate names with underscores
/// (`serde_derive`), while `pitbull.toml` allowlists are commonly
/// written with hyphens (`serde-derive`, `pitbull-spec`); both sides
/// are normalized (`-` → `_`) before comparison so either spelling
/// works.
///
/// Note: this is intended for `MacroKind::Derive`/`Attr` expansions
/// only — derive and attribute macros cannot be written with
/// `macro_rules!` (those are always function-like `Bang`), and built-in
/// derives live in the trusted crates above, so a Derive/Attr macro
/// from a non-trusted, non-local crate is, by construction, an external
/// proc-macro. This keeps the rule free of `macro_rules!` false
/// positives.
#[must_use]
pub fn pb059_proc_macro_rejected(macro_crate: &str, is_local: bool, allowed: &[String]) -> bool {
    if is_local {
        return false;
    }
    let norm = |s: &str| s.replace('-', "_");
    let macro_crate_n = norm(macro_crate);
    if PB059_TRUSTED_MACRO_CRATES
        .iter()
        .any(|t| *t == macro_crate_n)
    {
        return false;
    }
    !allowed.iter().any(|a| norm(a) == macro_crate_n)
}
/// An explicitly trusted `build.rs` entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustedBuildScript {
    /// Crate that owns the `build.rs`.
    #[serde(rename = "crate")]
    pub crate_name: String,
    /// SHA-256 of the `build.rs` file content (hex-encoded, lowercase).
    pub sha256: String,
    /// Human-readable rationale for the trust.
    pub reason: String,
}
/// `[reachability]` — call-graph roots and exclusions.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReachabilitySection {
    /// Item paths designated as verification roots. Glob-style with `*`
    /// trailing segment for "every item in this module."
    #[serde(default)]
    pub verify_roots: Vec<String>,
    /// Item paths excluded from reachability.
    #[serde(default)]
    pub exclude: Vec<String>,
}
/// `[reporting]` — where and how to emit results.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReportingSection {
    /// Path for the SARIF report.
    #[serde(default = "default_sarif_path")]
    pub sarif_path: PathBuf,
    /// Proof-certificate directory.
    #[serde(default = "default_certificate_dir")]
    pub certificate_dir: PathBuf,
    /// Whether to fail on certificate-replay disagreement.
    #[serde(default = "default_strict_replay")]
    pub strict_replay: bool,
}
impl Default for ReportingSection {
    fn default() -> Self {
        Self {
            sarif_path: default_sarif_path(),
            certificate_dir: default_certificate_dir(),
            strict_replay: default_strict_replay(),
        }
    }
}
fn default_sarif_path() -> PathBuf { "target/pitbull/report.sarif".into() }
fn default_certificate_dir() -> PathBuf { ".pitbull-cache/certs".into() }
fn default_strict_replay() -> bool { true }
/// `[cache]` — proof cache settings.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CacheSection {
    /// Whether the content-addressed proof cache is in use.
    #[serde(default = "default_cache_enabled")]
    pub enabled: bool,
    /// PSS-1 PB075: signing-key path for cache integrity.
    #[serde(default = "default_signing_key_path")]
    pub signing_key_path: PathBuf,
}
impl Default for CacheSection {
    fn default() -> Self {
        Self {
            enabled: default_cache_enabled(),
            signing_key_path: default_signing_key_path(),
        }
    }
}
fn default_cache_enabled() -> bool { true }
fn default_signing_key_path() -> PathBuf { ".pitbull-cache/signing.key".into() }
// -----------------------------------------------------------------------------
// Loading and validation.
// -----------------------------------------------------------------------------
/// Outcome of loading a config: the parsed config plus any PSS-1 violations
/// the config itself produces.
pub struct LoadOutcome {
    /// The parsed configuration.
    pub config: SubsetConfig,
    /// PSS-1 errors discovered during config validation.
    pub errors: Vec<SubsetError>,
}
/// Errors produced during raw TOML loading (distinct from PSS-1 errors).
#[derive(Debug, thiserror::Error)]
pub enum ConfigLoadError {
    /// Could not read the file from disk.
    #[error("could not read pitbull.toml: {0}")]
    Io(#[from] std::io::Error),
    /// Could not parse the file as TOML.
    #[error("malformed pitbull.toml: {0}")]
    Toml(#[from] toml::de::Error),
}
impl SubsetConfig {
    /// Load `pitbull.toml` from a path and validate it against PSS-1.
    pub fn load_and_validate(path: &std::path::Path) -> Result<LoadOutcome, ConfigLoadError> {
        let raw = std::fs::read_to_string(path)?;
        let config: SubsetConfig = toml::from_str(&raw)?;
        let errors = config.validate();
        Ok(LoadOutcome { config, errors })
    }
    /// Run PSS-1 config-level validations and return any violations.
    ///
    /// Project-level rules surfaced here:
    /// - PB048 panic strategy
    /// - PB049 overflow-checks: NOT yet enforced (the driver does not yet
    ///   inspect the build profile's `overflow-checks` flag) — see note
    ///   at the end of `validate`
    /// - PB068 trust budget shape (range, not actual ratio)
    /// - PB071–PB075 project hygiene
    #[must_use]
    pub fn validate(&self) -> Vec<SubsetError> {
        let mut errors = Vec::new();
        let span = Span::default(); // config violations carry the config file path elsewhere
        // PB048: panic strategy.
        if self.subset.panic_strategy != "abort" {
            errors.push(SubsetError {
                rule: PB048,
                span,
                detail: format!(
                    "panic_strategy = {:?}; must be \"abort\" in v0.1",
                    self.subset.panic_strategy
                ),
                in_spec: false,
            });
        }
        // PB068: trust budget out of [0, 1].
        if !(0.0..=1.0).contains(&self.subset.trust_budget_fraction) {
            errors.push(SubsetError {
                rule: PB068,
                span,
                detail: format!(
                    "trust_budget_fraction = {} is outside [0, 1]",
                    self.subset.trust_budget_fraction
                ),
                in_spec: false,
            });
        }
        // PB071: toolchain prefix must be a known Pitbull pinned pair. We
        // hard-code the v0.1 supported list here. New supported pairs are
        // added in lockstep with releases.
        if !is_supported_toolchain(&self.project.toolchain) {
            errors.push(SubsetError {
                rule: PB071,
                span,
                detail: format!("toolchain {:?} is not a Pitbull-supported pair", self.project.toolchain),
                in_spec: false,
            });
        }
        // PB052 sanity: pointer width must be a sensible value.
        if !matches!(self.subset.target_pointer_width, 16 | 32 | 64) {
            errors.push(SubsetError {
                rule: rules::PB052,
                span,
                detail: format!(
                    "target_pointer_width = {} is not 16, 32, or 64",
                    self.subset.target_pointer_width
                ),
                in_spec: false,
            });
        }
        // PB060: trusted build script SHA-256 must be 64 hex chars.
        for tbs in &self.subset.trusted_build_scripts {
            if !is_valid_sha256_hex(&tbs.sha256) {
                errors.push(SubsetError {
                    rule: PB060,
                    span,
                    detail: format!(
                        "trusted build script {} has malformed SHA-256",
                        tbs.crate_name
                    ),
                    in_spec: false,
                });
            }
            if tbs.reason.trim().is_empty() {
                errors.push(SubsetError {
                    rule: PB060,
                    span,
                    detail: format!(
                        "trusted build script {} has empty `reason`",
                        tbs.crate_name
                    ),
                    in_spec: false,
                });
            }
        }
        // PB072: Cargo.lock presence is checked by the driver (filesystem).
        // PB073: hermetic environment is checked by the driver.
        // PB074: pitbull-spec version match is checked by the driver.
        // PB075: cache signing key existence is checked at use time.
        // PB049 (overflow-checks): NOT yet enforced anywhere — neither here
        // nor in the driver, which does not yet inspect the build profile's
        // `overflow-checks`/`-C overflow-checks` flag. Tracked follow-up.
        // This is a hygiene-policy gap, not a soundness hole: Pitbull
        // proves absence of overflow via its own PB049 VC obligations
        // regardless of the runtime flag, and any undischarged obligation
        // already forces a nonzero exit.
        let _ = (PB049, PB072, PB073, PB074, PB075); // referenced for grep
        errors
    }
    /// Test-only convenience constructor.
    #[cfg(any(test, feature = "test-helpers"))]
    #[must_use]
    pub fn default_for_test() -> Self {
        Self {
            project: ProjectSection {
                name: "test-crate".into(),
                toolchain: SUPPORTED_TOOLCHAINS[0].into(),
            },
            verification: VerificationSection::default(),
            subset: SubsetSection::default(),
            reachability: ReachabilitySection::default(),
            reporting: ReportingSection::default(),
            cache: CacheSection::default(),
        }
    }
}
/// The toolchain identifiers Pitbull v0.1.0 supports.
///
/// Each entry must correspond to a (Ferrocene release, rustc nightly,
/// Creusot fork) triple validated by the release process. Adding an entry
/// here without adding the supporting matrix to CI is a release-blocking
/// bug.
pub const SUPPORTED_TOOLCHAINS: &[&str] = &[
    "pitbull-0.1.0-ferrocene-26.02.0",
];
fn is_supported_toolchain(s: &str) -> bool {
    SUPPORTED_TOOLCHAINS.contains(&s)
}
fn is_valid_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.chars().all(|c| c.is_ascii_hexdigit())
}
/// Configured `[verification.preconditions]` keys that matched no walked
/// function path.
///
/// A precondition key is a fully-qualified function path; the wrapper
/// looks it up against every function it actually walks. A key that
/// binds to nothing — a typo, or a function filtered out by
/// `verify_roots` / `exclude` — means the user's precondition silently
/// never applied. The project's "no silent skips" posture (audit
/// 2026-05-29) forbids letting that pass quietly, so the wrapper warns
/// on each entry returned here (mirroring the exclude-glob warning).
///
/// Pure half of that check, extracted so it is unit-tested on the stable
/// lane independently of the rustc-only wrapper. The result is
/// deterministic: `BTreeMap` keys iterate in sorted order, so the
/// returned vec is sorted with no extra work.
///
/// Direction note: a missing precondition is fail-safe — the obligation
/// is then checked with *fewer* assumptions (over-approximate), so this
/// is a usability/visibility warning, not a soundness gate.
#[must_use]
pub fn unmatched_precondition_keys(
    preconditions: &std::collections::BTreeMap<String, Vec<String>>,
    walked_fn_paths: &std::collections::HashSet<String>,
) -> Vec<String> {
    preconditions
        .keys()
        .filter(|k| !walked_fn_paths.contains(*k))
        .cloned()
        .collect()
}
// `default_for_test` above is `cfg(any(test, feature = "test-helpers"))`. The
// in-crate test modules in `visitor.rs`, `reachability.rs`, etc. compile under
// `cfg(test)` and can call it directly. External crates that want the helper
// (e.g. `pitbull-driver` integration tests) opt in via the `test-helpers`
// feature in their dev-dependencies on `pitbull-subset`.
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn defaults_validate_clean() {
        let cfg = SubsetConfig::default_for_test();
        let errs = cfg.validate();
        assert!(errs.is_empty(), "default test config produced {} errors", errs.len());
    }
    /// O.1: a `[verification.preconditions]` TOML table
    /// deserializes into a `BTreeMap<String, Vec<String>>` and
    /// each entry preserves order on lookup. Pins the on-disk
    /// schema the wrapper consumes.
    #[test]
    fn preconditions_table_round_trips_from_toml() {
        let text = r#"
[project]
name = "demo"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"

[verification.preconditions]
"demo::add_one"  = ["(assert (bvult lhs #x00000064))"]
"demo::add_two"  = [
    "(assert (bvult lhs #x00000064))",
    "(assert (bvult rhs #x00000064))",
]
"#;
        let cfg: SubsetConfig = toml::from_str(text)
            .expect("valid TOML deserializes");
        let preconds = &cfg.verification.preconditions;
        assert_eq!(preconds.len(), 2);
        assert_eq!(
            preconds.get("demo::add_one").map(Vec::as_slice),
            Some(&["(assert (bvult lhs #x00000064))".to_string()][..]),
        );
        let two = preconds.get("demo::add_two").expect("demo::add_two present");
        assert_eq!(two.len(), 2);
        assert!(two[0].contains("lhs"));
        assert!(two[1].contains("rhs"));
    }
    /// Configs without a `[verification.preconditions]` section
    /// still parse — the field defaults to an empty map. Backwards
    /// compatible with every pre-O.1 pitbull.toml in the wild.
    #[test]
    fn preconditions_table_optional() {
        let text = r#"
[project]
name = "demo"
toolchain = "pitbull-0.1.0-ferrocene-26.02.0"
"#;
        let cfg: SubsetConfig = toml::from_str(text)
            .expect("config without preconditions table still parses");
        assert!(
            cfg.verification.preconditions.is_empty(),
            "missing table should default to empty map",
        );
    }
    /// The shipped `pitbull.toml.example` must parse under the real loader —
    /// pins the "every documented field maps one-to-one to a struct field"
    /// invariant (the doc comment claims CI catches drift; this is that CI),
    /// and guards the `deny_unknown_fields` hardening: a field documented in
    /// the example but absent from the structs would now fail loudly.
    #[test]
    fn shipped_example_config_parses() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("pitbull.toml.example");
        let raw = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let parsed: Result<SubsetConfig, _> = toml::from_str(&raw);
        assert!(
            parsed.is_ok(),
            "pitbull.toml.example must parse under deny_unknown_fields; got {:?}",
            parsed.err(),
        );
    }
    /// `deny_unknown_fields` (assumption-audit L2, 2026-06-14): an unknown /
    /// typo'd config key — or an unsupported section like
    /// `[verification.ensures]` — must FAIL LOUD (a parse error), never be
    /// silently ignored with the default (a "no silent skips" gap, since the
    /// cert structs already deny unknown fields).
    #[test]
    fn unknown_config_field_is_rejected() {
        // Typo'd safety flag.
        let typo = "[project]\nname=\"d\"\ntoolchain=\"t\"\n\
                    [verification]\nstrict_library_acceptanse = false\n";
        assert!(
            toml::from_str::<SubsetConfig>(typo).is_err(),
            "a typo'd verification key must be rejected, not silently defaulted",
        );
        // Unsupported config-side ensures (only #[pitbull::ensures] attrs are wired).
        let ensures = "[project]\nname=\"d\"\ntoolchain=\"t\"\n\
                       [verification.ensures]\n\"demo::f\" = [\"x\"]\n";
        assert!(
            toml::from_str::<SubsetConfig>(ensures).is_err(),
            "config-side [verification.ensures] is not wired; it must fail loud, not be ignored",
        );
        // An unknown top-level section.
        let section = "[project]\nname=\"d\"\ntoolchain=\"t\"\n[bogus]\nx = 1\n";
        assert!(
            toml::from_str::<SubsetConfig>(section).is_err(),
            "an unknown top-level section must be rejected",
        );
    }
    #[test]
    fn unwind_panic_strategy_rejected() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.subset.panic_strategy = "unwind".into();
        let errs = cfg.validate();
        assert!(errs.iter().any(|e| e.rule == PB048));
    }
    #[test]
    fn unsupported_toolchain_rejected() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.project.toolchain = "stable-1.78".into();
        let errs = cfg.validate();
        assert!(errs.iter().any(|e| e.rule == PB071));
    }
    #[test]
    fn invalid_sha256_rejected() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.subset.trusted_build_scripts.push(TrustedBuildScript {
            crate_name: "bad".into(),
            sha256: "not_hex".into(),
            reason: "test".into(),
        });
        let errs = cfg.validate();
        assert!(errs.iter().any(|e| e.rule == PB060));
    }
    #[test]
    fn empty_reason_rejected() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.subset.trusted_build_scripts.push(TrustedBuildScript {
            crate_name: "x".into(),
            sha256: "0".repeat(64),
            reason: "   ".into(),
        });
        let errs = cfg.validate();
        assert!(errs.iter().any(|e| e.rule == PB060));
    }
    #[test]
    fn out_of_range_trust_budget_rejected() {
        let mut cfg = SubsetConfig::default_for_test();
        cfg.subset.trust_budget_fraction = 1.5;
        let errs = cfg.validate();
        assert!(errs.iter().any(|e| e.rule == PB068));
    }
    #[test]
    fn pb059_local_macro_never_rejected() {
        // The crate under verification's own macros are always allowed.
        assert!(!pb059_proc_macro_rejected("mycrate", true, &[]));
    }
    #[test]
    fn pb059_trusted_toolchain_crates_never_rejected() {
        // Built-in derives (Debug/Clone) and std macros come from these.
        for c in ["core", "std", "alloc", "proc_macro"] {
            assert!(
                !pb059_proc_macro_rejected(c, false, &[]),
                "{c} must be trusted",
            );
        }
    }
    #[test]
    fn pb059_non_allowlisted_external_macro_rejected() {
        let allowed = vec!["pitbull-spec".to_string()];
        assert!(
            pb059_proc_macro_rejected("serde_derive", false, &allowed),
            "an external proc-macro not on the allowlist must be rejected",
        );
    }
    #[test]
    fn pb059_allowlisted_external_macro_not_rejected() {
        let allowed = vec!["serde-derive".to_string(), "thiserror".to_string()];
        // rustc reports `serde_derive` (underscore); allowlist wrote
        // `serde-derive` (hyphen). Normalization must bridge them.
        assert!(!pb059_proc_macro_rejected("serde_derive", false, &allowed));
        assert!(!pb059_proc_macro_rejected("thiserror", false, &allowed));
    }
    #[test]
    fn pb059_default_allowlist_admits_pitbull_spec_only() {
        let allowed = default_allowed_proc_macros(); // ["pitbull-spec"]
        assert!(!pb059_proc_macro_rejected("pitbull_spec", false, &allowed));
        assert!(pb059_proc_macro_rejected("serde_derive", false, &allowed));
    }
    /// A precondition key that names no walked function is reported —
    /// the typo / filtered-out case the wrapper warns on (no silent
    /// skip), while a key that DID bind is not.
    #[test]
    fn unmatched_precondition_key_reported() {
        let mut pre: std::collections::BTreeMap<String, Vec<String>> =
            std::collections::BTreeMap::new();
        pre.insert("demo::typoed".to_string(), vec!["x < 1".to_string()]);
        pre.insert("demo::real".to_string(), vec!["y < 1".to_string()]);
        let mut walked: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        walked.insert("demo::real".to_string());
        assert_eq!(
            unmatched_precondition_keys(&pre, &walked),
            vec!["demo::typoed".to_string()],
        );
    }
    /// Every configured key bound to a walked function ⇒ nothing
    /// reported.
    #[test]
    fn all_precondition_keys_matched_is_clean() {
        let mut pre: std::collections::BTreeMap<String, Vec<String>> =
            std::collections::BTreeMap::new();
        pre.insert("demo::f".to_string(), vec!["x < 1".to_string()]);
        let mut walked: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        walked.insert("demo::f".to_string());
        assert!(unmatched_precondition_keys(&pre, &walked).is_empty());
    }
    /// Multiple unmatched keys come back sorted, so the wrapper's
    /// warnings are deterministic regardless of insertion order.
    #[test]
    fn unmatched_precondition_keys_sorted() {
        let mut pre: std::collections::BTreeMap<String, Vec<String>> =
            std::collections::BTreeMap::new();
        pre.insert("demo::zeta".to_string(), vec![]);
        pre.insert("demo::alpha".to_string(), vec![]);
        let walked: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        assert_eq!(
            unmatched_precondition_keys(&pre, &walked),
            vec!["demo::alpha".to_string(), "demo::zeta".to_string()],
        );
    }
}
