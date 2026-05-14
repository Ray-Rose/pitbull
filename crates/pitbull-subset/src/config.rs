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
pub struct ProjectSection {
    /// Crate name. Must match the verified `Cargo.toml`.
    pub name: String,
    /// PSS-1 PB071 / PB074: pinned Pitbull-toolchain identifier.
    pub toolchain: String,
}
/// `[verification]` — solver policy.
#[derive(Clone, Debug, Serialize, Deserialize)]
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
}
impl Default for VerificationSection {
    fn default() -> Self {
        Self {
            vc_timeout_seconds: default_vc_timeout(),
            solver_agreement: default_solver_agreement(),
            solvers: default_solvers(),
            solver_versions: std::collections::BTreeMap::new(),
            strict_panic_acceptance: false,
        }
    }
}
fn default_vc_timeout() -> u64 { 60 }
fn default_solver_agreement() -> u8 { 2 }
fn default_solvers() -> Vec<String> {
    vec!["z3".into(), "cvc5".into(), "alt-ergo".into()]
}
/// `[subset]` — PSS-1 enforcement knobs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubsetSection {
    /// PSS-1 PB020: per-local stack allocation limit, bytes.
    #[serde(default = "default_stack_limit")]
    pub stack_allocation_limit_bytes: u64,
    /// PSS-1 PB052: target pointer width, bits. Must be 16, 32, or 64.
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
/// An explicitly trusted `build.rs` entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
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
    /// - PB049 overflow-checks (checked by the driver against profile flags)
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
        let _ = (PB049, PB072, PB073, PB074, PB075); // referenced for grep; checked elsewhere
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
}
