//! Diagnostic emission for subset violations.
//!
//! ## Output channels
//!
//! - **Compiler-style terminal output** via `miette` for interactive runs.
//! - **SARIF 2.1.0** JSON for IDE and CI integration (consumed by GitHub
//!   code-scanning, GitLab, and most IDE LSP layers).
//! - **JUnit XML** for legacy CI systems (under feature flag, not in v0.1).
//!
//! ## Design rule
//!
//! Diagnostics are *terminal* artifacts. The compiler may have type errors
//! that suppress further analysis, in which case Pitbull emits its own
//! "did-not-run" report rather than mis-attributing the cause. The
//! `SubsetReport` carries a `phase_completed` field for this purpose.
pub use crate::rules::{RuleId, Severity};
use crate::mir_api::Span;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
/// A single subset violation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubsetError {
    /// The PSS-1 rule violated.
    pub rule: RuleId,
    /// Where in the source the violation occurred.
    pub span: Span,
    /// Human-readable extra information specific to the violation site.
    pub detail: String,
    /// Whether the violation occurred in a specification expression.
    pub in_spec: bool,
}
impl fmt::Display for SubsetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rule = crate::rules::lookup(self.rule).expect("registered rule");
        write!(
            f,
            "{rule_id}: {title} — {detail}",
            rule_id = self.rule,
            title = rule.title,
            detail = self.detail
        )
    }
}
/// A non-violation diagnostic recorded by the visitor when it
/// encounters a code shape it cannot fully classify but that does
/// not itself violate PSS-1.
///
/// Use case: when `classify_called_function` sees a callee whose path
/// it cannot extract (e.g. a non-FnDef-typed constant operand), it
/// would silently fall through with no rule firing. Audit posture
/// rejects silent skips, so the visitor records an audit note
/// instead. An auditor reviewing the SARIF / stderr output sees
/// "this call wasn't classified" and can investigate whether a
/// real PB rule should have fired.
///
/// Audit notes are informational, never block verification, and do
/// not count toward the violation total. They are surfaced alongside
/// errors in the wrapper's stderr and (future) in SARIF as
/// `result.kind = "informational"`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AuditNote {
    /// Source location of the unclassifiable construct.
    pub span: Span,
    /// Why the note exists.
    pub message: String,
}
impl fmt::Display for AuditNote {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "audit-note: {}", self.message)
    }
}
/// Phase the visitor reached before terminating.
///
/// Reported to distinguish "verified" from "we did not finish" — the latter
/// should never be silently equated with success.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PhaseCompleted {
    /// Subset checking ran on every reachable body.
    SubsetCheckComplete,
    /// Aborted before completion (e.g. compilation failed).
    Aborted,
}
/// The accumulated report of a verification run.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubsetReport {
    /// All recorded violations, in encounter order.
    pub errors: Vec<SubsetError>,
    /// Non-violation diagnostics: code shapes the visitor saw but
    /// could not fully classify. Audit-trail signal; never blocks
    /// verification. See `AuditNote`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub audit_notes: Vec<AuditNote>,
    /// What phase the visitor reached.
    pub phase_completed: PhaseCompleted,
    /// PSS version this report was produced against.
    pub pss_version: String,
    /// Optional file-id → URI resolution map. `Span::file` is an
    /// opaque u32 hash of the source filename (Copy-friendly, no
    /// owned strings in spans); when this table is populated, SARIF
    /// emission resolves each `Span::file` to a human-readable
    /// `artifactLocation.uri`. Absent for shadow tests (which never
    /// produce non-default spans through the adapter); populated by
    /// the rustc_public-backed wrapper via
    /// `adapter::take_filename_table()`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub filenames: Option<HashMap<u32, String>>,
}
impl SubsetReport {
    /// Construct a report from a list of errors. Marks the phase as
    /// `SubsetCheckComplete`; for aborted runs use `aborted()`.
    #[must_use]
    pub fn new(errors: Vec<SubsetError>) -> Self {
        Self {
            errors,
            audit_notes: Vec::new(),
            phase_completed: PhaseCompleted::SubsetCheckComplete,
            pss_version: crate::PSS_VERSION.to_string(),
            filenames: None,
        }
    }
    /// Construct an aborted report.
    #[must_use]
    pub fn aborted() -> Self {
        Self {
            errors: Vec::new(),
            audit_notes: Vec::new(),
            phase_completed: PhaseCompleted::Aborted,
            pss_version: crate::PSS_VERSION.to_string(),
            filenames: None,
        }
    }
    /// Whether the run found any violations.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
    /// Whether the run is a clean pass: completed phase, zero errors.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.phase_completed == PhaseCompleted::SubsetCheckComplete && self.errors.is_empty()
    }
    /// Render as SARIF 2.1.0 JSON. The schema is intentionally minimal here;
    /// full SARIF generation including code-flow stitching lives in
    /// `pitbull-report`. This method is provided for unit-test convenience.
    pub fn to_sarif_minimal(&self) -> serde_json::Value {
        let results: Vec<serde_json::Value> = self
            .errors
            .iter()
            .map(|e| {
                let rule = crate::rules::lookup(e.rule).expect("registered rule");
                // The fileId is an opaque hash of the source filename
                // — Copy-friendly for spans. When the report carries
                // a `filenames` resolution table (populated by the
                // wrapper via `adapter::take_filename_table()`), emit
                // both the opaque `index` (round-trip stable) and a
                // `uri` string for SARIF consumers. Without the table
                // (shadow tests), only `index` is emitted, preserving
                // the v0.1 behavior.
                let mut artifact_location = serde_json::json!({
                    "index": e.span.file,
                });
                if let Some(table) = &self.filenames {
                    if let Some(uri) = table.get(&e.span.file) {
                        artifact_location["uri"] = serde_json::json!(uri);
                    }
                }
                serde_json::json!({
                    "ruleId": format!("{}", e.rule),
                    "level": match rule.severity {
                        Severity::Error => "error",
                        Severity::Audit => "warning",
                    },
                    "message": {
                        "text": format!("{}: {}", rule.title, e.detail),
                    },
                    "locations": [{
                        "physicalLocation": {
                            // SARIF region: prefer line/col over byte
                            // offsets because rustc_public exposes
                            // line/col but not byte offsets. See the
                            // Span doc in mir_api.rs for the encoding.
                            // Lines and columns are 1-indexed in SARIF;
                            // the rustc_public LineInfo is also
                            // 1-indexed, so we pass values through.
                            "region": {
                                "startLine": e.span.start_line(),
                                "startColumn": e.span.start_col(),
                                "endLine": e.span.end_line(),
                                "endColumn": e.span.end_col(),
                            },
                            "artifactLocation": artifact_location,
                        },
                    }],
                })
            })
            .collect();
        serde_json::json!({
            "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
            "version": "2.1.0",
            "runs": [{
                "tool": {
                    "driver": {
                        "name": "pitbull-subset",
                        "version": env!("CARGO_PKG_VERSION"),
                        "informationUri": "https://github.com/pitbull-verify/pitbull",
                        "rules": crate::rules::RULES.iter().map(|r| serde_json::json!({
                            "id": format!("{}", r.id),
                            "name": r.title,
                            "shortDescription": { "text": r.rationale },
                        })).collect::<Vec<_>>(),
                    },
                },
                "results": results,
            }],
        })
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::PB001;
    #[test]
    fn clean_report_has_no_errors() {
        let r = SubsetReport::new(vec![]);
        assert!(r.is_clean());
    }
    #[test]
    fn aborted_report_is_not_clean() {
        let r = SubsetReport::aborted();
        assert!(!r.is_clean());
    }
    #[test]
    fn sarif_minimal_includes_rule_metadata() {
        let r = SubsetReport::new(vec![SubsetError {
            rule: PB001,
            span: Span::default(),
            detail: "test".into(),
            in_spec: false,
        }]);
        let s = r.to_sarif_minimal();
        let rules = &s["runs"][0]["tool"]["driver"]["rules"];
        assert!(rules.is_array());
        assert_eq!(rules.as_array().unwrap().len(), crate::RULE_COUNT);
    }
    /// SARIF physicalLocation regions encode line/col, not byte offsets.
    /// Pin the structural shape so future SARIF changes notice if a
    /// downstream consumer relies on the field names.
    #[test]
    fn sarif_minimal_emits_line_col_region() {
        let mut span = Span::default();
        span.lo = Span::pack(7, 12); // line 7, col 12
        span.hi = Span::pack(7, 18);
        span.file = 0xCAFE_BABE;
        let r = SubsetReport::new(vec![SubsetError {
            rule: PB001,
            span,
            detail: "test".into(),
            in_spec: false,
        }]);
        let s = r.to_sarif_minimal();
        let region = &s["runs"][0]["results"][0]["locations"][0]["physicalLocation"]["region"];
        assert_eq!(region["startLine"], 7);
        assert_eq!(region["startColumn"], 12);
        assert_eq!(region["endLine"], 7);
        assert_eq!(region["endColumn"], 18);
        let artifact = &s["runs"][0]["results"][0]["locations"][0]["physicalLocation"]["artifactLocation"];
        assert_eq!(artifact["index"], 0xCAFE_BABE_u32);
    }
    /// When the report carries a `filenames` resolution table, the
    /// SARIF artifactLocation surfaces the URI alongside the opaque
    /// index. Without the table (shadow-test default), the URI is
    /// absent and only the index is present (`sarif_minimal_emits_line_col_region`
    /// covers that path).
    #[test]
    fn sarif_minimal_emits_uri_when_filename_table_present() {
        let mut span = Span::default();
        span.lo = Span::pack(3, 5);
        span.hi = Span::pack(3, 10);
        span.file = 0xDEAD_BEEF;
        let mut table = HashMap::new();
        table.insert(0xDEAD_BEEF_u32, "src/lib.rs".to_string());
        let mut r = SubsetReport::new(vec![SubsetError {
            rule: PB001,
            span,
            detail: "test".into(),
            in_spec: false,
        }]);
        r.filenames = Some(table);
        let s = r.to_sarif_minimal();
        let artifact = &s["runs"][0]["results"][0]["locations"][0]
            ["physicalLocation"]["artifactLocation"];
        assert_eq!(artifact["uri"], "src/lib.rs");
        assert_eq!(artifact["index"], 0xDEAD_BEEF_u32);
    }
    /// Span::pack and the start_line/etc decoders are inverses for
    /// values in the u16 range. Pathological larger values clamp
    /// rather than wrap (defended in Span::pack).
    #[test]
    fn span_pack_round_trips() {
        let s = Span {
            lo: Span::pack(123, 4567),
            hi: Span::pack(8910, 11),
            file: 0,
        };
        assert_eq!(s.start_line(), 123);
        assert_eq!(s.start_col(), 4567);
        assert_eq!(s.end_line(), 8910);
        assert_eq!(s.end_col(), 11);
    }
    #[test]
    fn span_pack_clamps_overflow() {
        // Pathological: line > u16::MAX. Must clamp, not wrap.
        let packed = Span::pack(100_000, 50);
        let s = Span { lo: packed, hi: 0, file: 0 };
        assert_eq!(s.start_line(), u16::MAX);
        assert_eq!(s.start_col(), 50);
    }
}
