//! Proof certificates (Task T, 2026-05-29).
//!
//! A *proof certificate* is a replayable, self-contained record of
//! what the agreement gate decided for each verification obligation:
//! the exact SMT-LIB problem that was solved, each solver's verdict,
//! and the resulting agreement decision. The point is INDEPENDENT
//! RE-VERIFICATION — a third party (or CI, or a future you) can take a
//! certificate and *replay* it: re-run the recorded SMT through the
//! solver pool and confirm the same agreement verdict comes back.
//!
//! This is the differentiator no competing Rust verifier ships. It
//! also makes the TCB story concrete (Safety Manual §3.3): the gate's
//! decision is not a transient stderr line — it is a durable artifact
//! you can re-check on a different machine, with different solver
//! builds, long after the original `cargo pitbull check`.
//!
//! ## What replay catches
//! - **Solver drift / version skew** — a solver that has since changed
//!   its answer on the recorded problem (a `Mismatch`).
//! - **Environment differences** — a discharge that only reproduced
//!   because of a particular machine's solver set.
//! - **Tampering of the SMT problem** — if the recorded `smt` is
//!   altered, replaying it generally yields a different verdict.
//!
//! ## What is NOT here yet (deliberate)
//! - Cryptographic signing of the certificate (the "signed solver
//!   outputs" half of the v0.3 roadmap). Pitbull deliberately ships no
//!   hashing/crypto dependency today (see `pitbull-subset/Cargo.toml`),
//!   so a self-referential hash would give only weak,
//!   non-adversarial assurance. Replay (re-run + compare) is the
//!   substance; a signature layer is a deliberate later step that adds
//!   provenance/non-repudiation on top of this format.
//! - Emission from the wrapper and a `cargo pitbull replay`
//!   subcommand — wired in the follow-up increment (this module is the
//!   stable-buildable data model + replay logic those will use).
//!
//! Replay needs only the solvers and this crate — it does NOT need the
//! nightly `rustc_public` lane, because it re-runs recorded SMT rather
//! than recompiling Rust. So certificates produced by the nightly
//! wrapper can be replayed by anyone on stable Rust.
use crate::solver::{run_solvers, vote, AgreementVerdict, Solver, SolverResult};
use serde::{Deserialize, Serialize};
use std::time::Duration;

/// On-disk format version. Bump on any breaking schema change so a
/// replayer can refuse a format it doesn't understand (fail closed)
/// rather than silently misread it.
pub const CERT_FORMAT_VERSION: u32 = 1;

/// Stable short tag for a `SolverResult`, used in the serialized
/// certificate. Kept here (not a `SolverResult` method) so the
/// certificate's wire format is owned by this module.
#[must_use]
pub fn solver_result_tag(r: &SolverResult) -> &'static str {
    match r {
        SolverResult::Sat => "sat",
        SolverResult::Unsat => "unsat",
        SolverResult::Unknown => "unknown",
        SolverResult::NotInstalled => "not-installed",
        SolverResult::Timeout => "timeout",
        SolverResult::Error(_) => "error",
    }
}

/// Stable short tag for the agreement verdict. This is the value
/// replay compares: does re-running the SMT reproduce this decision?
#[must_use]
pub fn agreement_tag(v: &AgreementVerdict) -> &'static str {
    match v {
        AgreementVerdict::Discharged { .. } => "discharged",
        AgreementVerdict::Refuted => "refuted",
        AgreementVerdict::Disagreement { .. } => "disagreement",
        AgreementVerdict::Inconclusive { .. } => "inconclusive",
    }
}

/// Count of DISTINCT solvers that returned `unsat` — the same
/// distinct-name counting `vote` uses (so a duplicate solver entry
/// can't inflate the recorded vote count either).
#[must_use]
fn distinct_unsat_votes(results: &[(String, SolverResult)]) -> usize {
    let mut names: Vec<&str> = results
        .iter()
        .filter(|(_, r)| *r == SolverResult::Unsat)
        .map(|(n, _)| n.as_str())
        .collect();
    names.sort_unstable();
    names.dedup();
    names.len()
}

/// One solver's recorded verdict on a certificate's SMT problem.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverVerdictRecord {
    /// Solver name (`"z3"`, `"cvc5"`, ...).
    pub solver: String,
    /// Verdict tag (`solver_result_tag`): `sat`/`unsat`/`unknown`/
    /// `timeout`/`error`/`not-installed`.
    pub verdict: String,
}

/// A replayable record of one obligation's gate decision.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationCertificate {
    /// Obligation id (e.g. `pb049-neg-0`).
    pub id: String,
    /// Canonical PSS-1 rule (e.g. `PB049`).
    pub rule: String,
    /// The EXACT SMT-LIB 2 problem that was solved. Replay re-runs
    /// this verbatim — it is the heart of the certificate.
    pub smt: String,
    /// Per-solver verdicts at certification time.
    pub solver_results: Vec<SolverVerdictRecord>,
    /// The agreement-gate verdict tag (`agreement_tag`).
    pub verdict: String,
    /// Distinct `unsat` votes obtained at certification time.
    pub unsat_votes: usize,
    /// Agreement threshold in force when this was certified.
    pub threshold: usize,
}

impl ObligationCertificate {
    /// Build a certificate from a completed solver run. Derives the
    /// agreement verdict from `results` via the same `vote` policy the
    /// live gate uses, so the certificate records exactly the decision
    /// that was made.
    #[must_use]
    pub fn from_run(
        id: impl Into<String>,
        rule: impl Into<String>,
        smt: impl Into<String>,
        results: &[(String, SolverResult)],
        threshold: usize,
    ) -> Self {
        let verdict = vote(results, threshold);
        Self {
            id: id.into(),
            rule: rule.into(),
            smt: smt.into(),
            solver_results: results
                .iter()
                .map(|(name, r)| SolverVerdictRecord {
                    solver: name.clone(),
                    verdict: solver_result_tag(r).to_string(),
                })
                .collect(),
            verdict: agreement_tag(&verdict).to_string(),
            unsat_votes: distinct_unsat_votes(results),
            threshold,
        }
    }
    /// Whether this certificate records a discharged (proven-safe)
    /// obligation.
    #[must_use]
    pub fn is_discharged(&self) -> bool {
        self.verdict == "discharged"
    }
}

/// The result of replaying one certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplayOutcome {
    /// Re-running the recorded SMT reproduced the recorded verdict.
    Match {
        /// The reproduced verdict tag.
        verdict: String,
    },
    /// Re-running produced a DIFFERENT verdict than was recorded. This
    /// is the alarm the certificate exists to raise: solver drift, an
    /// environment difference, or a tampered SMT problem. A replayer
    /// MUST treat this as "the original proof does not reproduce" and
    /// fail closed.
    Mismatch {
        /// The verdict the certificate claims.
        recorded: String,
        /// The verdict the fresh solver run produced.
        replayed: String,
    },
}

impl ReplayOutcome {
    /// True only when the certificate reproduced exactly.
    #[must_use]
    pub fn is_match(&self) -> bool {
        matches!(self, ReplayOutcome::Match { .. })
    }
}

/// PURE replay: compare a certificate's recorded verdict against the
/// verdict a fresh set of solver results would produce, under the
/// certificate's own recorded threshold. No I/O — the soundness-
/// relevant comparison is exhaustively unit-testable without any
/// solver installed.
#[must_use]
pub fn replay_with_results(
    cert: &ObligationCertificate,
    fresh: &[(String, SolverResult)],
) -> ReplayOutcome {
    let replayed = agreement_tag(&vote(fresh, cert.threshold)).to_string();
    if replayed == cert.verdict {
        ReplayOutcome::Match { verdict: replayed }
    } else {
        ReplayOutcome::Mismatch {
            recorded: cert.verdict.clone(),
            replayed,
        }
    }
}

/// Re-run a certificate's recorded SMT through `solvers` and compare
/// the resulting agreement verdict to the recorded one. The I/O
/// wrapper around [`replay_with_results`].
#[must_use]
pub fn replay_certificate(
    cert: &ObligationCertificate,
    solvers: &[Solver],
    timeout: Duration,
) -> ReplayOutcome {
    let fresh = run_solvers(solvers, &cert.smt, timeout);
    replay_with_results(cert, &fresh)
}

/// A bundle of certificates for one verified crate, plus the context
/// needed to interpret and replay them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateBundle {
    /// Schema version (`CERT_FORMAT_VERSION`).
    pub format_version: u32,
    /// Pitbull tool version that produced the bundle.
    pub tool_version: String,
    /// Crate the obligations belong to.
    pub crate_name: String,
    /// Agreement threshold in force.
    pub threshold: usize,
    /// Solver pool names used to certify.
    pub solvers: Vec<String>,
    /// One entry per obligation that reached the solver.
    pub obligations: Vec<ObligationCertificate>,
}

impl CertificateBundle {
    /// Construct an empty bundle stamped with the current format
    /// version and the given context.
    #[must_use]
    pub fn new(
        tool_version: impl Into<String>,
        crate_name: impl Into<String>,
        threshold: usize,
        solvers: Vec<String>,
    ) -> Self {
        Self {
            format_version: CERT_FORMAT_VERSION,
            tool_version: tool_version.into(),
            crate_name: crate_name.into(),
            threshold,
            solvers,
            obligations: Vec::new(),
        }
    }
    /// Serialize to pretty JSON (the on-disk certificate format).
    ///
    /// # Errors
    /// Propagates any `serde_json` serialization error.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }
    /// Parse a bundle from JSON, refusing an unknown future format
    /// version (fail closed — a replayer must not silently misread a
    /// schema it doesn't understand).
    ///
    /// # Errors
    /// Returns `Err` on malformed JSON or an unsupported
    /// `format_version`.
    pub fn from_json(s: &str) -> Result<Self, String> {
        let bundle: CertificateBundle =
            serde_json::from_str(s).map_err(|e| format!("malformed certificate JSON: {e}"))?;
        if bundle.format_version > CERT_FORMAT_VERSION {
            return Err(format!(
                "certificate format_version {} is newer than this tool supports \
                 (max {CERT_FORMAT_VERSION}); refusing to replay (upgrade pitbull)",
                bundle.format_version,
            ));
        }
        Ok(bundle)
    }
}

/// Replay every certificate in a bundle, returning `(id, outcome)`
/// per obligation. Uses each certificate's own recorded threshold.
#[must_use]
pub fn replay_bundle(
    bundle: &CertificateBundle,
    solvers: &[Solver],
    timeout: Duration,
) -> Vec<(String, ReplayOutcome)> {
    bundle
        .obligations
        .iter()
        .map(|c| (c.id.clone(), replay_certificate(c, solvers, timeout)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(name: &str, res: SolverResult) -> (String, SolverResult) {
        (name.to_string(), res)
    }

    /// A discharged run (2 distinct unsat, threshold 2) records the
    /// `discharged` verdict and both solver verdicts.
    #[test]
    fn from_run_records_discharged() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let cert = ObligationCertificate::from_run(
            "pb049-neg-0",
            "PB049",
            "(set-logic QF_BV)\n(check-sat)\n",
            &results,
            2,
        );
        assert_eq!(cert.verdict, "discharged");
        assert!(cert.is_discharged());
        assert_eq!(cert.unsat_votes, 2);
        assert_eq!(cert.threshold, 2);
        assert_eq!(cert.solver_results.len(), 2);
        assert_eq!(cert.solver_results[0].solver, "z3");
        assert_eq!(cert.solver_results[0].verdict, "unsat");
    }

    /// A `sat` counterexample records `refuted` and is not discharged.
    #[test]
    fn from_run_records_refuted() {
        let results = [r("z3", SolverResult::Sat), r("cvc5", SolverResult::Sat)];
        let cert =
            ObligationCertificate::from_run("pb049-add-0", "PB049", "(check-sat)", &results, 2);
        assert_eq!(cert.verdict, "refuted");
        assert!(!cert.is_discharged());
        assert_eq!(cert.unsat_votes, 0);
    }

    /// The bundle round-trips through JSON, preserving everything.
    #[test]
    fn bundle_round_trips_through_json() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let mut bundle = CertificateBundle::new("0.1.0-dev", "mycrate", 2, vec![
            "z3".into(),
            "cvc5".into(),
        ]);
        bundle
            .obligations
            .push(ObligationCertificate::from_run("pb049-neg-0", "PB049", "(check-sat)", &results, 2));
        let json = bundle.to_json().expect("serialize");
        let back = CertificateBundle::from_json(&json).expect("deserialize");
        assert_eq!(back, bundle);
        assert_eq!(back.format_version, CERT_FORMAT_VERSION);
    }

    /// A bundle from a NEWER format version is refused (fail closed).
    #[test]
    fn from_json_refuses_newer_format() {
        let json = format!(
            "{{\"format_version\":{},\"tool_version\":\"x\",\"crate_name\":\"c\",\
             \"threshold\":2,\"solvers\":[],\"obligations\":[]}}",
            CERT_FORMAT_VERSION + 1,
        );
        let err = CertificateBundle::from_json(&json).expect_err("must refuse newer format");
        assert!(err.contains("newer than this tool supports"), "got: {err}");
    }

    /// Replay reproduces: a discharged cert, re-run with the same
    /// (2 unsat) results, MATCHES.
    #[test]
    fn replay_matches_when_verdict_reproduces() {
        let orig = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let cert = ObligationCertificate::from_run("o", "PB049", "(check-sat)", &orig, 2);
        let fresh = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        assert_eq!(
            replay_with_results(&cert, &fresh),
            ReplayOutcome::Match { verdict: "discharged".into() },
        );
    }

    /// Replay ALARM: a cert recorded as `discharged`, but a fresh run
    /// now returns a `sat` counterexample → `refuted` → Mismatch.
    /// This is the solver-drift / tamper detector working.
    #[test]
    fn replay_mismatch_when_fresh_run_disagrees() {
        let orig = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let cert = ObligationCertificate::from_run("o", "PB049", "(check-sat)", &orig, 2);
        // A solver now finds a counterexample on the same problem.
        let fresh = [r("z3", SolverResult::Sat), r("cvc5", SolverResult::Unsat)];
        match replay_with_results(&cert, &fresh) {
            ReplayOutcome::Mismatch { recorded, replayed } => {
                assert_eq!(recorded, "discharged");
                assert_eq!(replayed, "disagreement");
            }
            other => panic!("expected Mismatch, got {other:?}"),
        }
    }

    /// Replay uses the certificate's OWN recorded threshold: a cert
    /// certified at threshold 1 (single-solver) that recorded
    /// `discharged` reproduces when one solver returns unsat.
    #[test]
    fn replay_uses_recorded_threshold() {
        let orig = [r("z3", SolverResult::Unsat)];
        let cert = ObligationCertificate::from_run("o", "PB049", "(check-sat)", &orig, 1);
        assert_eq!(cert.verdict, "discharged");
        let fresh = [r("z3", SolverResult::Unsat)];
        assert!(replay_with_results(&cert, &fresh).is_match());
    }
}
