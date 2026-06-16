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
//! ## Status (updated 2026-06-15)
//! - **Signing: DONE (HMAC-SHA256, Task T.3).** `sign` / `verify_signature`
//!   below MAC the whole bundle — every field except `signature`, including the
//!   coverage ledger (`total_obligations` / `uncertified`) — so a swapped SMT,
//!   an edited verdict, or a lowered threshold is detectable to anyone holding
//!   the key. `pitbull-vc` depends on `sha2` + `hmac` for this (the
//!   `pitbull-subset` TCB core still ships no crypto dependency).
//! - **Emission + replay: DONE (Task T.2).** The wrapper emits a bundle to
//!   `PITBULL_CERT_OUT`; `cargo pitbull replay` re-runs each recorded SMT and
//!   confirms BOTH reproduction AND full-verification coverage (`replay`
//!   exit-0 requires `attests_full_verification`).
//! - **Still future:** cross-DOMAIN non-repudiation needs an ASYMMETRIC layer
//!   (Ed25519). HMAC is symmetric — it proves integrity within a trust domain,
//!   but a holder of the key could re-sign a forged bundle. That asymmetric
//!   layer is the remaining provenance step.
//!
//! Replay needs only the solvers and this crate — it does NOT need the
//! nightly `rustc_public` lane, because it re-runs recorded SMT rather
//! than recompiling Rust. So certificates produced by the nightly
//! wrapper can be replayed by anyone on stable Rust.
use crate::solver::{run_solvers, vote, AgreementVerdict, Solver, SolverResult};
use hmac::{Hmac, Mac};
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use std::time::Duration;

type HmacSha256 = Hmac<Sha256>;

/// Lowercase-hex encode bytes (no dependency on a `hex` crate).
#[must_use]
fn to_hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// Decode lowercase/uppercase hex; `None` on any non-hex or odd length.
///
/// Operates on BYTES, not `&str` char slices. A `signature` field from
/// an attacker-supplied certificate can contain arbitrary UTF-8, and
/// slicing a `&str` at a non-char boundary would PANIC; byte-indexing
/// with `to_digit` cannot panic and rejects any non-hex byte. So a
/// malformed signature fails closed to `Invalid` rather than crashing
/// the verifier (audit 2026-05-29, red-team HIGH).
#[must_use]
fn from_hex(s: &str) -> Option<Vec<u8>> {
    let b = s.as_bytes();
    if !b.len().is_multiple_of(2) {
        return None;
    }
    (0..b.len())
        .step_by(2)
        .map(|i| {
            let hi = char::from(b[i]).to_digit(16)?;
            let lo = char::from(b[i + 1]).to_digit(16)?;
            Some((hi * 16 + lo) as u8)
        })
        .collect()
}

/// HMAC-SHA256 of `bytes` under `key`.
#[must_use]
fn hmac_sha256(key: &[u8], bytes: &[u8]) -> Vec<u8> {
    // `Hmac::new_from_slice` only errors on key lengths it cannot
    // accept; HMAC accepts a key of ANY length (it hashes over-long
    // keys and zero-pads short ones), so this never fails.
    let mut mac =
        HmacSha256::new_from_slice(key).expect("HMAC-SHA256 accepts a key of any length");
    mac.update(bytes);
    mac.finalize().into_bytes().to_vec()
}

/// Maximum accepted size of an HMAC key file. Keys are tiny; the cap
/// defends against a hostile `PITBULL_CERT_KEY` (the env var is
/// build.rs-injectable) pointing at a huge file → a memory DoS when
/// read (red-team Low, 2026-05-29).
pub const MAX_KEY_FILE_BYTES: u64 = 64 * 1024;

/// Keys shorter than this are weak; the caller should warn (HMAC
/// accepts any length, but a few-byte key is brute-forceable).
pub const MIN_RECOMMENDED_KEY_BYTES: usize = 16;

/// Read an HMAC key from `path`, rejecting an over-large file (size
/// cap checked BEFORE reading) and an empty file. Shared by the
/// signer (wrapper) and verifier (`replay`) so both apply the same
/// bound and error shape.
///
/// # Errors
/// `Err` if the file is missing, unreadable, empty, or larger than
/// [`MAX_KEY_FILE_BYTES`].
pub fn read_key_file(path: &std::path::Path) -> Result<Vec<u8>, String> {
    let meta = std::fs::metadata(path)
        .map_err(|e| format!("cannot stat key file {}: {e}", path.display()))?;
    if meta.len() > MAX_KEY_FILE_BYTES {
        return Err(format!(
            "key file {} is {} bytes, over the {MAX_KEY_FILE_BYTES}-byte cap",
            path.display(),
            meta.len(),
        ));
    }
    let key = std::fs::read(path)
        .map_err(|e| format!("cannot read key file {}: {e}", path.display()))?;
    if key.is_empty() {
        return Err(format!("key file {} is empty", path.display()));
    }
    Ok(key)
}

/// Whether a certificate bundle carries a valid integrity signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignatureStatus {
    /// No signature present — the bundle was produced without a key.
    /// Re-run still confirms reproduction, but tampering of the
    /// certificate is NOT detectable.
    Unsigned,
    /// Signature present and verified against the provided key.
    Valid,
    /// Signature present but does NOT verify: the certificate was
    /// altered after signing, or a different key was used. Fail closed.
    Invalid,
}

/// On-disk format version. Bump on any breaking schema change so a
/// replayer can refuse a format it doesn't understand (fail closed)
/// rather than silently misread it.
///
/// v2 (2026-06-15 deep audit): added the coverage ledger
/// (`total_obligations` + `uncertified`) so a bundle attests the disposition
/// of EVERY obligation, not just the ones that reached the gate. A v1 bundle
/// still parses (the new fields default), but its coverage is treated as
/// unknown → fail closed at replay. An older (v1-only) tool refuses a v2
/// bundle via the `format_version > CERT_FORMAT_VERSION` check — also fail
/// closed.
pub const CERT_FORMAT_VERSION: u32 = 2;

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

/// Inverse of [`solver_result_tag`] for the internal-consistency
/// check. Only the `Sat`/`Unsat` distinction matters for re-deriving
/// the vote; every non-decisive tag maps to a non-voting result.
#[must_use]
fn solver_result_from_tag(tag: &str) -> SolverResult {
    match tag {
        "sat" => SolverResult::Sat,
        "unsat" => SolverResult::Unsat,
        "timeout" => SolverResult::Timeout,
        "not-installed" => SolverResult::NotInstalled,
        // "unknown", "error", and any unrecognized tag are all
        // non-voting for `vote`'s purposes.
        _ => SolverResult::Unknown,
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
#[serde(deny_unknown_fields)]
pub struct SolverVerdictRecord {
    /// Solver name (`"z3"`, `"cvc5"`, ...).
    pub solver: String,
    /// Verdict tag (`solver_result_tag`): `sat`/`unsat`/`unknown`/
    /// `timeout`/`error`/`not-installed`.
    pub verdict: String,
}

/// An obligation that produced NO replayable [`ObligationCertificate`]
/// because it never reached the agreement gate: the VC compiler returned no
/// goal (`pending`), or the precondition consistency guard refused it /
/// could not confirm it. Recorded so the bundle is a COMPLETE ledger of the
/// crate's obligations.
///
/// 2026-06-15 deep audit: before this, the wrapper counted these toward its
/// (correct) exit code but emitted no certificate for them — so the bundle
/// listed only the gate-reaching obligations with no denominator, and a
/// replayer seeing "every listed cert discharged" could wrongly conclude the
/// CRATE verified. A non-discharged obligation that DID reach the gate is
/// instead an `ObligationCertificate` with a non-`discharged` verdict; this
/// type is only for the ones that never got that far.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UncertifiedObligation {
    /// Obligation id (e.g. `pb043-panic-0`).
    pub id: String,
    /// Canonical PSS-1 rule (e.g. `PB043`).
    pub rule: String,
    /// Why it never reached the gate: `pending` (no SMT compiled),
    /// `consistency-refused` (preconditions contradictory), or
    /// `consistency-unconfirmed` (could not confirm preconditions jointly
    /// satisfiable).
    pub status: String,
}

/// A replayable record of one obligation's gate decision.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
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
    /// Cheap, no-crypto internal-consistency check (audit 2026-05-29):
    /// re-derive the agreement verdict and distinct-`unsat` count FROM
    /// the recorded per-solver verdicts, under the recorded threshold,
    /// and confirm they match the recorded `verdict`/`unsat_votes`. An
    /// honest producer's output always passes (it is built by exactly
    /// this `vote`); a HAND-FORGED or CORRUPTED certificate whose fields
    /// disagree (e.g. `verdict:"discharged"` over `solver_results` that
    /// don't actually meet the threshold) is rejected. NOTE: this does
    /// NOT catch a tamper that keeps the fields mutually consistent
    /// (e.g. lowering `threshold` 2→1, or swapping `smt` for a
    /// trivially-unsat problem) — that is what cryptographic signing
    /// (Task T.3) is for. This is defense-in-depth, not the whole
    /// integrity story.
    ///
    /// # Errors
    /// Returns `Err` describing the inconsistency if the recorded
    /// verdict/vote-count cannot be re-derived from the recorded
    /// per-solver results at the recorded threshold.
    pub fn check_internal_consistency(&self) -> Result<(), String> {
        let reconstructed: Vec<(String, SolverResult)> = self
            .solver_results
            .iter()
            .map(|r| (r.solver.clone(), solver_result_from_tag(&r.verdict)))
            .collect();
        let derived = vote(&reconstructed, self.threshold);
        let derived_tag = agreement_tag(&derived);
        if derived_tag != self.verdict {
            return Err(format!(
                "certificate {} is internally inconsistent: recorded verdict \
                 `{}` but its solver_results re-derive to `{}` at threshold {}",
                self.id, self.verdict, derived_tag, self.threshold,
            ));
        }
        let derived_votes = distinct_unsat_votes(&reconstructed);
        if derived_votes != self.unsat_votes {
            return Err(format!(
                "certificate {} is internally inconsistent: recorded unsat_votes \
                 {} but its solver_results have {} distinct unsat verdict(s)",
                self.id, self.unsat_votes, derived_votes,
            ));
        }
        Ok(())
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
#[serde(deny_unknown_fields)]
pub struct CertificateBundle {
    /// Schema version (`CERT_FORMAT_VERSION`).
    pub format_version: u32,
    /// Pitbull tool version that produced the bundle.
    pub tool_version: String,
    /// Crate the obligations belong to.
    pub crate_name: String,
    /// Agreement threshold in force.
    pub threshold: usize,
    /// Per-check solver timeout (seconds) used at certification time.
    /// Replay re-uses this so a non-default original timeout cannot
    /// cause a spurious MISMATCH (audit 2026-05-29).
    pub timeout_seconds: u64,
    /// Solver pool names used to certify.
    pub solvers: Vec<String>,
    /// One entry per obligation that reached the agreement gate (it has a
    /// replayable SMT decision). Obligations that never reached the gate are
    /// in `uncertified`, not here.
    pub obligations: Vec<ObligationCertificate>,
    /// Total VC obligations the crate produced — the denominator for
    /// coverage. The bundle is a COMPLETE ledger iff this equals
    /// `obligations.len() + uncertified.len()` (see `ledger_consistent`).
    /// Defaulted for back-compat with format_version-1 bundles (which did not
    /// record it); a 0 here on a bundle that has obligations means "coverage
    /// unknown" and replay treats it as fail-closed (2026-06-15 deep audit).
    #[serde(default)]
    pub total_obligations: usize,
    /// Obligations that produced no replayable certificate
    /// (pending / consistency-refused / consistency-unconfirmed). Listed so
    /// a replayer can detect PARTIAL coverage rather than mistaking "every
    /// listed cert discharged" for "crate verified". Empty in the
    /// fully-discharged case.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub uncertified: Vec<UncertifiedObligation>,
    /// Hex HMAC-SHA256 over the canonical bundle content (everything
    /// except this field), set by [`CertificateBundle::sign`]. `None`
    /// for an unsigned bundle; omitted from the JSON when absent so
    /// unsigned bundles and older certs round-trip cleanly (Task T.3).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
}

impl CertificateBundle {
    /// Construct an empty bundle stamped with the current format
    /// version and the given context.
    #[must_use]
    pub fn new(
        tool_version: impl Into<String>,
        crate_name: impl Into<String>,
        threshold: usize,
        timeout_seconds: u64,
        solvers: Vec<String>,
    ) -> Self {
        Self {
            format_version: CERT_FORMAT_VERSION,
            tool_version: tool_version.into(),
            crate_name: crate_name.into(),
            threshold,
            timeout_seconds,
            solvers,
            obligations: Vec::new(),
            total_obligations: 0,
            uncertified: Vec::new(),
            signature: None,
        }
    }
    /// Canonical bytes the signature covers: the bundle serialized with
    /// the `signature` field cleared (so the MAC is over content only).
    /// serde_json over a struct is deterministic (declaration field
    /// order; the bundle holds only `Vec`s, no nondeterministic maps),
    /// so producer and verifier agree on these bytes.
    fn canonical_bytes(&self) -> Result<Vec<u8>, serde_json::Error> {
        let mut copy = self.clone();
        copy.signature = None;
        serde_json::to_vec(&copy)
    }
    /// Sign the bundle in place with HMAC-SHA256 over its canonical
    /// content. Makes the certificate tamper-RESISTANT for anyone who
    /// does not hold `key` (Task T.3): altering any field — a swapped
    /// `smt`, a lowered `threshold`, an edited `verdict` — invalidates
    /// the signature.
    ///
    /// # Errors
    /// Returns `Err` if the bundle cannot be canonicalized (serde).
    pub fn sign(&mut self, key: &[u8]) -> Result<(), String> {
        let bytes = self
            .canonical_bytes()
            .map_err(|e| format!("canonicalizing bundle for signing: {e}"))?;
        self.signature = Some(to_hex(&hmac_sha256(key, &bytes)));
        Ok(())
    }
    /// Verify the bundle's signature against `key`. Constant-time
    /// (via the `hmac` crate's `verify_slice`). Returns `Unsigned` if no
    /// signature is present, `Valid` if it verifies, `Invalid` if it
    /// was tampered or signed with a different key.
    #[must_use]
    pub fn verify_signature(&self, key: &[u8]) -> SignatureStatus {
        let Some(sig_hex) = &self.signature else {
            return SignatureStatus::Unsigned;
        };
        let Some(sig_bytes) = from_hex(sig_hex) else {
            return SignatureStatus::Invalid;
        };
        let Ok(bytes) = self.canonical_bytes() else {
            return SignatureStatus::Invalid;
        };
        let Ok(mut mac) = HmacSha256::new_from_slice(key) else {
            return SignatureStatus::Invalid;
        };
        mac.update(&bytes);
        if mac.verify_slice(&sig_bytes).is_ok() {
            SignatureStatus::Valid
        } else {
            SignatureStatus::Invalid
        }
    }
    /// Whether the bundle carries a signature (verified or not).
    #[must_use]
    pub fn is_signed(&self) -> bool {
        self.signature.is_some()
    }
    /// Whether the obligation ledger adds up: `total_obligations` equals the
    /// certified-plus-uncertified count. A mismatch means the bundle is
    /// incomplete (a v1 bundle with `total_obligations == 0`) or tampered;
    /// either way replay must fail closed (2026-06-15 deep audit).
    #[must_use]
    pub fn ledger_consistent(&self) -> bool {
        self.total_obligations == self.obligations.len() + self.uncertified.len()
    }
    /// Whether this bundle attests a FULLY verified crate: the ledger is
    /// consistent, NO obligation was left uncertified, and EVERY certified
    /// obligation discharged. This is the artifact-level analogue of the
    /// wrapper's exit-0 — and precisely the property the 2026-06-15 audit
    /// found was not checkable from the bundle alone (it listed only the
    /// discharged certs, with no denominator, so "all listed certs
    /// discharged" did not imply "crate verified").
    ///
    /// It does NOT re-run solvers; a discharged cert could still fail to
    /// reproduce. A trustworthy "this crate is verified" decision is this
    /// AND every certificate reproducing under [`replay_bundle`] — see the
    /// `cargo pitbull replay` subcommand, which requires both.
    #[must_use]
    pub fn attests_full_verification(&self) -> bool {
        // A zero-obligation bundle attests NOTHING — there is nothing that was
        // verified, so it must not read as "fully verified". Defense in depth
        // (2026-06-15 red-team): `replay`'s empty-bundle guard already bails
        // before this is consulted, but a future caller without that guard
        // must not mistake an empty (or all-zero) bundle for a verification.
        self.total_obligations != 0
            && self.ledger_consistent()
            && self.uncertified.is_empty()
            && self
                .obligations
                .iter()
                .all(ObligationCertificate::is_discharged)
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
        // Reject a bundle whose certificates are internally inconsistent
        // (hand-forged or corrupted). Fail closed at load (audit
        // 2026-05-29) rather than silently replaying a self-contradictory
        // certificate.
        for ob in &bundle.obligations {
            ob.check_internal_consistency()?;
        }
        // Reject a bundle whose obligation ledger doesn't add up — incomplete
        // or tampered (2026-06-15 deep audit). Skipped when
        // `total_obligations == 0`: that is a format_version-1 bundle (the
        // field predates v2) whose coverage is simply unknown, and replay's
        // completeness gate (`attests_full_verification`) already fails closed
        // on it. A v2 producer always sets a non-zero, consistent total.
        if bundle.total_obligations != 0 && !bundle.ledger_consistent() {
            return Err(format!(
                "certificate bundle ledger is inconsistent: total_obligations {} \
                 != {} certified + {} uncertified; refusing to replay an \
                 incomplete or tampered bundle",
                bundle.total_obligations,
                bundle.obligations.len(),
                bundle.uncertified.len(),
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
        let mut bundle = CertificateBundle::new("0.1.0-dev", "mycrate", 2, 60, vec![
            "z3".into(),
            "cvc5".into(),
        ]);
        bundle
            .obligations
            .push(ObligationCertificate::from_run("pb049-neg-0", "PB049", "(check-sat)", &results, 2));
        bundle.total_obligations = 1; // a complete, consistent ledger
        let json = bundle.to_json().expect("serialize");
        let back = CertificateBundle::from_json(&json).expect("deserialize");
        assert_eq!(back, bundle);
        assert_eq!(back.format_version, CERT_FORMAT_VERSION);
        assert_eq!(back.timeout_seconds, 60);
        assert_eq!(back.total_obligations, 1);
    }

    /// A bundle from a NEWER format version is refused (fail closed).
    #[test]
    fn from_json_refuses_newer_format() {
        let json = format!(
            "{{\"format_version\":{},\"tool_version\":\"x\",\"crate_name\":\"c\",\
             \"threshold\":2,\"timeout_seconds\":60,\"solvers\":[],\"obligations\":[]}}",
            CERT_FORMAT_VERSION + 1,
        );
        let err = CertificateBundle::from_json(&json).expect_err("must refuse newer format");
        assert!(err.contains("newer than this tool supports"), "got: {err}");
    }

    /// A hand-forged/corrupted certificate whose recorded verdict
    /// disagrees with its solver_results is rejected at load (audit
    /// 2026-05-29 defense-in-depth). Here: `verdict:"discharged"` over
    /// solver_results that show a `sat` (which would re-derive to
    /// `refuted`/`disagreement`, never `discharged`).
    #[test]
    fn from_json_rejects_internally_inconsistent_cert() {
        let json = format!(
            "{{\"format_version\":{CERT_FORMAT_VERSION},\"tool_version\":\"x\",\
             \"crate_name\":\"c\",\"threshold\":1,\"timeout_seconds\":60,\
             \"solvers\":[\"z3\"],\"obligations\":[{{\
             \"id\":\"pb049-neg-0\",\"rule\":\"PB049\",\"smt\":\"(check-sat)\",\
             \"solver_results\":[{{\"solver\":\"z3\",\"verdict\":\"sat\"}}],\
             \"verdict\":\"discharged\",\"unsat_votes\":1,\"threshold\":1}}]}}",
        );
        let err = CertificateBundle::from_json(&json)
            .expect_err("must reject an internally inconsistent certificate");
        assert!(err.contains("internally inconsistent"), "got: {err}");
    }

    /// An honest producer's certificate always passes the internal
    /// consistency check (it is built by the same `vote`).
    #[test]
    fn honest_cert_passes_internal_consistency() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let cert = ObligationCertificate::from_run("o", "PB049", "(check-sat)", &results, 2);
        assert!(cert.check_internal_consistency().is_ok());
    }

    fn signed_bundle() -> (CertificateBundle, Vec<u8>) {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let mut b = CertificateBundle::new("0.1.0", "c", 2, 60, vec!["z3".into(), "cvc5".into()]);
        b.obligations
            .push(ObligationCertificate::from_run("pb049-neg-0", "PB049", "(check-sat)", &results, 2));
        b.total_obligations = 1; // complete ledger; the MAC now covers it too
        let key = b"super-secret-ci-key".to_vec();
        b.sign(&key).expect("sign");
        (b, key)
    }

    /// Task T.3: a signed bundle verifies under the same key.
    #[test]
    fn sign_then_verify_is_valid() {
        let (b, key) = signed_bundle();
        assert!(b.is_signed());
        assert_eq!(b.verify_signature(&key), SignatureStatus::Valid);
    }

    /// Tampering ANY signed field (here a swapped SMT — the Critical
    /// the audit found) invalidates the signature.
    #[test]
    fn tampered_smt_fails_verification() {
        let (mut b, key) = signed_bundle();
        // The swapped-SMT attack: replace the problem with a trivially
        // unsat one while leaving id/rule/verdict intact.
        b.obligations[0].smt = "(assert false)\n(check-sat)\n".into();
        assert_eq!(b.verify_signature(&key), SignatureStatus::Invalid);
    }

    /// Tampering the threshold (the High the audit found) invalidates.
    #[test]
    fn tampered_threshold_fails_verification() {
        let (mut b, key) = signed_bundle();
        b.obligations[0].threshold = 1;
        assert_eq!(b.verify_signature(&key), SignatureStatus::Invalid);
    }

    /// A different key does not verify.
    #[test]
    fn wrong_key_fails_verification() {
        let (b, _key) = signed_bundle();
        assert_eq!(b.verify_signature(b"a-different-key"), SignatureStatus::Invalid);
    }

    /// An unsigned bundle reports `Unsigned` (not `Invalid`).
    #[test]
    fn unsigned_bundle_is_unsigned() {
        let results = [r("z3", SolverResult::Unsat)];
        let mut b = CertificateBundle::new("0.1.0", "c", 1, 60, vec!["z3".into()]);
        b.obligations
            .push(ObligationCertificate::from_run("o", "PB049", "(check-sat)", &results, 1));
        assert!(!b.is_signed());
        assert_eq!(b.verify_signature(b"any-key"), SignatureStatus::Unsigned);
    }

    /// The signature survives a JSON round-trip and still verifies.
    #[test]
    fn signature_survives_json_round_trip() {
        let (b, key) = signed_bundle();
        let json = b.to_json().expect("serialize");
        let back = CertificateBundle::from_json(&json).expect("deserialize");
        assert_eq!(back.verify_signature(&key), SignatureStatus::Valid);
    }

    /// A malformed/non-ASCII signature string must fail closed to
    /// `Invalid` and MUST NOT panic the verifier (audit 2026-05-29
    /// red-team HIGH: `from_hex` used to slice a `&str` at a
    /// non-char-boundary, panicking on multibyte input).
    #[test]
    fn malformed_signature_is_invalid_not_panic() {
        let (mut b, key) = signed_bundle();
        // 4 bytes, even length, contains a 3-byte char — the old
        // `&s[i..i+2]` would panic here.
        b.signature = Some("a\u{20ac}".to_string());
        assert_eq!(b.verify_signature(&key), SignatureStatus::Invalid);
        // odd length, non-hex, empty — all Invalid, none panic.
        b.signature = Some("xyz".to_string());
        assert_eq!(b.verify_signature(&key), SignatureStatus::Invalid);
        b.signature = Some(String::new());
        assert_eq!(b.verify_signature(&key), SignatureStatus::Invalid);
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

    // ===== coverage ledger (2026-06-15 deep audit: cert completeness) =====

    /// A bundle whose `total_obligations` equals its discharged certs, with
    /// nothing uncertified, attests full verification.
    #[test]
    fn attests_full_verification_true_for_complete_discharged_bundle() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let mut b = CertificateBundle::new("0.1.0", "c", 2, 60, vec!["z3".into(), "cvc5".into()]);
        b.obligations
            .push(ObligationCertificate::from_run("o0", "PB049", "(check-sat)", &results, 2));
        b.total_obligations = 1;
        assert!(b.ledger_consistent());
        assert!(b.attests_full_verification());
    }

    /// Defense in depth (2026-06-15 red-team): a zero-obligation bundle is
    /// ledger-consistent (0 == 0) with nothing uncertified and `.all()`
    /// vacuously true — but it attests NOTHING and must NOT read as fully
    /// verified, lest a future caller (without `replay`'s empty-guard) treat
    /// an empty bundle as a verification.
    #[test]
    fn attests_full_verification_false_for_empty_bundle() {
        let b = CertificateBundle::new("0.1.0", "c", 2, 60, vec!["z3".into(), "cvc5".into()]);
        assert_eq!(b.total_obligations, 0);
        assert!(b.ledger_consistent(), "0 == 0 + 0");
        assert!(
            !b.attests_full_verification(),
            "a zero-obligation bundle must not attest full verification",
        );
    }

    /// An obligation left UNCERTIFIED (e.g. a pending PB043 panic) means the
    /// crate is NOT fully verified — even though the listed cert discharged.
    /// This is the exact silent-narrowing the audit flagged: a clean replay
    /// of a complete-looking bundle must no longer imply the crate verified.
    #[test]
    fn attests_full_verification_false_with_uncertified() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let mut b = CertificateBundle::new("0.1.0", "c", 2, 60, vec!["z3".into(), "cvc5".into()]);
        b.obligations
            .push(ObligationCertificate::from_run("o0", "PB049", "(check-sat)", &results, 2));
        b.uncertified.push(UncertifiedObligation {
            id: "pb043-panic-0".into(),
            rule: "PB043".into(),
            status: "pending".into(),
        });
        b.total_obligations = 2;
        assert!(b.ledger_consistent(), "1 certified + 1 uncertified == 2");
        assert!(
            !b.attests_full_verification(),
            "a pending/uncertified obligation must defeat full-verification",
        );
    }

    /// A certified-but-NOT-discharged obligation (here a `refuted`) defeats
    /// full verification.
    #[test]
    fn attests_full_verification_false_with_nondischarged_cert() {
        let unsat = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let sat = [r("z3", SolverResult::Sat), r("cvc5", SolverResult::Sat)];
        let mut b = CertificateBundle::new("0.1.0", "c", 2, 60, vec!["z3".into(), "cvc5".into()]);
        b.obligations
            .push(ObligationCertificate::from_run("o0", "PB049", "(check-sat)", &unsat, 2));
        b.obligations
            .push(ObligationCertificate::from_run("o1", "PB049", "(check-sat)", &sat, 2));
        b.total_obligations = 2;
        assert!(b.ledger_consistent());
        assert!(!b.obligations[1].is_discharged());
        assert!(!b.attests_full_verification());
    }

    /// A ledger that doesn't add up (total != certified + uncertified) is not
    /// full verification — and is refused at load (fail closed).
    #[test]
    fn ledger_inconsistent_defeats_full_verification_and_load() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let mut b = CertificateBundle::new("0.1.0", "c", 2, 60, vec!["z3".into(), "cvc5".into()]);
        b.obligations
            .push(ObligationCertificate::from_run("o0", "PB049", "(check-sat)", &results, 2));
        b.total_obligations = 5; // claims 5 obligations; only 1 accounted for
        assert!(!b.ledger_consistent());
        assert!(!b.attests_full_verification());
        let json = b.to_json().expect("serialize");
        let err = CertificateBundle::from_json(&json)
            .expect_err("ledger-inconsistent bundle must be refused at load");
        assert!(err.contains("ledger is inconsistent"), "got: {err}");
    }

    /// The coverage ledger (total + uncertified) survives a JSON round-trip.
    #[test]
    fn ledger_survives_json_round_trip() {
        let results = [r("z3", SolverResult::Unsat), r("cvc5", SolverResult::Unsat)];
        let mut b = CertificateBundle::new("0.1.0", "c", 2, 60, vec!["z3".into(), "cvc5".into()]);
        b.obligations
            .push(ObligationCertificate::from_run("o0", "PB049", "(check-sat)", &results, 2));
        b.uncertified.push(UncertifiedObligation {
            id: "pb043-panic-0".into(),
            rule: "PB043".into(),
            status: "pending".into(),
        });
        b.total_obligations = 2;
        let json = b.to_json().expect("serialize");
        let back = CertificateBundle::from_json(&json).expect("deserialize");
        assert_eq!(back, b);
        assert_eq!(back.total_obligations, 2);
        assert_eq!(back.uncertified.len(), 1);
        assert_eq!(back.uncertified[0].status, "pending");
    }

    /// A legacy format_version-1 bundle (no ledger fields) still LOADS — its
    /// `total_obligations` defaults to 0 — but does NOT attest full
    /// verification, because coverage is unknown (fail closed).
    #[test]
    fn v1_bundle_without_ledger_does_not_attest_full_verification() {
        let json = r#"{"format_version":1,"tool_version":"x","crate_name":"c","threshold":2,"timeout_seconds":60,"solvers":["z3","cvc5"],"obligations":[{"id":"o0","rule":"PB049","smt":"(check-sat)","solver_results":[{"solver":"z3","verdict":"unsat"},{"solver":"cvc5","verdict":"unsat"}],"verdict":"discharged","unsat_votes":2,"threshold":2}]}"#;
        let b = CertificateBundle::from_json(json).expect("v1 bundle still parses");
        assert_eq!(b.total_obligations, 0, "v1 has no ledger; defaults to 0");
        assert!(
            !b.attests_full_verification(),
            "unknown coverage (v1) must not be treated as full verification",
        );
    }
}
