# Pitbull subset corpus
This directory is the canonical body of evidence that the PSS-1 subset
checker is well-calibrated.
## Layout
- `reject/PB{nnn}_{slug}.rs` — must produce a subset violation with rule
  PB{nnn}. The file's first doc-comment line states the expected outcome.
- `accept/PB{nnn}_{slug}.rs` — adjacent valid program that must NOT
  produce any subset violation. Usually a direct rewrite of the matching
  reject example using safe constructs.
The naming convention is mandatory and is checked by
`tests/integration.rs::*_corpus_filenames_well_formed`.
## v0.1 baseline
The v0.1 release ships:
- One representative reject and one accept example per category (A–K).
PSS-1 §15 requires ≥10 rejects and ≥5 accepts per rule for full
qualification. That target is tracked separately.
## Adding a test
1. Decide the rule the test pins.
2. Pick a unique slug that names the *what*, not the *why*.
3. Drop the file in `reject/` or `accept/`.
4. The integration tests pick it up automatically on the next run.
## End-to-end via `corpus_runs_full_pipeline`
The integration test `corpus_runs_full_pipeline` (Milestone 2 Task C,
commit `50ec60d`) walks every corpus file through the real
`pitbull-rustc` wrapper subprocess. It runs by default when both the
nightly wrapper and the nightly toolchain are present; if either is
missing, it skips gracefully unless `PITBULL_REQUIRE_E2E=1` is set
(see HANDOFF.md §4 for the build incantation and §7 for the
`KNOWN_UNIMPLEMENTED_REJECT` / `KNOWN_UNDISCHARGED_ACCEPT` skip lists
covering rules that are not yet discharged end-to-end).
