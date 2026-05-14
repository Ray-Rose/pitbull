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
## When real MIR ingestion lands
The integration test `corpus_runs_full_pipeline` is currently marked
`#[ignore]` because the v0.1 skeleton does not yet drive `rustc_public`.
When that wiring lands (milestone 2), the `#[ignore]` comes off and the
corpus runs end-to-end. The corpus content does not change with that
transition; only the test driver does.
