# Julia oracle lane

This directory contains reproducible, non-authoritative Julia implementations for BPA/SCC experiments, substitution census analysis, and counterexample search.

## Contract

- Consume committed boundary fixtures or explicitly versioned research inputs.
- Emit canonical, deterministic result vectors whenever exact types are available.
- Record Julia, package-manifest, input, seed, and precision metadata.
- Compare results with the repository's authoritative checker; never issue an acceptance verdict.
- Treat disagreement as a failing conformance result requiring investigation, not as authority transfer.

Oracle code may become durable and CI-enforced, but remains independently labelled as an oracle.
