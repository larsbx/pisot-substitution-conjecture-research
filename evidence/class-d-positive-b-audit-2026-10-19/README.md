# Positive-b class-D refusal audit

These are failed candidate runs, **not successful family certificates**.
The available release compiler is Mojo 1.1.0 (8189361e), not the repository's
pinned nightly. Exact source hashes and exit codes are in `run-context.json`.

From `kernel/`, build each source with `mojo build -I . SOURCE -o BINARY`,
then run the binary (with `plus` or `minus` for the complete driver).
For the regression use `mojo run -I . tests/test_class_d_positive_b_obstructions.mojo`.
Mojo's Crashpad warning is environmental and does not prevent execution.

The mathematical interpretation, exact source labels, changing-sign polynomials,
and next correction are in `docs/p1b-class-d-positive-b-wedge-2026-10-19.md`,
section 10. No boundary strip was reached. No label escaped a checked cover.
No successful `COMPLETE_*` receipt was emitted.
