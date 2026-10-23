# Class-D scoped G1 dependency validation

This packet records **dependency-model execution**, not a new mathematical
certificate or current-head hosted CI acceptance. The mathematical proof is
`docs/class-d-g1-corollary-2026-10-22.md`; the canonical Mojo certificate and
its accepted runtime provenance are unchanged.

Base contribution: `3052b150582f1764c3c13c91dd43de7cd97b58eb` (PR #324).
Reconciled with main through PR #325; `source-digests.json` pins the generator,
tests, written corollary, and exact TLA inputs used in this replay.

`tlc.log` is the unedited stdout/stderr from `proof/tla/check.sh`;
`tlc.exit` is its process exit code, zero. All 18 models have the expected
outcome: 17 satisfy their invariants and the existing `MCNonProductive`
control violates `Productive` as intended. The Open model's positive
reachability includes `ClassDFiniteBPA`, while its universal G1 and PDS
nonestablishment invariants still hold.

Runtime: Java with TLC 2.19 (08 August 2024), downloaded from the repository
workflow's public `tlaplus/tlaplus/releases/latest/download/tla2tools.jar`
location. The exact downloaded jar has SHA-256
`936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`.
The mutable download location alone is not a version pin; verify this digest
for an identical-runtime replay. `runtime.txt` records the local JVM identity.

## Regression outcomes

- The three new registration/premise tests first failed because the scoped
  record did not yet exist, then passed after registration and generation.
- All 24 ledger tests passed with `TLA_TOOLS` set, including both actual TLC
  false-invariant mutations (universal G1 under its assumed gate, and scoped
  `ClassDFiniteBPA` in Open). Neither TLC test was skipped.
- Another 73 governance, proof-bank, Markdown-link, show-your-work and
  class-D acceptance-provenance tests passed. These 97 results are regression
  outcomes, not assertions that the new proof is Lean-formalized.
- Removing either hitting or finite-graph input makes the scoped result
  conditional and unreachable. Adding the existing spectral import still
  does not promote scoped finiteness to G1, productivity or PDS.
- `verify_all.sh provenance` and the accepted class-D source/CI checker pass.
  Generated source locators were regenerated after the final prose additions.

No Mojo or Lean run was performed in this continuation: neither code changed.
The full unrelated Python suite was not rerun. The separate hosted CI for
the revised PR head must be inspected before integration; the queued checks
on the older head are not successful receipts.

## Replay

From repository root, with the jar digest verified as above:

```sh
python tools/make_ledger.py --check
python tools/make_proof_bank.py --check
TLA_TOOLS=/absolute/path/to/tla2tools.jar ./proof/tla/check.sh
TLA_TOOLS=/absolute/path/to/tla2tools.jar python -m pytest -q tests/test_ledger_generation.py
python -m pytest -q tests/test_claim_governance.py tests/test_proof_bank.py tests/test_markdown_links.py tests/test_show_your_work_policy.py tests/test_class_d_integration_ci.py
python tools/check_class_d_integration_ci.py
./tools/verify_all.sh provenance
```

`SHA256SUMS` pins every packet file other than itself. Source paths in the
JSON are repository-relative; hash the corresponding current files and
compare before attributing these receipts to a later revision.
