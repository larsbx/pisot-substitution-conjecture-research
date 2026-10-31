# PR #438 acceptance repair, 2026-10-31

Status: local regression acceptance recorded; hosted exact-head acceptance pending.

The original `4356500637a2f171ef802bd35ee3f88ade6c64a0` test passed natively
but omitted the mandatory contract declaration. The repair imports
`mojo_smoke.claims.require_contract` and calls it after the assertions,
explicitly naming regression specimens, the research normalization and
supplied-prefix transport. It does not claim literal-address validation by
this parent helper, arbitrary native normalization, carrier completeness or
universal descendant productivity.

`full-governance-before.log` preserves six inherited README anchor failures.
Restoring the existing status anchors repairs them without changing a claim
record. `coverage.log`, `full-governance.log`, `python.log`, `mojo.log`, and
`mojo-version.txt` record the local repaired-source results; the JSON manifest
binds the executable sources and lockfile. These logs are local evidence,
not substitute hosted CI receipts or independent human review.

Replay from the repository root (Pixi on PATH):

```sh
python -m pytest -q tests/test_class_a_parikh_field_bridge.py
PYTHONPATH=tools python -m claim_governance.cli --root . --check coverage
PYTHONPATH=tools python -m claim_governance.cli --root .
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_parikh_field_bridge.mojo)
```

The last command must print both `CLASS_A_PARIKH_FIELD_BRIDGE_EXACT_PASS 6125`
and the exact `contract-receipt:` declared by the test. The focused workflow
checks out the PR head rather than a synthetic merge and uploads those logs,
its actual tested commit and source hashes. Repository-wide suite receipts
continue to be collected by `kernel/run_tests.sh`; this targeted replay does
not manufacture or replace that suite's receipt file.
