# Explicit transport of the two named carrier checks

This packet binds the follow-up to PR #569's failed source
`52614a3b5a7199b1d17cb7a0b435da71e1e80569` and records the source/protocol
checks completed before publication. It does not claim complete Lean
acceptance. The published commit containing this packet is the new candidate;
successful hosted results must name that actual commit.

## Contract and repair

The theorem `Psc.NamedForwardCarrier.check_checkedStates` keeps its original
statement. Each branch selects its actual carrier by a local equality, then
uses `congrArg₂` to transport the existing checked theorem across that equality
and the exact literal-substitution equality. Both carrier tables and their
generated checks are unchanged. The proof introduces no top-level declaration,
axiom, recursion-limit override, new seed or altered notion of termination.

This is a regression repair of the previously reviewed forward-carrier
contract. The earlier targeted literature decisions remain applicable.

## Evidence and replay

- `previous-hosted-failures.json` preserves selected exact lines fetched from
  the original GitHub job logs. Both actual carrier modules compiled before
  the same consumer recursion error at the #560 and #569 source revisions.
  These excerpts are not full artifacts or successful gate receipts.
- `focused-tests-receipt.json` records the actual successful terminal output
  of the three existing test suites: 327 tests and 35 subtests passed. The
  warning concerns the installed pytest plugin's deprecated `CallSpec2` import.
- `source-and-checks.json` binds the proof source, both generated checkers,
  both literal-data modules and the regenerated proof bank by SHA-256. It
  records successful proof-bank, generated-ledger and claim-governance checks.

Run the same source/protocol checks from the repository root:

```sh
python3 -m pytest tests/test_archived_payload_lean_replay.py tests/test_forward_carrier_evidence.py tests/test_proof_bank.py
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
```

The existing controls reject wrong termination types independently, missing
endpoints, nonstandard axioms, literal-fixture rebinding, omitted ordered
seeds or child occurrences, and inconsistent generated imports. Their success
does not establish that the repaired production Lean theorem compiles.

## Remaining acceptance

At publication, actual two-fixture production compilation, the complete
isolated compiled axiom audit and both original archives' nine-endpoint replay
remain pending. The previous empty-slot probe cannot replace those checks.
Use the unchanged commands in the
[acceptance note](../../docs/c4-named-termination-acceptance-2026-11-13.md#replay).
Later successful provider records must remain bound to their source revision;
updating a PR description does not change the candidate source.

All 126 governed claim statuses remain unchanged. The intended result covers
the two literal substitutions' ordered swap seeds and actual descendants;
universal A1′, BH, G1, C4, PDS and PSC are outside this repair.

`SHA256SUMS` covers every other file in this packet. Verify it from this
directory with `sha256sum --check SHA256SUMS`.
