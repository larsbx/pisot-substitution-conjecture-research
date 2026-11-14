# Finite-productivity development evidence

This packet records development checks for the source published in
`510239ac0005fb24f880369e55a4b54776224981` (draft PR #565), including the
private-inventory regression repair inherited from
`95e3c6ccb022dcc3fa269e69b334b5632040f64d` (PR #560).
It is **not a compiled Lean acceptance packet**.

## Completed checks

`source-checks/results.json` records the exact commands, exit codes,
elapsed times and raw-log hashes for the proof-bank inventory, claim
ledger, vendored-source check, Markdown check, manuscript check,
governance check, and the complete `tests/test_proof_bank.py` test file.
All seven commands returned zero. The test file reports **57 passed** and
one existing AnyIO plugin deprecation warning. The proof inventory has
126 governed claims, 2,813 named Lean proofs and 411 source openings;
inventory counts do not establish kernel acceptance.

`private-inventory-repair/` preserves the separate 57-test result on the
repair branch. Its receipt binds the repaired test file by SHA-256 and
identifies the original parent revision. The repair keeps the full
production private-proof inventory and refuses omission of synthetic or
production private declarations.

`provenance.json` binds the relevant published source files by SHA-256,
records the pinned compiler identity and distinguishes these earlier
working-tree checks from this later evidence and documentation commit.
No governed claim status was changed.

## Incomplete Lean verification

The first focused development attempt exited with code 1 before
elaboration because its output namespace shadowed the cached project
objects. Both the error log and terminal receipt are preserved in
`focused-lean/generic-build-01.*`. The second attempt uses an owned
directory containing symlinks to the real cached project objects.
`focused-lean/status.json` records the observation of that attempt; a
pending observation is not a terminal result.

These attempts use local development dependencies. Even a subsequent
successful focused compilation would not replace the unchanged
`tools/check_lean.sh` isolated build and compiled transitive-axiom audit.
The named consumer also depends on the parent strict-exclusion packet
theorem and the complete seven-proof concrete-payload replay. The older
six-proof replay on PR #560 does not satisfy that newer obligation.

The GitHub workflow snapshot is bound to the actual source heads. Queued
workflows supply no acceptance evidence. Any later terminal result must
be recorded separately against its exact source revision.

## Replay and scope

Run the commands in `source-checks/results.json` from the repository root.
The governance package is under `tools/`, so its module invocation needs
the same import path used in CI:

```sh
PYTHONPATH=tools python3 -m claim_governance.cli --root .
```

`followup-checks/governance.json` and its raw log record a fresh successful
audit with this explicit environment. The receipt also records two
earlier launch failures that could not import the package and therefore
did not run an audit.

The normal focused Lean development command is:

```sh
(cd proof/PscVerif && lake build PscVerif.FiniteProductivity PscVerif.NamedFiniteProductivity)
```

The complete unchanged gate remains:

```sh
./tools/check_lean.sh
```

The [proof note](../../docs/c4-finite-productivity.md) gives the argument,
the actual Thue–Morse and Fibonacci controls, and the explicit remaining
finite-forward-reachability premise. No finite carrier for either named
fixture is supplied here. This packet promotes no G1, unconditional
named termination, universal C4, spectral, or PSC conclusion.

All files except `SHA256SUMS` itself are listed in that manifest. Verify
them from this directory with `sha256sum -c SHA256SUMS`.
