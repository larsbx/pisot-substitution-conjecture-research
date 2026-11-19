# Ordinary hull topology: fresh scoped acceptance

Base: `ec026774e666fb8e8ac43b1ba975b9a4df8891b2` (PR #623).
Verified local source checkpoint: `9fb7c7d7f528f3ccf35d9f393dc050d063e26762`.
Published source checkpoint: `f407bd05f4ca12603e78026a08b7058e18e09cea`.
Both source checkpoints have Git tree
`5d4cdfca23cac14478efd5a84c3bd4813cb0016b`; fetching the published checkpoint
and comparing its complete tree with the local checkpoint produced no diff.

The final documentation/evidence commit preserves all checked Lean files,
toolchain pins and acceptance support. This packet is local scoped
acceptance, not a full root-library build or a hosted acceptance receipt.
Independent human review is pending; agent scope review does not change
that status.

## Accepted formal scope

The unchanged canonical gate rebuilt the entire periodic-partner local
import closure in a new temporary project. It cloned the pinned dependency
repositories and restored only selected upstream source-hash artifacts;
no local project object was reused. Lean is 4.34.0-rc2, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, with mathlib revision
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.

The compiled audit checks **24 modules and 1,458 declarations**, including
**1,068 theorem declarations and all 577 source-named proofs**. Only
`propext`, `Classical.choice` and `Quot.sound` are accepted. The four new
modules add **44 named proofs**: 15 exact-hull continuity proofs, 21
ordinary-topology proofs, five topology controls and three realization
adapter proofs. Definitions and generated helper declarations are counted
separately by the compiled audit, not added to the 44 source-named proofs.

All **236 source and pin bindings** match the canonical snapshot
`7bee0352555808162025eb1c3596ee278b90d5482348a1512bf5b0cdebbd45d8`.
The gate rechecked the sources and exact dependency pins after cloning,
after upstream cache restoration, after compilation and after the audit.
Binding all project sources does not mean every bound module was built:
the accepted compilation scope is the 24-module periodic-partner closure.

## Records

| Record | Meaning |
| --- | --- |
| `periodic-partner-gate.log.gz` | Lossless combined stdout/stderr of the completed canonical gate; empty audit fields and original line endings are preserved. |
| `gate-summary.log` | Selected terminal receipts extracted from that log without changing their text. |
| `receipt.json` | Source revisions, scope, exact counts, pins, allowed axioms and review boundary. |
| `source-bindings.json` | The canonical JSON manifest reconstructed from the logged source-binding records; its SHA-256 equals the gate's snapshot digest. |
| `support-bindings.json` | SHA-256 of the unchanged gate and proof-bank generator, checked against the verified source checkpoint. |
| `replay-command.txt` | Replay command and the environment supplied to the recorded invocation. |
| `repository-checks.log.gz` | Lossless generated proof inventory, generated ledger, claim governance and Markdown-source check output. |
| `repository-tests.log` | The final focused Python regression run, archived after completion. |
| `repository-tests.xml` | The corresponding JUnit receipt: 252 tests, zero failures, errors or skips. |
| `SHA256SUMS` | Checksums of exactly the files in this packet, excluding the checksum manifest itself. |

The standalone repository checks and regression receipt are separate from
the Lean gate. All **252 focused regression tests pass**. A development check initially found a stale generated proof
inventory after the final adapter edit; regeneration corrected it before
the recorded canonical gate. No mathematical statement or acceptance
criterion was weakened to make the checks pass.

## Mathematical boundary

The same legal carrier now has the ordinary small-translation/window
topology, a checked neighbourhood basis, jointly continuous translation
and continuous forward inflation. General negative controls prove that
the old exact-agreement orbit maps are discontinuous at zero and that the
reverse carrier projection is not continuous whenever a hull tiling exists.

The unchanged concrete realization on the ordinary presentation is
continuous if and only if its exact-source map is continuous, under its
existing hypotheses. **Neither side is proved here.** No source
compactness, Hausdorffness, inverse-inflation continuity, recognizability,
normalized BBK identification, surjectivity or finite fibres are supplied.
No BDS, witness-selection or remaining rank-two obligation is discharged;
C4 and PSC remain open.

See the [implementation note](../../docs/c4-ordinary-hull-topology-2026-11-19.md)
for the derivation, theorem names, source assumptions and negative controls,
and the [pre-code source decision](../../docs/c4-ordinary-hull-topology-stop-go-2026-11-19.md)
for the literature and hypothesis checks.

## Replay

From the repository root, with the pinned Lean/Lake executables and Python
test dependencies available:

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 tools/check_markdown_source.py
python3 -m pytest -q tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_recorded_data_integrity.py
sha256sum -c evidence/ordinary-hull-topology-2026-11-19/SHA256SUMS
```

Keep subsequent replay outputs outside this packet. The regression log and
JUnit receipt were added after their run, and the complete final manifest was checked again
after that addition; the regression run does not purport to checksum its
own still-unwritten output.
