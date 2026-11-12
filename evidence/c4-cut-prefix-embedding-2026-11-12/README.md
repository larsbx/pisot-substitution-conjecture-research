# Local replay of actual cut-prefix embedding

Tested code revision: `73a0b6a95539beb1b6712afec0f8412571b41cd3`.

Tested tree: `8233701f593a8ba680356a88c2c6fc8e4cf01df5`.

Base: `main@9a1357ed5dae3b4502d29c34396d0e9403ccca75`.

This directory records local verification of the new literal embedding,
uniform named-prefix proximity, paired balanced-cut witnesses, and controls.
The later evidence commit archives the code revision above; it does not
claim a hosted run of itself. The mathematical derivation and precise
scope are in [the implementation note](../../docs/c4-cut-prefix-embedding-2026-11-12.md).

## Verification status

| Check | Observed result |
| --- | --- |
| Full isolated Lean source build and compiled axiom audit | Passed at the exact code revision: all 2,670 source-named proofs reached; 6,589 compiled declarations and 4,819 theorem constants audited. Only `propext`, `Classical.choice`, and `Quot.sound`. |
| Focused new Lean modules and controls | All three new modules compiled in the required isolated run. Their 37 explicit theorems and seven definitions were matched to compiled records; 52 owned constants include generated helpers. |
| Canonical native test | Passed: 1,204 complete marks, 7,860 residue witnesses, 272 balanced cuts, 19 refusal controls. |
| Complete native packet / independent oracle | All fields and records agree: 3,220 marks, 21,028 residues, 272 cuts, including 51 with distinct following letters. |
| Python tests with the actual native packet | Eight passed, zero skipped. The optimized-mode oracle also passed 18 refusals and one residue sanity control. |
| Existing named-chart Quint model | At the exact code head/tree: 22 tests passed; 10 mutations rejected. |
| Existing prefix-window Quint model | At the exact code head/tree: 19 tests passed; nine mutations rejected. |
| Complete local locked-pixi provisioning | Failed on a network dependency download. Native replay used the exact version-pinned compiler from an existing auxiliary environment; full environment success is not claimed. |
| Final proof-bank / ledger / governance checks | Passed after the evidence documentation was added; 32 generated ledger surfaces remain current and all 126 governed claim statuses are unchanged. |
| Prepared PR body policy | Passed the local required-heading and visible-content check; the complete prepared body is archived. |
| Hosted candidate CI | Not run; this local archive does not assert hosted acceptance. |

The native compiler was `Mojo 1.1.0.dev2026090805 (34562fa1)`. Its installed
package metadata matches the checked-in lock. The exact binary, lock,
source, packet, and log hashes and the development-run timing are recorded
in [native-local-receipt.json](native-local-receipt.json). The package archive
itself was not rehashed for that receipt. The native and oracle runs preceded
the code commit; the receipt verifies that all five candidate source files
match the committed blobs.

The Quint checks are bounded checks of their unchanged model interfaces.
Their receipts preserve the domain sizes, exact revisions, model and runner
hashes, named tests, mutation descriptions, and individual log hashes. They
do not establish the universal Lean conclusions.

The unchanged `tools/check_lean.sh` exited **0**. The source worktree was
clean at the tested commit/tree before and after the run. Its complete log
has SHA-256 `a6b1cfd63bc8750830c9533e5a204e1326c8e3958fd386d258dd70a3a6da5a43`. The pinned compiler and
the fixed upstream source-hash Mathlib cache remain explicit trust inputs.
No locally cached compiled project or dependency artifacts entered this
isolated acceptance run. Hosted CI remains unrun.

## Inspectable artifacts

- [isolated-lean.log.gz](isolated-lean.log.gz) preserves the complete required
  source-build and axiom-audit output.
- [compiled-audit-inspection.json](compiled-audit-inspection.json) independently
  checks exact ownership, declaration kinds, source hashes, completion
  counts and permitted axioms; [compiled-new-declarations.log.gz](compiled-new-declarations.log.gz)
  contains every compiled record owned by the three new modules.
- [new-proof-inventory.json](new-proof-inventory.json) lists the 37 explicit
  theorem names at the code revision.
- [pr-body.md](pr-body.md) is the complete prepared PR text;
  [pr-body-policy-check.json](pr-body-policy-check.json) records its local
  show-your-work check.
- [receipt.json](receipt.json) summarizes the exact local outcomes, and
  `files.sha256` binds every file in this archive.
- [sources.json](sources.json) binds all changed candidate files and relevant
  gate configuration to the tested code commit.
- [packet.json.gz](packet.json.gz) contains the complete native packet without
  dropping any witness fields or records.
- [oracle-receipt.json](oracle-receipt.json), [native-tests.log](native-tests.log),
  and [python-tests.log](python-tests.log) retain the actual finite replay.
- [chart-quint/quint-receipt.json](chart-quint/quint-receipt.json) and
  [window-quint/quint-receipt.json](window-quint/quint-receipt.json) bind their
  complete adjacent test and mutation logs.
- [development-controls-axioms.log](development-controls-axioms.log) retains
  the separate fresh-import audit of all 15 negative-control lemmas.
- [compact-followon-plan.md](compact-followon-plan.md) records the precise
  next compact-cover target and the inspected Mathlib route. It is a proof
  plan, with no additional Lean theorem claimed complete.

The decompressed packet is 2,060,008 bytes with SHA-256
`440127dd5d0617cc1f3b75a960db4fbde7e7c31cc931146a1635637a967b030e`.
Compression preserves the entire packet, rather than substituting a digest
or summary for record-level replay.

## Preserved failed attempts

The first complete isolated Lean attempt used a 4.9 GB temporary filesystem.
It failed while unpacking the freshly fetched dependency cache with
`No space left on device`; it did not complete the project build or axiom
audit. Its complete log is retained in
[failed-isolated-tmpfs.log.gz](failed-isolated-tmpfs.log.gz). The subsequent
attempt used the unchanged gate with `TMPDIR` on the larger workspace
filesystem. No local compiled PSC or Mathlib artifacts were substituted
into that isolated verification.

An initial named-chart Quint run was refused because the Git head changed
while it was running. The failed receipt and every associated log remain
in [failed-chart-quint-stale-head](failed-chart-quint-stale-head/), with the
explicit refusal in [failed-chart-quint-stale-head.log](failed-chart-quint-stale-head.log).
Only the subsequent successful run at the stable code head/tree receives
acceptance credit.

Two separate development compilation runs were manually interrupted to
avoid duplicating resource use while the full isolated gate progressed.
The timing probe remained inconclusive; no proof failure or complete-build
acceptance is inferred. [development-attempts.json](development-attempts.json)
records the exit statuses and retained logs.

## Replay

From the repository root, replay the preserved packet independently:

```sh
gzip -dc evidence/c4-cut-prefix-embedding-2026-11-12/packet.json.gz > /tmp/cut-prefix-packet.json
python -O oracles/python/c4_cut_prefix_embedding.py --native /tmp/cut-prefix-packet.json --controls
C4_CUT_PREFIX_NATIVE=/tmp/cut-prefix-packet.json python -m pytest --assert=plain -o addopts='' -q tests/test_c4_cut_prefix_embedding_oracle.py
```

The implementation note also gives the canonical locked-environment native
reconstruction and full isolated Lean commands. The isolated gate needs
enough temporary disk space for the fresh dependency artifacts; `TMPDIR`
may select a larger filesystem without changing the gate.

## Scope retained

The new formal statements concern actual prefix witnesses for both named
substitutions, every finite source word, every actual mark, and cofinal
powers `12n`. They give a fixed-source stable error bound tending to zero
and exact agreement at every specified finite residue depth. Their paired
form applies to a common balanced-cut Parikh vector; strict label separation
requires an actual supplied `StrictSystem`.

The finite executable replay covers its declared powers `0,2,4,6`, source
words, caps, and complete packet. It neither supplies a strict system nor
proves convergence or positive measure. Compact-cover containment, the
fixed-origin regular-cylinder lattice count with correct normalization,
and the strict-cut density / positive-measure assembly remain separate
formal obligations. All 126 governed claim statuses remain unchanged.
Independent human review remains pending.
