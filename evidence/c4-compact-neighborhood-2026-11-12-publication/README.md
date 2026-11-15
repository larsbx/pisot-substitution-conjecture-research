# Compact-neighborhood publication provenance

This packet preserves the three original commits and maps them to their
verified GitHub mirrors. The original local proof acceptance remains bound
to **`6915e8d592b7ea5cb7c6950249811e354dc6c3e7`**, tree
**`c79e97bdae1224068895afa9dcf6cca6d7fe9fbb`**. The later archive-integrity
check applies to the staged evidence tree committed unchanged as
**`f9bcf72ebcbf6d51795beb0d1971596922ceedd5`**, tree
**`6fd49792046948eeb78ab063212fcbb164bd9513`**. Neither result is relabelled
as execution at the future commit that installs this packet.

## Original commits and published mirrors

| Role | Original commit | Published mirror | Shared tree |
| --- | --- | --- | --- |
| Pre-code literature GO | `571c8df9b5223aeef6b7f137c49b4495590d090e` | `d6ac60d44eaee938e06bff1b973fc3d0a775570f` | `9bdb1e1a896f4f29b570d843693d8672de29d06b` |
| Proof implementation | `6915e8d592b7ea5cb7c6950249811e354dc6c3e7` | `630415d2a90dac8e8e1de6625bed13edcc9a5523` | `c79e97bdae1224068895afa9dcf6cca6d7fe9fbb` |
| Accepted evidence and checksum metadata | `f9bcf72ebcbf6d51795beb0d1971596922ceedd5` | `67932724c0fb9899fec37ddd6a05de13a16327cf` | `6fd49792046948eeb78ab063212fcbb164bd9513` |

The shared prerequisite is `bdf033f647f73f911a47260e8bdad5f2e96f3c7a`. Each original
commit has the preceding original as its parent; each mirror has the
corresponding published parent. `commit-map.json` records every exact parent,
tree and original message. The root's recorded checks verified mirror tree
identity, parent translation and byte-identical raw Git messages.

The available API publication path creates its own commit metadata and
does not expose fields to preserve all original author/committer metadata.
Consequently, commit IDs change even though the source trees and messages
are preserved; changed parent IDs also propagate through the mirrored
chain. `compact-original-commits.bundle` retains the actual original objects
and their metadata, so all three original IDs remain recoverable.

## Bundle and restoration scope

- Bundle: `compact-original-commits.bundle`
- Bytes: **295,890**
- SHA256: `9d910c2bc22ad7c5c4bb810e9c51aadaf278ffa2ff36cd2ab559650e217c64ee`
- Required base: `bdf033f647f73f911a47260e8bdad5f2e96f3c7a`
- Original tip: `f9bcf72ebcbf6d51795beb0d1971596922ceedd5`

`bundle-restore-verification.json` is copied unchanged from the recorded
local replay. That replay fetched the exact base snapshot at depth one,
verified and imported the incremental bundle, recovered all three original
commit objects and trees, and checked 64 distinct changed blobs and entry
modes. Its recorded connectivity check passed within that shallow-base
scope. It does not establish the completeness of pre-existing ancestor
history. No restoration was rerun while assembling this packet.

To restore in a fresh repository, run from this packet's directory. The
base fetch below needs network access; an existing local repository holding
the exact base may replace the GitHub URL, as in the recorded replay.

```bash
sha256sum --check SHA256SUMS
psc_compact_bundle="$(pwd)/compact-original-commits.bundle"
psc_compact_restore=$(mktemp -d)
git -C "$psc_compact_restore" init --quiet
git -C "$psc_compact_restore" fetch --depth=1 --no-tags \
  https://github.com/larsbx/pisot-substitution-conjecture-research.git \
  bdf033f647f73f911a47260e8bdad5f2e96f3c7a
git -C "$psc_compact_restore" bundle verify "$psc_compact_bundle"
git -C "$psc_compact_restore" fetch --no-tags "$psc_compact_bundle" \
  HEAD:refs/heads/restored
git -C "$psc_compact_restore" rev-list --reverse \
  bdf033f647f73f911a47260e8bdad5f2e96f3c7a..refs/heads/restored
git -C "$psc_compact_restore" rev-parse \
  refs/heads/restored 'refs/heads/restored^{tree}'
git -C "$psc_compact_restore" checkout --detach \
  f9bcf72ebcbf6d51795beb0d1971596922ceedd5
```

The revision list must contain the three original IDs in the table, in
order. The restored tip and tree must equal the original evidence commit
and tree identified above. The bundle advertises `HEAD` at that original
tip; this is why the fetch refspec uses `HEAD:refs/heads/restored`.

## Local acceptance and archive integrity

The original isolated Lean gate completed with exit zero at
`2026-11-12T19:37:14.200269+00:00`. Its recorded audit contains
**6,628 compiled constants and 4,850 theorem constants**, with all
**23 explicit new theorems and eight definitions** matched to their source
names, kinds and owners. The broader new-module inventory is 39 constants
and 31 theorem constants. Those records remain in the accepted evidence
packet and retain their original code-revision binding.

The copied `checks/compact-evidence-integrity-attempt-02.json` and `.log`
record **160 passed, one warning, exit zero** at
`2026-11-12T19:38:48.899745+00:00`. This was
`tests/test_recorded_data_integrity.py`, run with pytest 9.2.0 against the
staged original evidence content above `6915e8d5`, before this provenance
packet existed. The root recorded that this tested staged content was
committed unchanged as `f9bcf72`, tree `6fd4979`. The original receipt uses
that staged-content description; this packet supplies the later commit/tree
binding without changing the receipt. This is not a test result for a
mirror commit or the future provenance tree.

The first invocation could not import pytest and exited one. Its exact
receipt and log are retained under `history/`, with no success credit.
No test or build was run during this packet's preparation.

## Metadata-only repair records

`metadata-repair/plan.json` and `metadata-repair/installation.json` are exact
copies. They record the two required `SHA256SUMS` additions to the earlier
cut-prefix evidence and publication packets. Their 74 and four pre-existing
files, respectively, including their original manifests, were preserved.
The plan and installation receipt agree on both new checksum digests. These
metadata additions are part of the original evidence tree `6fd4979`; they
do not modify the proof sources or upgrade a mathematical claim.

## Publication boundary and this packet's checksums

The planned provenance-only commit has parent
`67932724c0fb9899fec37ddd6a05de13a16327cf` and adds only this dedicated
packet. Its own future commit/tree identity is deliberately absent, so the
packet has no final-head self-reference. `SHA256SUMS` lists every other file
exactly once with a `./` packet-relative path and excludes only itself.
It pins the bundle, unchanged source records and generated documentation.

This packet makes no hosted-CI success or independent human-review claim.
Any final-head integrity test or hosted observation must be recorded
separately at the actual resulting revision. The existing incomplete,
failed and diagnostic build histories retain their scopes in the accepted
evidence packet. No claim status is promoted by this provenance record.
