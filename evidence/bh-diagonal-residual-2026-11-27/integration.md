# Integration with the concurrent beta-numeration note

The initial proof and replay packet was checked against
`8bf2a627913bb7a9eb2f05b0ed3f08c54dc647d7`. During the work, main advanced to
`366430a5d3b1adb29bbe092166a9a70f362ba408` through PR #658.

That main change adds `docs/beta-numeration-research-route-2026-11-27.md` and
appends its finding to `docs/side-notes-ledger.md`. It changes no Lean,
kernel, dependency, oracle or test input. Local integration commit
`46e854924c440e21ffcf9d64d90172089888701f` retains the new route and both
append-only side findings. The single merge conflict was the two independent
appends at the end of that ledger; neither entry was removed.

After integration, all 1,230 hashes in `isolated/source-bindings.json`
matched the worktree exactly. The generated proof bank remained current,
and the full claim-governance audit passed. The same source-bound Lean and
native receipts therefore apply to these unchanged inputs. This observation
does not relabel the earlier execution as a new hosted or integrated run.

The 284-test receipt remains attached to its actual pre-integration run.
The final documentation and recorded-data checks are logged separately in
`integration-checks.log`. The archive records and original checksums retain
their prior bytes; this integration note and its check log are appended.

Publication may use a GitHub-created commit with different metadata from
the local history. Before creating the draft PR, compare its full tree SHA
with the locally validated tree. The PR records both identifiers. No merge
or hosted acceptance is implied by this integration record.
