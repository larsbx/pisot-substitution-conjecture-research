# Frozen referee-dossier replay receipts

The [dossier](../../docs/referee-dossier-2026-11-04/README.md) gives the commands, hypotheses, and bounded certificate scopes.

| Receipt | Source and result |
|---|---|
| `python-main.log` | `fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5`, 57 passes and 2 failures |
| `mojo-main.log` | Same baseline, pinned compiler build, 9 passes and 2 failures |
| `provenance-main.log` and `governance-main.log` | Same baseline, stale generated proof bank and unrecognized multiline contract declaration |
| `python-repair-485.log` and `mojo-repair-485.log` | Separate PR #485 head `b7c1f804cb258c23c88be30d69522ddaa618d210`, 59 focused Python passes, passing proof-bank check and 2 targeted native passes |
| `mojo-family-diagnostic.log` | Baseline plus the displayed one-line ownership patch in a detached worktree, passing bounded native replay |

These historical logs preserve original outcomes. Checkout directory prefixes and trailing whitespace were removed for portability. The archive is separate from checks on the commit that integrates the dossier.
