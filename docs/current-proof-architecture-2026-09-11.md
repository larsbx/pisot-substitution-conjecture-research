# Current PSC proof architecture — 2026-09-11

> **Superseded as the live architecture on 2026-09-14.**
>
> Use `docs/current-proof-architecture-2026-09-14.md` for the canonical current
> architecture and `docs/completion-ledger-2026-09-14.md` for the latest weekly
> completion ledger.

This file is retained as a dated historical pointer because it previously carried
the two-gate finite-BPA framing. The mathematical status changed after the
seed-patch overlap finiteness/coincidence-density results and the import of the
Barge–Štimac–Williams dense-eventual-coincidence criterion (merged through PRs
#72, #76, #77 and sharpened by #82).

The important superseding fact is:

```text
bounded discrepancy                       [PROVED]
=> finite seed-patch overlap graph         [PROVED]
=> one-seed overlap productivity           [OPEN]
=> dense eventual coincidence              [PROVED repository equivalence]
=> pure discrete spectrum                  [IMPORTED theorem]
```

Thus G1b-2 and the finite-BPA carrier programme remain open and important, but
are no longer prerequisites of the shortest PDS sufficiency route. Historical
claims from this snapshot should not be used when they conflict with the
2026-09-14 architecture, the live claim/source map, or the manuscript.
