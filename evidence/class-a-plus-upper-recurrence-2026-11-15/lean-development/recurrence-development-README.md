# Upper recurrence Lean development history

These raw development logs are preserved as historical evidence. They are not the
fresh isolated acceptance receipt. Every log was copied byte-for-byte; the JSON
receipt records SHA-256, byte length, outcome and source-binding availability.

The final proof module and final independent audit are preserved under
`recurrence-final-sources/`. Their bytes match both the repository files and the
unchanged copies in the development workspace. The final module build is
`development-4`; the final independent audit is `audit-2`.

Intermediate snapshots for `development-1`, `development-2`, `development-3` and
the audit file used by `audit-1` were overwritten during development and were not
retained. Their exact source hashes are **unavailable**. The logs remain preserved,
but are not bound to the final source hashes, and no reconstructed file is
presented as an original snapshot. The proof module imported by both audits is the
unchanged final module. The first audit failed on an unqualified
`IndexedDigitStep` in its independently stated expected type; the second audit
qualified that name and passed.

Numerical process exit codes were not stored inside the redirected raw logs, so
the receipt records them as null. Status is based on explicit compiler error or
completion output and the recorded execution sequence, with no invented code.

| Attempt | Outcome | Raw-log SHA-256 | Source mapping |
| --- | --- | --- | --- |
| `development-1` | failed | `a45dc2baa2c45798f8b8abb0e83bb0c56ba28e77edcfac1eab12ac9752e4ea00` | Intermediate source unavailable |
| `development-2` | failed | `f7264222879338c9679e33a232f0d2587ab17d873366596cf6d9aaa513a44ab1` | Intermediate source unavailable |
| `development-3` | passed | `21f1b1fe75553b6d3d5c50e164987cb13b3eee92cc85a0030a27cbdbae30d2ca` | Intermediate source unavailable |
| `development-4` | passed | `b7ca6b6bd7da44254aef0181e6600f39a125c01f9b674eb8a7b7964dfbcfecbb` | Final module |
| `audit-1` | failed | `f4dbcf7a500a6b5757df96fbcf62e9fc07bc7afee3b0e8ce1c6714aecd1075ec` | Final module; earlier audit unavailable |
| `audit-2` | passed | `211b83acd3e912a2cae6674dcf36225b3d541a9133d195e7d7da2f7a8d799eae` | Final module and final audit |

The final audit checks 96 owned declarations, including 80 theorems, 13 exact
independently stated endpoint types and 39 missing/wrong-type/extra-premise
negative controls. Its complete marker is
`PSC_CLASS_A_PLUS_UPPER_RECURRENCE_AUDIT_COMPLETE	13	39`.

The pinned dependency manifest, toolchain declaration, project configuration,
25-root cache request, raw cache log and final local source-hash inventory are
preserved as supporting context. The local source inventory describes the state
at preservation; it is not used to backfill earlier missing snapshots. The cache
log records 2,165 downloaded/decompressed upstream artifacts; no full-Mathlib
cache request was made.

For final-source replay, use the repository's dedicated fresh acceptance gate.
The development procedure ran `lake --no-cache build
PscVerif.ClassAPlusUpperRecurrence` and then `lake --no-cache env lean
ClassAPlusUpperRecurrenceAudit.lean` in the pinned development project, with the
pinned toolchain directory prepended to `PATH`.
