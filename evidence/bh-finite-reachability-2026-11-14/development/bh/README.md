# Local BH bridge compilation and exact-type audit

These are original terminal records from the recovered executor. Every run used
Lean `4.34.0-rc2`, `-DautoImplicit=false`, and at most two compiler threads.
The JSON receipts bind the source bytes, command, import-object hashes, terminal
exit, elapsed time, and observed source stability. The ordinary carrier and audit
receipts additionally verify that all directly imported objects stayed unchanged.

## Accepted local result

The ordinary source compilation in [bh-004.json](bh-004.json) and
[bh-004.log](bh-004.log) passed with exit `0`, without an incremental snapshot
load or save. It checked `BHFiniteReachability.lean` at SHA-256
`5b9f2fd96957c25211ebadb767ba7747dd2966b474bce2922c56e87d4f623e94`.

The composed finite closed-carrier consumer passed unchanged in
[carrier-001.json](carrier-001.json) and [carrier-001.log](carrier-001.log),
at source SHA-256
`58ca13926d84d3107cf69408c457a4e7da3ca96761818e5cc0086d2c017537fe`.

The ordinary exact-type audit passed in [audit-001.json](audit-001.json) and
[audit-001.log](audit-001.log), at source SHA-256
`5469fdefea80286841bb3b40b7944a4674de5dce03ca12b490ee72b77ca2b79d`.
It accepted all **11** independently specified whole-declaration types,
rejected **22** missing/right-kind-wrong-type controls, and inspected all
**45** owned declarations, including **40** theorems, in these three modules:

| Module | Owned declarations | Theorems |
| --- | ---: | ---: |
| `OccurrenceAncestry` | 16 | 14 |
| `BHFiniteReachability` | 26 | 23 |
| `BHFiniteCarrier` | 3 | 3 |

Every owned declaration and accepted endpoint was checked against the unchanged
standard allowlist `propext`, `Classical.choice`, and `Quot.sound`. Actual mark
coverage and the literal prefix-cut predicate are independently spelled out in
the audit. Supplying an extra finite-word-carrier or factor-bound premise would
therefore fail the whole-type checks.

## Development attempts retained

| Attempt | Mode | Exit | Outcome |
| --- | --- | ---: | --- |
| `bh-001` | Import-header save | 1 | First elaboration diagnostics; no object |
| `bh-002` | Header-cache load | 1 | Remaining concrete-control normalization diagnostics; no object |
| `bh-003` | Header-cache load | 0 | Cached development pass |
| `bh-004` | Ordinary compiler | 0 | Final local source compilation |
| `carrier-001` | Ordinary compiler | 0 | Composed consumer compilation |
| `audit-001` | Ordinary compiler | 0 | Full owned-module and exact-endpoint audit |

The two failed source versions are retained as
[bh-001.lean](failed-source/bh-001.lean) and
[bh-002.lean](failed-source/bh-002.lean). Their original scratch locations remain
in the unmodified receipts; the linked copies preserve their exact bytes.
The development cache was bound to the import header and the direct imported
objects. No cache image, compiled object, or live process marker is included
in this evidence packet.

## Scope and earlier executor loss

These are local compilation and endpoint-audit results against the centrally
compiled dependency objects. They are not the separate source-isolated hosted
gate or independent human review. The mathematical conclusion remains
conditional on the stated finite actual overlap cover, literal edge closure,
and integral-zero hits; neither a universal hitting theorem nor productivity
or pure discrete spectrum is asserted by this bridge.

The earlier executor was replaced during an unchanged dependency build. Those
outcomes are separately and explicitly labelled as transcript reconstructions
in [historical-outcomes-reconstructed.json](../../local-history/historical-outcomes-reconstructed.json).
They are not substituted for the original terminal records in this directory.
