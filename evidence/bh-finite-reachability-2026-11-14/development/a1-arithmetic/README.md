# A1′ arithmetic: terminal development records

These are completed local compiler runs with pinned Lean 4.34.0-rc2,
`-DautoImplicit=false`, and two compiler threads. They use dependencies
compiled centrally from the recovered checkout. The final fresh focused
source gate is a separate acceptance step.

The JSON receipts and logs are byte-for-byte copies of the terminal files.
Their absolute paths record the original development environment. No live
log, object file, dependency cache, or inferred successful outcome is stored
here. `sha256.json` records the archived payload hashes.

| Run | Terminal exit | Scope and result |
|---|---:|---|
| `core-001` | 1 | Scratch matrix diagnostic; rejected because the input lay outside the compiler root. |
| `core-002` | 1 | Scratch matrix diagnostic; private namespace overlay lacked an imported object. |
| `core-003` | 1 | Scratch matrix diagnostic; IVT cast normalization and the norm-one guard failed. |
| `core-004` | 1 | Scratch matrix diagnostic; only the norm-one guard remained. |
| `core-005` | 0 | Scratch matrix arithmetic for both `j=1,2` and the `j=3` guard passed. This excludes actual word bindings and the residual run classification. |
| `pisot-001` | 0 | The complete actual-word arithmetic module passed against the initial accepted Coincidence object, before simultaneous endpoints were added. |
| `pisot-002` | 0 | The complete actual-word arithmetic module passed against the final frozen Coincidence object, including its simultaneous endpoints. |
| `audit-001` | 0 | All 15 independently literal exact endpoints passed; all 30 wrong-type/missing controls were rejected. Both complete owned modules passed the axiom scan. |

The final scan covers **249 declarations and 189 theorems**:
Coincidence contributes 179/125 and Pisot contributes 70/64. The only
transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.
`acceptance-summary.json` lists the 15 unique endpoint names and the final
source hashes.

`sources/` preserves the source corresponding to every receipt's SHA-256.
The actual module and audit snapshots are original source snapshots.
The scratch core snapshots were recovered by the runner's deterministic
extraction from its original repository snapshots; every resulting byte
hash was checked against the already-recorded compiler-input hash. This
recovery does not reconstruct or modify any compiler receipt or log.

The earlier failed matrix-only `j=1` run from the lost executor is a
different, explicitly reconstructed historical record at
`../../local-history/a1-arithmetic-reconstructed.json`. Its original log
was unavailable; it is not an original log in this directory.

These results establish the displayed primitive irreducible Pisot literal
families and their audited coincidence endpoints. They do not assert
finite balanced-pair termination or universal boundary hitting or PSC.
