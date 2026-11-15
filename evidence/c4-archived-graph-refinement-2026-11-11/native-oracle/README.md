# Archived graph refinement: native and independent oracle evidence

This directory records a **local development replay bound to exact source
SHA-256 values**. The new files were not yet committed when the replay was
recorded. Hosted acceptance at a published Git revision is a separate gate.
`receipt.json` contains the original graph digests, new full-address packet
digests, source hashes and every named oracle rejection. `local-replay.json`
records commands' results, runtime, full native packet hash and native
negative-control receipts.

## Reconstructed finite objects

| Original source | States | Positional edges | Swapped slots | Repeated endpoint slots | Maximum discovery depth |
| --- | ---: | ---: | ---: | ---: | ---: |
| `1/021/001` | 7,150 | 34,826 | 17,313 | 1,648 | 13 |
| `1/012/001` | 7,083 | 34,853 | 17,279 | 1,650 | 13 |

Each source has exactly 15 literal positions in its actual squared image
words. A position retains its parent letter, flat block position, nested
outer and local positions, selected letter and complete Parikh prefix.
Every retained edge names both positions and the normalization orientation.
Every nonroot state has a well-founded first-discovery edge from an earlier
state. All incoming rows are exhausted. A separate direct forward scan
checks all 139,358 positional occurrences on the doubled ordered domains.

The original sharp enclosure is `(16,8)`, the block exponent is two, and
the incoming direction is fixed. The later `(24,12)` certificate is refused
as a replacement. Residue exclusion uses the exact original matrix-square
equation. Stable exclusion requires strict interval separation; touching
endpoints are retained. An absent admitted ancestor or an exhausted
coordinate budget refuses acceptance.

The canonical original graph text, including potentials, reproduces both
archived SHA-256 values exactly. The new address packets have separate
digests; they do not replace or rewrite the historical receipt.

## Results and controls

- Existing historical Python regression: nine tests passed.
- Existing historical native regression: passed after setting the matching
  runtime configuration.
- New native graph and address regression: both complete graphs passed and
  24 named mutation attempts were rejected.
- Independent Python regression with the actual native packet: nine tests
  passed, including graph/domain truncation, packet omission and optimized
  Python admission controls.
- Full native packet parity: passed. Both graph-address streams and all
  potential entries match the independent oracle; 30 named oracle mutation
  attempts were rejected.

Deleting a repeated positional edge leaves the positive-potential inequality
valid and is nevertheless rejected by source refinement. An altered swap,
ancestry witness, original source, local address, period, box or exclusion
count can likewise leave the numerical matrix inequality untouched. Exact
row reconstruction rejects those mutations. Actual row transposition and
removal of an ancestor together with all stored references are also rejected.

The initial historical native attempt failed before source compilation
because the standalone runtime could not locate `std` without its
`MODULAR_HOME`. Its log remains recorded as an environment failure. The
corrected-environment retry and new native runs passed. A nonfatal Crashpad
initialization diagnostic and an unrelated pytest plugin deprecation warning
remain visible in the successful logs.

## Replay

Canonical locked-environment commands:

```bash
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_archived_graph_refinement.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_archived_graph_refinement.mojo) > /tmp/c4-archived-native.txt
PSC_ARCHIVED_GRAPH_REFINEMENT_NATIVE_OUTPUT=/tmp/c4-archived-native.txt python -m pytest -o addopts='' -q tests/test_c4_archived_graph_refinement_oracle.py
python oracles/python/c4_archived_graph_refinement.py --native /tmp/c4-archived-native.txt --controls
```

The recorded local runs used the existing minimal installation of pinned
Mojo `1.1.0.dev2026090805 (34562fa1)`, with its own `share/max` directory as
`MODULAR_HOME`. They are distinguished from a clean locked Pixi installation.
The 2,475,711-byte full packet remains a development/CI artifact. Its exact
hash and 98,184-line size are in `local-replay.json`; the compact receipts and
logs are committed here.

## Scope boundary

These controls authenticate finite source data, complete admitted inverse
rows, literal addresses, swap orientation, multiplicity, rooted ancestry and
the finite positive-potential inequalities. They are not a Lean
deserializer. Geometric sharp-box admission and its formal bridge, and any
claim covering all noncomputable strict packets, require their own proof.
No positive strict-root Haar measure, C4 closure or general Pisot
Substitution Conjecture closure follows from this finite replay alone.
