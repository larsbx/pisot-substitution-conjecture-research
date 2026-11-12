# Lean replay of the two archived C4 tables

This stage imports the canonical Mojo packet from the original `(16,8)`
construction. The two addressed fixture digests are pinned to the accepted
PR #550 receipt. The existing Python oracle independently reconstructs the
graphs from the original words and checks every native packet line as well
as the historical graph digests. The importer emits rows from the native
bytes after this comparison.

The Lean replay recomputes every two-step literal mark, including its
parent, flat and nested positions, and prefix counts. For every source row
it enumerates every pair selecting the current letters, checks integer
divisibility and the sharp exclusion inequality, and compares the complete
admitted list to the stored slots in order. Each slot keeps its positional
address and its original swap bit. A sorted rank witness checks that
canonical representatives increase strictly, with each row pointing back
from its rank to its original ID. Discovery uses the original earlier
source and slot. The weight inequality sums over every positional slot.

| Fixture | Rows | Slots | Rate |
| --- | ---: | ---: | --- |
| `1/021/001` | 7,150 | 34,826 | `99/20` |
| `1/012/001` | 7,083 | 34,853 | `101/20` |

The generated declarations use kernel reduction on intervals of at most
32 rows and prove acceptance for every row by combining the intervals.
The bridge constructs the existing `OverlapContraction.Certificate` from
the checked degree, target and potential and proves `certificate.check =
true` through `Certificate.check_iff`. It also proves the exact three root
bindings and proves `TableDiscovery` given the typed table. A conditional
consumer uses the accepted potential on these same rows.

The remaining proof obligations are `TableBinding` (the typed `Slot`
construction, swap-orbit distinctness and exact rows) and
`DecodedCandidatesClosed`. The executable row checks have yet to be
connected by soundness theorems to those propositions. The geometric
consumer therefore still has hypotheses. This stage establishes no
geometric nullity, positive-measure claim, or general Pisot result.

## Replay

Run from a checkout with the pinned Lean and Mojo environments.

```bash
root=$PWD
out=$(mktemp -d)
(cd kernel && pixi run --locked mojo run -I . c4_archived_graph_refinement.mojo) > "$out/native-packet.txt"
./tools/setup_lean.sh
cd proof/PscVerif
lake --no-cache build PscVerif.NamedArchivedGraph
lake --no-cache env "$root/tools/check_archived_c4_import.sh" "$out/native-packet.txt" "$out/generated"
```

The importer rejects a changed addressed payload hash. Generated Lean
controls alter each real fixture by removing an edge, duplicating a
position, swapping a packet identity, changing a root, removing a birth,
and corrupting an integer weight. The focused workflow records the
checked revision, tree, native packet, independent oracle receipt, and
Lean output with axiom inventories for the generated bridge.
