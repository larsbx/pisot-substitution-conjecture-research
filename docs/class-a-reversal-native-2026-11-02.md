# Native reversal-quotient audit for finite class-A X graphs — 2026-11-02

**Status:** finite-instance proof-support implementation, under review. **Not** a universal Class-A theorem, BH, G1, PDS or PSC closure.

## Exact target and prior work

This is a canonical Mojo implementation slice of [issue #442](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/442), supporting [BH #139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139). The 18 oriented swapped-patch seeds, selected paths to X, finite source-closure graph, and reversal-quotient idea come from mainline #428–#436. Native `class_a_x_productivity.mojo` already constructs complete **finite** indexed graphs for fixed k,t and has 22 fixed specimens independently compared with literal-word/Fraction oracles. The earlier reversal quotient and path-lifting checker in `oracles/python/class_a_reversal_quotient.py` is retained as an independent reference.

## New native contract

For minus class A, k,t >= 0, n=k+t+3 and d=k+2t+5. `verify_indexed_reversal_quotient` takes a completed native `IndexedGraph` and the actual substitution tables. It refuses malformed lengths and words, duplicate/noninjective states, non-strict vertices, incomplete occurrence arrays, impossible or unsorted (i,j) addresses, wrong literal child letters, wrong bottom-minus-top Parikh coordinates, non-strict child images, missing reversed vertices, missing transposed occurrence-indexed edges, or false terminalization. It constructs an orbit quotient with one canonical **native vertex ID** representative per real reversal orbit and retains the original top/bottom occurrence indices on each selected representative edge.

The representative convention is ID order, not the Python oracle's tuple-lexicographic order. The quotient cardinalities and lifted occurrence semantics are independent of this naming choice. Every actual oriented source can lift a selected quotient edge by using (i,j) from its representative or the genuine transposed (j,i) when starting in the reversed orientation. The native lift recomputes the literal child and exact strict geometry rather than trusting an abstract quotient arrow.

The initial #447 local symmetry checker could accept a fabricated incomplete graph if omitted children were paired consistently. The extended checker now independently scans every literal address pair, checks all S18 seeds and exact seed reachability, and refuses such omissions. Symmetry alone still implies no completeness. Realized-overlap coverage and the nonunit/adelic transfer remain separate obligations.

## Scope, tests and negative controls

The initial native test used (k,t)=(0,0),(3,0),(0,3), with 784, 352 and 1440 actual states and 393, 177 and 721 quotient orbits respectively. The extension covers all 22 completed specimens of the native indexed-graph suite: {0,1,2,3}² plus (0,4),(4,0),(4,4),(0,8),(8,0),(8,8). It checks every recorded original indexed edge, every reversible counterpart and selected shortest-coincidence path lifts from **each** actual source orientation. A quotient rank is obtained by reverse BFS to typed full-zero terminals on the completed finite graph; this verifies a finite selected-edge forest, not all-edge strict descent. A genuine productive graph may contain directed cycles.

Mutations exercise invalid occurrence index, wrong typed target, nonterminalized coincidence, mismatched parameter/word tables and cap refusal. The existing independent Python reversal oracle adds actual-lift and reversal-edge negative controls. These tests are wired into the Class-A X workflow on the exact PR head; a queued workflow is not a pass.

Run from `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_class_a_reversal_certificate.mojo
pixi run --locked mojo run -I . tests/test_class_a_x_productivity.mojo --emit-indexed > /tmp/x-native.log
```

Run from repository root:

```sh
python -m pytest -q tests/test_class_a_reversal_quotient.py -k 'actual_lift or reversal_edge'
python oracles/python/class_a_x_productivity.py --native-log /tmp/x-native.log
```

At PR opening the editing environment lacked Pixi/Mojo. During this extension the locked toolchain was installed and the new native 22-specimen test and its 16 negative controls executed successfully. Independent full-literal replay, deterministic archived certificates, exact source revision/hashes and hosted acceptance are recorded separately; neither a previous receipt nor a queued job counts as a new pass.

## Next proof obligation

This finite reversal factorization does not show that the entire X-generated reachability set is uniformly productive as k,t vary. Next derive a parameter-uniform characterization of every seed-reachable cyclic strict-zipper state (or a complete finite-by-chambers forward-closed carrier), prove a selected coincidence/boundary-hit escape for each original occurrence-compatible state, and then prove the realized-overlap/representation-space coverage needed by BH. Keep the separate aligned A1′ question open. Proof status and `claim_governance.toml` remain unchanged.

## Complete outgoing occurrence and exact distance certificate extension

Pre-implementation decision: [bounded stop/go note](class-a-completeness-distance-gate-2026-11-02.md).
The canonical entry point is `verify_finite_distance_certificate` in
`kernel/psc/class_a_reversal_certificate.mojo`.

For each nonterminal original state, scan the **entire Cartesian product** of
zero-based literal top/bottom occurrence indices, independently of the native
builder's streaming interval sweep. Recompute literal-prefix child geometry,
use exact strict signs, and compare accepted ordered triples (destination,i,j)
one-for-one with the supplied row. Check the typed full-Parikh child as well.
Terminals have zero scanned pairs and no outgoing edges by the declared
absorbing-coincidence convention. Require all eighteen oriented seeds and
require every listed state reachable from them: together with outgoing
closure this proves the supplied graph is exactly their finite closure.

The state cap is 6,000 and total nonterminal literal pair cap 20,000,000 per
specimen. All pair counts use checked arithmetic and the whole budget is
checked before the Cartesian scan. Equality with the cap is allowed; cap-1
refusal is tested. Arithmetic/sign refusal propagates. No partial certificate
is accepted when the budget is exhausted.

Export one `RC_VERTEX` row per original state containing its full five-tuple,
orbit ID, original distance and scanned pair count; every `RC_EDGE` retains
its actual two ordinals. Each `RC_ORBIT` gives its representative, distance
and selected outgoing row index (-1 exactly for terminals). `RC_COMPLETE`
records both caps and cardinalities. Completion and contract receipts are
mandatory. Orbit names follow original IDs, never an orientation-blind label.

For supplied labels d_G,d_Q, the checker requires equal labels on each
original/orbit pair and zero **iff** typed full-zero coincidence. For **every**
edge v->w in both graphs it checks d(v)<=1+d(w). Iteration along any terminal
path proves d(v) is a lower bound on its length. A genuine selected quotient
occurrence descends by exactly one; lifting the entire path from each actual
orientation reaches a typed terminal in d(v) steps. Thus it is also an upper
bound, proving the two shortest distances equal. Every quotient edge is also
lifted from both orientations independently of the chosen paths. Cycles are
allowed; this is not all-edge strict rank descent.

Negative controls cover paired omission (the former symmetry checker accepts
it), bad typed targets/addresses, fabricated terminalization, inconsistent
parameters, original and quotient bad distances, false zero terminals,
nonexistent selected occurrences, fabricated terminal paths, a real longer
path hiding a direct shorter edge, omitted seeds, unrelated absorbing states,
and independent builder/state/pair cap exhaustion. The public certificate
checker rebuilds the quotient rather than trusting a mutable quotient object.

Replay from `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_class_a_reversal_certificate.mojo --emit-certificates > /tmp/native-certificates.log
```

Then from the repository root:

```sh
python -m pytest -q tests/test_class_a_finite_certificates.py tests/test_class_a_reversal_quotient.py
python oracles/python/class_a_finite_certificates.py --native-log /tmp/native-certificates.log --certificates /tmp/certificates.json.gz
python oracles/python/class_a_finite_certificates.py --certificate /tmp/certificates.json.gz
```

The independent checker reconstructs literal Fraction closures, independently
computes original/quotient BFS distances, and replays all quotient edges and
selected full paths using literal words and full Parikh coordinates. Gzip
certificates use mtime=0; decompressed canonical JSON has sorted keys and fixed
member/row ordering. Source revision, source SHA-256 manifest, native output
and deterministic certificates accompany the replay receipts. The dedicated
workflow explicitly checks out the PR head SHA and uploads receipts even on
failure. See `evidence/class-a-finite-certificates-2026-11-02/README.md`.

### Exact remaining universal boundary

This discharges executable finite graph completeness and shortest-distance
comparison for the completed named specimens only. It supports their use as
calibrations for the conditional reversal/hitting lemma. It proves neither
finiteness for every k,t, a parameter-uniform forward-closed X-carrier, nor
uniform all-descendant escape/productivity. The nonunit representation-space
realization/coverage bridge and aligned A1′ remain separate. No refinement of
native semantics into the Lean interface has been proved, and no governed
claim status or general PSC assertion is promoted by these receipts.

## Hosted acceptance supplement (2026-11-02)

PR #447 is merged at `9ecc5f8de3411054256d4358795b126c5468be8b`.
The exact implementation/evidence head `4ec572a60993a0e0d1d9f97ab64257fa61ee209f`
passed dedicated hosted run 41448531108, including native execution, independent
complete occurrence/distance/lift comparison and archive replay. Its downloaded
artifact verifies and matches the local native log and decompressed certificate
exactly. Original pending receipts remain historical, unchanged. See the
[hosted supplement](../evidence/class-a-finite-hosted-acceptance-2026-11-02/README.md).
The next [conditional Lean distance interface](finite-quotient-distance-lean-2026-11-02.md)
makes projection, every-source lifting and typed terminal equivalence explicit;
it does not discharge native-to-Lean semantic refinement.
