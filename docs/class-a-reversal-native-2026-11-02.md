# Native reversal-quotient audit for finite class-A X graphs — 2026-11-02

**Status:** finite-instance proof-support implementation, under review. **Not** a universal Class-A theorem, BH, G1, PDS or PSC closure.

## Exact target and prior work

This is a canonical Mojo implementation slice of [issue #442](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/442), supporting [BH #139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139). The 18 oriented swapped-patch seeds, selected paths to X, finite source-closure graph, and reversal-quotient idea come from mainline #428–#436. Native `class_a_x_productivity.mojo` already constructs complete **finite** indexed graphs for fixed k,t and has 22 fixed specimens independently compared with literal-word/Fraction oracles. The earlier reversal quotient and path-lifting checker in `oracles/python/class_a_reversal_quotient.py` is retained as an independent reference.

## New native contract

For minus class A, k,t >= 0, n=k+t+3 and d=k+2t+5. `verify_indexed_reversal_quotient` takes a completed native `IndexedGraph` and the actual substitution tables. It refuses malformed lengths and words, duplicate/noninjective states, non-strict vertices, incomplete occurrence arrays, impossible or unsorted (i,j) addresses, wrong literal child letters, wrong bottom-minus-top Parikh coordinates, non-strict child images, missing reversed vertices, missing transposed occurrence-indexed edges, or false terminalization. It constructs an orbit quotient with one canonical **native vertex ID** representative per real reversal orbit and retains the original top/bottom occurrence indices on each selected representative edge.

The representative convention is ID order, not the Python oracle's tuple-lexicographic order. The quotient cardinalities and lifted occurrence semantics are independent of this naming choice. Every actual oriented source can lift a selected quotient edge by using (i,j) from its representative or the genuine transposed (j,i) when starting in the reversed orientation. The native lift recomputes the literal child and exact strict geometry rather than trusting an abstract quotient arrow.

The finite graph and quotient are not promoted to all-parameter coverage: a fabricated incomplete graph could still pass a *local* checker if its omitted children were paired consistently. Completeness comes from the separate capped/fail-closed `build_indexed` enumeration and independent full-adjacency comparisons, not from symmetry alone. Realized-overlap coverage and the nonunit/adelic transfer remain separate obligations.

## Scope, tests and negative controls

The new native test uses the full 18-oriented-seed graphs at (k,t)=(0,0),(3,0),(0,3), with 784, 352 and 1440 actual states and 393, 177 and 721 quotient orbits respectively. It checks every recorded original indexed edge, every reversible counterpart and selected shortest-coincidence path lifts from **each** actual source orientation. A quotient rank is obtained by reverse BFS to typed full-zero terminals on the completed finite graph; this verifies a finite selected-edge forest, not all-edge strict descent. A genuine productive graph may contain directed cycles.

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

The local assistant environment did not have the locked Mojo/Pixi executable, so it has **not** independently executed the new test. Exact-head CI and subsequent independent replay must establish acceptance before merging. Earlier mainline receipts are not reused as fresh acceptance.

## Next proof obligation

This finite reversal factorization does not show that the entire X-generated reachability set is uniformly productive as k,t vary. Next derive a parameter-uniform characterization of every seed-reachable cyclic strict-zipper state (or a complete finite-by-chambers forward-closed carrier), prove a selected coincidence/boundary-hit escape for each original occurrence-compatible state, and then prove the realized-overlap/representation-space coverage needed by BH. Keep the separate aligned A1′ question open. Proof status and `claim_governance.toml` remain unchanged.
