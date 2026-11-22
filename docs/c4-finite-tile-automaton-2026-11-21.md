# Finite tile-chain automaton for the literal sigma-k family

**Follow-up:** the [actual-hull interpretation](c4-finite-hull-witnesses-2026-11-21.md)
now binds these exact certificates to legal tilings and proves the universal
zero-fibre witness endpoint. The source decision and acceptance below retain
the original PR #647 scope; they are not retroactively expanded.

## Source decision before implementation

Proceed with a finite integer certificate for the five tile-chain generators
`00`, `01`, `11`, `12`, and `20`. The user requested automata and the existing
finite-kernel infrastructure in place of further limit-based analysis.
The source baseline is main `f5ca04063db75722e7736cfbad36629b7cd36d35`.

The proposed result concerns a finite-control automaton with output in
`Z^3`: every target label and every integer displacement are reachable
from label 1 using signed edges. The control graph is finite; its lifted
integer-labelled configurations are not asserted to form a finite set.
The implementation must reuse the vendored DFA, graph, and exact arithmetic
packages and retain literal edge witnesses. No numerical approximation,
topological closure, or sequence limit is needed for this algebraic step.

### Primary sources inspected

1. Barge, Stimac and Williams, *Pure discrete spectrum in substitution
   tiling spaces*, DCDS 33 (2013), 579--597,
   [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf),
   Theorem 3.1 and Corollary 2. The existing family Lean proofs already
   supply the balanced-pair inputs and the shared-tile legal-patch
   coincidence transfer. The finite certificate below is intended to feed
   that established interface; it does not reprove the spectral theorem.
2. Baker, Barge and Kwapisz, *Geometric realization and coincidence for
   reducible non-unimodular Pisot tiling spaces*, Ann. Inst. Fourier 56
   (2006), 2213--2248,
   [published PDF](https://www.numdam.org/item/AIF_2006__56_7_2213_0.pdf).
   The geometric coincidence condition concerns the actual realization
   and its return structure. A graph whose edges lack actual legal-hull
   witnesses cannot substitute for that structure.
3. Barge and Kellendonk, *Proximality and pure point spectrum for tiling
   dynamical systems*, Michigan Math. J. 62 (2013), 793--822,
   [author preprint](https://arxiv.org/pdf/1108.4065).
   Finite rank and closed proximality do not remove the stated
   full-measure fibre-distality hypothesis. The present finite algebra
   makes no assertion about that hypothesis or an `L2` conclusion.

### Hypotheses and boundaries

For an actual tile-chain interpretation, each forward edge `a -> b` must
come from a legal tiling containing adjacent tiles of those labels, and
the edge output is the formal coordinate vector `e_a`. Reversal negates
that output. Different edges may be realized in different legal tilings.
An accepted chain is not asserted to be a legal substitution word.

The five edges are uniform in the literal family `sigma_k=(1,0 1^k 2,001)`
for `k >= 2`: `00,01` occur in `sigma_k(2)`, `11,12` in
`sigma_k(1)`, and `20` at the image boundary of a legal `11` pair.
The formal finite-walk theorem must keep this actual-hull interpretation
separate from its integer reachability conclusion.

Negative controls must reject a discontinuous edge word, a signed-output
error, and a weakened graph whose reachable integer displacements have
proper rank. An exhausted search budget must never become a negative
mathematical answer. The construction here has fixed control size and
uses symbolic integer coefficients rather than an expanding box search.

### Relationship to current work

The existing `all_pair_witnesses_iff_periodic_lattice_anchor` theorem
reduces zero-fibre witnesses to anchor coincidence for periodic tilings
with integer-lattice origins. Concurrent local tile-chain work develops
the actual-hull bridge. This increment is independently based on main;
it must not import or declare acceptance for unpublished concurrent files.

The existing `compare_zero_fibre` executable is useful for individual
substitutions, but its legacy Perron builder's maximum image length 6
directly admits this family only through `k=4`. Increasing that bound is
not the uniform proof. The finite generator identity covers arbitrary
integer displacements independently of that enumerator.

## Finite certificate

Number the forward edges `0..4` as `00,01,11,12,20`, and give inverse
edges the IDs `5..9`. The following are closed walks at label 1:

| Walk | Edge IDs | Exact output |
| --- | --- | --- |
| `c0` | `6,0,1` | `e0` |
| `c1` | `2` | `e1` |
| `c2` | `3,4,1` | `e0+e1+e2` |

Their output matrix, with those columns, is

```text
B = [[1,0,1], [0,1,1], [0,0,1]], det(B)=1.
```

For any integer vector `v=(a,b,c)`, concatenate
`c0^(a-c)`, `c1^(b-c)`, and `c2^c`. A negative exponent uses the reversed
word with every edge orientation reversed; zero uses the empty word.
Finite addition proves the output is exactly `v`. Append `6,0,1,6` to
end at label 0, no edges to end at label 1, or `7,3` to end at label 2.
Each of these terminal words has output zero. This gives an explicit
finite witness for every integer vector and every target label.

The construction is uniform in `k`, because its edge witnesses are:

| Edge | Finite family word | Zero-based occurrence start |
| --- | --- | --- |
| `00` | `sigma_k(2)` | `0` |
| `01` | `sigma_k(2)` | `1` |
| `11` | `sigma_k(1)` | `1` |
| `12` | `sigma_k(1)` | `k` |
| `20` | `sigma_k^2(1)` | `k+2` |

The formal word proof retains the exact prefixes and suffixes. Reversed
traversal uses the same forward occurrence; it does not assert that
reversing a legal word preserves the substitution language.

## Implementation and evidence

`kernel/psc/family_tile_automaton.mojo` uses the already vendored
`finite_automata.Dfa`, `finite_graph.scc`, `finite_exact.BigZ`, and
`finite_linear_algebra.Mat3`. It builds three controls plus a total
rejecting sink, accumulates signed output with unbounded integers, and
returns compressed integer powers instead of materializing a huge walk.
No vendored source is patched and no new arithmetic type is introduced.

`PscVerif.C4FiniteTileAutomaton` specifies the exact edge replay and proves
correctness of the constructed finite word for arbitrary integer vectors.
Its `certificate_replay` is a universal theorem, not a scan over a chosen
range. The fixed 40-entry control table is checked in both the native
test and Lean. This is correspondence for this concrete certificate,
not a claim that the generic native DFA engine has a formal refinement
proof.

`PscVerif.C4FamilyTileAutomatonWords` imports the existing family
substitution and proves every forward and reversed-traversal edge has
the stated finite-word witness for all `k>=2`.

### Negative controls

The native test refuses discontinuous walks, wrong endpoints, malformed
edge IDs and malformed integer recipes. It verifies inverse orientation
and a compressed recipe with 151-bit integer coordinates.

Deleting `00` and its inverse leaves the label graph connected, but every
remaining edge satisfies

```text
output[0] - output[2] = h(target) - h(source),
h(0)=-1, h(1)=h(2)=0.
```

Finite telescoping therefore forces `v[0]=v[2]` on every loop at label 1,
so `e0` becomes unreachable. The Lean model proves this for arbitrary
finite walks. The native test checks the coboundary equation on every
remaining edge. This rejects the overstrong inference from ordinary
graph connectivity to full integer-displacement reachability.

### Replay and scope

From `kernel/`:

```bash
pixi run --locked mojo run -I . tests/test_family_tile_automaton.mojo
```

The existing isolated family gate compiles the finite modules and runs
their dedicated audit. Local source-bound receipts are archived under
`evidence/c4-finite-tile-automaton-2026-11-21/`; hosted acceptance is a
separate result and must be read at the submitted revision.

The next semantic obligation is to interpret the uniformly legal
co-occurrences as actual hull bridges and apply the established
shared-tile coincidence theorem along the constructed finite chain.
This increment does not claim that this actual-hull bridge, universal
zero-fibre agreement, or the invariant-measure spectral conclusion has
been completed by its automaton theorem. It also supplies no theorem
about every possible continuation of the graph: the proved property is
an explicit selected witness for each integer target.
