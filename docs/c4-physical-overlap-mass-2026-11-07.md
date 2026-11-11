# Exact physical mass loss on the twelve-source overlap graphs

This continuation of issue #461 is based on PR #497 at
`49bc7e1af11b6ab04f84b79f8737500b6de3748b`. See the
[literature decision](c4-physical-mass-literature-gate-2026-11-07.md).
The twelve substitutions have images `11`, a permutation of `012`, and
`01` or `10`. Use the complete two-step inverse-prefix graph from
[the finite-carrier proof](c4-finite-overlap-carrier-2026-11-05.md).
Its row index is the inverse parent and its column index is the inverse
child. The scope is the 36 declared distinct-letter, zero-offset roots
and their entire authenticated closure.

## Physical length and orbit counts

Write `ell=(1,beta/2,(beta²-beta-2)/2)` for the positive physical length
row. The authenticated algebra gives `ell M²=beta² ell`. Irreducibility of
the cubic makes these three length coordinates linearly independent over
the rationals. Endpoints and differences therefore have unique integer
vectors in this basis. Sign comparisons use certified rational bounds.
If a nonzero vector is not separated from zero, the implementation refuses.

For the inverse state `s=(a,b,z)`, define `h_s` as the length of
`[0,ell_a] ∩ [-ell z,ell_b-ell z]`. The typed strip in Lemma F1 implies
`h_s>0` on the authenticated closure. The minus sign follows from reversing
the inverse occurrence formula. For a pair of positions with prefix
vectors `p,q` in the two-step images of `a,b`, the forward child offset
is `M²z+p-q`. In physical space the bottom inflated interval begins at
`-ell M²z`. Intersect the two full partitions of these inflated intervals.
Their positive intersections have disjoint interiors and exactly
partition length `beta² h_s`. Keep each pair of literal positions
separately, even when two pairs yield the same state.

The track swap sends `(a,b,z)` to `(b,a,-z)` and preserves length.
It is equivariant on edges when the two literal positions are also
swapped. Let `m_i` be the number of ordered states in orbit `i`. Count the
ordered inverse occurrences from orbit `i` to orbit `j` first by inverse
parents and then by inverse children. This gives `m_i T_ij=m_j F_ji`, where
`F` is the retained forward multiplicity matrix per ordered representative.
A fixed state would require equal letters and zero offset. In an inverse
transition to a fixed state, equal source letters and cancellation of the
offset can occur only if the current physical children are distinct
positions in the same word or the same position. Distinct positions in a
single partition have disjoint interiors and would violate strict physical
overlap. The same position would make the inverse parent fixed too.
The roots are free, so every retained state has orbit size two. Both
implementations check this directly. In this class `F=Tᵀ`. In a
mixed-orbit class the budget would use `H_i=m_i h_i` instead.

The retained forward partitions may omit positive intervals whose
states are outside the graph. Thus `e=beta² h-Tᵀh≥0`, and each coordinate
of `e` is exactly the length of the omitted intervals. Authenticating
the complete inverse graph is essential. A deleted inverse edge could
fabricate a positive deficit.

## Why one loss in each inverse source SCC suffices

Let `theta=beta²` and suppose `v≥0` satisfies `Tv≥theta v`. This includes
the written compact Haar measure equation of #497. Pair the two
inequalities to get

```text
0 ≤ hᵀ(Tv-theta v) = -eᵀv ≤ 0.
```

Strict positivity of `h` gives equality in every coordinate of
`Tv-theta v`. Every vertex with positive deficit has zero coordinate.
If a vertex has zero coordinate, its equation and nonnegativity imply
that all its inverse children also have zero coordinate. Hence a losing
vertex zeros its entire SCC and every descendant. Every finite SCC
condensation vertex is reachable from a source SCC. One positive loss
in every source SCC therefore implies `v=0`. This uses source SCCs of
`T`, which are terminal SCCs for physical forward subdivision. Their
number is bounded by the root count because the graph is generated from
those roots. A conservative source SCC must instead be left unresolved
by this certificate.

## Exact replay

The native verifier rebuilds the canonical inverse graph before deriving
the physical lengths and every transpose deficit. The independent Python
replay sweeps the two literal partitions from left to right. It checks that
the total overlap is the entire budget, compares the full retained
multiplicity counter per row to the transposed inverse row, and sums the
omitted intervals directly. Native Tarjan and Python Kosaraju agree on
the source blocks and chosen losing vertices.

Across 43,915 states and 253,395 retained occurrences, exactly 3,508
rows have positive deficit. Each substitution has one inverse source SCC,
and each has a strictly losing row. The 12 source SCCs contain 2,648
vertices altogether. Their maximum size is 622. As an example, source
`11/012/01` has inverse source SCC consisting of vertex 2, with
`h_2=ell_2` and `e_2=ell_0+3ell_1+ell_2`.

The native and independent exports agree byte for byte on 43,940 records
and 1,085,652 bytes. The
[checksum](../evidence/c4-physical-overlap-mass-2026-11-07/packet.sha256)
and [per-source witnesses](../evidence/c4-physical-overlap-mass-2026-11-07/summary.txt)
are committed. Replay from the repository root:

```bash
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_physical_mass.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_overlap_physical_mass.mojo) > /tmp/physical-native.txt
python oracles/python/c4_overlap_physical_mass.py > /tmp/physical-oracle.txt
cmp /tmp/physical-native.txt /tmp/physical-oracle.txt
root=$PWD
(cd /tmp && sha256sum -c "$root/evidence/c4-physical-overlap-mass-2026-11-07/packet.sha256")
```

The native controls distinguish source and sink SCCs, reject a
conservative source even when its sink loses, reject a source block with
no declared root, and detect deletion of a repeated occurrence before
checking losses. The finite graph and carrier retain the parent PR's
operational caps. This certificate uses neither modular determinants
nor fitted positive weight vectors. It derives nullity for this finite
class under the written compact measure equation. General conservative
class exclusion and general C4 and PSC remain open.
