# Literature check for periodic compatibility at rank two

Test whether bounded gaps between shared vertices can remove only some
of the periodic pair supply at coincidence rank two. For a specified
nonzero periodic base class, enumerate the full legal fibre by returning
literal centre tiles and record the induced permutation. Test gaps in
each pair using the entire descendant closure of its centre overlap.

| Source | Exact input and boundary |
| --- | --- |
| [Baker–Barge–Kwapisz, Proposition 2.3, Definition 3.1, Theorem 4.2](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | The full integral lattice in the irreducible case, bounded stable strand positions, finitely many legal lifts, and exactly two lifts on a full-measure subset at rank two. A periodic base class can have extra lifts. |
| [Barge, Theorem 4](https://arxiv.org/pdf/1301.7094) | A maximal family of pairwise noncoincident tilings exists in every fibre. The condition is absence of a common labelled tile at every inflation stage. |
| [Akiyama–Lee, §3 and Theorem 4.1](https://arxiv.org/pdf/1003.2898) | Overlaps and inflation descendants give the finite state method. Their equal-tile coincidence condition is stronger than a shared endpoint. |
| [Barge–Kwapisz, geometric realization](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf) | The unimodular tiling action and the geometric factor. The argument below uses the normalized lattice from BBK. |
| [Barge–Diamond–Swanson, branch locus](https://arxiv.org/pdf/0804.0930) | The branch locus records periodic asymptotic tilings. The prescribed-fibre catalogue retains all periodic lifts, including disjoint and non-asymptotic ones. |

[Theorem W](c4-rank-two-wall-2026-11-16.md) already proves uniqueness
of a compact minimal joining of distinct fibre-mates at rank two.
[Proposition V](p1b-vertex-coincidence-box-2026-10-02.md) decides whether
an interior periodic pair has any shared vertex, with an equivalent
test over the entire box for all pairs.
[The zero-fibre criterion](psc-zero-fibre-coincidence-2026-11-17.md)
already enumerates the periodic interior and seam tilings at the
identity. [PR #576](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/576)
handles gaps along first-letter rays.

Proceed with the uniform gap consequence of rank-two uniqueness and
with the nonzero rational-coset extension of the centre-tile
catalogue. Reuse the existing overlap graph and contracting bounds.
Test the larger fibres of `1/2/021` and `01/12/021`, including the
lifts exchanged at the specified return. Treat reducible strict
systems as controls on the hypotheses. A unit PIP example with an
offset-zero-free legal pair would already contradict pure discreteness.
