# Literature check for the one-track seam spectrum

The proposed computation recovers the signed correction to odd
algebraic multiplicities in the strict bigon matrix from the literal
overlap alphabet. It uses the three eventual cycle lists for first
ends, last ends and legal adjacent cells at a one-track seam.

| Source | Input and scope |
| --- | --- |
| [Barge–Diamond, §§2–3 and Theorem 4](https://arxiv.org/pdf/math/0702669) | The boundary graph uses a bipartite edge for each legal adjacent pair and the map given by last and first letters. Its eventual range distinguishes asymptotic cycles from connected components. Here each endpoint also retains the interior tile of the other track. |
| [Anderson–Putnam](https://dspace.library.uvic.ca/items/5da98f53-6901-46ac-98c5-ecac27f6aed5) | Finite tiling complexes and the substitution zeta function give the established setting for trace corrections. The computation here uses the literal overlap and bigon trace identities of #598. |
| [Baker–Barge–Kwapisz, §§2–4](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | Integral strand starts and finite geometric fibres. At unit incidence a periodic one-track seam lies in the zero fibre, with a periodic integral interior state on its other track. |
| [Barge, §3 and Theorem 22](https://arxiv.org/pdf/1301.7094) | Rank-two tilings have constraints on cohomology and asymptotic cycles. These do not force every boundary graph to be a forest or exclude a neutral odd eigenvalue of a literal bigon system. |

Proceed by extracting cycles instead of scanning powers through a
least common multiple. Use `01/12/021` to compare the row closure
with independent periodic zero-fibre origins on a productive
specimen. Use an explicit subdivision to test the correction
against a known signed matrix. Keep any eigenvalue transfer
conditional on the aligned sink and rank-two assumptions in
[PR #598](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/598).
Test whether legal one-track seams can give a positive correction
before adopting a sign bound.
