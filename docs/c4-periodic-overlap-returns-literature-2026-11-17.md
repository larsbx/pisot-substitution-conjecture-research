# Literature check for periodic returns in the literal overlap component

The proposed test counts returning ordered pairs with the origin inside
both source tiles. It reads ordinary and swap returns from the complete
finite overlap graph, then locates those returns that can come from the
strict component at coincidence rank two. The count must retain
multiplicity and use the original left and right child occurrences.

| Primary source | Input and scope |
| --- | --- |
| [Baker–Barge–Kwapisz, §§2–4](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | The normalized integral strand lattice, its stable bound, the geometric factor and finite fibres. Generic fibre cardinality alone gives no count of the returns inside a particular joining. |
| [Sirvent–Solomyak, Theorem 5.6](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/4BC0FD9DBA6ECA027A32568F9E5C1D12/S0008439500017537a.pdf/pure_discrete_spectrum_for_onedimensional_substitution_systems_of_pisot_type.pdf) | Half-coincidences bound gaps between balanced cuts in a translated fixed-point pair. Here the overlap states instead retain both indexed occurrences and are used to count two-sided periodic pairs. |
| [Akiyama–Lee, §4](https://arxiv.org/pdf/1003.2898) | Literal overlap descendants partition the inflated common interval. The spectral comparison uses these widths. The pure-point criterion there does not identify the periodic part of a specified strict joining. |
| [Anderson–Putnam](https://doi.org/10.1017/S0143385798100457) | The substitution zeta function uses the finite tiling complex. Use the repository's [Theorem FP](c4-rank-two-wall-2026-11-16.md) for the one-dimensional occurrence trace with boundary corrections. The present test uses the physical first and last overlap occurrence, including ones that leave the SCC. |

[PR #471](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/471)
and its [ordered version](c4-oriented-alignment-2026-11-04.md) put the
overlaps of a supplied strict component in a sink SCC. The open
[PR #576](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/576)
already decides strict existence for an individual substitution from
periodic first-letter rays. The aligned-sink reformulation reuses its
source-word construction. Proceed with the two-sided periodic
membership test and indexed counts, including the exact correction
for swap returns. Use the full fibre catalogues as a separate check.
The known reducible strict controls check the role of rational
independence. Leave rank-two and universal C4 exclusion pending.
