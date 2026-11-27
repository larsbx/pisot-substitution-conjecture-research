# Source review for forward carriers at higher determinant

The [bilateral newborn exclusion](c4-bilateral-newborn-family-2026-11-14.md)
covers every primitive irreducible Pisot member of `(1,01^k2,0^r1)`.
Forward termination through `01/10` is established separately at
determinants two and three. The next target is a certificate with both
parameters varying. Near the Pisot threshold `k=r`, cap exhaustion
remains inconclusive.

| Primary source | Applicable scope |
| --- | --- |
| [Barge–Štimac–Williams, Theorem 3.2 and Corollary 2](https://doi.org/10.3934/dcds.2013.33.579) | Exact finite closure and a reachable coincidence from every factor suffice for the single swap. One cannot discard noncoincident children after finding a coincidence. |
| [Sirvent–Solomyak, §5](https://doi.org/10.4153/CMB-2002-062-3) | Balanced-pair and overlap replays both depend on genuine cuts and coincidences. Strict-component exclusion supplies neither a bound on factors nor a termination certificate by itself. |
| [Barge, initial injectivity and final constancy](https://doi.org/10.3934/dcds.2016.36.1159) | The initial map of the present substitution identifies 1 and 2, and its final map fixes both 1 and 2. Every positive power keeps these features. Reversal exchanges the two endpoint maps and still supplies no constant map. |
| [Barge, the beta-substitution theorem](https://arxiv.org/abs/1505.04408) | An equality of Perron polynomials is insufficient for transfer. A conjugacy of the appropriate symbolic or tiling systems would need a separate proof. |

**Decision.** First search for complete ordered rows in a parameter
region where all run comparisons can be decided uniformly, then check
the literal word identities and every irreducibility condition. The
determinant-three example at `k=3` rules out using the large-parameter
table everywhere, and also rules out demanding immediate coincidence
as a prerequisite for termination. No computational cap on either
parameter can serve as a proof.
