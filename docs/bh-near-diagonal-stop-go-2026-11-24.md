# Source review for the two near-diagonal determinant bands

The prior higher-determinant carrier verified the three residual bands
on 4 ≤ r ≤ 11. The present target is a uniform all-source theorem for
r ≥ 12, k ∈ {r+1,r+2}, for the literal substitution (1, 0 1^k 2, 0^r 1).
Each strict ordered packet retains its two source types and three integral
coordinates. The target is equal type 1/1 at full displacement zero.

The overlap and bounded-gap framework is due to [Sirvent and Solomyak,
Sections 4–5](https://doi.org/10.4153/CMB-2002-062-3).
[Akiyama and Lee, Sections 3–4](https://arxiv.org/abs/1003.2898)
supply the Meyer finiteness and finite-overlap graph setting.
[Barge, Štimac and Williams, Corollary 2](https://doi.org/10.3934/dcds.2013.33.579)
consume actual balanced-pair termination with labelled coincidence for
a swap. These implications leave the uniform literal exits to prove.

The scalar update is related to the floor map of [Akiyama, Borbély,
Brunotte, Pethő and Thuswaldner](https://arato.inf.unideb.hu/petho.attila/cikkek/CNS_SRS/Aki_Bor_Bru_Pet_Thus_I.pdf).
Here the rounding choice is constrained by a symmetric geometric window
and must be an actual difference of image positions. Matrix contraction
or the finiteness of a fixed-floor map alone does not prove the claim.
The existing OccurrenceWidth.reaches_half_mass gives the first geometric
input independently of the recurrence.

Proceed with a quadratic descent on the last two integral coordinates.
Use truncation where it stays inside the run window. At the other integer
the rounding error is smaller than the contraction margin. Check the
small integer pairs directly, then bind the chosen roundings to actual
run positions in Lean. For entry, inflate a half-minimum-width overlap
three times. Long gaps without a 1 come from actual copies of the
image of 2 and are far apart. Between them the short gaps allow a wide
overlap of two 1 tiles.

Calibrate strict endpoint exclusion, rounding at both ends of the
window, and the run bound on k=r, where k-1 ≥ r fails. Preserve the
finite r ≤ 11 results and the other PSC branches at their current scopes.
