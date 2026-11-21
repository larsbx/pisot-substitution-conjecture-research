# C4 homoclinic winding counts and literature decision

## Target

Continue the [even stack residue](c4-even-stack-residue-2026-11-19.md)
and [literal-defect obstruction](c4-literal-periodic-defect-2026-11-20.md).
For a substitution whose modulo-two image-count columns are zero or the
same column, test whether a common-padding pair is determined by its
integer count of letters selecting that column. For the stack quotient,
identify the marked letters and check what an equivariant transfer of
original counts would imply for a deck-switch winding. Test whether an
additive correction in the two original rays can produce that winding
modulo four on the seam cycle.

## Sources and hypotheses

| Source | Consequence for this step |
| --- | --- |
| [Barge, *Factors of Pisot tiling spaces*, Theorems 12 and 17, Proposition 19, and proof of Theorem 22](https://arxiv.org/pdf/1301.7094) | The proper rewrite, stack quotient and pair substitutions supply the presentations. The rewrite uses return words at a legal periodic cut. Its letter morphism is on the reblocked alphabet. The odd-norm lower bound is outside the even case. |
| [Barge–Diamond, *Cohomology of substitution tiling spaces*, Theorem 4](https://arxiv.org/pdf/math/0702669) | Separates the tile-count direct limit from the eventual-range transition graph. In the ordered pair the component difference leads to the sheet marking in [Lemma S⁺](c4-rank-two-wall-2026-11-16.md#7-barges-ordered-pair-substitution-at-rank-two-lemma-s-and-theorem-p). |
| [Lejeune–Leroy–Rigo, *Computing the k-binomial complexity of the Thue–Morse word*, §4](https://arxiv.org/pdf/1812.07330) | Counts scattered subwords under iterated morphisms and uses equal lower-order counts to constrain differences. The common-padding equation and projection onto a single marked count are the specialization here. |
| [Lejeune–Rigo–Rosenfeld, *On the binomial equivalence classes of finite words*, §1](https://arxiv.org/pdf/2001.11732) | Interprets the coefficients as counts of scattered occurrences. Here the coefficient comparison is modulo two. |

The period-doubling common-prefix pair persists under a power with
rank-one incidence modulo two. Its marked counts differ. This calibrates
the finite-word condition and the limit of a transfer from the even-count
Thue–Morse alphabet to the unordered factor.

## Decision

Proceed with finite-word rigidity and the transfer criteria in the
pair-substitution presentation. A chosen periodic seam can be the
proper return marker. The second quotient representative can have an
interior origin, so cut the difference at common vertices past both
ends. The actual boundary transfer from the original seams remains a
separate calculation.
