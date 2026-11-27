# Diagonal closure: literal Pisot arithmetic and transfer boundary

**Status:** pre-code source decision for the additional arithmetic endpoint.
Date: 27 November 2026. This continues the
[residual-exit source decision](bh-diagonal-residual-stop-go-2026-11-27.md)
and reuses the standard polynomial method in the
[earlier family arithmetic decision](c4-family-pisot-bridge-stop-go-2026-11-14.md).

## Exact proposed target

For every integer `r>=12`, bind the literal words
`sigma_r=(1,0 1^r 2,0^r 1)` to their actual incidence matrix,
prove primitivity, and prove that its characteristic polynomial
`X^3-r X^2-2 X-r` is irreducible over the rationals and has one
expanding real root with every other complex root of modulus less than one.
The bracketed real root is constructed, not assumed to exist. This removes
arithmetic premises before any future family spectral application.

## Primary sources checked and hypothesis boundaries

1. Barge, Stimac and Williams, *Pure discrete spectrum in substitution tiling
   spaces*, [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf),
   section 2 and Corollary 2. The one-swap balanced-pair criterion requires
   irreducible Pisot arithmetic and termination with coincidence of every
   relevant factor. Its standing tiling assumptions include primitivity,
   aperiodicity and finite local complexity. Arithmetic alone supplies none
   of the required occurrence paths or the factor-termination assertion.
2. Akiyama and Lee, *Algorithm for determining pure pointedness of self-affine
   tilings*, [author manuscript](https://arxiv.org/pdf/1003.2898),
   Definition 2.4 and Theorem 2.5. Overlap coincidence is an all-overlap
   statement with a common finite level; the spectral equivalence retains
   the Meyer hypothesis. A pointwise path theorem still needs its actual
   overlap representation and finite-type/uniformization bridge.
3. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   [publisher PDF](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf),
   section 2 and Theorem 9.10. Irreducibility concerns the actual incidence
   characteristic polynomial. The nonunit representation contains the
   appropriate non-Archimedean factors. Strong coincidence and geometric
   property (F) remain separate premises of that paper's tiling theorem.

These sources were inspected on the date above. No newly discovered
universal PSC theorem is imported. Standard root arguments are not claimed
as new mathematics.

## Reconstruction and decision

**Proceed with the precise arithmetic specialization.** The positive
incidence square proves primitivity. The bracket `(r,r+1)` follows from
opposite signs of the cubic. For `A=beta-r` and `B=r/beta`, division by
`X-beta` leaves `X^2+A X+B`, where `0<A<1/4` and `48/49<B<1`.
The quadratic is strictly positive on the real line, so the cubic's only
real root lies strictly between consecutive integers. A rational root of
the monic integer cubic would be integral; a degree-three rational
polynomial without rational roots is irreducible. The exact real and
imaginary parts of the quadratic equation show that the two remaining
complex roots have squared norm `B<1`.

Retain actual image-letter counts throughout. The determinant is `r`, so
no unimodular-only inverse or unit representation may be silently used.
Do not promote the arithmetic endpoint to a spectral theorem, claim a
finite parameter sample proves the family, or treat the separate diagonal
entry/exit proof as universal BH or residual A1-prime. Any downstream
spectral application must list and discharge its own geometric and
factor/overlap hypotheses.

## Same-session extension to the two adjacent bands

Proceed with the identical standard arithmetic proof for `k=r+1,r+2`.
Use the actual matrix `[[0,1,r],[1,k,1],[0,1,0]]` and characteristic
polynomial `X^3-k X^2-2 X-r`. The existing near-diagonal `Family` supplies
the constructed root in `(k,k+1)`, `0<beta-k<1/4`, and
`4/5<r/beta<1`. These bounds again make the remaining real quadratic
strictly positive and its complex roots have squared norm `r/beta`.
The same rational-root argument and positive incidence square apply.
The source decision and all spectral/nonunit boundaries above are unchanged;
this extension adds arithmetic for the two already reviewed literal exit
bands rather than a new recurrence mechanism.

## Same-session finite-carrier formalization decision

The completed all-source proof permits the already reviewed Pisot enclosure
from the [near-diagonal derivation](bh-near-diagonal-exit-2026-11-24.md) to be
assembled with `BHBoundedFactors.terminates_of_closed_diagonal_cover`.
Proceed with this existing mechanism: derive `ContractionData` from actual
irreducibility, the positive literal eigenlength row and contracting roots;
transport packets to the existing strict-overlap relation by negating the
full displacement; take the finite union of complete forward reachable
sets from the actual finite seed marks. This gives an all-child closed
carrier before the all-source exit is used for productivity.

The three primary-source boundaries above still govern the spectral step.
This adapter does not assume property (F), invert the incidence matrix,
discard finite-place information, or infer finite BPA merely from selected
paths. The published Barge--Stimac--Williams implication remains external
to Lean. The control with finite zero-hit reachability but no labelled
coincidence remains necessary, as does the generic control showing that
productivity alone does not force a finite balanced-pair carrier outside
the Pisot assumptions. This is formal assembly of an existing reviewed
enclosure, not a new proposed universal invariant.
