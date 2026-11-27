# C4 original-word marker parity and literature decision

## Target

Use the [return-word calculation](c4-return-seam-boundary-2026-11-20.md)
to express stack winding as a necessary parity law on an original
balanced word pair. The target compares counts of one selected
adjacent marker after projecting original letters to their periodic
endpoint groups. Restrict to pairs whose stack images are twins,
and use only intervals bounded by common original vertices.

## Sources and scope

| Source | Use in this step |
| --- | --- |
| [Barge, *Factors of Pisot tiling spaces*, Lemmas 13–15 and Theorem 17](https://arxiv.org/pdf/1301.7094) | Twins are interchanged by the deck involution, which commutes with inflation and translation. The cover gives an antipodal sheet phase in the standing even reduction. The odd-norm lower bound supplies no even-case exclusion. |
| [Barge–Diamond, *Cohomology of substitution tiling spaces*, Theorem 4](https://arxiv.org/pdf/math/0702669) | The original periodic seam graph gives the fixed cohomology contribution. Its connectedness follows here from the absence of eigenvalue one on original letter counts. |
| [Sadun, *Pattern-equivariant cohomology with integer coefficients*, Theorem 4](https://arxiv.org/pdf/math/0602066) | Integral and finite-coefficient tiling cohomology can be represented by local cochains. Use the explicit circle map which winds immediately after the marked adjacent pair and the coefficient sequence for reduction modulo two. |
| [Barge–Kellendonk–Schmieding, *Maximal equicontinuous factors and cohomology for tiling spaces*, §3](https://arxiv.org/pdf/1204.1432) | Provides the circle-map interpretation of degree-one cohomology. A class divisible by two gives a continuous square root after correcting by a real logarithm. |

For the endpoint calculation, normalize the square-root ratio at a
common vertex. Agreement on the left fixes it by the left rays.
Agreement on the right fixes it after correcting by the original
marker at that vertex. The connected original seam graph and its
singleton corner should identify all normalized values. The exact
word identity must use common padding at the two boundary vertices
and equal original letter counts when cancelling inflated interiors.

## Decision

Proceed with the scoped necessary condition and its finite algebra.
Use the genuine Thue–Morse two-sheet system to check compatibility,
and a cubic control to test whether the parity can fail on literal
balanced words. The marker identity is a condition on a hypothetical
twin pair. A general existence or exclusion result needs an argument
that forces an offending pair in every candidate cubic hull.

The companion family `1/2/(1 0^m 2^r 1)` also has an explicit boundary
obligation at `m = r`. The earlier level-three cut exhausts a run and
fails there. Reuse the [literal word criterion](c4-literal-periodic-defect-2026-11-20.md)
and check one more substitution level. The balanced-pair use of
aligned coincidences is standard in
[Barge–Štimac–Williams, Theorem 1](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf).
Proceed with a literal equal-Parikh witness and the existing
strict-system exclusion, keeping this companion check independent of
the stack hypotheses.
