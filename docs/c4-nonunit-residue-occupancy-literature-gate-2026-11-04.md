# Non-unit residue occupancy: literature stop/go gate

**Decision (2026-11-04): proceed with a finite-residue upper bound.**
This gate precedes the new executable implementation. The intended result is
an exact, reproducible bound on Euclidean occupancy for a named specimen,
plus a written general counting argument. It is not an exact fractal-volume
calculation, a full adelic realization, or a proof of general C4 or PSC.

## Proposed claim and source observation

The final correction in [PR #493](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/493),
at `d9f8f0a69d6ae0b311578b255a53f2403d428eee`, classifies the reported
occupancy of `0 -> 1, 1 -> 021, 2 -> 001` as an **unverified scratch
observation**. The scratch program is not a dependency of this work.

For the incidence matrix `M`, set `D = abs(det M)`. At a fixed depth `q`,
partition the actual proper-prefix Parikh vectors in each `sigma^q(d)`
by their classes in `Z^3 / M^q Z^3`, retaining both the following letter
and the source letter `d`. Write the resulting counts as `a[c,r,d]`.
If `f` is the positive right Perron vector and `beta` its eigenvalue,
the proposed bound is

```text
theta_c <= beta^q f_c / (D^q max_r sum_d a[c,r,d] f_d).
```

Its analytic input is a regular-window count for each fixed coset of the
finite-index lattice. Its executable input is finite literal word counting
and exact arithmetic. These are different kinds of evidence.

## Primary sources inspected

| Source and location | Relevant result | Transfer boundary |
| --- | --- | --- |
| [Moody, Uniform Distribution in Model Sets (2002)](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/2304DD08EC0AD970DEF94D7C180C4752/S0008439500015630a.pdf/div-class-title-uniform-distribution-in-model-sets-div.pdf), Proposition 1 and Theorem 1, pp. 125-127 | The torus action is uniquely ergodic; regular windows have the density formula at every torus parameter. | Apply to finite box covers and the lattice `Phi(M^q Z^3)`, whose covolume is `kappa D^q`. Do not apply the arbitrary measurable-window almost-sure clause at a prescribed fractal window. |
| [Minervino--Thuswaldner, The geometry of non-unit Pisot substitutions](https://arxiv.org/pdf/1402.2002), Section 3, Lemma 3.1, Theorem 8.3, Section 8.2, Theorems 9.2 and 9.9 | The internal space includes the finite places dividing the Pisot number. Full internal Haar measure scales by `beta^-1`; the graph-directed pieces are measure-disjoint there. Multiple tiling and sufficient conditions for tiling are distinguished. | These are statements in the full representation space. Euclidean projection discards finite-place information. Neither strong coincidence nor a finite residue table alone supplies the additional tiling premise. |
| [Arnoux--Ito, Pisot Substitutions and Rauzy fractals (2001)](https://projecteuclid.org/journals/bulletin-of-the-belgian-mathematical-society-simon-stevin/volume-8/issue-2/Pisot-substitutions-and-Rauzy-fractals/10.36045/bbms/1102714169.pdf), Lemma 12 and Corollary 2, p. 198 | The unimodular volume inequality is forced to equality by Perron--Frobenius, giving measure-disjoint set-equation pieces. | Here `D=2`, so Euclidean contraction has determinant `2/beta`, not `1/beta`. The unimodular equality argument does not transfer. |

The first two sources were inspected in their full PDF texts at the locations
above; the Arnoux--Ito page was read through the primary PDF's indexed text.
The direct finite-index counting proof will be included with the new note,
so its conclusion does not require an unexamined all-translates import.

## Existing repository work and controls

- Read the [side-notes ledger](side-notes-ledger.md), including the retired
  occupancy route and the distinction between finite quotients and a complete
  non-Archimedean state.
- The same specimen already occurs in the
  [sidewise finite-cokernel diagnostic](p1b-sidewise-finite-cokernel.md).
  Its exact quotient arithmetic can be reused. Its residual collision with
  equal integral side translations prevents treating a residue class as a
  complete occurrence or ancestry state.
- A unit determinant is a negative control: every such quotient is trivial,
  and this refinement must return only the elementary upper bound `1`.
- A first-level bound equal to `1/2` is not a strict inequality. The program
  must preserve this distinction and must not turn an exhausted depth or
  arithmetic budget into a result.
- Strong-coincidence witnesses on the named non-unit specimen are checked
  separately in the literal words. Low occupancy cannot be used to infer a
  strict nonproductive system.

## Scope decision

**Proceed:** exact finite-residue counts, exact Perron-field inequalities,
the fixed-coset counting lemma, and a monotone sequence of occupancy upper
bounds. The same source review supports the written compact matrix-adic
lift and its finite-cylinder outer-bound target; this construction is
defined explicitly and is not silently identified with a localized adelic
model. The novelty claim is limited to their explicit specialization and
reproducible certificate in this repository; prefix numeration, lattice
density, and the non-unit representation space are established machinery.

**Do not infer:** an exact occupancy value from an upper bound; Euclidean
measure-disjointness from a non-unit strong-coincidence witness; a complete
adelic state from finitely many residues; PDS, BH, A1', G1, or general C4/PSC.
Any extension toward those goals must preserve literal occurrence data and
state its additional realization and measure hypotheses explicitly.
