# Literature gate: named real stable charts and actual compact prefix tiles

Date: 2026-11-11. This gate precedes implementation and continues
[PR #543](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/543)
at mechanically certified source
`8f1df32902c248baec35546e22e9145a2ea1a138`. The side-notes ledger, the
[actual-prefix window derivation](c4-stable-prefix-window-2026-11-11.md),
and the unchanged canonical finite-cylinder certificate were inspected
before choosing this target. Independent human review remains separate
nonblocking validation debt.

## Stop/go decision

**Proceed with closed named qualitative compactness instances for the two
literal substitutions `1/021/001` and `1/012/001`.** Construct the real
root and the rank-two coordinate map, prove exact incidence commutation
and a strict block-twelve contraction, and apply the canonical complete
digit-sum theorem to the actual period-two words constructed from seed
`[0]`. This discharges the supplied real-chart/contraction hypotheses for
these named instances. It does not construct spectral data for arbitrary
primitive irreducible Pisot input.

The existing exact native code is reused. There is no new census and no
replacement rational arithmetic implementation. The numerical digit
bound of five and radius forty remain a separate sharper refinement;
qualitative compactness uses the internally proved complete digit sum.
The proposed formal fixture is proved directly in Lean and is not a
general parser or decoder for arbitrary native certificate packets.

## Primary sources inspected

| Source | Relevant construction | Transfer boundary |
| --- | --- | --- |
| Arnoux, Mizutani and Sellami, *Random product of substitutions with the same incidence matrix*, [primary preprint](https://arxiv.org/pdf/1301.7316), Section 3.1, Lemma 3.1 and Proposition 3.2. | The actual prefix stepped line is projected along the expanding eigenline; incidence commutes with projection, and a contracting norm plus finite local prefixes bounds its image. | The displayed common-matrix setting is unimodular. Reprove the explicit named chart and contraction algebra, rather than importing a unimodular tiling conclusion into the determinant-two example. |
| Barge and Kwapisz, *Geometric theory of unimodular Pisot substitutions*, [author-hosted paper](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf), Section 5, Lemma 5.1; Section 17 discussion of computing the adapted radius. | A stable norm gives an invariant enclosure through a contraction plus a bounded error. The norm is part of the construction and can affect practical bounds. | A spectral statement does not imply contraction in an arbitrary coordinate norm at a selected short exponent. Authenticate the actual block in the stated sup norm. Do not import torus, coincidence or measure theorems. |
| Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*, [primary preprint](https://arxiv.org/pdf/1402.2002), Sections 3, 4.4 and 6. | The nonunit representation retains non-Archimedean factors; compact prefix constructions and their graph-directed equations are developed in that representation. | Keep the repository's already constructed original `H_M`. This target does not identify it with the full adelic representation, normalize Haar measure, or assert a tiling or positive overlap measure. |

The proof organization uses standard real algebra, finite-dimensional
linear topology and stable-coordinate contraction. No novelty is claimed
for those general principles. The new result sought is an exact named
formal realization feeding the repository's actual-word constructions.

## Exact named data and intended proof

The common incidence is

\[
M=\begin{pmatrix}0&1&2\\1&1&1\\0&1&0\end{pmatrix},
\qquad \det M=2,
\qquad f(t)=t^3-t^2-2t-2.
\]

The existing canonical native packet isolates its real root between

\[
L=638816140918905/281474976710656,
\quad U=638816140918906/281474976710656.
\]

The endpoints and signs must be proved in Lean. A coarser explicitly
proved enclosing rational interval is permissible for elementary bounds;
it must still identify the same root. Existence follows from continuity
and opposite endpoint signs, and uniqueness above two can be proved by
factoring the difference of two cubic values. Native floating-point
approximations are not premises of these real proofs.

For the selected root `beta`, use

\[
a=(3\beta-\beta^2)/2,
\qquad b=(\beta^2-\beta-2)/2=1/\beta,
\]
\[
Wz=(z_0-a z_1,z_2-b z_1),
\quad J(x_0,x_1)=(x_0,0,x_1),
\quad B=\begin{pmatrix}-a&2-a\\-b&-b\end{pmatrix}.
\]

The intended algebra authenticates all of the following, rather than
only a contraction of an unspecified or zero map:

- `W M = B W` for the actual incidence;
- `W J = I`, so the internal coordinates have full rank two;
- `ker W` is the line through `(a,1,b)`, and this is the positive
  expanding eigenline with eigenvalue `beta`;
- the original integral incidence is injective, and `B` is injective
  with determinant `2*b != 0`;
- the actual twelfth power has entries
  `3941-4755*a`, `7415-8945*a`, `2095-4755*b`, `3941-8945*b`.

The section `J` alone is not the inclusion of an invariant stable plane.
For the positive left eigenrow `ell=(1,beta,beta^2-beta-1)`, prove
`ell M = beta ell` and `kappa=ell(a,1,b)=4*beta-beta^2>0`. The corrected
section `L y = J y - (a,1,b)*ell(J y)/kappa` takes values in `ker ell`.
Its inverse identities with `W` authenticate the stable-plane coordinates;
the same block contraction then authenticates stability. This algebraic
normalization is not a claim about Haar measure or covolume.

Define the internal normed space as `Fin 2 -> Real` with its sup norm.
Prove a bound on each absolute row sum of the actual `B^12`, sufficient
for `norm(B^12 x) <= (7/8)*norm x`. The entrywise maximum norm on matrices
is not the induced infinity-operator norm. Nor may the Euclidean norm
be substituted without a separate proof.

Properness and the closed-embedding fact come from the finite-dimensional
real linear realization. In the pinned mathlib source, the relevant
interfaces include the intermediate-value theorem,
`Matrix.mulVec_injective_of_det_ne_zero`,
`LinearMap.isClosedEmbedding_of_injective`, and finite-dimensional real
properness. The exact APIs are checked against the repository's pinned
mathlib revision `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`; no changed
dependency or new axiom is needed. Powered additive maps are explicitly
`AddMonoid.End` so their powers mean composition.

For each literal substitution, prove nonerasure, the actual incidence,
period-two prolongation of `[0]`, and strict seed growth. Use `seedWord`
to construct the infinite word and `period_two_to_twelve` to retain that
same word at the contraction exponent. Then the existing theorem gives

\[
D_{\rm can}=\operatorname{digitNormSum}(\sigma^{12},\pi),
\quad R_{\rm can}=8D_{\rm can},
\quad \forall n,\;\|\pi(\operatorname{parikhZ}w[0,n))\|\le R_{\rm can}.
\]

It follows that the actual letter-indexed prefix closures in the original
`E x H_M` are compact. Where composed with the existing tile-equation or
history theorems, keep the proved closed embedding and exact period scale
explicit. No abstract attractor replaces these defined prefix sets.

## Negative controls and acceptance

- A zero projection can satisfy formal commutation and contraction;
  `W J = I` and the exact kernel/eigenline identity prevent that from
  masquerading as the named stable realization.
- Equal incidence does not identify the two literal words. Construct
  each period-two word from its own literal images and preserve each
  named instance.
- Period two is not the useful contraction block for this coordinate
  norm. Authenticate block twelve, and preserve the existing native
  wrong-block refusal. The actual vector `(1,-1)` has
  `B^2(1,-1)=(2*a,2*b)`, providing a direct short-block countercontrol.
- A maximum-entry matrix bound does not bound the sup-norm action with
  the same constant. Include a two-dimensional row-sum countercontrol.
- Incorrect root intervals or polynomial/chart coefficients must fail
  exact identities or bounds. Passing a rounded numerical sample is
  not a real-number proof.
- Preserve the existing `q=1`, noninjective zero action, incomplete digit
  inventory and `00/11/22` physical forward-leak controls. Its `4/2/2`
  calibration remains physical, not a compact-overlap mass equation.

Acceptance requires the complete isolated Lean build and compiled axiom
audit at the published source, generated proof-bank consistency,
canonical native replay with independent oracle checking, bounded
independent controls for any new matrix-norm abstraction, source/revision
bindings and the repository's provenance checks. Local development probes
are not acceptance. Failed earlier revisions remain historical failures.

## Adjacent work and remaining gaps

[PR #544](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/544)
separately develops a finite ancestor carrier from supplied authentic
chart/reconstruction and enclosure hypotheses. Its current source and
acceptance must be checked independently before composition. This target
supplies concrete real geometry; it does not duplicate that carrier work
or silently assume its remaining premises.

This target does not establish a uniform constructor for arbitrary Pisot
input, the sharp radius forty, full adelic equivalence, a complete
executable ancestor constructor, forward completeness, product-Haar
scaling, an overlap-measure recurrence or positive strict-root measure.
C4, global G1, Concentration and general PSC remain open. No governed
claim is promoted merely by recording this gate.
