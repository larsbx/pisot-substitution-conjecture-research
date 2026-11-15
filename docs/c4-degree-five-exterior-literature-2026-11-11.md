# Degree-five exterior connection: targeted stop/go — 2026-11-11

## Proposed claim

Make the previously identified algebraic connection explicit in Lean. For a
three-by-three matrix over a commutative ring, let d = det M and W = wedge2 M,
where wedge2 is the repository's explicit matrix of two-by-two minors. Prove

\[
\chi_{dW}(X)
=X^3-d\,\operatorname{tr}(W)X^2
+d^3\operatorname{tr}(M)X-d^5.
\]

Over the rationals the right side is exactly Degree5Completion.reciprocal M.
Rewrite the accepted q5 image-polynomial and rank theorems through this matrix,
preserving every existing word-system, degree-four balance, primitivity,
irreducibility and Pisot hypothesis. Retain the zero image and k = 0.

A second small target is the maximum-image-length spectral bound. For the
incidence convention in this repository, column sums are literal image lengths.
A row of ones is therefore subinvariant at any supplied common image-length
bound B. The existing subinvariant spectral theorem gives norm(beta) <= B for
every incidence eigenvalue. Compose B = 3 with the already accepted
degree-five determinant exclusion, under its unchanged PIP/Equiv4 hypotheses,
to make the documented nonunit short-image consequence a named Lean theorem.

## Primary sources inspected before implementation

The actual local mathlib sources were read at pinned revision
4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09. Online source URLs below identify that
same revision; no current unpinned API signature is assumed.

| Source | Exact result and transfer boundary |
| --- | --- |
| [Mathlib matrix characteristic polynomial](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean) | charpoly is det(XI-M); charpoly_zero and charpoly_diagonal retain singular and signed examples. No inverse is required by the polynomial identity. |
| [Mathlib trace](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/LinearAlgebra/Matrix/Trace.lean) and [determinant](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean) | trace_smul and det_smul give degree-one and degree-three scaling respectively. The determinant twist must retain its sign. |
| [Mathlib adjugate](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/LinearAlgebra/Matrix/Adjugate.lean) | mul_adjugate, adjugate_mul and adjugate_smul explain the standard cofactor/exterior-dual interpretation. The proposed coefficient proof avoids denominators and remains valid when det M = 0. |
| [Accepted Cyclicity source](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/2848e5f67b605669a550f362a1de4bf1c1529f7c/proof/PscVerif/PscVerif/Cyclicity.lean) | charpoly_fin_three, trace_wedge2_wedge2 and det_wedge2 supply the exact minor-matrix identities. Its explicit warning about the separate Mathlib exterior-algebra identification remains in force. |
| [Accepted degree-five completion](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/2848e5f67b605669a550f362a1de4bf1c1529f7c/proof/PscVerif/PscVerif/Degree5Completion.lean) and [earlier source gate](c4-degree-five-completion-literature-2026-11-10.md) | q5_eq_pow_rank, its nonzero version and columns_eq_zero_of_nonunit_small_perron provide all PSC-specific conclusions to be restated. Characteristic-polynomial equality alone proves no similarity or word realizability. |
| [ParikhIntertwiner](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/2848e5f67b605669a550f362a1de4bf1c1529f7c/proof/PscVerif/PscVerif/ParikhIntertwiner.lean) and [spectral-transport note](c4-degree-five-spectral-transport.md) | spectral_bound_of_subinvariant supplies the positive-row bound. The note already derives beta <= 3 mathematically and explicitly leaves the named Lean composition open. The new proof must derive column sums from actual substitution images. |

These are standard matrix and spectral facts. The contribution is the explicit
formal connection between existing PSC definitions and the previously written
short-image corollary, not a new exterior-algebra result.

## Derivation and hypotheses

The minor definition gives wedge2(c M) = c^2 wedge2(M). With W = wedge2 M,
the existing formulas imply

\[
\operatorname{tr}(dW)=d\operatorname{tr}(W),\quad
\operatorname{tr}(\operatorname{wedge2}(dW))=d^3\operatorname{tr}(M),\quad
\det(dW)=d^5.
\]

Substitute into the three-by-three characteristic polynomial identity. The
generic identity needs only a commutative ring: neither determinant
nonvanishing nor characteristic zero is added. The root description d^2/r
does require nonzero roots, and is not a premise of this proof.

For the image-length bound, count every letter occurrence in each image to
obtain the incidence column sum. Apply the already proved positive-row
subinvariant spectral bound to an actual incidence eigenvector. A bound of
three gives norm(beta) <= 3 < 8. With norm(det M) >= 2, the existing
degree-five theorem forces the actual column map to zero, provided degree-four
balance holds throughout the supplied normalized child system.

## Controls and excluded stronger claims

- A nonunit diagonal or scalar example distinguishes the determinant twist
  from the unscaled exterior square.
- A negative-determinant example distinguishes d from abs(d).
- A singular example retains the valid identity when W is nonzero but dW = 0.
- The zero image retains characteristic polynomial 1 and exponent zero.
- The incidence-root bound retains its actual maximum-image-length premise.
- Degree-four agreement is a premise of the degree-five consequence; a
  nonzero column alone cannot supply it.
- The unit plastic reciprocal sector remains an allowed abstract survivor.
- Equality of characteristic polynomials does not prove an actual image
  decomposition, semisimplicity, a degree-five-to-degree-two defect map,
  a strict word realization, or productive crossing.
- No new corpus, canonical research algorithm, global strict-carrier
  extraction, C4, G1, Concentration or PSC conclusion is part of this increment.

## Decision

**Proceed with the narrowed deductive integration.** Add the explicit matrix
identity and scoped restatements, then the image-length corollary if the
existing spectral interface elaborates with its genuine imports. Meaningful
singular, sign and scaling controls belong with the proofs. Full exact-head
Lean compilation and the compiled-declaration axiom audit remain required.

The geometric continuation is already active in open PR #543 on top of #542.
Its compact-window theorem and remaining authentic stable-realization,
global finite-domain and measure premises will be tracked separately.

