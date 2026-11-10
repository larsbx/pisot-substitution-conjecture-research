# Degree-five reciprocal completion: targeted stop/go — 2026-11-10

## Proposed claim

Retain the exact hypotheses of `Degree5Sieve.sieve5_of_primitive`: a supplied
normalised ternary child system, degree-four balance on every state, primitive
incidence with irreducible characteristic polynomial, and a Pisot root. With
`d = det M`, `e1 = trace M` and `e2 = trace (wedge2 M)`, prove that the actual
degree-five image polynomial has the form

\[
g=X^3-de_2X^2+d^3e_1X-d^5,\qquad q_5=g^k,\qquad
\dim_{\mathbb Q}\operatorname{im}Q_5=3k.
\]

The zero image must remain permitted (`k=0`). Separately, derive the zero-map
consequence of `beta < |det M|^3` from the already proved nonzero-image bound.
No actual strict carrier, uniform occurrence productivity, or C4 closure is
part of this claim.

## Primary sources inspected before implementation

The following are primary library sources for the standard algebra being
specialized. The executable proof must use the repository's pinned mathlib
revision, not assume that the current online declaration signatures match it.

| Source | Relevant result and transfer boundary |
| --- | --- |
| [mathlib: polynomial reversal](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Reverse.html) | Coefficient reversal realizes `X^n f(1/X)`, and respects multiplication over a domain. Scaling the reciprocal roots yields the displayed cubic. A nonzero constant term is essential: inversion cannot preserve a zero root. |
| [mathlib: minimal polynomials over a field](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Minpoly/Field.html) | A polynomial vanishing at an algebraic element is divisible by its minimal polynomial; irreducibility plus monicity identifies that polynomial. This provides divisibility of the reciprocal cubic into a rational image factor from a shared complex root. It does not identify the source signed characteristic polynomial with the image polynomial. |
| [mathlib: polynomials of specific degree](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/SpecificDegree.html) | Over a field, a cubic with no rational root is irreducible. A rational root of the reciprocal cubic would yield a rational root of the original irreducible cubic by `x -> d^2/x`; both denominators must be proved nonzero. |
| [mathlib: characteristic polynomial of a linear map](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Charpoly/Basic.html) | The characteristic polynomial is monic and its degree is the dimension of its underlying vector space. Apply this to the action restricted to the actual defect image, including its zero-dimensional case. |

The PSC-specific starting point is the accepted
[`Degree5Sieve` source](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/43e3da1493e2cbe46d5cc8776178f58abe285036/proof/PscVerif/PscVerif/Degree5Sieve.lean),
which already proves root containment and the nonzero-image determinant bound.
The new argument consumes these scoped statements directly; it does not
replace their child-system and lower-balance hypotheses.

These are standard reciprocal-polynomial, minimal-polynomial and
characteristic-polynomial facts. The proposed contribution is their checked
specialization to the existing degree-five image transport and signed sieve,
not a new algebraic theorem or a proof of realizability.

## Proof route and hypothesis checks

Use the existing cubic characteristic-polynomial identity and prove the
reciprocal cubic's evaluation identity exactly. Irreducibility of the original
cubic supplies `d != 0`; a rational root of `g` would transfer to an impossible
rational root of the original cubic. The existing sieve places every complex
root of `q5` among the three reciprocal values. Divide a nonconstant monic
rational polynomial by `g` at a shared root and induct on degree; each quotient
retains the same root-containment property. Finally take degrees, using the
actual image characteristic polynomial's dimension identity.

The argument uses containment of root sets plus rational irreducibility to
force equal multiplicities. Merely listing the three roots over the complex
numbers does not do so. No semisimplicity hypothesis is needed for this
factorization, and the factorization by itself does not prove semisimplicity.

## Retained controls and non-claims

- The zero image has characteristic polynomial `1`; positivity of `k` must
  require an actual nonzero defect column.
- The plastic-cubic reciprocal control in
  [the spectral-transport note](c4-degree-five-spectral-transport.md) permits a
  nonzero abstract survivor. This algebra does not construct a literal strict
  child system or exclude that survivor through word order.
- Degree-four balance on every state remains necessary for the defect
  intertwiner. A first-defect or strict-system wrapper cannot be inferred
  from a single nonzero column.
- A signed-source eigenvalue lying in the defect kernel is still not an image
  eigenvalue. All spectral conclusions concern `q5` as already defined.
- Non-unit incidence is included; no unimodularity assumption is introduced.

## Decision

**Proceed with the narrowed formal completion.** The algebraic mechanism is
standard and compatible with the standing hypotheses. Preserve the separate
word-realizability, uniform forced-crossing and G1 obligations. This review
authorizes proof development; acceptance still requires successful Lean
elaboration and kernel/axiom replay at the exact candidate revision.
