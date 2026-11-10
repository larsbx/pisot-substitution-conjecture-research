# Degree-five spectral transport and word realizability

## Current acceptance and scope — 2026-11-10

At main revision `c38e381cc8105d87597b0a9bfbe418b7bca86fc0`, the transport,
mixed-weight, root-lift and signed-sieve results below are merged through
[PR #528](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/528).
Its exact head `0f0043c98c69313ac927f7640e85ca12e882e00e` passed the
[isolated Lean build and whole-bank axiom audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42743831329)
with 4,048 declarations and 3,070 theorems reached. The log explicitly audits
`sieve5_roots`, `sieve5_full_orbit_of_primitive` and `det_cube_le_of_nonzero`
using only `propext`, `Classical.choice` and `Quot.sound`. This hosted result
supersedes the PR body's earlier local exit-137/pending-audit report; that
failed local attempt remains part of the evidence history. This update
records the existing run and does not claim a new local Lean replay.

The accepted results classify the image's root set and give a necessary
determinant bound. Reciprocal-cubic multiplicities, image-rank divisibility,
and strict ordered-word exclusion remain separate obligations. Independent
human review remains pending and is not a gate on continued development.

## Literature and decision

The exact target is a transport theorem for the image of the degree-five
defect map of a supplied finite ternary child system. The [November
Diophantine construction](https://github.com/elliotglazer/diophantine-z-q)
motivates separating witness generation, finite identity replay, and the
proof that transfers a result between domains. Its arithmetic construction
supplies no PSC hypothesis. [Barge and Diamond's coincidence theorem](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
requires actual aligned occurrences with equal prefix abelianizations.
[Sirvent and Solomyak's balanced-pair criterion](https://citeseerx.ist.psu.edu/document?doi=ac6481cf41605ed271988fa1354fbf057680ba4e&repid=rep1&type=pdf)
has separate termination and coincidence premises. Neither premise follows
from a rational tensor image. The quotient specialization and narrowly scoped
spectral control are now implemented as recorded above. Continue with the
factorization target below and word realizability; keep global extraction as
a separate obligation.

## Interfaces and evidence

| Map or obligation | What is preserved | What would require another proof |
| --- | --- | --- |
| Literal ordered child data to the signed defect columns | Substitution, ordered block additivity and the actual swap signs under degree-four balance of all states | Reconstruction of a word pair, first cut or child ordinal from a column |
| Signed representative space to the rational image | Intertwining and the induced action. Quotienting by the kernel gives an equivariant linear isomorphism onto the image | Lifting a rational vector to a single realized word pair |
| Rational image to spectral data | The rational characteristic polynomial and its roots after scalar extension. Conjugating a root preserves its occurrence | A particular eigenbasis sector without the weight theorem and treatment of colliding weights |
| Sector to strict carrier exclusion | Requires a further invariant of actual words or child transitions | Excluding a nonzero abstract invariant image by the Perron bound alone |

Use the existing degree-four proof-bank components as the interface.
`Degree5Transport.quotient_intertwines_range` supplies the equivariant
first isomorphism. The rational image polynomial `q5` divides the signed
and ambient tensor characteristic polynomials. The orbit lemma transports
known weight roots to the signed spectrum. The root lift and Lie classification
below show that each image root has a mixed weight. Pure word coordinates
vanish in the transported eigenvector even if a pure monomial has the same
numerical value as a mixed weight.
Then use the existing `GaloisOrbit.orbit_exponent_on_beta` to move an exponent
onto the Perron root in the rational characteristic polynomial. Conjugation
transports a spectral value. When different contents have the same value,
identify the projected spaces before claiming support in a particular content.

For finite replay, use the checked ternary Lyndon basis from
[the degree-five note](c4-degree-five-2026-11-09.md). An exact change-of-basis
certificate should verify the inverse and the five-slot action over the
chosen splitting field, with separately identified coefficient and field
relations. Replay independently of the generator and bind the receipt to
the exact theorem statement, coefficient domain and source revision.
Check a slot permutation or a single changed exponent against a matrix for
which the mutated identity fails. One certificate checks one presented
instance. The universal implication from the certified identity to the
defect image belongs in Lean.

## Abstract surviving-sector control

For the plastic cubic `f(t) = t^3 - t - 1`, let its roots be `b,x,y`, with
`b > 1` and the other two contracting. Their product is one. The three
`(2,2,1)` weights are `1/b,1/x,1/y`. Their common rational polynomial is
`g(t) = t^3 + t^2 - 1`, obtained from `-t^3 f(1/t)`.
All three have modulus strictly below `b`, by the degree-five unit
comparison. An integer companion matrix for `g` therefore meets the
scalar spectral bound with nonzero reciprocal weights.

There is also an abstract Lie subspace giving precisely these weights.
In a splitting-field eigenbasis `X,Y,Z`, take
`[[X,Y],[[X,Y],Z]]` and the two cyclic rotations. Each vector is nonzero
(the associative expansion contains `XYXYZ` with coefficient one in the
first vector) and the three contents are distinct. Permuting the root
labels permutes the three lines since exchanging the two doubled letters
changes both inner brackets' signs. To see descent, use eigenvectors
`(1,t,t^2)` of the transpose companion of `f`, so that Galois conjugation
permutes the eigenvectors as well. The span is Galois invariant, hence
descends to a rational invariant subspace. This is a mathematical control
for the spectral implication. It gives no literal child system, no signed
normalization of actual pairs, and no dominance of its companion matrix by
a realizable unsigned child matrix.

## Next adversarial obligation

Test candidate word invariants against the abstract control, then against
literal first-cut data. Record the first premise that fails, distinguishing
degree-four balance, factorization, closure, strictness, and the proposed
conclusion. Reuse the exact bounded corpus and its Mojo child-graph
machinery if a finite search is needed. An exhausted search reports its
bound and coverage. The objective is either a genuine strict, child-closed
Pisot witness with a nonzero surviving image or a universal word identity
excluding one. Concentration, G1, C4 and PSC remain open.

## Splitting-field eigenvector criterion

The degree-five tensor action is the right-associated fifth Kronecker
power. Given an invertible left eigenbasis matrix `Q`, transport an
eigenvector by `Q⊗5`. In a pure coordinate `iiiii`, the coefficient from a
word depends only on the word's content because all five factors come from
row `i` of `Q`. The coefficients of each Lyndon bracket sum to zero within
each content. The integer check in `Degree5Weights.bracket_content_sums`
and the independent replay verify this cancellation. Thus every pure
coordinate of a transformed Lie vector vanishes over the splitting field.

A nonzero coordinate of the transported eigenvector then has one of the
four mixed shapes `(4,1,0)`, `(3,2,0)`, `(3,1,1)`, or `(2,2,1)`. Its weight
equals the eigenvalue. The argument applies to each nonzero coordinate,
including when distinct contents yield the same value. For example,
`(2,4,8)` gives weight 512 at both contents `(1,4,0)` and `(2,2,1)`. This
diagonal control tests the distinct-root premise alone.

### Signed Perron sieve on the rational image

`Degree5RootLift.exists_image_eigenvector` lifts a root of `q5` to a
nonzero eigenvector in the scalar-extended defect image and exhibits its
Lyndon combination. In a rational basis of the image, let `A` be the
restricted action, `B` the inclusion into word coordinates and `T` the
ambient tensor action. Then `TB = BA`. The inclusion admits a rational
left inverse `C` with `CB = I`. Both matrix identities survive scalar
extension. A nonzero eigenvector of the extended `A` therefore maps to a
nonzero eigenvector of the extended `T` inside the image. Its Lyndon
coefficients come from the verified rational brackets on the basis vectors.

This step must use the image polynomial itself. For a projection from
`diag(2,3)` onto its first coordinate, the source has a root at 3 and the
image has no such root. A source eigenvector at 3 lies in the kernel.
`root_q5_is_mixed` applies the classification to each image root given
three distinct incidence roots. `exists_signed_mixed_weight` supplies a
common image and signed spectral value when there is a nonzero actual
column and the incidence cubic is irreducible.

`Degree5Sieve.sieve5_roots` combines the mixed-weight classification with
Galois transitivity and the signed Perron bound. The image polynomial
divides the signed characteristic polynomial. For each excluded shape
`(4,1,0)`, `(3,2,0)` or `(3,1,1)`, moving the largest exponent onto the
Perron root gives an image root of modulus strictly larger than the
bound. Both orders of the contracting roots satisfy the modulus estimate.
The argument works if the original value also has a `(2,2,1)` representation.

`sieve5_of_primitive` obtains the signed bound from primitivity and the
degree-one balance implied by the degree-four hypotheses.
`sieve5_full_orbit_of_primitive` shows that when there is a nonzero defect
column, the roots of the image polynomial are exactly the three
`(2,2,1)` values. It moves the single exponent onto each incidence root in
turn. The result classifies the root set. The following factorization
argument would also determine the form of the multiplicities and is not yet
a Lean theorem.

* Let the incidence roots be `r₀,r₁,r₂`, let `d = r₀r₁r₂ ≠ 0`, and write
  `e₁,e₂` for their first two elementary symmetric functions. The three
  remaining weights are `d²/rᵢ`, so they are distinct for distinct roots.
  Their monic cubic is `t³ − d e₂ t² + d³ e₁ t − d⁵`. For an irreducible
  incidence cubic it is irreducible, since
  `ℚ(d²/rᵢ) = ℚ(rᵢ)`. If all roots of `q5` lie in this set, rational
  factorization forces `q5` to be a power of this cubic. In particular,
  a nonzero image must have rank divisible by three, and its signed
  spectrum must contain all three reciprocal weights.
* All three reciprocal weights must satisfy the signed bound. In
  particular, the two contracting-root weights give
  `|d| |α| ≤ 1` and `|d| |γ| ≤ 1`. Multiplying and using
  `|d| = |β| |α| |γ|` gives `|det M|³ ≤ |β|`, formalized as
  `det_cube_le_of_nonzero`. The unit plastic control satisfies this
  necessary condition, so the surviving case still needs information
  from actual ordered words.

## Next bounded algebraic targets

These are planned formalizations of the preceding argument, not additional
accepted theorems. Preserve the current normalization, `Equiv4` on every
state, irreducible incidence cubic and Pisot/primitive hypotheses.

1. **Reciprocal cubic and multiplicities.** Define
   `g(t) = t³ − d e₂ t² + d³ e₁ t − d⁵`, prove its irreducibility from that
   of the incidence cubic, and prove `q5 = g^k` for some `k : ℕ`.
   Include the zero image explicitly: `q5 = 1` and `k = 0` there; a nonzero
   image requires `k ≥ 1`. The root-set theorem supplies the roots, not their
   multiplicities. Use the characteristic polynomial of the actual image,
   not the whole signed source space.
2. **Rank divisibility.** Connect the degree of that characteristic
   polynomial to the rational image dimension to obtain `rank Q5 = 3k`.
   The optional stronger bound `k ≤ 6` needs a transported homogeneous
   decomposition: each of the three `(2,2,1)` contents has six basis
   elements, but the finite count alone is not a proof of `rank Q5 ≤ 18`.
   Preserve the numerical-weight collision controls when identifying the
   relevant spectral subspaces.
3. **Determinant exclusion corollary.** Under the same hypotheses,
   `|det M| ≥ 2` and `β < 8` force `Q5 = 0`: a nonzero column would give
   `8 ≤ |det M|³ ≤ β`. For substitutions with every image of length at most
   three, `β ≤ 3` follows from the incidence matrix's maximum column sum.
   Thus a nonzero degree-five image in that parameter class would require
   unimodularity. These are consequences to formalize, not new Lean
   declarations or a new corpus computation.

The main mathematical task remains a constraint on actual first-cut words
which excludes the surviving image. The degree-three determinant-sector
control and degree-four configuration (R) must remain in the adversarial
suite alongside the reciprocal plastic control. Excluding degree five alone
does not settle those cases, degrees `r ≥ 6`, or Concentration. The
`StrictSystem` first-defect selection interface at degree five also remains
to be connected; the present theorems assume degree-four balance directly.
