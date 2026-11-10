# Degree-five spectral transport and word realizability

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
from a rational tensor image. Proceed with the quotient specialization and
a narrowly scoped spectral control. Keep literal realization and global
extraction as separate obligations.

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
known weight roots to the signed spectrum. The next step must show
that each image root is a weight on the **Lie** space, with the pure fifth powers excluded.
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

### Conditional restriction on the rational image

The remaining Lean interface is to lift a root of `q5` to a nonzero
splitting-field eigenvector of the actual defect image and exhibit its
Lyndon combination there. The eigenvector theorem can then be used with
the existing Galois transport. The following deductions are conditional on
that interface and the signed Perron bound.

* If a nonzero transformed coordinate has one of the three excluded
  shapes, move its maximal exponent onto the Perron root. The resulting
  signed spectral value contradicts the bound. This reasoning applies to
  every such coordinate even if its original value also admits a
  `(2,2,1)` representation.
* Let the incidence roots be `r₀,r₁,r₂`, let `d = r₀r₁r₂ ≠ 0`, and write
  `e₁,e₂` for their first two elementary symmetric functions. The three
  remaining weights are `d²/rᵢ`, so they are distinct for distinct roots.
  Their monic cubic is `t³ − d e₂ t² + d³ e₁ t − d⁵`. For an irreducible
  incidence cubic it is irreducible, since
  `ℚ(d²/rᵢ) = ℚ(rᵢ)`. If all roots of `q5` lie in this set, rational
  factorization forces `q5` to be a power of this cubic. In particular,
  a nonzero image must have rank divisible by three, and its signed
  spectrum must contain all three reciprocal weights.
* Consequently `maxᵢ |d²/rᵢ| ≤ |β|` is a necessary condition for a nonzero
  image. The unit plastic control satisfies it, so the surviving case
  still needs information from actual ordered words.
