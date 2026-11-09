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
