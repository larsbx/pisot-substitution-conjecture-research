# The marked-tile count of the C4 homoclinic pair

The [even stack residue](c4-even-stack-residue-2026-11-19.md) gives an
odd winding on the unordered factor from four grouped periodic seams.
In its pair-substitution presentation the winding is an integer count
difference of marked tiles. The incidence eventually has rank one
modulo two, and the marked count determines a word reproduced between
fixed pads. A balanced original seam cycle tests whether the count
splits into independent contributions of the two original rays. See
the [literature decision](c4-homoclinic-winding-counts-stop-go-2026-11-20.md).

## Work shown

### Assumptions and hypotheses

For the word result, take a morphism `s` and a set of marked letters.
Modulo two, each marked letter has the same image-count column `v₀`
and each unmarked letter has zero column. The words `u` and `v`
satisfy `s(u) = L u R` and `s(v) = L v R` with common pads `L,R`.
Write `c(w)` for the letter-count column and `m(w)` for the number of
marked letters over the integers. Set `K = m(u) − m(v)`.

For the application, use the written even stack reduction for a
hypothetical even-determinant PIP3 rank-two strict system. Here `X`
is the stack quotient, `Y` its unordered factor, and the two
periodic homoclinic tilings in `Y` are
`A = p(Q₀₀) = p(Q₁₁)` and `B = p(Q₀₁) = p(Q₁₀)`. Use the ordered
endpoint bits and the circle map `F` defined there. The original
periodic seams are indexed by the last left letter and first right
letter. Each side has at most three letters grouped into two nonempty
sets.

### Derivation / reduction

#### Rank-one incidence and common padding

Let `E(w) = ∏_(a in w) (1 + X_a)` in the free associative algebra
over `𝔽₂`. Its degree-one coefficients are the reductions of `c(w)`
and its constant coefficient is one. The substitution acts by the
algebra map `S(X_a) = E(s(a)) − 1`. Let `t = E(s(a₀)) − 1` for a
reference letter with column `v₀`. Compare `S` with the map `G` sending
marked variables to `t` and unmarked variables to zero. Both maps
send variables to elements of degree at least one with the same
degree-one part. Telescope their difference on a monomial of degree
`d` over the `d` factors. Each term has one factor of degree at least
two and `d − 1` factors of degree at least one. Thus `S − G` raises
the least degree by at least one.

For `D = E(u) − E(v)`, the padding gives `S(D) = E(L) D E(R)`. The
pads have constant coefficient one, so `S(D) − D` starts above the
least degree of `D`. Also `G(E(w)) = (1 + t)^m(w)`. If `K = 0` then
`G(D) = 0`, and induction from its zero constant term gives `D = 0`.
The expansion is injective by the inverse shift `X_a ↦ X_a − 1`.
Therefore `u = v`. The [even-count lemma](c4-literal-periodic-defect-2026-11-20.md)
is the zero-column case.

If `u ≠ v` and `v₀ ≠ 0`, the first differing degree of the expansions
is exactly `2^v₂(|K|)`. The preceding comparison shows that `G(D)`
and `D` have the same first nonzero homogeneous part. Write
`|K| = 2^e h` with `h` odd. The lowest term of
`(1+t)^|K| − 1 = (1+t^(2^e))^h − 1` is the `2^e`-th power of the
linear part of `t`. A variable with nonzero linear coefficient
contributes coefficient one at its pure power, so this term is
nonzero. The factor `(1+t)^min(m(u),m(v))` has constant coefficient
one. Independently by ordinary letter counts, the difference
`c(u) − c(v)` is fixed by the incidence of `s`. Modulo two it satisfies
`c(u) − c(v) = (K mod 2) v₀`.

#### The actual quotient pair

Let `N` be the unordered incidence in [Lemma S⁺](c4-rank-two-wall-2026-11-16.md#7-barges-ordered-pair-substitution-at-rank-two-lemma-s-and-theorem-p).
In the admissible-power presentation its characteristic polynomial
with zero factors removed is `χ_(M^n)(t−1)`. The original matrix `M`
is nilpotent modulo two by the even stack reduction. If `d` is the
size of `N`, Cayley–Hamilton on `t^(d−1)(t−1)` gives
`N^d = N^(d−1)` modulo two. The image of `N^(d−1)` is the fixed
space. That space has dimension one because `1` is a simple root.
All higher powers have that image.

The mark `b_c = (e_c − a_c) mod 2` for an ordered tile descends
to an unordered mark since the deck swap complements both endpoint
bits. The bits agree across adjacent cuts and are preserved at the
outer endpoints of a substituted tile. Telescoping gives `bN = b`
modulo two. The row is nonzero by Lemma S⁺. It has value one at the
unique nonzero fixed column `v₀` since `bN^k = b`. The column of
each sufficiently high power is thus `b_c v₀` at tile `c`.

Ordinary tiling asymptoticity gives exact agreement past a distant
vertex on each tail. Compare windows of a fixed radius greater than
twice the maximum tile length plus two, centered at successive
integers far along a tail. The relative translations matching the
windows tend to zero. Far enough out, two successive errors differ by
less than the minimum tile length. In the overlap a vertex of the
first tiling maps to a vertex of the second by either error. The two
images must be the same vertex, so the errors agree. Their constant
value on the tail must be zero. Reflection handles the other tail.

Choose common vertices `x₋ < 0 < x₊` past the difference and take
`u,v` to be the two words between them. A sufficiently high common
inflation power fixes both tilings, has the columns above and moves
the endpoints outwards. The additional intervals supply identical
pads. The real phase of `F` increases by one turn across each marked
tile and zero otherwise. Its difference along the two patches
therefore increases by `K`. On the two exactly matched tails the
circle difference is zero. The left-normalized real lift has value
`K` on the right, which is the winding. The [deck switch](c4-homoclinic-winding-2026-11-20.md)
makes `K` odd. The quotient defect consequently has exactly the
nonzero count column `v₀` modulo two, with first differing
scattered-subword degree one.

One can choose the proper return marker at a legal periodic seam
in group `(0,0)`, which makes `A` the unique quotient periodic
tiling with a vertex at zero. Then `B` has zero inside a tile
`c`. Inflating the endpoints of that tile sufficiently far gives
a choice of `x₋,x₊` on the matched tails. On this interval the
`B` patch is an inflated image of `c`, so its marked parity is
`b_c`. The other patch has parity `1 − b_c` and spans the
vertex of `A`. This uses the proper rewrite and the periodic
vertex count in [Barge, `4](https://arxiv.org/pdf/1301.7094).

#### Two checks on the original-to-quotient transfer

Let `C` be a linear transfer of original letter counts into quotient
counts modulo two, intertwining incidence maps `M'` and `N'` at
a common power. For any count vector `x`, invariance and commutation
give `b C x = b N'^k C x = b C M'^k x = 0` for large `k`.
If the actual quotient difference is `C x + E`, its winding parity
is therefore exactly `b E`. An equivariant transfer with an even
marked boundary term would exclude the residue.

There is also a test on the original seam cycle. Number both sides
so group zero is a singleton. Both singletons exist by the ternary
alphabet bound. The existing original seam cycle with nonzero grouped
image uses the unique original edge over `(0,0)` with nonzero weight.
That edge belongs to a simple cycle. A bridge has zero weight in a
balanced flow, by summing divergence over one component after its
deletion. Orient the simple cycle and give it integer weights
`+1,−1` with zero row and column sums and `+1` on the singleton
edge. The grouped cycle has `+1` on each diagonal edge and `−1`
off diagonal.

The quotient marked count on `[x₋,x₊]` for every original seam
of this cycle is `m(u)` on the diagonal groups and `m(v)` off
diagonal. The weighted sum is `2K ≡ 2 (mod 4)`. If each such count
were `left(a) + right(b)` modulo four, its weighted sum would be
zero by the row and column sums. The same obstruction applies to
a count row on original patches split at the seam, augmented by
separate left and right trimming terms. Each original ray piece
depends on just its endpoint letter. A candidate reblocking can be
tested by recording the quotient marked count on each edge of this
original simple cycle.

### Evidence and replay

| Lean endpoint | Verified implication |
| --- | --- |
| `eq_of_common_padding_of_marked_count` | Equal integer marked counts force equality for common padding and the stated columns |
| `count_difference_mod_two_of_common_padding` | Marked parity determines every component of the letter-count difference |
| `winding_eq_boundary_of_nilpotent_transfer` | An invariant row kills the part transferred equivariantly from a nilpotent source |

The endpoints are in [PeriodicPartnerLiteralDefect.lean](../proof/PscVerif/PscVerif/PeriodicPartnerLiteralDefect.lean).
The quotient geometry, the least-degree formula and the modulo-four
seam test are written deductions.

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

### Negative controls

Period doubling has `δ(0) = 01` and `δ(1) = 00`. At the square its
images are `0100` and `0101` with common left pad `010` and empty
right pad. The columns modulo two are `(1,1)` and zero. Marking
`0` gives `K = 1` and a distinct common-padding pair. Lean checks
the padding and column facts in `period_doubling_padding_control`
and `period_doubling_marked_count_control`. The Thue–Morse cover
realizes this odd winding at even norm and degree one, as recorded
in the [even stack reduction](c4-even-stack-residue-2026-11-19.md#negative-controls).

### Non-claims / remaining gaps

The quotient constraints force a joint contribution from the two
original rays modulo four. The [return-word follow-up](c4-return-seam-boundary-2026-11-20.md)
identifies the fixed count vector behind that term and its readout
from twin vertices. An exclusion still needs a cubic restriction on
that readout or an independent argument. The general even-determinant
rank-two case and C4 remain open. Independent human review is pending.
