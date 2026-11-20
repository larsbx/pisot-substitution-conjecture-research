# The even-determinant rank-two residue

This follows the [odd-determinant exclusion](c4-rank-two-stack-cycle-exclusion-2026-11-19.md)
in [PR #617](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/617),
merged at `e79e3e31b7391a216aed697f2adfef0d020dc823`.

**Written reduction.** An even-determinant PIP3 strict system at coincidence
rank two requires nilpotent incidence modulo two, a complete grouped seam
square, and a periodic pair in the pure discrete quotient that is
asymptotic on both tails and has an odd winding difference.

## Literature decision

The target is a necessary condition on the even-determinant strict systems
left by #617. Extend its upper bound to even determinant and test whether the
two-sheet covering of the stack quotient forces a sharper parity condition
than Theorem P⁺ on the original hull.

| Source | Transfer used |
| --- | --- |
| [Barge (2015), Theorem 12, Lemmas 13–14, Theorem 17 and Proposition 19](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | The stack quotient, its ordered-pair presentation, the two-sheet covering of its pure discrete factor, and injectivity of the first-cohomology pullback from the stack quotient. These results apply at even norm. Lemma 13's proof gives the stack equivalence of two disjoint partners before using the triviality of the stack relation. Theorem 22's larger lower bound requires odd norm. |
| [Barge–Kellendonk–Schmieding (2012), Corollary 3 and Theorem 5](https://arxiv.org/pdf/1204.1432) | Continuous eigenfunction classes give an integral injection with torsion-free cokernel in degree one. Equal rational ranks therefore imply that every integral class is represented by an eigenfunction. |
| [Baker–Barge–Kwapisz (2006), Theorems 4.2 and 5.1](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) and [Barge–Diamond (2008), Theorem 4](https://arxiv.org/pdf/math/0702669) | The minimal fibre size is the coincidence rank, the cubic solenoid supplies three independent continuous eigenvalues, and the eventual-range sequence computes first cohomology equivariantly. |
| [Barge–Bruin–Jones–Sadun (2012), Theorem 6](https://www.mat.univie.ac.at/~bruin/papers/HPC.pdf) and [Lemma S⁺ and Theorem P⁺](c4-rank-two-wall-2026-11-16.md#7-barges-ordered-pair-substitution-at-rank-two-lemma-s-and-theorem-p) | The signed incidence matrices agree modulo two. Use the existing cubic parity identity with the even and odd degrees kept separate. |

Proceed with a conditional rank-two reduction. The Thue–Morse double cover
at norm two, after border forcing, has the period-doubling factor described
by Barge. The dimension gap of one above the dilation degree and the
nilpotent parity class both occur there. They require an additional cubic
argument for a contradiction. Calibrate the new conditions on the exact
short-image corpus and a cubic control beyond it. On specimens passing the
arithmetic filter, test the literal common-vertex requirement of (Z3)
through positive strong-coincidence witnesses. Count a witness only when
its prefix Parikh equality replays in the literal words.

## Work shown

### Assumptions and hypotheses

Let `σ ∈ PIP3` have even determinant and coincidence rank two, and suppose
there is a strict system. Use the strict component and realization of
[Theorem W](c4-rank-two-wall-2026-11-16.md#62-statement), the origin
normalization (R4), and simultaneous periodicization as in #617. Let
`X = Ω_s` be Barge's stack quotient of the original hull and `Y = Ω_p`
its unordered-pair factor. All dimensions below are rational first Čech
cohomology dimensions.

### Derivation / reduction

#### The upper bound applies at even determinant

The incidence matrix is nonsingular. Even determinant therefore implies
nonunimodularity. In Theorem W, (W2) supplies a strict fibre with exactly
one partner, and the last sentence of (W4) supplies a fibre with two
different partners. Thus the [directional extraction](c4-complete-range-covering-2026-11-19.md#directional-extraction-from-a-singleton-fibre)
gives witnesses in both directions without an additional covering argument.

On any side with three periodic letters, the endpoint map is a permutation.
Choose the witness in that injective direction and anchor it at the origin
by the branch-location argument of #617. Its vertex leaves have two
different endpoint letters on the opposite ray. Their dense eventual
coincidence from (W4) identifies those two ray germs for the stack relation.
On a side with at most two periodic letters use the singleton groups. The
proper presentation and Barge's cohomology injection used in #617 apply at
even norm. Its winding calculation therefore gives

```text
dim H¹(X; ℚ) ≤ 3 + dim image(C(ER) → C(grouped ER)) ≤ 4.
```

The stack quotient has coincidence rank two as in #617. Each original
realization fibre has a strict pair, and the two entries have distinct
stack images. A two-element original fibre maps onto the corresponding
stack fibre. Barge's Theorem 17 now supplies a two-sheet covering
`p : X → Y` with deck involution `ι`, through which the maximal
equicontinuous factor map of `X` factors. Both `p` and `ι` commute with the
translation action in the corresponding sense.

#### The cover requires four classes on its base

There is a continuous circle-valued function `z` on `X` with
`z(ιx) = −z(x)`. For a concrete construction use the ordered-pair
presentation in [Lemma S⁺](c4-rank-two-wall-2026-11-16.md#7-barges-ordered-pair-substitution-at-rank-two-lemma-s-and-theorem-p).
Its two fixed eventual-range edges are exchanged by `ι`. For a tile
label `c`, assign the bits `a_c,e_c` of its eventual first and last
endpoints, using bit `0` for the corresponding endpoint of one fixed edge.
Adjacent tiles satisfy `e_c = a_d`. On the tile `c` of length `L_c`,
starting at coordinate `0`, put

```text
z(s) = exp(πi(a_c + b_c s/L_c)),   b_c ∈ {0,1},   b_c ≡ e_c − a_c (mod 2).
```

The endpoint values agree at a legal cut. The swap complements `a_c` and
`e_c`, preserves `b_c` and the tile length, and hence negates `z`.

The square of `z` descends to a continuous function `F : Y → S¹`.
The continuous eigenvalue group of `Y` has rank at least three, from
the cubic solenoid through which its flow factors. Suppose `dim H¹(Y;ℚ) = 3`.
By Barge–Kellendonk–Schmieding, the class of `F` is the class of an
eigenfunction `f` on `Y`. Write `F = f exp(2πi u)` for a continuous real
function `u` on `Y`. Then `w = z exp(−πi u ∘ p)` remains odd under `ι`
and has `w² = f ∘ p`. Write the translation flow as `A_t`. If `f` has
frequency `λ`, for fixed `x` the quantity

```text
exp(−πi λt) w(A_t x) / w(x)
```

is continuous in `t`, takes values in `{1,−1}`, and is 1 at `t = 0`.
Thus `w` is a continuous eigenfunction of frequency `λ/2`. All continuous
eigenfunctions on `X` factor through its maximal equicontinuous factor,
so they are constant on the `p` fibres. This contradicts the oddness of
`w`. Consequently `dim H¹(Y;ℚ) ≥ 4`.

The pullback `p*` is injective over `ℚ`. Indeed, for a continuous circle
map `h` on `X`, its norm on `Y` is `N(h)(p(x)) = h(x) h(ιx)`. This is
continuous by the covering property. A continuous real logarithm of `h`
gives one of `N(h)` by addition over the fibre. The norm therefore induces
a map on integral first cohomology and `N ∘ p*` is multiplication by two.
Combining the bounds gives

```text
dim H¹(Y; ℚ) = dim H¹(X; ℚ) = 4,     H¹(X; ℚ)^− = 0.
```

For the last equality, the rational pullback is now surjective and its
image is fixed by the deck involution. The winding image has dimension
one, so the map from cycles of `ER` to cycles of the grouped graph is
nonzero. After padding both sides to two classes, its matrix has entries
`c,−c,−c,c` for some nonzero `c`. In particular all four grouped edges
are present and the grouped graph is `K₂,₂`.

#### The signed parity identity forces nilpotence

Use the admissible power (n=6) in Lemma S⁺. Let `r,q₁` be its factors in
`nz χ₊ = χ_(Mⁿ) r` and `nz χ₋ = (t−1)q₁`. The eventual-range sequence
for the ordered-pair presentation removes a single line, in the odd
part, generated by the difference of the two exchanged components.
Thus `3 + deg r` is the even cohomology dimension and `deg q₁` is the
odd cohomology dimension. From the cover calculation they are 4 and 0,
so `deg r = 1` and `deg q₁ = 0`. In Theorem P⁺ the relation
`h_n r̄ = (t+1)q̄₁` has degree equation

```text
d₂ + deg r = 1 + deg q₁.
```

Hence `d₂ = 0`, and the original cubic characteristic polynomial reduces
to `t³` modulo two. Cayley–Hamilton gives `(M mod 2)^3 = 0`. In particular,
the trace and the sum of the principal two-by-two minors must both be even.

#### The grouped square forces a homoclinic winding on the base

For either side, consider the relation of sharing no labelled tile at
any nonnegative inflation level between the aligned periodic rays.
The periodic seam pair from (Z3) gives a nonempty relation on each side.
With two periodic letters the only possible unordered disjoint pair is
the pair of singleton groups. With three letters, the chosen two rays
have dense eventual coincidence by (W4). This transports disjointness
with each other ray between those two labels. Indeed, intersect the open
interval of any purported coincidence with an open eventual coincidence
interval of the chosen pair, then inflate to the larger level. The
[ternary disjointness calculation](c4-complete-range-covering-2026-11-19.md#noncoincidence-among-seams-of-a-complete-range)
shows that the disjoint pairs are exactly the pairs across the two groups.

Write `Q_(i,j)` for the stack image of the seam group `(i,j)`. All four
images are distinct, since a pair of different groups on either side
has a half-line without eventual coincidence. Opposite corners have
original seam representatives disjoint on both sides at all inflation
levels. Their stack images are twins. To see this, fix the representative
of one corner and choose a strict partner from `Z`. Barge's proof of
Lemma 13 puts the opposite representative and this strict partner in
the same stack class. The image of `Z` in `X × X` is the graph of the
deck involution. Both are compact minimal translation joinings of
distinct `g_s` fibre-mates and project onto `X`. They meet over a
two-element fibre, where only one second entry is possible. Minimality
then makes the two joinings equal. Thus

```text
ι(Q_(i,j)) = Q_(1−i,1−j).
```

Fix an original seam cycle with nonzero grouped image. Each row group
has an original row incident to both column groups. Otherwise the sum
over either grouped cell in that row group is a sum of entire original
row sums and is zero. This contradicts the nonzero value in every
grouped cell. The same argument applies to columns. In a grouped row,
choose representatives with the same original last letter. Their left
rays agree, so their stack images are left-asymptotic by continuity and
translation equivariance. Grouped columns similarly give right-asymptotic
stack images. The base therefore has two distinct tilings

```text
A = p(Q_(0,0)) = p(Q_(1,1)),
B = p(Q_(0,1)) = p(Q_(1,0)).
```

They are fixed by a common inflation power, lie in the same realization
fibre, and are asymptotic on both tails. Distinctness follows from the
degree-two covering and the four distinct stack images.

For a continuous circle map on `Y`, take the difference of the left and
right tail-normalized lifts of its ratio along `A,B` as in #617. That
difference is integral and vanishes for a map with a continuous real
logarithm, so it defines a first-cohomology evaluation. For `F` given by
the square of the odd sheet function `z`, the left lift is twice the
left normalized lift for `Q_(0,0),Q_(0,1)` and the right lift is twice
the right normalized lift for `Q_(0,0),Q_(1,0)`. At zero the two `z`
ratios differ by a sign, since the two denominators are deck twins.
Their real lifts differ modulo `ℤ` by `1/2`. The evaluation of `[F]`
on the homoclinic pair `A,B` is therefore odd. Eigenfunction classes
evaluate to zero because `A,B` share their maximal equicontinuous image.

### Evidence and replay

Lean checks `grouped_cycle_support` and `grouped_row_crosses` in
[PeriodicPartnerSeamCycles](../proof/PscVerif/PscVerif/PeriodicPartnerSeamCycles.lean).
The constancy of the normalized phase and the degree argument are checked by
`continuous_square_one_eq_one` and `even_stack_residue_degrees` in
[PeriodicPartnerDirectional](../proof/PscVerif/PscVerif/PeriodicPartnerDirectional.lean).
The [homoclinic winding formalization](c4-homoclinic-winding-2026-11-20.md)
checks the lift construction and odd winding from the stated seam phase
conditions. The geometric factor construction and its transfer of the
tail and sheet conditions use the written arguments and published inputs above.

The [Mojo regression](../kernel/tests/test_c4_even_stack_residue.mojo)
uses the standing 4,554-specimen PIP3 corpus, the Barge–Diamond profile,
and the existing exact strong-coincidence automaton. Of 1,926 specimens
with even determinant, 564 have positive eventual-range cycle rank.
The nilpotent parity condition retains 96, with original cohomology
dimensions `4/5/7` on `36/48/12` respectively. The other 336 nilpotent
specimens have dimension three and are outside the positive-cycle class.
The independent [Anderson–Putnam oracle](../oracles/python/h1_census_ap.py)
agrees on the cohomology counts and the long-image control. In that replay
nilpotence is tested by cubing the reduced matrix directly.

All 288 unordered letter pairs on the 96 retained specimens have
shortest left strong-coincidence witnesses. Their literal prefix replay
agrees at every pair, with levels between one and seven. The automaton
uses the standing 20,000-state cap and raises on exhaustion. The literal
test allows up to level twelve and `3^12` letters, and a refused or missing
witness fails the regression. Thus on these 96 cases every putative
strict origin pair from (Z3) has a matching tile at some inflation level.
These are finite checks on the listed corpus.

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_even_stack_residue.mojo)
```

### Negative controls

- The cubic `1/2/10022221` is beyond the short-image corpus. Its incidence
  polynomial is `t³ − 4t² − 2t − 2`, its determinant is 2, and both endpoint
  maps send `0,1,2` to `1,2,1`. Its eventual range is the complete square
  on letters `1,2`, with `dim H¹ = 4`. It passes the arithmetic and graph
  conditions. A literal coincidence of the periodic first letters 1 and 2
  occurs at index 16 of both third powers, with tile 2 and prefix Parikh
  vector `(4,5,7)`. It excludes a strict origin pair for this control.
- Period doubling `0→01, 1→00` has two periodic seam tilings with the same
  right ray whose left rays differ only at the last tile. The even powers
  of its two letters have identical prefixes up to their final letter.
  A circle map winding once across each tile of type 1 has winding
  difference of absolute value one on this pair. With the Thue–Morse
  cover this realizes the odd homoclinic winding at degree one and even
  norm. The example lies outside irreducible cubic incidence.

### Non-claims / remaining gaps

The next even-determinant obligation concerns primitive irreducible cubic
substitutions with nilpotent incidence modulo two and a surviving grouped
seam square. It needs either a cubic obstruction to the periodic
homoclinic winding with four seam lifts from the original ternary hull,
or an independent strict-system exclusion on this class. The
[literal follow-up](c4-literal-periodic-defect-2026-11-20.md) rules out a
periodic finite difference in the original hull and excludes a companion
family with every positive even determinant. The unordered factor can
still have a finite difference whose original lifts do not agree on both
tails. Higher coincidence ranks, universal C4 and PSC remain open.
