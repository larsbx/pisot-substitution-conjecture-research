# Literal finite differences at even nilpotent incidence

The [even-determinant rank-two reduction](c4-even-stack-residue-2026-11-19.md)
produces a periodic bi-asymptotic pair in the unordered stack factor. In
the original substitution, nilpotence modulo two rules out such a periodic
finite difference in literal tiles. It also constrains the one-sided
asymptotic relations among the original periodic seams. The same even
residue contains an explicit two-parameter companion family that can be
excluded directly by literal coincidences. See the [source decision](c4-literal-periodic-defect-stop-go-2026-11-20.md).

## Finite word rigidity

Let `τ` be a substitution whose image of each letter has even counts of
every letter. If finite words satisfy `τ(u) = L u R` and `τ(v) = L v R`
with common words `L,R`, then `u = v`. No length equality is required.

In the monoid algebra of words over `𝔽₂`, let `E(w)` be the ordered product
of `1 + X_a` over letters of `w`. The degree of a monomial is its word
length. The constant term is one and the coefficient of `X_b` is the
count of `b` modulo two. Substituting `E(τ(a)) − 1` for `X_a` sends
`E(w)` to `E(τ(w))`. The new generator expressions start in degree at
least two. Consequently a difference vanishing below degree `d`
is sent to one vanishing below degree `2d`.

Put `D = E(u) − E(v)`. The two padding equations send `D` to
`E(L) D E(R)`. If `D` vanishes below `d`, the difference between this
product and `D` vanishes below `d+1` since `E(L)−1` and `E(R)−1` have
zero constant coefficient. Starting at `d=1`, the image vanishes below
`2d ≥ d+1` and so does `D`. Induction gives zero in every degree. The
substitution `X_a ↦ X_a−1` sends `E(w)` back to the basis monomial `w`,
so `E(u)=E(v)` implies `u=v`.

## Consequences for the original tilings

Let `M` be the original incidence matrix with `M^j ≡ 0 (mod 2)` for some
positive `j`. For two tilings fixed by a common positive power `Φ^p`, take
`τ = σ^(jp)`. Its letter counts are the columns of `M^(jp)` and are even.
Write `Λ > 1` for its inflation. If the tilings agree exactly on both
tails, choose common vertices `a<0<b` beyond the finite disagreement.
Let `u,v` be the words on `[a,b]` in the two tilings. Inflation gives
their words on `[Λa,Λb]`. Outside `[a,b]`, the longer interval has the
same left and right padding in both tilings. The word theorem gives
`u=v`, and the tilings agree everywhere.

If both tilings have a vertex at the inflation centre and share the
right tail, take `[0,b]` with a common vertex on that tail. The argument
uses empty left padding and proves agreement on the entire right ray
from zero. Reflect to obtain the left version. Thus for marked periodic
seams in the original tiling, exact eventual agreement on the right is
equivalent to the same first letter. On the left it is equivalent to the
same last letter. The converses use the common growing iterates of those
letters under the substitution power. This argument applies to equal
labelled tails as opposed to dense eventual coincidence of different rays.

## Companion family with arbitrary even determinant

For positive integers `m < r`, set

```text
σ(0) = 1,    σ(1) = 2,    σ(2) = W = 1 0^m 2^r 1.
A = 2 1^m,   P = 1 0^m,   Q = 2^m,
D = A W^r 2.
```

These give `σ³(1)=D` and `σ³(2)=W Q D^r W`. Cut the former after
`A W P Q` and the latter after `W Q A P`. The first cut lies inside the
second `W` and the second cut inside the first `W` in the first `D`.
Both are followed by `2`, because `r>m`. Their prefix Parikh vector is
`(2m,m+3,r+m+1)`. This witnesses left strong coincidence for `1,2` at
level three. The pair `0,2` shares its first letter at level one, and
`0,1` reduces to `1,2` after one substitution. The repository's checked
all-pair exclusion theorem therefore rules out every finite strict
system in this family. [Existing exclusion theorem](../proof/PscVerif/PscVerif/StrictSystemCore.lean)

For `r>m≥2`, the incidence matrix is primitive, with characteristic
polynomial `x³ − r x² − 2x − m`. The directed letter graph contains the
cycle `0→1→2→0` and a loop at `2`. The polynomial has a real root
`β ∈ (r,r+1)` by its signs at the endpoints. The quadratic factor has
constant term `m/β` and linear coefficient `β-r=(2+m/β)/β < 3/β`.
Its discriminant is negative since `9 < 4mβ`. Its two conjugate roots
thus have modulus `√(m/β)<1`. The cubic is irreducible over `ℚ`, since
a rational root would be an integer and its only real root lies strictly
between consecutive integers. If `m,r` are both even, the incidence
matrix modulo two is strictly lower triangular with subdiagonal ones.
Its cube vanishes. Both endpoint maps have two periodic letters `1,2`.
The word `σ²(2)=D` contains `11`, `12` and `21`, and `W` contains `22`.
The original eventual range is the complete square on those letters.
This gives a strict-system exclusion within the even, complete-square
Pisot class for each even determinant `m≥2`.

## Evidence and controls

Lean checks `eq_of_common_padding` and `period_doubling_padding_control`
in [PeriodicPartnerLiteralDefect](../proof/PscVerif/PscVerif/PeriodicPartnerLiteralDefect.lean).
It checks the two literal level-three cuts and their equal Parikh vectors
in [PeriodicPartnerCompanionWords](../proof/PscVerif/PscVerif/PeriodicPartnerCompanionWords.lean).
The interval argument, the composition with the existing strict-system
theorem and the Pisot calculation are written deductions above.

```sh
(cd proof/PscVerif && lake build PscVerif.PeriodicPartnerLiteralDefect PscVerif.PeriodicPartnerCompanionWords)
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

Period doubling has `δ²(0)=0100` and `δ²(1)=0101`. With `L=010`, empty
`R`, and `u=0,v=1`, it satisfies both padding equations. The even-count
hypothesis fails. At the companion boundary `m=r` the proposed first
cut has consumed the entire run of `2`s and the following tile is `1`.
The explicit coincidence cut is a claim for `m<r`.

The quotient may have a bi-asymptotic pair although none of its distinct
periodic original representatives agree on both literal tails. The word
rigidity therefore leaves the obstruction for arbitrary literal lifts of
the quotient pair open. The family exclusion does not cover that general
case. Independent human review is pending.
