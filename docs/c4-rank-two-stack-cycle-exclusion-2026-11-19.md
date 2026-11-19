# Stack quotient cohomology excludes odd-determinant rank-two strict systems

**Written theorem.** Let `σ` be a primitive substitution on three letters
whose incidence matrix has irreducible Pisot characteristic polynomial and
odd determinant. If its coincidence rank is two, there is no strict system
of legal noncoincident irreducible balanced pairs closed under all literal
children. This uses the strict-component and realization results specified
below. The proof bounds the rational first cohomology dimension of Barge's
stack quotient by four, whereas the quotient still has degree three, odd
norm, and coincidence rank two.

## Literature decision and hypotheses

The question is whether the identifications forced by the two directed
witnesses impose a rank bound on the stack quotient. Use the actual map on
circle-valued functions to test that bound. The eventual range of the
original substitution serves as a source of winding evaluations.

| Input | Scope used |
| --- | --- |
| [Barge–Diamond (2008), §3 and Theorem 4](https://arxiv.org/pdf/math/0702669) and [eventual-range connectivity](c4-geometric-f-class-2026-11-16.md#5-lemma-s-and-theorem-p-a-parity-refinement-of-barge-2015-thm-22) | The seam graph gives aligned periodic vertex tilings and `dim H¹(Ω;ℚ) = 3 + β₁(ER)` for the irreducible cubic. |
| [Barge (2015), §2, Theorem 12, §4 and Proposition 19](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | Stable equivalence and the stack relation, proper rewriting, the translation-equivariant stack factor, and injective pullback on rational cohomology. |
| [Barge (2015), Theorems 4 and 22](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | Coincidence rank is the minimum fibre cardinality of the maximal equicontinuous factor. The odd-norm bound applies to the quotient's Pisot substitution, including if its incidence is reducible. |
| [Andress–Robinson, Theorem 3.1](https://bpb-us-e1.wpmucdn.com/blogs.gwu.edu/dist/2/115/files/2016/03/AndressRobinsonPub-15tlli8.pdf) | First integral Čech cohomology is the group of circle-valued maps modulo continuous real logarithms. |
| [Baker–Barge–Kwapisz, Theorems 4.2 and 5.1](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), [Barge–Diamond–Swanson, §2](https://arxiv.org/pdf/0804.0930), [Theorem W](c4-rank-two-wall-2026-11-16.md#62-statement) and [directional extraction](c4-complete-range-covering-2026-11-19.md) | The geometric and maximal equicontinuous fibres agree in the standing hypotheses. A strict component has a singleton partner fibre and a multiple partner fibre at odd determinant and rank two. On every side with an injective endpoint map, a witness has two vertex leaves in the zero fibre, and (W4) gives their dense eventual coincidence. |

Proceed using the rank of the winding evaluations on pullbacks. Identifying
periodic seam tilings does not by itself give a presentation of the stack
tiling space, so the argument computes only the restriction of cohomology
to the original seam cycles. The two-by-two Thue–Morse residue lacks odd
norm, and the cited `01/210/1021` counterexample to (NM_V) does not supply
a rank-two strict system. These are distinct controls for the hypotheses.

## Cohomology evaluations on the eventual range

Write `G = (L ⊔ R, E)` for the eventual-range graph, with edges oriented
from the last-letter side `L` to the first-letter side `R`. For an edge
`e = (l,r)`, let `T_e` be its periodic seam tiling at the origin. Seams
in a row `l` share their left ray exactly. Seams in a column `r` share
their right ray exactly. Put

```text
C(G) = {x in Q^E : sum of x_e incident to v is zero for every vertex v}.
```

This is the rational cycle space because all incident edges have the same
orientation at each given vertex. Fix an incident reference edge `e_v`
for each vertex. For a continuous `f : Ω → S¹` and an edge `e` incident
to `v`, let `d_v(e)` be the value at zero of the continuous real lift of

```text
t ↦ f(T_e − t) / f(T_(e_v) − t)
```

that tends to zero at the appropriate end of the line. The end is `−∞`
for `v ∈ L` and `+∞` for `v ∈ R`. The ratio tends to 1 there by exact ray
agreement and uniform continuity. Take the small real argument far out
on that tail and extend by path lifting. The normalization fixes the
integer ambiguity. Define

```text
W_f(x) = sum over e = (l,r) of x_e (d_l(e) − d_r(e)).
```

Changing a reference edge adds a constant to `d_v` on its incidence set,
which cancels by the cycle condition. For integral `x`, exponentiating
the sum gives 1. The factors from `f(T_e)` cancel term by term between
`d_l(e)` and `d_r(e)`, and the factors at reference edges cancel at each
vertex. Thus `W_f` is integral on integral cycles. Multiplying circle
maps adds evaluations. If `f = exp(2πi u)` for continuous real `u`, its
normalized lift has `d_v(e) = u(T_e) − u(T_(e_v))` by uniform continuity
along the common tail. Its evaluation is zero. Bruschlinsky's theorem
therefore gives a homomorphism from integral first cohomology. Tensor
with `ℚ` to obtain

```text
W : H¹(Ω; ℚ) → C(G)*.
```

The rationalization commutes with first cohomology for the substitution
tiling spaces here, using their finite-graph inverse limit descriptions
and direct limits in cohomology.

**Surjectivity.** Fix an edge `e₀` and choose `ε` less than one third of
the minimum tile length. Define a circle map `f_(e₀)` that winds once as
the origin runs from `−ε` to `ε` relative to an occurrence of the seam
`e₀`, and is 1 outside these seam neighbourhoods. More precisely, the
value at signed offset `s` is `exp(2πi(s+ε)/(2ε))` if `|s| ≤ ε` at such
a seam. The neighbourhoods are disjoint. The map is continuous in the
ordinary tiling topology since the seam type is locally determined and
the value is 1 at both ends. At `T_e − t` with `|t| ≤ ε`, the only seam
that can contribute is the one at the original origin. On the shared
tail beyond this interval the two reference values agree. Accordingly
`d_l(e) = (1_(e=e₀) − 1_(e_l=e₀))/2` and
`d_r(e) = −(1_(e=e₀) − 1_(e_r=e₀))/2`. The reference terms cancel, giving
`W_(f_(e₀))(x) = x_(e₀)`. These coordinate evaluations span the dual of
`C(G)`, so `dim ker W = dim H¹(Ω;ℚ) − β₁(G) = 3`.

## Effect of a factor identifying periodic seam tilings

Let `q : Ω → X` be a continuous translation-equivariant factor. Suppose
there are partitions `l ↦ l̄` and `r ↦ r̄` with at most two classes on
each side, and `q(T_(l,r))` depends only on `(l̄,r̄)`. Write `Q_(l̄,r̄)` for
that image wherever the group pair occurs. Given `x ∈ C(G)`, set

```text
x̄_(u,v) = sum of x_(l,r) over edges with (l̄,r̄) = (u,v).
```

Values at missing group pairs are zero. Each row and column sum of `x̄`
is zero by grouping the zero row and column sums of `x`. After padding
to two classes per side, `x̄` belongs to the one-dimensional cycle space
of the complete two-by-two graph. Its four entries are `c,−c,−c,c`.

Consider `f = g ∘ q` for a continuous circle map `g` on `X`. For a fixed
left group `u`, there are at most two points `Q_(u,v)` to consider. If
some original row in `u` meets both groups `v`, those two points are
left-asymptotic since they come from that row. Choose a reference among
them and define `A_u(v)` by the left normalized lifts on `X`. By
additivity of normalized lifts, for any original row `l` in `u` the
value `d_l(e)` is `A_u(r̄) − A_u(r̄(e_l))`. This also holds with
`A_u ≡ 0` if no original row in `u` meets both groups, since then every
within-row ratio on `X` is identically 1. Use the opposite direction
on columns to obtain `B_v(u)` with `d_r(e) = B_v(l̄) − B_v(l̄(e_r))`.
Cancellation of the reference terms now gives

```text
W_(g ∘ q)(x) = sum over (u,v) of x̄_(u,v) (A_u(v) − B_v(u)).
```

Hence `W` on the image of `q*` takes values in the subspace of the dual
that factors through `x ↦ x̄`, of dimension at most one. For a factor
with injective rational cohomology pullback this proves

```text
dim H¹(X; ℚ) ≤ dim ker W + 1 = 4.
```

The grouped graph here only bounds the rank of these evaluations. The
argument makes no identification of it with a presentation for `X`.

## Application to the stack quotient

Assume a strict system exists. Use the usual normalized realization, the
compact strict component `Z` with (Z1)–(Z4), and (W1), (W2), (W4) of
[Theorem W](c4-rank-two-wall-2026-11-16.md#62-statement). Barge's lower
bound on `Ω` gives `β₁(ER) ≥ 2`. The covering exclusion and singleton-fibre
return argument in the [preceding note](c4-complete-range-covering-2026-11-19.md)
give an exact witness on either side. The origin-anchoring result puts
both leaves at periodic seams in each direction where the relevant
endpoint map is injective.

- If `R` has three letters, `g_L` is a permutation. Choose the left
  witness. Its vertex leaves have different first letters `a,b` and their
  aligned right rays have dense eventual coincidence on `(0,∞)` by (W4).
  Group `a,b` on `R` and keep the third letter separate. If `R` has at
  most two letters, use singleton groups.
- If `L` has three letters, apply the mirror argument using `g_R` and a
  right witness to group two last letters. If `L` has at most two letters,
  use singleton groups.

Take `q : Ω → Ω_s` to be the stack quotient. For two seams in the same
pair of groups their right rays are either equal or have the dense
eventual coincidence supplied by the selected pair of first letters.
The left rays have the corresponding property by their last letters.
An eventual coincidence in the interior of a tile produces stable
equivalence at that location, because all later inflations refine the
same common tile on an expanding neighbourhood. The two sides together
give stable equivalence on a dense set of translations. All seams are in
the same geometric fibre, so these two seam tilings are `≈_s`-equivalent
and have equal images under `q`. No property of the common partner's
central tile is required for this step.

Here are the proper rewriting and rank inputs for using the stack factor
on the original hull. Choose a legal periodic seam and pass to a power
`σ^m` fixing its endpoints. Barge's proper presentation uses the blocks
between consecutive occurrences of this seam. Such occurrences persist
at the inflated boundaries. Cutting the inflated blocks at all marker
occurrences is exactly the induced substitution. The return-block coding
intertwines `Φ^m` with that substitution and preserves the translation
flow with the inherited lengths. Stable equivalence along all iterates
is equivalent to stable equivalence along the positive multiples of `m`,
by uniform continuity of the finitely many intervening powers on the
compact hull. Thus the coding and passage to a power preserve `≈_s`.
The proper version forces its border, and the one-dimensional rank-two
flow has no almost automorphic subaction in the sense of Barge's Theorem
12. This theorem gives a proper Pisot stack substitution with dilation
`β^m` and `g_max = g_s ∘ q`. Proposition 19 gives injectivity of `q*` in
first rational cohomology.

The rank of `Ω_s` is two. Each maximal equicontinuous fibre of `Ω` has a
strict pair by (Z4) and surjectivity of `π₁`. The two tilings of a strict
pair have no eventual common tile under any translation, so they are in
different `≈_s` classes and their images under `q` are distinct. On the
other hand a fibre of size two in `Ω` maps onto the corresponding fibre
of `Ω_s`, since `q` is onto and `g_max = g_s ∘ q`. The minimum fibre
cardinality is therefore two, which is the coincidence rank by Barge's
Theorem 4. The number `β^m` has degree three since its Pisot conjugates
have modulus below one and the cubic field has prime degree. Its norm
is `(det M)^m`, which is odd.

The factor bound gives `dim H¹(Ω_s;ℚ) ≤ 4`. Barge's Theorem 22 applied to
the stack substitution gives `dim H¹(Ω_s;ℚ) ≥ 5`. This excludes the
assumed strict system under the stated odd-determinant rank-two
hypotheses.

## Verification boundary

The cohomology evaluation, its surjectivity, and the passage to the
stack quotient are written mathematics using the sources above. The
finite grouping calculation is checked by `grouped_cycle_entries` in
[PeriodicPartnerDirectional](../proof/PscVerif/PscVerif/PeriodicPartnerDirectional.lean).
The scoped periodic-partner gate also checks the preceding finite covering
proof, the singleton-fibre convergence lemma and the local branch laws.
The exact unit-corpus replay and independent literal-ray checks exercise
the asymptote premises and controls. They supply no strict system and
are independent of the cohomological contradiction.

This argument leaves even determinant and coincidence ranks above two
outside its exclusion. It does not settle universal C4 or PSC.
