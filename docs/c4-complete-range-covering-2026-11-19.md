# Covering exclusion on the complete two-by-three eventual range

Base revision `3b5a8a9ca3ac01c6345b157beedbcf061eb4bc5b` includes #615
and the witness-selection evidence repair in #616.

## Literature decision

The remaining case in #615 is a strict joining at a complete `K_{2,3}` or
`K_{3,2}` eventual range. The first target is to decide whether its top-track
projection can be a covering when only the three-letter endpoint map is
injective. The second target is to instantiate the two local contracts of
the witness-selection theorem on the legal tiling hull and choose the
direction of a strict witness before periodicization.

| Source | Scope used in this argument |
| --- | --- |
| [Barge–Diamond (2008), §3 and Theorem 4](https://arxiv.org/pdf/math/0702669) | Legal periodic seams are the edges in the eventual range. The cohomology exact sequence gives the rank contribution of that graph. |
| [Baker–Barge–Kwapisz (2006), §3 and Theorem 4.2](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | The geometric realization is equivariant and has finite fibres. At coincidence rank two there are fibres of size two. Use the origin normalization already specified in round 3, (R4). |
| [Barge (2015), Theorem 22](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | The odd-norm lower bound at coincidence rank two is an input to the corollary. The covering argument itself is independent of the bound. |
| [Barge (2015), §3 and Lemma 13](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) and [Theorem W](c4-rank-two-wall-2026-11-16.md#62-statement) | Two partners of one tiling have dense eventual coincidence, used here through (W4). Uniqueness of partners in Barge's quotient uses triviality of the stack relation and does not transfer to the original hull. |
| [Barge–Diamond–Swanson (2009), §2](https://arxiv.org/pdf/0804.0930) | Periodicization remains an input when applying the geometric branch alternative to an arbitrary witness. The two local hull contracts use half-open tile supports and elementary order geometry. |
| [Round 4, Lemmas A, C and L](c4-round4-2026-11-17.md#33-proofs), [UP′](c4-unique-partner-exclusion-2026-11-18.md#theorem-up-coverings), [#615](c4-nmv-eventual-range-2026-11-19.md) | Covering lifts exact rays and separates asymptotic partners. The injective endpoint direction of Lemma A locates a periodic branch at zero. UP′ requires both directions of (NM_V), while #615 supplies complete graphs in the remaining case. |

The comparison controls are the two-by-two Thue–Morse double cover and the
rank-two eventual ranges from #615 where (NM_V) fails. A finite model of
partners can have repeated degrees and asymptotic siblings when the covering
hypotheses are dropped, as in the [extraction controls](c4-periodic-partner-extraction-2026-11-18.md#negative-controls).
Proceed on the complete two-by-three range using only isolation of interior
tilings on the injective endpoint side and the lifting and uniqueness
consequences of a covering. For directional selection, use one strict fibre
with exactly one partner, supplied by (W2) at coincidence rank two, and
one with multiple partners. This permits unbounded return times on either
tail and allows the first-disagreement cut of Lemma C(c) to be taken on a
specified side. Keep the topological and realization inputs explicit in
the Lean interfaces.

For the remaining strict contradiction, apply (W4) to the two selected
vertex leaves before asking for the type of their common partner. The
target is the noncoincidence relation on the periodic seam tilings, using
the legal common-vertex pair (Z3) as a disjointness constraint. The
[Barge–Diamond endpoint eliminator](c4-barge-diamond-endpoint-eliminator.md)
already handles an endpoint map that is a three-cycle. The target here is
the full relation on the complete two-by-three range. The finite partner
model in the extraction note allows a fork without a triangle, so a seam
classification needs a separate argument to constrain membership in `Z`.

## Work shown

### Assumptions and hypotheses

Let `σ ∈ PIP3` and suppose `Z` is a swap-invariant strict component with the
round-4 hypotheses. Its projection `π₁` is onto by minimality. Strict
partners are in the same normalized geometric fibre and share no labelled
tile, in particular at level zero. Write `F₀ = h⁻¹(0)`. By (R4), this finite
set consists of periodic tilings, with one vertex tiling `T_(b,a)` for each
edge of `ER`. Tilings in a row share the left ray from zero. Tilings in a
column share the right ray from zero.

Orient `ER = K_{2,3}` with two last letters on the left and three first
letters on the right. The map `g_L` is a permutation because all three
letters are periodic. It is the map that controls distinct **left**-asymptotic
periodic tilings in Lemma A. Its injectivity forces their branch to be at
zero, so each is vertex-type by (R4). Reflect the argument for `K_{3,2}`.

### Derivation / reduction

#### The complete range forbids a covering

Suppose `π₁` is a covering. By Lemma L, a left or right ray shared by top
tilings yields a matching of their partners along the corresponding
direction. By Lemma C(b), distinct partners of one tiling cannot be
asymptotic on either side.

1. **Every partner of a vertex tiling is a vertex tiling.** Let `U` be a
   partner of `T_(b,a)`, and choose another column `a′` in the same row.
   Lemma L gives a partner `U′` of `T_(b,a′)` left-asymptotic to `U`.
   Both partners belong to `F₀` because their top tilings do. If `U = U′`,
   swap-invariance gives `U` the two distinct left-asymptotic partners
   `T_(b,a)` and `T_(b,a′)`, contrary to Lemma C(b). Therefore `U ≠ U′`.
   Injectivity of `g_L` makes their left-asymptotic branch an origin seam,
   so `U` is vertex-type.

2. **Each vertex tiling has exactly one partner.** Existence follows from
   surjectivity. Its partner is in the opposite row, since tilings in the
   same row share a left ray and hence share tiles. All possible partners in
   the opposite row are left-asymptotic to one another, so Lemma C(b) gives
   uniqueness. By swap-invariance the resulting map on the six seams is
   involutive. Write its column maps as `f` from row zero to row one and
   `g` from row one to row zero. They are inverses. Both change the column
   because tilings in the same column share a right ray. A derangement on
   three columns is a three-cycle, so `g² = f`.

3. **Right ray lifting contradicts a strict link.** Fix a column `x` and
   set `a = g(x)`. The two top tilings in column `a` agree on the right.
   Their unique partners must also be right-asymptotic by Lemma L. These
   partners are in row one at column `f(a) = x` and in row zero at column
   `g(a) = f(x)`. Right-asymptoticity depends only on the right rays of
   vertex tilings, so the vertices in row zero at `x` and row one at `f(x)`
   are right-asymptotic. This is the original strict partner link at
   column `x`, and it would share tiles. This is the contradiction.

Injectivity of the endpoint map on the three-letter side suffices. The proof
applies at either determinant parity whenever there is a symmetric strict
component with this range.

#### Consequence at odd determinant and coincidence rank two

Theorem W supplies swap-invariance for a strict component at coincidence rank
two. Barge's lower bound and the connected eventual-range formula give
`β₁(ER) ≥ 2` at odd determinant. When both sides of (NM_V) hold, apply UP′.
When (NM_V) fails, #615 gives one of the two complete ranges above. The new
argument then also forbids a covering. Thus every such strict component has
`π₁` nowhere locally injective, by round-4 Lemma C, without assuming
(NM_V). In particular `π₁` has a multiple fibre. If every fibre were a
singleton, a continuous bijection from the compact `Z` to the Hausdorff
hull would be a homeomorphism and hence a covering of degree one.

#### Directional extraction from a singleton fibre

Let `Z` be a compact translation-invariant strict component projecting
onto a minimal tiling hull, with (R3) and (Z4). Suppose `π₁` has one
singleton fibre and one multiple fibre. There is a pair of distinct strict
partners agreeing on a left ray, with different tiles starting at its
terminal vertex. There is also a pair agreeing on a right ray, with
different tiles ending at its initial vertex. The common top tiling may
depend on the direction.

To prove the left statement, let the singleton fibre be over `T*`, with
sole lift `(T*, U*)`. Choose two different partners `U,V` of `T` and a
tile of their symmetric difference starting at `x`. By minimality, every
negative tail of the orbit `t ↦ T−t` is dense. Indeed, its negative
limit set is nonempty by compactness and invariant under the whole flow,
so it is the entire hull. The positive limit set gives the corresponding
claim for positive time.

For `t → −∞` along returns to `T*`, both lifted pairs converge to the
sole lift. For any open neighbourhood `O` of that lift, `π₁(Z ∖ O)`
is compact and therefore closed, and it misses `T*`. A sufficiently close
return to `T*` forces every point over that return into `O`. Thus for
each positive integer `n` one can take a return `t_n` with `t_n+n < x`
such that `U−t_n` and `V−t_n` agree exactly on `(-n,n)`. For this
last step use ordinary local tiling convergence: agreement after small
translations on a larger window gives matching labels with displacement
less than the uniform bound (R3). They are fibre-mates by (Z4), so the
matching tiles coincide in the smaller window.

In the original coordinates follow the common tiles to the right from
the window until the first different tile. This happens at a common
vertex `y_n ≥ t_n+n`, no later than `x`. The search is finite for each
`n`, since the alphabet is finite and the minimum tile length is
positive. Translate both pairs by `y_n`. Their top tilings are equal,
their bottom tilings agree on `(-n,0)`, and their tiles starting at zero
have different labels. Take a common convergent subsequence in `Z × Z`,
with fixed different labels at zero. The two limits have the same top
and retain the fixed tiles at zero. To see exact agreement to the left,
local convergence matches each tile on that ray in both approximants
up to errors tending to zero. Its exact matches in the common portions
converge to the same tile. The two limits therefore agree on `(-∞,0)`.
Use far positive returns and follow common tiles to the left to prove
the right statement. These compactness steps use the ordinary tiling
topology. The concrete Lean hull uses the finer exact-agreement
ultrametric for its ray identities.

#### Select the injective direction at odd determinant

At coincidence rank two, (W2) supplies a singleton strict fibre. The
covering exclusion gives a multiple one. Further, `β₁(ER) ≥ 2` implies
that at least one of the endpoint maps is injective. If both were
noninjective, both sides would have at most two periodic letters and
the connected bipartite graph would have `β₁(ER) ≤ 1`.

Use the left witness if `g_L` is injective and the right witness if
`g_R` is injective. By Lemma P the three tilings have a common periodic
translate. Injectivity makes the differing endpoint labels persistent,
so Lemma A puts the branch of the periodic pair at zero. Both leaves
are vertex-type members of `F₀` by (R4). The common partner is also
in `F₀` by (Z4). This closes the origin witness-selection obligation
at odd determinant and coincidence rank two, given the standing strict
component and realization results. In either orientation the two leaves
are distinct and share an exact ray from the origin.

#### Noncoincidence among seams of a complete range

Orient the complete range as `K_{2,3}`. Use the left witness, whose two
leaves start their different right rays with letters `a,b`. For each
periodic first letter `i`, write `ρ_i` for the aligned right ray at zero.
It is independent of the seam's left letter. Let `N(i,j)` mean that
`ρ_i,ρ_j` share no labelled tile at any nonnegative inflation level.
This is a symmetric, irreflexive relation on the three first letters.

By (W4), `ρ_a,ρ_b` have an eventual coincidence on a dense open subset
of the positive half-line, in scaled-back coordinates. Thus
`N(a,i) ↔ N(b,i)` for every `i`. Indeed, a coincidence of `ρ_a,ρ_i`
occurs on an open interval in these coordinates. Intersect it with an
open coincidence interval for `ρ_a,ρ_b` and pass to the larger of the
two levels. A descendant in the intersection is common to all three
rays. Persistence of shared tiles under inflation makes this work at
different levels. Interchanging `a` and `b` gives the converse.

The periodic pair with common origin vertex in (Z3) is a pair of seam
tilings. Strictness gives at least one `N` pair among its right letters.
Consequently, writing `d` for the third first letter, `N` consists
exactly of the two unordered pairs `{d,a}` and `{d,b}`. On the left of
zero there are only the two periodic last letters. Both must occur in
the (Z3) pair, since equal last letters would give a common left ray.
Hence the two distinct left rays are noncoincident at all levels. A pair
of seam tilings is therefore noncoincident exactly when its rows differ
and exactly one of its columns is `d`.

On the six seams this gives two disjoint three-vertex paths. In each
path the centre has column `d` and the leaves lie in the opposite row
with columns `a,b`. They share their left ray. This gives an all-vertex
noncoincident fork in `F₀` even if the original strict witness has an
interior common partner. Membership in `Z` of both links of a seam fork
does not follow from the classification. Even if both links belong to
`Z`, the seam relation itself has no triangle. Reflection gives the
corresponding classification on `K_{3,2}`.

#### Local laws on the concrete hull

The implementation uses the half-open tile supports of
[PeriodicPartnerHull](../proof/PscVerif/PscVerif/PeriodicPartnerHull.lean).

- **Vertex laws.** The tile covering a known right endpoint starts at that
  endpoint, since any earlier start would overlap the ending tile.
  For two periodic tilings sharing a tile that starts at zero, take a common
  period `n`. The `kn`-fold inflations of the shared tile belong to both
  tilings and tile the intervals `[0, β^(kn)ℓ(a))`. These intervals cover
  every positive position. Uniqueness of the covering tile proves exact
  agreement on the right ray.
- **First branch.** For distinct tilings with a common right ray, take the
  supremum `y` of the right endpoints of tiles belonging to exactly one
  tiling. The set is nonempty, and any agreement cutoff bounds it above.
  The two tilings agree beyond `y`. The tile covering `y` is common and
  starts at `y`, since otherwise the common ray would extend to its earlier
  start. On a finite alphabet the positive tile lengths have a positive
  minimum `d`. The tile covering `y−d` ends at `y`. If it ended earlier,
  the next tile would extend past `y` and overlap the known tile starting
  there. This supplies the tiles ending at `y` in both tilings. Their
  labels differ, since a common ending tile would extend agreement to its
  start and contradict the supremum.
- **Witness selection.** The concrete instances discharge `VertexLaws`
  and `BranchExistence` in Theorem S. Separately, whenever a witness is
  found in an injective endpoint direction, `hull_origin_witness_of_injective`
  uses periodicization, the persistent endpoint labels and (R4) to put all
  three translated tilings in `F₀` with branch at zero. This implication
  needs no (NM_V) input.

### Evidence and replay

| Scope | Lean declarations |
| --- | --- |
| The two-by-three covering obstruction from explicit lifting hypotheses | `partner_of_seam_is_vertex`, `partners_of_seam_equal`, `square_inverse_of_derangement`, `covering_impossible` in [PeriodicPartnerCompleteRange](../proof/PscVerif/PscVerif/PeriodicPartnerCompleteRange.lean) |
| Concrete hull instances and their consequences | `branchExistence`, `vertexLaws`, `periodic_branch_at_origin_of_injective`, `hull_origin_witness_of_injective`, `hull_selection_dichotomy` in [PeriodicPartnerHullSelection](../proof/PscVerif/PscVerif/PeriodicPartnerHullSelection.lean) |
| Singleton-fibre convergence, the endpoint bound and the ternary germ split | `tendsto_of_singleton_fibre`, `injective_endpoint_of_large_cycle_rank`, `three_letter_germ_disjointness` in [PeriodicPartnerDirectional](../proof/PscVerif/PscVerif/PeriodicPartnerDirectional.lean) |

The passage from a topological covering to the lifting hypotheses, the
return-time and recentering argument in the ordinary tiling topology, the
application of (W4) to the seam relation, and the odd-determinant corollary
are written deductions. Baker–Barge–Kwapisz
realization, recognizability, BDS periodicization, (R3), (R4), and the
strict-component results are inputs. The general form of Theorem S also
has (E1) and (NM_V) as inputs.

```sh
(cd proof/PscVerif && lake build PscVerif.PeriodicPartnerCompleteRange PscVerif.PeriodicPartnerHullSelection PscVerif.PeriodicPartnerDirectional)
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

### Negative controls

- In the two-by-two Thue–Morse model, complementing both coordinates is
  an involution that changes the row and column and preserves rays in
  the other fibre. The order-three argument requires three columns.
- The `01/210/1021` failure from #615 has the complete two-by-three
  range and the required injective first-letter map. It still has a
  right vertex/interior asymptote. This tests the distinction between
  an asymptote in the zero fibre and a covering of strict partners.
- The #614 interior/interior controls show why an asymptotic pair by
  itself is insufficient to resolve the strict witness problem.

### Non-claims / remaining gaps

The general anchored witness may have an interior common partner. On a
complete range, the four seam links allowed by the noncoincidence pattern
still need a separate membership argument in `Z`. The [stack quotient
follow-up](c4-rank-two-stack-cycle-exclusion-2026-11-19.md) bypasses those
questions at odd determinant and coincidence rank two by bounding the
cohomology of the quotient. Universal C4 and PSC remain open.
