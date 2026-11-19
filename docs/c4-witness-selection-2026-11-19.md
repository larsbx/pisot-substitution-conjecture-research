# Witness selection under (NM_V): the branch reduction and its residual

**Status:** Written proofs, checked in Lean from explicit local contracts and named
inputs, plus an exact census over the unit corpus. Independent human review is pending.
This addresses gap 1 of the
[periodic-partner extraction](c4-periodic-partner-extraction-2026-11-18.md#non-claims--remaining-gaps).
It **does not close it**. (NM_V) excludes a vertex-type leaf from every failing branch,
and the failing branches reduce to one configuration. The census finds that
configuration inside the zero fibre on (NM_V) specimens with `β₁(ER) = 2`, so (NM_V)
alone cannot select a witness. C4 and PSC remain open; no governed claim changes.

Starting revision: `main@9774624` (merge of #613).
[Source decision](c4-witness-selection-stop-go-2026-11-19.md).

## Setting

As in the [extraction note](c4-periodic-partner-extraction-2026-11-18.md#assumptions-and-hypotheses):
`σ ∈ PIP3`, inflation `Φ` with expansion `β > 1`, realization `h` with `hΦ = Ah` and
finite fibres, zero fibre `F₀ = h⁻¹(0)`, strict component `Z` with (Z1)–(Z4). A
*witness* is `(T, S, U)` with `(T,S), (T,U) ∈ Z`, `S ≠ U`, and `S, U` asymptotic.
Round-4 [Lemma C(c)](c4-round4-2026-11-17.md#33-proofs) supplies one wherever `π₁` is
not locally injective; under (NM_V), odd determinant and rank two this is everywhere
([UP′](c4-unique-partner-exclusion-2026-11-18.md)).

Orient right: `S, U` agree on `[y, ∞)` and the tiles ending at `y` carry letters
`b ≠ c` (the *branch* at `y`). `g = g_R` is the last-letter map. The left case is the
mirror with `g_L`, by the reflection of
[`PeriodicPartnerReflection`](../proof/PscVerif/PscVerif/PeriodicPartnerReflection.lean).

The *collapsed pair* of `g` is the unordered pair `{b, c}`, `b ≠ c`, with `g b = g c`.

## Results

**Lemma K (three letters).** Let `g : {0,1,2} → {0,1,2}` have at least two periodic
letters. Then `g^2 b = g^2 c` with `b ≠ c` implies `g b = g c`, and `g` has at most one
collapsed pair. Without the hypothesis both fail (the constant map merges every pair).

**Lemma A′ (location).** A periodic pair's branch satisfies `y ≥ 0`, and `y = 0` when its
letters never merge.

**Lemma V (vertex leaves branch at the origin).** Assume (R4), (E1) and (NM_V). If a
periodic asymptotic pair has a leaf with a vertex at the origin, its branch is at `0`.

**Theorem S (branch reduction).** Assume the inputs of Lemmas P and V, and that `g`
has two periodic letters. Every witness has a translate `(T′, S′, U′)` that is fixed by
a common positive power of `Φ`, keeps both links in `Z`, and has a branch `(y, b, c)`
in exactly one of two cases:

| Case | Branch | Endpoint test | Leaves at the origin | Fibre |
| --- | --- | --- | --- | --- |
| (A) | `y = 0` | `g² b ≠ g² c` | both end a tile at `0` (vertex-type) | `h(T′) = h(S′) = h(U′) = 0` |
| (B) | `y > 0` | `g² b = g² c`, indeed `g b = g c`: `{b, c}` is the collapsed pair | neither has a vertex at `0` (interior-type) | common periodic point `q`, not identified |

When `g` is injective nothing merges, so (B) is empty even without (NM_V); this is
round-4 Lemma A.

### Proofs

*Lemma K.* After two steps every letter of a three-letter map lies on a cycle
([`endpoint_period_six`](../proof/PscVerif/PscVerif/PeriodicPartner.lean)). With two
periodic letters the image of `g` has at least two elements. If it has three, `g` is a
bijection and nothing merges. If it has two, both are periodic and `g` permutes them,
so the only merge is the fibre of `g` over one of them. Lean decides both statements
over all 27 maps.

*Lemma A′.* The pair is fixed by `Φⁿ`, which sends agreement on `[y, ∞)` to agreement on
`[βⁿ y, ∞)`. If `y < 0` then `βⁿ y < y`, and the letters at `y` would agree. If the
letters never merge, `Φⁿ` sends the branch at `y` to a branch at `βⁿ y`; branch
uniqueness gives `y = βⁿ y`, so `y = 0`.

*Lemma V.* Let `S` have a vertex at `0`. By (R4) `S ∈ F₀`; by (E1) `U ∈ F₀`. (NM_V)
makes `U` vertex-type with the same right letter `a`. Two periodic tilings that both start
a tile `a` at `0` carry the substituted ray of `a` (`VertexLaws.periodic_ray`), so they
agree on `[0, ∞)`. If `y > 0` the letters at `y` would then agree. With Lemma A′,
`y = 0`. The same argument with the roles exchanged handles a vertex at `U`.

*Theorem S.* Lemma P gives the periodic translate. Take its first branch `(y, b, c)`. If
`g² b ≠ g² c`, the letters never merge
([`endpoint_persistent_iff`](../proof/PscVerif/PscVerif/PeriodicPartner.lean)), so
`y = 0` by Lemma A′, both leaves end a tile at `0`, (R4) puts them in `F₀`, and (Z4)
puts `T′` there. If `g² b = g² c`, then `y ≠ 0`, since a branch at `0` of a periodic
pair has persistent letters. Hence `y > 0`. Lemma V excludes a vertex at either leaf,
and Lemma K gives `g b = g c`. ∎

### What (B) is, and what it is not

(B) is a periodic pair of **interior** leaves branching on the collapsed pair, with
their common partner in the same periodic fibre `q`. Two sub-cases remain:

- **(B₀) `q = 0`.** The triple still lies in `F₀`; only vertex type is lost. Gap 2's
  zero-fibre input is available, but the leaves are interior members.
- **(B₁) `q ≠ 0`.** A periodic fibre that is not the zero fibre.

Lemma E is not contradicted: its branch-normalized pair lies outside `F₀` exactly in
(B), while the unnormalized periodic pair of (B₀) is in `F₀`.

## The residual on the corpus

`kernel/nmv_census.mojo` now reports every pair of **distinct interior members of `F₀`
that are asymptotic** on a side. That is (B₀) at the level of pairs: Theorem S forbids a
vertex-type leaf there, so these are the only zero-fibre pairs that can carry a
(B₀) branch. The decision is the exact one of
[`psc.zero_fibre_asymptotes`](../kernel/psc/zero_fibre_asymptotes.mojo); every cap raises.

| Count | Value |
| --- | --- |
| domain (unit, two periodic letters for both endpoint maps) | 936 |
| members with an interior–interior asymptote in `F₀` | 36 |
| of those, in scope (`β₁(ER) ≥ 2`, where (NM_V) holds throughout) | **12** |
| residual pairs whose origin tiles carry that side's collapsed pair | 36 of 36 |
| determinant of the 36 members | `−1` in every case |

Checks alongside:

- **Theorem S consistency.** A residual pair on a side needs a non-injective endpoint map
  on that side. The census asserts this (`raise` otherwise); it holds throughout.
- **Literal rays.** The regression pins one left and one right in-scope residual pair,
  `01/12/110` (`g_L = (0,1,1)`, pair `(1;1,0,0) ~ (2;1,0,0)`) and `10/200/02`
  (`g_R = (0,0,2)`, pair `(0;1,0,−1) ~ (1;0,1,−1)`). It rebuilds both rays of each from
  the substitution words with literal interior addresses, sharing no code with the
  overlap decision. Tribonacci and `01/122/201` have no residual pair.

**Consequence.** On 12 in-scope specimens, (NM_V) holds and two interior members of `F₀`
are asymptotic. So no argument from (NM_V), (R4) and (E1) alone can exclude (B₀). A
selection theorem, or a contradiction inside (B), must use the strict system: the
links in `Z`, (Z2)'s absence of common tiles, or (W4). The corpus has no strict system,
so these are pairs, not witnesses.

The two last rows of the table are **observations**, not theorems. The census does not
assert them, and nothing here explains them. Pairs in nonzero periodic fibres, which
is (B₁), are outside the census.

## Negative controls

- **(NM_V) is needed for Lemma V.** On `1/012/21` the vertex member `T_(1,2)` and an
  interior member of `F₀` are right-asymptotic, with their branch at `ℓ(z) > 0` and
  `g_R(0) = g_R(2)`
  ([extraction note, controls](c4-periodic-partner-extraction-2026-11-18.md#the-documented-nm_v-failure-101221)).
  A vertex leaf in case (B) therefore occurs without (NM_V). The finite identities are
  in `PeriodicPartnerControls`; the tiling statement is written.
- **Two periodic letters are needed for Lemma K.** `constant_map_merges_all`.
- **Lemma K does not prevent merging.** `collapsed_pair_example`: `g = (0,1,1)` has two
  periodic letters and collapses `{1,2}`. This is the left map of the pinned residual
  specimen `01/12/110`.

## Evidence and replay

[`PeriodicPartnerSelection.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerSelection.lean),
namespace `Psc.PeriodicPartnerSelection`:

| Statement | Lean |
| --- | --- |
| periodic ⇔ `g⁶ p = p` on three letters | `mem_periodicPts_iff_six` |
| Lemma K | `collapse_at_first_step`, `collapsed_pair_unique`, `TwoPeriodicLetters.collapse` |
| Lemma A′ | `branch_nonneg_of_pairPeriodic`, `branch_eq_zero_of_persistent` |
| Lemma V | `branch_eq_zero_of_vertex_leaf` |
| merging ⇒ interior, `y > 0` | `interior_leaves_of_merge` |
| Theorem S | `selection_dichotomy` |
| controls | `constant_map_merges_all`, `collapsed_pair_example` |

Inputs are the structures `RightBranchLaws` and `VertexLaws`, the contract
`BranchExistence`, and the named hypotheses `BDSPeriodicization`, `R4ZeroFibre`,
`AsymptoticSameFibre` (E1) and `NMVRight`. None is an axiom. `VertexLaws` and
`BranchExistence` are discharged on
[`PeriodicPartnerHull`](c4-tiling-hull-realization-2026-11-19.md) in the
[hull-selection note](c4-hull-selection-2026-11-19.md).

```sh
cd proof/PscVerif && lake build PscVerif.PeriodicPartnerSelection
./tools/check_c4_periodic_partner.sh        # fresh clone, all ten periodic-partner modules
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_zero_fibre_asymptotes.mojo)
(cd kernel && pixi run --locked mojo run -I . nmv_census.mojo)
```

Local acceptance is recorded in
[`evidence/witness-selection-2026-11-19`](../evidence/witness-selection-2026-11-19/README.md).

## Non-claims / remaining gaps

1. **(B) is open.** Exclude it for strict witnesses, or carry gap 2 through it. For
   (B₀) gap 2 receives a zero-fibre triple with interior leaves; for (B₁) a triple in a
   nonzero periodic fibre. The census shows (B₀) cannot be excluded by (NM_V) alone.
2. **Contracts on the hull.** `VertexLaws` and `BranchExistence` are local but are not
   yet proved for `PeriodicPartnerHull`. *Update:* both are proved, and Theorem S is
   instantiated on the hull, in the [hull-selection note](c4-hull-selection-2026-11-19.md).
3. **Census reach.** Unit corpus only, zero fibre only, pairs only. The two
   observations (collapsed origin letters, determinant `−1`) are unexplained.

No assertion here makes (NM_V) universal, excludes a strict system, or changes the
status of C4 or PSC.
