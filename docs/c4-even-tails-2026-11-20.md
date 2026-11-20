# Even incidence on literal tilings: the tail argument in Lean

**Status:** Lean proof, standard axioms only. Independent human review is pending. This
discharges the written interval argument of the
[literal-defect note](c4-literal-periodic-defect-2026-11-20.md#consequences-for-the-original-tilings).
It excludes no strict system on its own, and no governed claim changes. Starting revision:
`origin/main@796be5a`.

## Source decision

| Source | Used for |
| --- | --- |
| [Literal-defect note](c4-literal-periodic-defect-2026-11-20.md), `eq_of_common_padding` | the word theorem under even image counts |
| [Hull note](c4-tiling-hull-realization-2026-11-19.md), `PeriodicPartnerHull` | tile sets with half-open supports, `place`, `inflate`, the hull |

No external source is imported. **Decision: proceed.** The target is a formal check of a
recorded written deduction; no novelty is claimed.

## Statements

Let `τ` be a substitution whose images have even letter counts, with `1 ≤ β`, over a finite
alphabet. Tilings are sets of labelled half-open tiles covering the line exactly once. They
need not be legal, and no Pisot or primitivity hypothesis enters.

**Both tails** (`eq_of_two_tails`). Let `S`, `U` be `τ`-fixed tilings with common vertices
`a ≤ 0 ≤ b`. If they agree on every tile meeting `(−∞, a)` and every tile meeting `(b, ∞)`,
then `S = U`.

**Origin vertex** (`agree_right_of_vertex`). If `S`, `U` are `τ`-fixed, both have a vertex at
`0`, and they agree beyond a common vertex `b ≥ 0`, then they agree on every tile meeting
`(0, ∞)`.

On the hull (`hull_eq_of_two_tails`, `hull_agree_right_of_vertex`), take tilings fixed by
`Φⁿ` and require even counts in the images of `σⁿ`. When `M^j ≡ 0 (mod 2)` and `p` is a
common period, `n = jp` qualifies, since the image counts of `σⁿ` are the columns of `Mⁿ`.
That identification of counts with matrix columns is standard and is not formalized here.

## Proof structure

1. **Words from tile sets.** Between two vertices of a tiling lies a placed word
   (`exists_word`, by induction on the gap measured in minimal tile lengths). Two placed
   words from one point with equal total length are equal (`word_unique`).
2. **Inflation.** A placed word inflates to the placed image word (`place_flatMap_subset`).
   An inflation-fixed tiling has a vertex at `βa` when it has one at `a` (`vertex_inflate`).
3. **Decomposition** (`inflate_word`). With `a ≤ 0 ≤ b`, the image of the word `u` on
   `[a, b]` equals `l ++ u ++ r`, where `l`, `r` are the words on `[βa, a]` and `[b, βb]`.
4. **Common pads.** Agreement on the tails makes `l` and `r` the same in both tilings
   (`pad_eq`). In the origin case `l` is empty. The word theorem gives `u = v`.
5. **Conclusion.** A tile in the middle is the tile of the common word covering its start
   (`mem_of_word`). In the origin case a tile meeting `(0, ∞)` cannot start before `0`,
   since it would then share the point `0` with the tile starting there.
6. **Powers.** `LengthSubst.pow k` has images `σ^k(a)` (`iterWord`), the same lengths and
   dilation `β^k`. Its inflation is the `k`-th iterate (`inflate_pow`). This is what lets the
   hull statements use a common period.

## Consequence

For periodic vertex seams of the original hull at even nilpotent incidence, exact
right-tail agreement forces agreement on `(0, ∞)`, so equal first letters. The left version
follows by reflection and is not instantiated. This is the vertex–vertex part of (NM_V) at
nilpotent incidence. Interior members of `F₀` are not covered: the origin argument needs
vertices at `0` in both tilings.

## Controls

Period doubling `0 → 01, 1 → 00` satisfies both padding equations with distinct words. Its
counts are odd, so the evenness hypothesis cannot be dropped; this is the existing
`period_doubling_padding_control`.

## Lean

[`PeriodicPartnerEvenTails.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerEvenTails.lean),
namespace `Psc.PeriodicPartnerEvenTails`.

| Statement | Lean |
| --- | --- |
| word between vertices; uniqueness | `exists_word`, `word_unique` |
| inflation of placed words | `place_flatMap_subset`, `mem_place_flatMap`, `vertex_inflate` |
| decomposition | `inflate_word` |
| both tails; origin vertex | `eq_of_two_tails`, `agree_right_of_vertex` |
| powers | `LengthSubst.pow`, `inflate_pow` |
| on the hull | `hull_eq_of_two_tails`, `hull_agree_right_of_vertex` |

```sh
cd proof/PscVerif && lake build PscVerif.PeriodicPartnerEvenTails
lake env lean PeriodicPartnerAudit.lean
cd ../.. && ./tools/check_c4_periodic_partner.sh
```

Locally the module builds without warnings, and the periodic-partner audit reports only
`propext`, `Classical.choice` and `Quot.sound`. The isolated gate's receipt must come from CI.

## Non-claims / remaining gaps

1. The identification of image counts with columns of `Mⁿ` is not formalized.
2. The left-hand origin version is not instantiated.
3. The open even-determinant obligation is unchanged. It needs a cubic restriction on the
   twin-vertex readout of the fixed return vectors, or an independent strict-system
   exclusion ([return-seam note](c4-return-seam-boundary-2026-11-20.md#non-claims--remaining-gaps)).
   The literal lifts of the quotient pair need not agree on both tails, so this module does
   not reach them. C4 and PSC remain open.
