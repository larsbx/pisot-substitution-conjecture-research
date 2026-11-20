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

**Origin vertex, left** (`agree_left_of_vertex`). The mirror: tilings with a vertex at `0`
that agree before a common vertex `a ≤ 0` agree on every tile meeting `(−∞, 0)`.

**Counts are matrix columns** (`count_iterWord`). The letter counts of `σⁿ(a)` are column `a`
of `Mⁿ`, where `M = incidence` counts letters of `σ(a)`. Hence `M^j ≡ 0 (mod 2)` and `0 < p`
make every image of `σ^(jp)` even (`even_of_nilpotent`).

On the hull the hypothesis is stated directly as nilpotence modulo two. Take
`M^j ≡ 0 (mod 2)` and tilings fixed by `Φᵖ` with `0 < p`. Then two-sided agreement forces
equality (`hull_eq_of_two_tails_of_nilpotent`). Origin-vertex tilings share their whole
right, resp. left, ray once they agree beyond, resp. before, a common vertex
(`hull_rays_of_nilpotent`).

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

For periodic vertex seams of the original hull at nilpotent incidence modulo two, exact
right-tail agreement forces agreement on `(0, ∞)`, hence equal first letters. Exact left-tail
agreement forces equal last letters. This is the vertex–vertex part of (NM_V) at
nilpotent incidence. Interior members of `F₀` are not covered: the origin argument needs
vertices at `0` in both tilings.

## The hard step: one route attempted, and where it stops

The open obligation is the even-determinant rank-two residue: nilpotent incidence modulo
two with a surviving grouped seam square. **It is not discharged here.** The route tried
uses only nilpotence and the strict bigon system `B` of Theorem W. Single prover, no
verifier.

*Route.* For a balanced pair `(u, v)`, let `δ(u, v)` be the least degree of
`E(u) − E(v)` in the expansion over `𝔽₂` used by the word theorem. Then `δ ≥ 2`, since the
degree-one part is the parity of the Parikh vector. `δ` is finite for `u ≠ v`, by
injectivity of the expansion. Substituting `σ³` raises least degrees at least twofold,
because its images have even counts. Telescoping over the irreducible blocks of
`(σ³u, σ³v)` writes the image difference as a sum of block differences multiplied by
expansions with constant term one. Let `δ₀` be the least `δ` over `B`, and `λ` the
degree-`δ₀` part of the block difference on bigons with `δ = δ₀`, extended by zero. Every
bigon's image vanishes below degree `2δ₀ > δ₀`. This gives the linear condition

```text
λ · N³ ≡ 0 (mod 2)   on the bigon system,   λ ≠ 0,
```

where `N` is the child matrix of `B`.

*Where it stops.* The condition is satisfiable. (W3) gives `χ_M | χ_{N₊}`, and
`χ_M ≡ t³ (mod 2)`, so `N` is singular modulo two. The route needs invertibility of `N`
modulo two, and that premise fails. It cannot be rescued from mod-2 data alone. The square
of Thue–Morse has incidence `≡ 0 (mod 2)` and the child-closed strict bigon system
`{(01, 10), (10, 01)}` (`thueMorseSq_even`, `thueMorseSq_strict_bigons`). Its
characteristic polynomial `t(t − 4)` is reducible and its matrix singular. So an exclusion must use
the irreducible Pisot cubic, not just its reduction modulo two. This agrees with the
algebraic consistency model of the [solenoid note](c4-even-solenoid-2026-11-19.md#non-claims--remaining-gaps),
which reaches the same boundary from the cohomological side.

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
| both tails; origin vertex | `eq_of_two_tails`, `agree_right_of_vertex`, `agree_left_of_vertex` |
| counts and nilpotence | `count_iterWord`, `even_of_nilpotent` |
| nilpotent hull forms | `hull_eq_of_two_tails_of_nilpotent`, `hull_rays_of_nilpotent` |
| control | `thueMorseSq_even`, `thueMorseSq_strict_bigons` |
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

1. The open even-determinant obligation is unchanged. It needs a cubic restriction on the
   twin-vertex readout of the fixed return vectors, or an independent strict-system
   exclusion ([return-seam note](c4-return-seam-boundary-2026-11-20.md#non-claims--remaining-gaps)).
   The literal lifts of the quotient pair need not agree on both tails, so this module does
   not reach them. C4 and PSC remain open.
