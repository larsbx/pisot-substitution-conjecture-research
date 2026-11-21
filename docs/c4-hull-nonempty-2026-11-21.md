# The legal hull is nonempty for every census member

**Status:** Lean proves that the legal two-sided hull of every length substitution on a finite
nonempty alphabet with `1 < β` is nonempty. In particular it is nonempty for every PIP3 member,
for each of the 4,554 census specimens (alongside their derived `PisotData`), and for
Tribonacci. This closes gap 5 of the
[hull note](c4-tiling-hull-realization-2026-11-19.md#non-claims-and-remaining-gaps). No
external theorem is used. Independent human review is pending. C4 and PSC remain open;
no governed claim changes.

Starting revision: `main@8bbc05b8`. [Source decision](c4-hull-nonempty-stop-go-2026-11-21.md).

## Work shown

Module [`PeriodicPartnerHullNonempty.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerHullNonempty.lean).

| Step | Lean | Argument |
| --- | --- | --- |
| words | `subst`, `subst_iterate_append`, `sum_subst_iterate` | `σⁿ(uv) = σⁿ(u)σⁿ(v)`; `ℓ(σⁿ w) = βⁿ ℓ(w)` |
| endpoints | `subst_iterate_head`, `subst_iterate_last` | `σⁿ(c)` begins with `g_Lⁿ c` and ends with `g_Rⁿ c` |
| placement | `place_append`, `inflate_place`, `inflate_iterate_singleton` | `inflateⁿ {(c, x)}` is `σⁿ(c)` laid out from `βⁿ x` |
| two letters | `exists_two_letters` | if every image were one letter, `ℓ(g_Lⁿ c) = βⁿ ℓ(c)`; a repeat on the finite orbit forces `βⁱ = βʲ`, impossible for `β > 1` |
| periodic pair | `exists_periodic_iterate` | pigeonhole on `n ↦ Fⁿ p` for `F = (g_R, g_L)` on `α × α` |
| seed | `hull_nonempty` | with `σ(c) = x y r`, `b = g_Rᵐ x`, `a = g_Lᵐ y` periodic of period `k`: the patch `{(b, −ℓ b), (a, 0)}` tiles `[−ℓ b, ℓ a)` and lies in its `k`-fold inflation (last tile of `σᵏ(b)`, first tile of `σᵏ(a)`). It is the junction `b.a` of `σᵐ⁺¹(c) = σᵐ(x) σᵐ(y) σᵐ(r)`, so it is legal. `hull_nonempty_of_seed` concludes. |
| PIP3 | `PIP3.hull_nonempty` | `1 < β` is a PIP3 field |
| census | `census_hull_nonempty` | composes with `PeriodicPartnerSpectralCensus.census` |
| Tribonacci | `tribonacci_hull_nonempty` | direct |

Primitivity and the Pisot property are not used. Only `1 < β`, nonempty images and positive
lengths enter.

## Replay

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

## Non-claims / remaining gaps

The hull note's other gaps are unchanged.

- Recognizability, BDS and finite fibres are still imported.
- The strict joining relation for Lemma P is not instantiated on the hull.
- The left-hand reflection consumers are not instantiated on the hull.

Continuity of the realization and the Barge–Diamond binding are the subjects of open
PRs #627 and #624. Witness selection under (NM_V) and the global rank-two contradiction are
untouched. Nonemptiness says nothing about minimality or compactness of the hull.
