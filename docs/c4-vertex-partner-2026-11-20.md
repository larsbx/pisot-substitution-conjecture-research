# A vertex-type common partner forces a permutation

**Status:** Lean proof, standard axioms only. Independent human review is pending. No strict
system is excluded by this note, and no governed claim changes. Starting revision:
`origin/main@11c15bc`.

## Setting

This is case (A) of [Theorem S](c4-witness-selection-2026-11-19.md#results), on the
[legal hull](c4-tiling-hull-realization-2026-11-19.md), whose local contracts are discharged
in [`PeriodicPartnerHullSelection`](../proof/PscVerif/PscVerif/PeriodicPartnerHullSelection.lean).
The leaves `S`, `U` of a witness branch at `0` with end letters `b ≠ c`. The triple
`(T, S, U)` is `Φⁿ`-fixed. Split by the common partner `T`:

- **(A_v)** `T` has a vertex at `0`, ending a tile `x`;
- **(A_i)** `0` is interior to a tile of `T`.

## Lemma VP

**Lemma VP.** In (A_v), the last-letter map `g_R` is a permutation of the three letters.

*Proof.* (Z2) at level zero says `T` shares no tile with `S` or `U`, so `x ≠ b` and `x ≠ c`.
The letter ending at `0` in a `Φⁿ`-fixed tiling is `g_R`-periodic, by endpoint transport
and endpoint uniqueness. So `x, b, c` are three distinct periodic letters of a map on three
letters, which is then injective. ∎

No determinant hypothesis enters.

**Consequence.** In (A_v), round-4 Lemma A gives right-hand (NM_V) with no further
hypothesis, and case (B) of Theorem S is empty on the right. On a side with a non-injective
`g_R`, every witness falls in (A_i) or (B). This is the converse direction to the
[directional extraction](c4-complete-range-covering-2026-11-19.md), which puts two vertex
leaves in `F₀` on every side with an injective endpoint map.

**Scope.** At odd determinant and rank two the written
[stack-cohomology exclusion](c4-rank-two-stack-cycle-exclusion-2026-11-19.md) already
excludes strict systems. Lemma VP is relevant where that argument does not reach: even
determinant (the [even residue](c4-even-stack-residue-2026-11-19.md)) and coincidence
rank above two.

## Controls

- `two_periodic_not_injective`: two periodic letters do not force injectivity (`g = (0,1,1)`),
  so the third letter is needed.
- The `K_{3,2}` seam model of
  [`PeriodicPartnerControls`](../proof/PscVerif/PscVerif/PeriodicPartnerControls.lean)
  realizes (A_v) at the seam level (`model_asymptotic_copartners`). Lemma VP's conclusion
  holds there, so seam-level data does not exclude (A_v).

## Lean

[`PeriodicPartnerVertexPartner.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerVertexPartner.lean),
namespace `Psc.PeriodicPartnerVertexPartner`:

| Statement | Lean |
| --- | --- |
| periodic origin letter | `periodic_letter` |
| three periodic letters ⇒ injective | `injective_of_three_periodic` |
| Lemma VP, abstract | `injective_of_vertex_partner` |
| Lemma VP, on the hull | `hull_lastLetter_injective_of_vertex_partner` |
| control | `two_periodic_not_injective` |

```sh
cd proof/PscVerif && lake build PscVerif.PeriodicPartnerVertexPartner
lake env lean PeriodicPartnerAudit.lean
cd ../.. && ./tools/check_c4_periodic_partner.sh
```

The module builds locally against the pinned toolchain, and the audit reports only
`propext`, `Classical.choice` and `Quot.sound`. The isolated gate's receipt must come from CI.

## Non-claims

(A_i) and (B) are not excluded. Nothing here concerns the even-determinant residue beyond
the case split. C4 and PSC remain open.
