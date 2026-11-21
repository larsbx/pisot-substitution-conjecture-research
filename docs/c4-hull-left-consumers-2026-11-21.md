# Left-hand periodic-partner consumers on the legal hull

**Status:** Lean instantiates the left-oriented (reflected) branch consumers on the concrete
legal hull. This closes gap 6 of the
[hull note](c4-tiling-hull-realization-2026-11-19.md#non-claims-and-remaining-gaps). The
left local laws, the left common patch, the left ray/metric correspondence, and the
equivalence of (R4) at origin starts and origin ends are proved. The only new external
input is the left BDS statement, `LeftBDS`. Independent human review is pending. C4 and
PSC remain open; no governed claim changes.

Starting revision: `main@7de25513`.
[Source decision](c4-hull-left-consumers-stop-go-2026-11-21.md).

## Work shown

Module [`PeriodicPartnerHullLeft.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerHullLeft.lean).

| Lean | Content | External input |
| --- | --- | --- |
| `AgreeLeft`, `StartsAt` | tiles meeting `(-∞, y)`; `(b, y) ∈ T` | — |
| `leftBranchLaws` | all seven fields of `LeftBranchLaws inflateH translate β g_L AgreeLeft StartsAt` | none |
| `left_common_patch`, `reflected_common_patch` | common left ray at `0` plus common start `a` give agreement of radius `ℓ a` | none |
| `leftAsymptotic_iff_metric`, `left_bds_ray_iff_metric` | exact left rays coincide with metric asymptoticity under `t ↦ translate (-t)`, and the two forms of left BDS coincide | none |
| `startsAt_of_endsAt` | a tile ending at `y` is followed by one starting at `y` | none |
| `endsAt_of_startsAt` | on a finite alphabet, a tile starting at `y` is preceded by one ending at `y`. Cover `y − m/2`, with `m` the minimum length; a gap before `y` would contain a tile start whose tile reaches past `y`. | none |
| `r4_startsAt_iff_endsAt` | (R4) at origin starts is (R4) at origin ends | none |
| `hull_left_collapse_of_merge` | left Lemma M | none |
| `hull_left_two_step_iff_pairPeriodic` | `g_L²` test ⇔ joint periodicity | `LeftBDS` |
| `hull_left_two_step_iff_zero_fibre`, `hull_left_branch_triple_dichotomy` | left Lemma E and the left triple dichotomy | `LeftBDS`, `PublishedInputs` (its end-form `r4` is converted) |

Every compiled declaration uses only `propext`, `Classical.choice` and `Quot.sound`.

## Non-claims / remaining gaps

- `LeftBDS` is imported, like its right-hand mirror. It is not derived from the right form.
- The hull note's gaps 2 and 4 are unchanged:
  - recognizability, BDS and finite fibres are still imported;
  - the strict joining relation for Lemma P is not instantiated.
- Witness selection under (NM_V) and the global rank-two contradiction are untouched.
