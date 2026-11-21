# Left-hand consumers on the legal hull: source decision

**Status:** Source decision for gap 6 of the
[hull note](c4-tiling-hull-realization-2026-11-19.md#non-claims-and-remaining-gaps): the
reflected consumers of `PeriodicPartnerReflection` are not instantiated on the hull.
Starting revision: `main@7de25513`. No governed claim changes.

## Exact target

On the concrete hull, define the left ray predicate `AgreeLeft` (tiles meeting `(-∞, y)`)
and the start predicate `StartsAt` (`(b, y) ∈ T`). Prove `LeftBranchLaws` for
`inflateH`, `translate`, `β` and the first-letter map `g_L`, together with the left common
patch. Then instantiate the reflected two-step, zero-fibre, collapse and dichotomy
consumers.

## Sources and inputs

| Input | Status here |
| --- | --- |
| BDS periodicization for **left**-asymptotic pairs | Barge–Diamond–Swanson's theorem is stated for asymptotic pairs without an orientation; the [#612 source decision](c4-periodic-partner-formalization-stop-go-2026-11-19.md) records it. It is a separate field, `LeftBDS`, in its metric form. It is **not** derived from the right form: reflecting tilings changes the substitution to its reversal. |
| (R4) | Already a field of `PublishedInputs`, and proved for the constructed realization, at tiles **ending** at `0`. It is to be converted, not re-imported: on a finite alphabet a tile starts at `0` iff one ends there. |
| Local laws, common patch, ray/metric correspondence | Elementary facts about literal tile sets, to be proved. |

No new source is cited. Both published inputs are those already recorded.

## Decision

**Proceed.** The left BDS input stays named, and everything else is proved.
