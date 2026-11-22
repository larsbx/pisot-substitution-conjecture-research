# Hull flow, inflation homeomorphism and the bundled criterion: source decision

**Status:** Source decision for three open items of the
[family Lean roadmap](c4-family-lean-dynamical-roadmap-2026-11-21.md):
- F2 "action laws" (open, small);
- the recognizability negative control `a ↦ aa`;
- F3 "one criterion definition".

Starting revision: `main@968fabde`, with this branch's Hausdorff, nonempty-hull and
left-consumer modules. No governed claim changes.

## Exact targets

1. `AddAction ℝ (LocalHull S)` by translation, `ContinuousVAdd`, and
   `inflate (t +ᵥ T) = (β t) +ᵥ inflate T`.
2. On finite alphabets, bijective `inflateH` gives a homeomorphism of `LocalHull S`. This is
   the topological form of recognizability. The σₖ instance follows from the proved
   `inflateH_bijective`.
3. `a ↦ aa`: the hull is nonempty, but inflation is not injective.
4. `FullFactorCriterion s T`, its equivalence with `TerminatesWithCoincidence` for blocks, the
   family instance, the bundled spectral inputs, and the identity control.

## Sources and inputs

| Input | Status |
| --- | --- |
| Compact ↦ Hausdorff continuous bijection is a homeomorphism | Mathlib `Continuous.homeoOfEquivCompactToT2`. |
| Compactness of `LocalHull S` | `PeriodicPartnerRealizationOnto.localHull_compactSpace`, on main. |
| Hausdorffness of `LocalHull S` | `PeriodicPartnerLocalHausdorff`, this branch. |
| σₖ bijectivity | `ParameterFamilyRecognizability.inflateH_bijective`, on main. |
| Criterion equivalence | `TerminationFactors.terminates_iff_finite_factors_and_coincidences`, on main. |

No external mathematics is imported.

## Decision

**Proceed.** Keep the σₖ corollaries in family modules audited by the family gate. Keep the
generic modules in the periodic-partner closure. Split the census corollaries of hull
nonemptiness into their own module, so that the generic theorem does not pull the census
into the family gate.
