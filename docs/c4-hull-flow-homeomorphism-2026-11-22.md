# The hull flow, inflation as a homeomorphism, and the bundled criterion

**Status:** Lean closes three open items of the
[family Lean roadmap](c4-family-lean-dynamical-roadmap-2026-11-21.md):
- **F2 action laws:** the ordinary hull is a continuous `ℝ`-set, and inflation intertwines it.
- **Inflation homeomorphism:** bijective inflation is a homeomorphism of the ordinary hull. For
  σₖ this holds for every `k ≥ 1`.
- **F3:** one `FullFactorCriterion` structure, equivalent to termination with coincidence and
  instantiated for σₖ, `k ≥ 2`.

The `a ↦ aa` negative control shows that bijectivity is a genuine hypothesis. No external
input is used. Independent human review is pending. C4 and PSC remain open; no governed claim
changes.

Starting revision: `main@968fabde`.
[Source decision](c4-hull-flow-homeomorphism-stop-go-2026-11-22.md).

## Work shown

| Lean | Module | Statement |
| --- | --- | --- |
| `instance : AddAction ℝ (LocalHull S)`, `instance : ContinuousVAdd ℝ (LocalHull S)` | [`PeriodicPartnerLocalAction`](../proof/PscVerif/PscVerif/PeriodicPartnerLocalAction.lean) | `t +ᵥ T = translate t T`; the laws are `translate_zero`, `translate_translate`; continuity is `continuous_translate` |
| `inflate_vadd` | same | `inflate (t +ᵥ T) = (β t) +ᵥ inflate T` |
| `inflateHomeomorph`, `inflateHomeomorph_apply` | same | on a finite alphabet, `Bijective inflateH` gives `LocalHull S ≃ₜ LocalHull S`. It is a continuous bijection from a compact space (`localHull_compactSpace`) to a Hausdorff one (`PeriodicPartnerLocalHausdorff`) |
| `doubling`, `doubling_translate_one`, `doubling_not_injective` | same | `a ↦ aa`: every tiling is `1`-periodic, so `T` and `T − ½` have the same inflation; the hull is nonempty by `hull_nonempty` |
| `ParameterFamilyFlow.inflateHomeomorph`, `inflate_isHomeomorph` | [`C4ParameterFamilyFlow`](../proof/PscVerif/PscVerif/C4ParameterFamilyFlow.lean) | σₖ, `k ≥ 1`, from `inflateH_bijective` |
| `Psc.FullFactorCriterion`, `terminates_iff_fullFactorCriterion` | [`C4FullFactorCriterion`](../proof/PscVerif/PscVerif/C4FullFactorCriterion.lean) | the bundled `finite`/`productive` criterion is `TerminatesWithCoincidence` for blocks |
| `family_fullFactorCriterion`, `spectral_criterion_inputs_bundled` | same | σₖ at `01/10`, `k ≥ 2`; the spectral inputs with the criterion as one conjunct |
| `identity_not_fullFactorCriterion` | same | `finite` without `productive`: the identity substitution |

The census corollaries of hull nonemptiness moved to
[`PeriodicPartnerHullNonemptyCensus`](../proof/PscVerif/PscVerif/PeriodicPartnerHullNonemptyCensus.lean), so
the generic theorem no longer depends on the census.

The family endpoint audit now also pins four endpoints:
- `terminates_iff_fullFactorCriterion` (universe-polymorphic);
- `family_fullFactorCriterion`;
- `identity_not_fullFactorCriterion`;
- `inflate_isHomeomorph`.

It also inventories the four new owned modules (39 endpoints, 27 modules).

## Non-claims / remaining gaps

- No productive-but-infinite control for the `finite` field is formalized. The roadmap's
  non-Pisot control is not in Lean.
- F4(c) and F5 of the family roadmap are unchanged. The symbolic-shift transfer remains open.
- `spectral_criterion_inputs` keeps its unbundled form for existing consumers. The bundled form
  is an additional theorem.
- Recognizability for general `LengthSubst` remains an input; only σₖ has it proved.
