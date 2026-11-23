import PscVerif.C4FamilyMeasuredRealization
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Uniqueness of the invariant probability on the actual ordinary legal
hull of the literal σₖ family. Invariance under the dense real flow forces
the solenoid marginal to be normalized Haar, and the existing conull
singleton-fibre theorem then determines the hull measure.

Source decision: `docs/c4-family-canonical-measure-2026-11-23.md`.
This specialization retains `k ≥ 2` and makes no universal PSC claim. -/

namespace Psc.C4FamilyInvariantMeasureUniqueness

open Function Filter MeasureTheory Set
open scoped Topology Psc.PeriodicPartnerSolenoidHaar Psc.C4FamilyMeasuredRealization
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize continuous_solenoidRealize
  solenoidRealize_translate)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate)
open Psc.PeriodicPartnerRealization (Solenoid flow continuous_flow)
open Psc.PeriodicPartnerRealizationOnto (denseRange_flow_zero)
open Psc.PeriodicPartnerSolenoidHaar (haar)
open Psc.C4FamilyMeasuredRealization (hullMeasure hullMeasure_eq_of_map)

variable (k : ℕ) (hk : 1 ≤ k)

local notation "G" => Solenoid (geometry k hk)
local notation "X" => LocalHull (geometry k hk)

/-- The compatible histories inherit a countable topological basis from
the countable product of finite-dimensional tori. -/
instance solenoidSecondCountable : SecondCountableTopology G :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

private theorem integral_add_eq_of_flow_invariant
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hμ : ∀ t : ℝ, MeasurePreserving (flow (pisotData k hk) t) μ μ)
    (f : BoundedContinuousFunction G ℝ) (z : G) :
    (∫ y, f (z + y) ∂μ) = ∫ y, f y ∂μ := by
  have hc : Continuous (fun z : G => ∫ y, f (z + y) ∂μ) := by
    have h := (continuous_integral_apply_neg_add (μ := μ)
      (f.continuous.comp continuous_neg)
      (HasCompactSupport.of_compactSpace (fun y : G => f (-y)))).comp continuous_neg
    simpa only [Function.comp_def, neg_add_rev, neg_neg] using h
  have hd := (denseRange_flow_zero (pisotData k hk)).equalizer hc continuous_const
    (funext fun t => by
      change (∫ y, f (flow (pisotData k hk) t 0 + y) ∂μ) = ∫ y, f y ∂μ
      have hm := integral_map (μ := μ) (hμ t).measurable.aemeasurable
        f.continuous.aestronglyMeasurable
      rw [(hμ t).map_eq] at hm
      simpa only [flow, zero_add, add_comm] using hm.symm)
  exact congrFun hd z

/-- Every probability invariant under the actual dense real solenoid flow
is normalized Haar. No ergodicity assumption on this probability is used. -/
theorem solenoidMeasure_eq_haar_of_flow_invariant
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hμ : ∀ t : ℝ, MeasurePreserving (flow (pisotData k hk) t) μ μ) :
    μ = haar (geometry k hk) := by
  let : μ.IsAddLeftInvariant := ⟨fun z => by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hz : Measurable (fun y : G => z + y) := measurable_const.add measurable_id
    rw [integral_map hz.aemeasurable
      f.continuous.aestronglyMeasurable]
    exact integral_add_eq_of_flow_invariant k hk μ hμ f z⟩
  have heq := Measure.isAddInvariant_eq_smul_of_compactSpace μ (haar (geometry k hk))
  have hc := congrArg (fun m : Measure G => m univ) heq
  simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at hc
  ext s hs
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ← hc, one_mul] using
    congrArg (fun m : Measure G => m s) heq

/-- Translation invariance determines the actual hull probability for
every literal family parameter `k ≥ 2`. -/
theorem hullMeasure_eq_of_invariant (hk₂ : 2 ≤ k)
    (ν : Measure X) [IsProbabilityMeasure ν]
    (hν : ∀ t : ℝ, MeasurePreserving (translate (geometry k hk) t) ν ν) :
    ν = hullMeasure k hk hk₂ := by
  let π := solenoidRealize k hk
  have hπ : Measurable π := (continuous_solenoidRealize k hk).measurable
  apply hullMeasure_eq_of_map k hk hk₂
  apply solenoidMeasure_eq_haar_of_flow_invariant k hk (ν.map π)
  intro t
  have he : flow (pisotData k hk) t ∘ π = π ∘ translate (geometry k hk) t :=
    (funext (solenoidRealize_translate k hk t)).symm
  have hf : Measurable (flow (pisotData k hk) t) :=
    ((continuous_flow (geometry k hk) (pisotData k hk)).comp
      (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hf, ?_⟩
  rw [Measure.map_map hf hπ, he, ← Measure.map_map hπ (hν t).measurable, (hν t).map_eq]

end Psc.C4FamilyInvariantMeasureUniqueness
