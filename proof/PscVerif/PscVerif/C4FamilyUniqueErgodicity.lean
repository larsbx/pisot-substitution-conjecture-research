import PscVerif.C4FamilyMeasuredSpectrum
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Metrizable.Urysohn

/-!
# The invariant probability measure of the literal σₖ translation flow is unique

A Borel probability measure on the full-history solenoid that is preserved by the real flow
is normalized Haar measure, for `k ≥ 1`. Consequently, for `k ≥ 2`, a Borel probability
measure on the ordinary legal hull preserved by every translation is the measure
`hullMeasure` for which `C4FamilyMeasuredSpectrum.pureDiscrete_translation` is proved.

The argument integrates the explicit characters. A character with nonzero frequency has
integral zero against any flow-invariant probability, by the half-period phase `-1`; a
character with zero frequency is the constant one. The characters span a uniformly dense
subspace of the continuous functions, and a finite Borel measure on a metrizable space is
determined by the integrals of continuous functions.

Source decision: `docs/c4-family-unique-ergodicity-2026-11-22.md`.
-/

namespace Psc.C4FamilyUniqueErgodicity

open Function Filter MeasureTheory Set
open scoped Psc.PeriodicPartnerSolenoidHaar Psc.C4FamilyMeasuredRealization BoundedContinuousFunction
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize solenoidRealize_translate
  continuous_solenoidRealize)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate)
open Psc.PeriodicPartnerRealization (Solenoid flow continuous_flow)
open Psc.PeriodicPartnerSolenoidHaar (haar)
open Psc.PeriodicPartnerSolenoidCharacters
open Psc.C4FamilyCharacterOrbits (character_eq_one_of_frequency_eq_zero)
open Psc.C4FamilyMeasuredRealization (hullMeasure hullMeasure_eq_of_map)

variable (k : ℕ) (hk : 1 ≤ k)

local notation "X" => LocalHull (geometry k hk)
local notation "G" => Solenoid (geometry k hk)
local notation "π" => solenoidRealize k hk
local notation "μₛ" => haar (geometry k hk)
local notation "P" => pisotData k hk

theorem integrable_continuousMap (ν : Measure G) [IsFiniteMeasure ν] (f : C(G, ℂ)) :
    Integrable (fun z => f z) ν :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall fun z => f.norm_coe_le_norm z)

/-- The half-period phase is `-1`. -/
theorem half_period_phase {ξ : ℝ} (hξ : ξ ≠ 0) :
    Complex.exp (((2 * Real.pi * (1 / (2 * ξ) * ξ) : ℝ) : ℂ) * Complex.I) = -1 := by
  have h : (2 * Real.pi * (1 / (2 * ξ) * ξ) : ℝ) = Real.pi := by field_simp
  rw [h, Complex.exp_pi_mul_I]

/-- **Character integrals are forced by flow invariance.** -/
theorem integral_character (ν : Measure G) [IsProbabilityMeasure ν]
    (hν : ∀ t, MeasurePreserving (flow P t) ν ν) (c : Certificate (Fin 3)) :
    ∫ z, character (geometry k hk) c z ∂ν =
      if frequency (geometry k hk) P c = 0 then 1 else 0 := by
  split_ifs with hξ
  · rw [character_eq_one_of_frequency_eq_zero k hk c hξ]
    simp
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, Complex.exp (((2 * Real.pi *
        (t * frequency (geometry k hk) P c) : ℝ) : ℂ) * Complex.I) = -1 :=
      ⟨_, half_period_phase hξ⟩
    have hmap : ∫ z, character (geometry k hk) c (flow P t z) ∂ν =
        ∫ z, character (geometry k hk) c z ∂ν := by
      have h : ∫ y, character (geometry k hk) c y ∂(Measure.map (flow P t) ν) =
          ∫ z, character (geometry k hk) c (flow P t z) ∂ν :=
        integral_map (hν t).measurable.aemeasurable
          (character (geometry k hk) c).continuous.aestronglyMeasurable
      rw [(hν t).map_eq] at h
      exact h.symm
    have hpoint : ∀ z, character (geometry k hk) c (flow P t z) =
        -character (geometry k hk) c z := fun z => by
      rw [character_flow (geometry k hk) P c t z, ht, neg_one_mul]
    have hphase : ∫ z, character (geometry k hk) c (flow P t z) ∂ν =
        -∫ z, character (geometry k hk) c z ∂ν := by
      simp_rw [hpoint]
      exact integral_neg _
    have h2 : (2 : ℂ) * ∫ z, character (geometry k hk) c z ∂ν = 0 := by
      have := hmap.symm.trans hphase
      linear_combination this
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

theorem flow_haar (t : ℝ) : MeasurePreserving (flow P t) μₛ μₛ := by
  have heq : flow P t = fun z => z + flow P t 0 := by
    funext z
    simp only [flow, zero_add]
  rw [heq]
  exact measurePreserving_add_right _ _

/-- Two flow-invariant probabilities integrate every continuous function alike. -/
theorem integral_continuous_eq (ν : Measure G) [IsProbabilityMeasure ν]
    (hν : ∀ t, MeasurePreserving (flow P t) ν ν) (f : C(G, ℂ)) :
    ∫ z, f z ∂ν = ∫ z, f z ∂μₛ := by
  have hlip : ∀ (ρ : Measure G) [IsProbabilityMeasure ρ],
      Continuous (fun f : C(G, ℂ) => ∫ z, f z ∂ρ) := by
    intro ρ _
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
      ← integral_sub (integrable_continuousMap k hk ρ f) (integrable_continuousMap k hk ρ g)]
    have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun z => f z - g z)
      (C := ‖f - g‖) (Eventually.of_forall fun z => (f - g).norm_coe_le_norm z)
    simpa using h
  let E : Submodule ℂ C(G, ℂ) :=
    { carrier := {f | ∫ z, f z ∂ν = ∫ z, f z ∂μₛ}
      add_mem' := by
        intro f g hf hg
        simp only [Set.mem_ofPred_eq, ContinuousMap.add_apply] at hf hg ⊢
        rw [integral_add (integrable_continuousMap k hk ν f) (integrable_continuousMap k hk ν g),
          integral_add (integrable_continuousMap k hk μₛ f)
            (integrable_continuousMap k hk μₛ g), hf, hg]
      zero_mem' := by simp
      smul_mem' := by
        intro a f hf
        simp only [Set.mem_ofPred_eq, ContinuousMap.smul_apply, smul_eq_mul] at hf ⊢
        rw [integral_const_mul, integral_const_mul, hf] }
  have hclosed : IsClosed (E : Set C(G, ℂ)) := isClosed_eq (hlip ν) (hlip μₛ)
  have hspan : Submodule.span ℂ (range (character (geometry k hk))) ≤ E := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    show ∫ z, character (geometry k hk) c z ∂ν = ∫ z, character (geometry k hk) c z ∂μₛ
    rw [integral_character k hk ν hν c, integral_character k hk μₛ (flow_haar k hk) c]
  have htop : (⊤ : Submodule ℂ C(G, ℂ)) ≤ E := by
    rw [← span_character_closure_eq_top (geometry k hk)]
    exact Submodule.topologicalClosure_minimal _ hspan hclosed
  exact htop (Submodule.mem_top (x := f))

/-- **Unique ergodicity of the solenoid flow.** -/
theorem flowInvariant_eq_haar (ν : Measure G) [IsProbabilityMeasure ν]
    (hν : ∀ t, MeasurePreserving (flow P t) ν ν) : ν = μₛ := by
  have : SecondCountableTopology G := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : TopologicalSpace.PseudoMetrizableSpace G := inferInstance
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  let g : C(G, ℂ) := ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have h := integral_continuous_eq k hk ν hν g
  have hν' : ∫ z, g z ∂ν = ((∫ z, f z ∂ν : ℝ) : ℂ) := integral_ofReal
  have hμ' : ∫ z, g z ∂μₛ = ((∫ z, f z ∂μₛ : ℝ) : ℂ) := integral_ofReal
  rw [hν', hμ'] at h
  exact Complex.ofReal_injective h

variable (hk₂ : 2 ≤ k)

/-- **Unique ergodicity of the hull translation flow.** Every translation-invariant Borel
probability on the ordinary legal hull is the lifted Haar measure. -/
theorem translationInvariant_eq_hullMeasure (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ) :
    μ = hullMeasure k hk hk₂ := by
  have hπ : Measurable π := (continuous_solenoidRealize k hk).measurable
  have : IsProbabilityMeasure (Measure.map π μ) :=
    (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
  refine hullMeasure_eq_of_map k hk hk₂ μ (flowInvariant_eq_haar k hk _ fun t => ?_)
  have hflow : Measurable (flow P t) :=
    ((continuous_flow (geometry k hk) P).comp (Continuous.prodMk_right t)).measurable
  refine ⟨hflow, ?_⟩
  have hc : flow P t ∘ π = π ∘ translate (geometry k hk) t :=
    funext fun T => (solenoidRealize_translate k hk t T).symm
  rw [Measure.map_map hflow hπ, hc, ← Measure.map_map hπ (hμ t).measurable, (hμ t).map_eq]

include hk₂ in
/-- **Pure discrete spectrum for every invariant probability.** For `k ≥ 2` and every Borel
probability on the ordinary legal hull preserved by all translations, the nonzero joint
translation eigenvectors span a dense subspace of `L²`. No measure is chosen by the caller
beyond its invariance. -/
theorem pureDiscrete_of_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ) :
    (Submodule.span ℂ {v : Lp ℂ 2 μ | v ≠ 0 ∧ ∃ ξ : ℝ, ∀ t : ℝ,
      Lp.compMeasurePreservingₗᵢ ℂ (translate (geometry k hk) t) (hμ t) v =
        Psc.C4FamilyMeasuredSpectrum.translationPhase t ξ • v}).topologicalClosure = ⊤ := by
  have h := translationInvariant_eq_hullMeasure k hk hk₂ μ hμ
  subst h
  exact Psc.C4FamilyMeasuredSpectrum.pureDiscrete_translation k hk hk₂

end Psc.C4FamilyUniqueErgodicity
