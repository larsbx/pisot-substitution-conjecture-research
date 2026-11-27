import PscVerif.C4FamilyHaarSingletonFibres
import Mathlib.Topology.LocalAtTarget

/-! The ordinary legal hull and the full-history solenoid are isomorphic
almost everywhere for the hull probability lifted from normalized Haar.

Source decision: `docs/c4-family-measured-spectrum-2026-11-21.md`. -/

namespace Psc.C4FamilyMeasuredRealization

open Function Filter MeasureTheory Set
open scoped Psc.PeriodicPartnerSolenoidHaar
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (continuous_solenoidRealize pisotData solenoidRealize
  solenoidRealize_inflate solenoidRealize_surjective solenoidRealize_translate)
open Psc.PeriodicPartnerHull (LengthSubst)
open Psc.PeriodicPartnerLocalTopology (LocalHull continuous_inflate inflate translate
  translateHomeomorph)
open Psc.PeriodicPartnerRealization (Solenoid flow shiftS)
open Psc.PeriodicPartnerRealizationOnto (localHull_compactSpace)
open Psc.PeriodicPartnerSolenoidHaar (haar measurePreserving_shiftS)
open Psc.C4FamilyHaarSingletonFibres (exists_conull_singleton_fibres)

noncomputable scoped instance localHullMeasurableSpace {α : Type*} (S : LengthSubst α) :
    MeasurableSpace (LocalHull S) := borel _

scoped instance localHullBorelSpace {α : Type*} (S : LengthSubst α) :
    BorelSpace (LocalHull S) := ⟨rfl⟩

variable (k : ℕ) (hk : 1 ≤ k)

local notation "X" => LocalHull (geometry k hk)
local notation "G" => Solenoid (geometry k hk)
local notation "π" => solenoidRealize k hk
local notation "μₛ" => haar (geometry k hk)

variable (hk₂ : 2 ≤ k)

/-- A conull subset of the actual solenoid on which all fibres are singletons. -/
noncomputable def singletonSet : Set G :=
  (exists_conull_singleton_fibres k hk hk₂).choose

theorem singletonSet_spec :
    IsGδ (singletonSet k hk hk₂) ∧ (∀ᵐ z ∂μₛ, z ∈ singletonSet k hk hk₂) ∧
      ∀ z ∈ singletonSet k hk hk₂, ∃! T : X, π T = z :=
  (exists_conull_singleton_fibres k hk hk₂).choose_spec

private theorem restrictPreimage_bijective :
    Bijective ((singletonSet k hk hk₂).restrictPreimage π) := by
  constructor
  · intro T U h
    apply Subtype.ext
    have hTU : π T.1 = π U.1 := congrArg Subtype.val h
    exact ((singletonSet_spec k hk hk₂).2.2 (π U.1) U.2).unique hTU rfl
  · intro z
    obtain ⟨T, hT⟩ := solenoidRealize_surjective k hk z.1
    refine ⟨⟨T, ?_⟩, Subtype.ext hT⟩
    change π T ∈ singletonSet k hk hk₂
    rw [hT]
    exact z.2

/-- The actual factor, restricted to the preimage of the conull set, is a
homeomorphism. Compactness of the hull gives closedness of the original map. -/
noncomputable def singletonHomeomorph :
    (π ⁻¹' singletonSet k hk hk₂) ≃ₜ singletonSet k hk hk₂ := by
  letI : CompactSpace X := localHull_compactSpace
  let f := (singletonSet k hk hk₂).restrictPreimage π
  have hc : Continuous π := continuous_solenoidRealize k hk
  exact Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective f (restrictPreimage_bijective k hk hk₂)) hc.restrictPreimage
    (hc.isClosedMap.restrictPreimage (singletonSet k hk hk₂))

/-- Lift a conull solenoid point through the restricted homeomorphism.
Use a fixed legal tiling on the remaining points. -/
noncomputable def measurableInverse : G → X :=
  extend Subtype.val (Subtype.val ∘ (singletonHomeomorph k hk hk₂).symm)
    (fun _ => (solenoidRealize_surjective k hk 0).choose)

theorem measurable_measurableInverse : Measurable (measurableInverse k hk hk₂) :=
  (MeasurableEmbedding.subtype_coe (singletonSet_spec k hk hk₂).1.measurableSet).measurable_extend
    (continuous_subtype_val.comp (singletonHomeomorph k hk hk₂).symm.continuous).measurable
    measurable_const

theorem factor_inverse_on {z : G} (hz : z ∈ singletonSet k hk hk₂) :
    π (measurableInverse k hk hk₂ z) = z := by
  let s := singletonHomeomorph k hk hk₂
  let a : singletonSet k hk hk₂ := ⟨z, hz⟩
  change π (extend Subtype.val (Subtype.val ∘ s.symm) _ a.1) = a.1
  rw [Subtype.val_injective.extend_apply]
  exact congrArg Subtype.val (s.apply_symm_apply a)

theorem factor_inverse_ae : (π ∘ measurableInverse k hk hk₂) =ᵐ[μₛ] id :=
  (singletonSet_spec k hk hk₂).2.1.mono fun _ hz => factor_inverse_on k hk hk₂ hz

/-- The Borel probability on the ordinary hull is the lift of normalized Haar. -/
noncomputable def hullMeasure : Measure X := Measure.map (measurableInverse k hk hk₂) μₛ

theorem measurePreserving_inverse :
    MeasurePreserving (measurableInverse k hk hk₂) μₛ (hullMeasure k hk hk₂) :=
  ⟨measurable_measurableInverse k hk hk₂, rfl⟩

instance isProbabilityMeasure_hullMeasure : IsProbabilityMeasure (hullMeasure k hk hk₂) := by
  refine ⟨?_⟩
  rw [hullMeasure, Measure.map_apply (measurable_measurableInverse k hk hk₂) MeasurableSet.univ,
    preimage_univ, measure_univ]

theorem measurePreserving_factor : MeasurePreserving π (hullMeasure k hk hk₂) μₛ := by
  refine ⟨(continuous_solenoidRealize k hk).measurable, ?_⟩
  rw [hullMeasure, Measure.map_map (continuous_solenoidRealize k hk).measurable
    (measurable_measurableInverse k hk hk₂), Measure.map_congr (factor_inverse_ae k hk hk₂),
    Measure.map_id]

private theorem inverse_factor_ae_of_measurePreserving (ν : Measure X)
    (hπ : MeasurePreserving π ν μₛ) : (measurableInverse k hk hk₂ ∘ π) =ᵐ[ν] id := by
  filter_upwards [hπ.quasiMeasurePreserving.ae (singletonSet_spec k hk hk₂).2.1] with T hT
  exact ((singletonSet_spec k hk hk₂).2.2 (π T) hT).unique
    (factor_inverse_on k hk hk₂ hT) rfl

theorem inverse_factor_ae : (measurableInverse k hk hk₂ ∘ π) =ᵐ[hullMeasure k hk hk₂] id :=
  inverse_factor_ae_of_measurePreserving k hk hk₂ _ (measurePreserving_factor k hk hk₂)

/-- A measure on the ordinary hull is determined whenever its factor is Haar. -/
theorem hullMeasure_eq_of_map (ν : Measure X) (hν : Measure.map π ν = μₛ) :
    ν = hullMeasure k hk hk₂ := by
  have hπ : MeasurePreserving π ν μₛ := ⟨(continuous_solenoidRealize k hk).measurable, hν⟩
  calc
    ν = Measure.map id ν := Measure.map_id.symm
    _ = Measure.map (measurableInverse k hk hk₂ ∘ π) ν :=
      (Measure.map_congr (inverse_factor_ae_of_measurePreserving k hk hk₂ ν hπ)).symm
    _ = hullMeasure k hk hk₂ := by
      rw [← Measure.map_map (measurable_measurableInverse k hk hk₂) hπ.measurable, hν]
      rfl

private theorem measurePreserving_of_semiconj {f : X → X} {g : G → G}
    (hf : Measurable f) (hg : MeasurePreserving g μₛ μₛ) (h : Semiconj π f g) :
    MeasurePreserving f (hullMeasure k hk hk₂) (hullMeasure k hk hk₂) := by
  have hπ := measurePreserving_factor k hk hk₂
  refine ⟨hf, hullMeasure_eq_of_map k hk hk₂ _ ?_⟩
  rw [Measure.map_map hπ.measurable hf, show π ∘ f = g ∘ π from funext h,
    ← Measure.map_map hg.measurable hπ.measurable, hπ.map_eq, hg.map_eq]

theorem measurePreserving_translate (t : ℝ) :
    MeasurePreserving (translate (geometry k hk) t) (hullMeasure k hk hk₂)
      (hullMeasure k hk hk₂) := by
  have hflow : MeasurePreserving (flow (pisotData k hk) t) μₛ μₛ := by
    have heq : flow (pisotData k hk) t = fun z => z + flow (pisotData k hk) t 0 := by
      funext z
      simp only [flow, zero_add]
    rw [heq]
    exact measurePreserving_add_right _ _
  exact measurePreserving_of_semiconj k hk hk₂
    (translateHomeomorph (geometry k hk) t).continuous.measurable hflow
    (solenoidRealize_translate k hk t)

theorem measurePreserving_inflate :
    MeasurePreserving (inflate (geometry k hk)) (hullMeasure k hk hk₂)
      (hullMeasure k hk hk₂) :=
  measurePreserving_of_semiconj k hk hk₂ (continuous_inflate (geometry k hk)).measurable
    (measurePreserving_shiftS _) (solenoidRealize_inflate k hk)

end Psc.C4FamilyMeasuredRealization
