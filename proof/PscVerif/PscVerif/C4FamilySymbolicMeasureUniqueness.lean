import PscVerif.C4FamilyInvariantMeasureUniqueness
import PscVerif.C4FamilySymbolicSpectrum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

/-! Every invariant probability on the literal legal word shift is the
existing induced probability. An arbitrary invariant return probability is
lifted through the actual corrected constant strip. Continuous test integrals
make its solenoid marginal invariant under every real time, hence Haar.
The existing conull singleton fibres determine the lifted measure, and its
base marginal recovers the originally supplied probability.

Source decision: `docs/c4-family-canonical-measure-2026-11-23.md`.
No canonical probability is introduced by renaming the induced measure. -/

namespace Psc.C4FamilySymbolicMeasureUniqueness

open Function Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction Psc.C4FamilyMeasuredRealization Psc.C4FamilySymbolicSpectrum
  Psc.PeriodicPartnerSolenoidHaar
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize continuous_solenoidRealize
  solenoidRealize_translate)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate translate_translate translateHomeomorph)
open Psc.PeriodicPartnerRealization (Solenoid flow continuous_flow)
open Psc.C4FamilyMeasuredRealization (hullMeasure hullMeasure_eq_of_map)
open Psc.C4FamilyInvariantMeasureUniqueness (solenoidMeasure_eq_haar_of_flow_invariant)
open Psc.C4FamilySymbolicSection
open Psc.C4FamilySymbolicSpectrum (symbolicMeasure wordMeasure symbolicFactor
  measurable_symbolicFactor constantStripEquiv)
open Psc.C4FamilySymbolicLanguage (SymbolicHull itineraryHomeomorph
  itineraryHomeomorph_next shift continuous_shift)

variable (k : ℕ) (hk : 1 ≤ k)

local notation "B" => Transversal k hk
local notation "X" => LocalHull (geometry k hk)
local notation "Z" => Solenoid (geometry k hk)
local notation "c" => meanRoof k hk

/-- Normalized Lebesgue measure on the genuine half-open constant roof. -/
noncomputable def timeMeasure : Measure ℝ :=
  (ENNReal.ofReal c)⁻¹ • volume.restrict (Ico 0 c)

instance isProbabilityMeasure_timeMeasure : IsProbabilityMeasure (timeMeasure k hk) := by
  constructor
  simp only [timeMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ico, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr meanRoof_pos))
    ENNReal.ofReal_ne_top

theorem timeMeasure_ae_mem : ∀ᵐ s ∂timeMeasure k hk, s ∈ Ico 0 c :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ico) _

/-- Suspend an arbitrary return probability in the same ordinary legal hull. -/
noncomputable def suspensionMeasure (μ : Measure B) : Measure X :=
  (μ.prod (timeMeasure k hk)).map strip

instance isProbabilityMeasure_suspensionMeasure (μ : Measure B) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (suspensionMeasure k hk μ) :=
  inferInstanceAs (IsProbabilityMeasure ((μ.prod (timeMeasure k hk)).map strip))

theorem symbolicFactor_strip {p : B × ℝ} (hp : p ∈ ConstantStrip k hk) :
    symbolicFactor k hk (strip p) = p.1 := by
  exact congrArg (fun q : ConstantStrip k hk => q.1.1)
    ((constantStripEquiv k hk).symm_apply_apply ⟨p, hp⟩)

/-- Recover the given base probability, including the half-open endpoints. -/
theorem map_symbolicFactor_suspensionMeasure (μ : Measure B) [IsProbabilityMeasure μ] :
    (suspensionMeasure k hk μ).map (symbolicFactor k hk) = μ := by
  have ha : ∀ᵐ p ∂μ.prod (timeMeasure k hk), p.2 ∈ Ico 0 c :=
    (measurePreserving_snd (μ := μ) (ν := timeMeasure k hk)).quasiMeasurePreserving.ae
      (timeMeasure_ae_mem k hk)
  have he : (symbolicFactor k hk ∘ strip) =ᵐ[μ.prod (timeMeasure k hk)] Prod.fst :=
    ha.mono fun p hp => symbolicFactor_strip k hk hp
  rw [suspensionMeasure, Measure.map_map (measurable_symbolicFactor k hk)
    continuous_strip.measurable, Measure.map_congr he,
    Measure.map_fst_prod, measure_univ, one_smul]

private theorem integral_timeMeasure (f : ℝ → ℝ) :
    (∫ s, f s ∂timeMeasure k hk) = c⁻¹ * ∫ s in 0..c, f s := by
  rw [timeMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (meanRoof_pos.le), smul_eq_mul,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (meanRoof_pos.le)]

private theorem integral_suspensionMeasure (μ : Measure B) [IsProbabilityMeasure μ]
    (f : X →ᵇ ℝ) :
    (∫ T, f T ∂suspensionMeasure k hk μ) =
      c⁻¹ * ∫ s in 0..c, ∫ b, f (strip (b, s)) ∂μ := by
  have hi : Integrable (fun p : B × ℝ => f (strip p)) (μ.prod (timeMeasure k hk)) :=
    ⟨(f.continuous.comp continuous_strip).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Eventually.of_forall fun p => f.norm_coe_le_norm _)⟩
  rw [suspensionMeasure, integral_map continuous_strip.measurable.aemeasurable
    f.continuous.aestronglyMeasurable, integral_prod_symm _ hi, integral_timeMeasure]

private theorem strip_next_eq (b : B) (s : ℝ) :
    strip (next b, s) = strip (b, s + c) := by
  rw [← translate_mean_strip, strip, translate_translate]
  congr 1
  exact add_comm _ _

/-- All continuous test integrals of the suspended probability are flow invariant.
This statement does not assume regularity of an arbitrary hull measure. -/
theorem integral_translate_suspensionMeasure (μ : Measure B) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (next (k := k) (hk := hk)) μ μ)
    (f : X →ᵇ ℝ) (t : ℝ) :
    (∫ T, f (translate (geometry k hk) t T) ∂suspensionMeasure k hk μ) =
      ∫ T, f T ∂suspensionMeasure k hk μ := by
  let F : ℝ → ℝ := fun s => ∫ b, f (strip (b, s)) ∂μ
  have hF : Periodic F c := by
    intro s
    have hm := integral_map (μ := μ) (f := fun b : B => f (strip (b, s)))
      hμ.measurable.aemeasurable
      (f.continuous.comp (continuous_strip.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
    rw [hμ.map_eq] at hm
    change F (s + c) = F s
    simpa only [F, strip_next_eq k hk] using hm.symm
  let ft : X →ᵇ ℝ := f.compContinuous
    ⟨translate (geometry k hk) t, (translateHomeomorph (geometry k hk) t).continuous⟩
  change (∫ T, ft T ∂suspensionMeasure k hk μ) = _
  rw [integral_suspensionMeasure k hk μ ft, integral_suspensionMeasure k hk μ f]
  apply congrArg (fun v : ℝ => c⁻¹ * v)
  have he (s : ℝ) : (∫ b, ft (strip (b, s)) ∂μ) = F (s + t) := by
    apply integral_congr_ae
    filter_upwards with b
    change f (translate (geometry k hk) t (translate (geometry k hk) s (corrected b))) =
      f (translate (geometry k hk) (s + t) (corrected b))
    rw [translate_translate, add_comm t s]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm c t] using hF.intervalIntegral_add_eq t 0

/-- The solenoid marginal of the suspended probability is invariant under
every real time; measure extensionality is used only on the solenoid. -/
theorem measurePreserving_flow_suspensionFactor (μ : Measure B) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (next (k := k) (hk := hk)) μ μ) (t : ℝ) :
    MeasurePreserving (flow (pisotData k hk) t)
      ((suspensionMeasure k hk μ).map (solenoidRealize k hk))
      ((suspensionMeasure k hk μ).map (solenoidRealize k hk)) := by
  have hπ := (continuous_solenoidRealize k hk).measurable
  have hc : Continuous (flow (pisotData k hk) t) :=
    (continuous_flow (geometry k hk) (pisotData k hk)).comp
      (continuous_const.prodMk continuous_id)
  have hf := hc.measurable
  refine ⟨hf, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hf.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map (μ := suspensionMeasure k hk μ) (f := fun z : Z => f (flow (pisotData k hk) t z))
      hπ.aemeasurable (f.continuous.comp hc).aestronglyMeasurable,
    integral_map hπ.aemeasurable f.continuous.aestronglyMeasurable]
  let g : X →ᵇ ℝ := f.compContinuous
    ⟨solenoidRealize k hk, continuous_solenoidRealize k hk⟩
  have ht := integral_translate_suspensionMeasure k hk μ hμ g t
  change (∫ T, f (solenoidRealize k hk (translate (geometry k hk) t T))
      ∂suspensionMeasure k hk μ) =
    ∫ T, f (solenoidRealize k hk T) ∂suspensionMeasure k hk μ at ht
  simpa only [solenoidRealize_translate] using ht

variable (hk₂ : 2 ≤ k)

/-- An arbitrary invariant return probability suspends to the specified
hull probability, by the existing conull singleton-fibre theorem. -/
theorem suspensionMeasure_eq_hullMeasure (μ : Measure B) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (next (k := k) (hk := hk)) μ μ) :
    suspensionMeasure k hk μ = hullMeasure k hk hk₂ := by
  apply hullMeasure_eq_of_map k hk hk₂
  exact solenoidMeasure_eq_haar_of_flow_invariant k hk _
    (measurePreserving_flow_suspensionFactor k hk μ hμ)

/-- Uniqueness of the invariant Borel probability on the actual transversal. -/
theorem invariant_probability_eq_symbolicMeasure
    (μ : Measure B) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (next (k := k) (hk := hk)) μ μ) :
    μ = symbolicMeasure k hk hk₂ := by
  rw [← map_symbolicFactor_suspensionMeasure k hk μ,
    suspensionMeasure_eq_hullMeasure k hk hk₂ μ hμ]
  rfl

/-- Any independently supplied invariant Borel probability on the literal
two-sided legal shift equals the induced `wordMeasure`, for every `k ≥ 2`. -/
theorem invariant_probability_eq_wordMeasure
    (μ : Measure (SymbolicHull k hk)) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift (k := k) (hk := hk)) μ μ) :
    μ = wordMeasure k hk hk₂ := by
  let e : B ≃ᵐ SymbolicHull k hk :=
    (itineraryHomeomorph (k := k) (hk := hk)).toMeasurableEquiv
  let μB : Measure B := μ.map e.symm
  have hq : next ∘ e.symm = e.symm ∘ shift := by
    funext x
    apply e.injective
    change itineraryHomeomorph (next (e.symm x)) = e (e.symm (shift x))
    rw [itineraryHomeomorph_next, e.apply_symm_apply]
    exact congrArg shift (e.apply_symm_apply x)
  have hB : MeasurePreserving (next (k := k) (hk := hk)) μB μB := by
    refine ⟨continuous_next.measurable, ?_⟩
    change (μ.map e.symm).map next = μ.map e.symm
    rw [Measure.map_map continuous_next.measurable e.symm.measurable, hq,
      ← Measure.map_map e.symm.measurable hμ.measurable, hμ.map_eq]
  have hident := invariant_probability_eq_symbolicMeasure k hk hk₂ μB hB
  calc
    μ = μB.map e := by
      rw [show μB = μ.map e.symm from rfl,
        Measure.map_map e.measurable e.symm.measurable]
      simp only [Function.comp_def, e.apply_symm_apply, Measure.map_id']
    _ = (symbolicMeasure k hk hk₂).map e := congrArg (fun m : Measure B => m.map e) hident
    _ = wordMeasure k hk hk₂ := rfl

end Psc.C4FamilySymbolicMeasureUniqueness
