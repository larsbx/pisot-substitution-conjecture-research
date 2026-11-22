import PscVerif.C4ParameterFamilySolenoid
import PscVerif.PeriodicPartnerSolenoidPureDiscrete

/-!
# The measured spectral interface of the literal σₖ hull

For the literal family, `k ≥ 1`, and any translation-invariant finite Borel measure `μ` on
the ordinary legal hull, the image measure on the full solenoid is flow invariant and the
solenoid flow has pure discrete spectrum for it. If the realization has a measurable almost
everywhere inverse, the hull translation flow has pure discrete spectrum for `μ`.

Three inputs are hypotheses and are **not** proved here: an invariant measure exists, its
image is weakly regular, and the almost everywhere inverse exists. The last is the
almost-everywhere singleton-fibre statement.

Source decision: `docs/c4-measured-pure-discrete-2026-11-22.md`.
-/

namespace Psc.C4FamilyMeasuredSpectrum

open MeasureTheory Function Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerLocalTopology
open Psc.MeasuredPureDiscrete Psc.PeriodicPartnerSolenoidPureDiscrete

variable (k : ℕ) (hk : 1 ≤ k)
  [MeasurableSpace (LocalHull (geometry k hk))] [BorelSpace (LocalHull (geometry k hk))]
  [MeasurableSpace (Solenoid (geometry k hk))] [BorelSpace (Solenoid (geometry k hk))]

/-- The translation flow of the ordinary hull, for a measure it preserves. -/
noncomputable def hullFlow (μ : Measure (LocalHull (geometry k hk)))
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ) : MeasuredFlow μ :=
  ⟨translate (geometry k hk), hμ⟩

theorem measurable_solenoidRealize : Measurable (solenoidRealize k hk) :=
  (continuous_solenoidRealize k hk).measurable

omit [MeasurableSpace (LocalHull (geometry k hk))] [BorelSpace (LocalHull (geometry k hk))] in
theorem measurable_flow (t : ℝ) : Measurable (flow (pisotData k hk) t) :=
  ((continuous_flow (geometry k hk) (pisotData k hk)).comp
    (Continuous.prodMk_right t)).measurable

/-- The image of a translation-invariant hull measure is invariant under the solenoid flow. -/
theorem image_flow_invariant (μ : Measure (LocalHull (geometry k hk)))
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ) (t : ℝ) :
    MeasurePreserving (flow (pisotData k hk) t)
      (μ.map (solenoidRealize k hk)) (μ.map (solenoidRealize k hk)) :=
  measurePreserving_map_of_semiconj (measurable_solenoidRealize k hk) (hμ t)
    (measurable_flow k hk t) (solenoidRealize_translate k hk t)

/-- **The target is pure discrete for the image of every invariant hull measure.** -/
theorem image_pureDiscrete (μ : Measure (LocalHull (geometry k hk))) [IsFiniteMeasure μ]
    [(μ.map (solenoidRealize k hk)).WeaklyRegular]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ) :
    PureDiscrete (solenoidFlow (geometry k hk) (pisotData k hk)
      (μ.map (solenoidRealize k hk)) (image_flow_invariant k hk μ hμ)) :=
  solenoid_pureDiscrete _ _ _ _

/-- **Conditional measured endpoint.** A measurable almost everywhere inverse of the
realization carries pure discreteness to the hull translation flow. -/
theorem hull_pureDiscrete_of_ae_inverse (μ : Measure (LocalHull (geometry k hk)))
    [IsFiniteMeasure μ] [(μ.map (solenoidRealize k hk)).WeaklyRegular]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ)
    {h : Solenoid (geometry k hk) → LocalHull (geometry k hk)} (hh : Measurable h)
    (hinv : h ∘ solenoidRealize k hk =ᵐ[μ] id) :
    PureDiscrete (hullFlow k hk μ hμ) :=
  pureDiscrete_of_ae_inverse (hullFlow k hk μ hμ)
    (solenoidFlow (geometry k hk) (pisotData k hk) _ (image_flow_invariant k hk μ hμ))
    ((measurable_solenoidRealize k hk).measurePreserving μ)
    (fun t => Filter.Eventually.of_forall fun T => solenoidRealize_translate k hk t T)
    hh hinv (image_pureDiscrete k hk μ hμ)

end Psc.C4FamilyMeasuredSpectrum
