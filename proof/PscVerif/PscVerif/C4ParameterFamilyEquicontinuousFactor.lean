import PscVerif.C4ParameterFamilyRotationFactor
import PscVerif.PeriodicPartnerEquicontinuousFactor

/-!
# The concrete solenoid as an equicontinuous factor

The actual solenoid's inherited uniformity makes its existing flow uniformly
equicontinuous. The factor's universal property among equicontinuous actions
is proved under the same explicit common-tile anchor premise, without a
representation theorem for abstract equicontinuous systems as rotations.

Source decision: `docs/c4-rotation-factor-rank-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyEquicontinuousFactor

open Function Set Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyRecognizability Psc.ParameterFamilyOrdinaryProximal
open Psc.PeriodicPartnerLocalTopology Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerEquicontinuousFactor

variable (k : ℕ) (hk : 1 ≤ k)

/-- The existing solenoid flow is uniformly equicontinuous for its inherited
quotient/product/subgroup uniformity. No new uniform structure is imposed. -/
theorem uniformEquicontinuous_solenoid_flow :
    UniformEquicontinuous (flow (pisotData k hk)) := by
  have h := uniformEquicontinuous_add_right_rotations
    (fun t : ℝ => flow (pisotData k hk) t 0)
  have he : flow (pisotData k hk) =
      (fun t z => z + flow (pisotData k hk) t 0) := by
    funext t z
    simp only [flow, zero_add]
  rw [he]
  exact h

theorem equicontinuous_solenoid_flow : Equicontinuous (flow (pisotData k hk)) :=
  (uniformEquicontinuous_solenoid_flow k hk).equicontinuous

/-- Zero-time and the time-composition law follow from the onto equivariant
realization and the already constructed ordinary hull action. -/
theorem solenoid_flow_zero (z : Solenoid (geometry k hk)) :
    flow (pisotData k hk) 0 z = z := by
  obtain ⟨T, rfl⟩ := solenoidRealize_surjective k hk z
  rw [← solenoidRealize_translate, translate_zero]

theorem solenoid_flow_add (s t : ℝ) (z : Solenoid (geometry k hk)) :
    flow (pisotData k hk) s (flow (pisotData k hk) t z) =
      flow (pisotData k hk) (s + t) z := by
  obtain ⟨T, rfl⟩ := solenoidRealize_surjective k hk z
  rw [← solenoidRealize_translate, ← solenoidRealize_translate,
    translate_translate, solenoidRealize_translate]

/-- The ordinary equicontinuous-factor universal property, conditional only
on the explicit common-tile anchor obligation. The target has the usual
Equicontinuous family of time maps, not a stronger uniform hypothesis. -/
theorem equicontinuous_factor_descent_of_zero_anchor_common_tile
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hanchor : ∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty)
    {Z : Type*} [UniformSpace Z] [T2Space Z]
    (act : ℝ → Z → Z) (hzero : ∀ z, act 0 z = z)
    (hadd : ∀ s t z, act s (act t z) = act (s + t) z)
    (hequi : Equicontinuous act)
    (f : LocalHull (geometry k hk) → Z) (hf : Continuous f)
    (hf_equiv : ∀ t T, f (translate (geometry k hk) t T) = act t (f T)) :
    ∃! d : Solenoid (geometry k hk) → Z,
      Continuous d ∧ (∀ T, d (solenoidRealize k hk T) = f T) ∧
        ∀ t z, d (flow (pisotData k hk) t z) = act t (d z) := by
  let : CompactSpace (LocalHull (geometry k hk)) :=
    Psc.PeriodicPartnerRealizationOnto.localHull_compactSpace
  let : T2Space (Solenoid (geometry k hk)) := solenoid_t2Space _
  exact existsUnique_equicontinuous_descent (translate (geometry k hk))
    (flow (pisotData k hk)) act (solenoidRealize k hk) (continuous_solenoidRealize k hk)
    (solenoidRealize_surjective k hk) (solenoidRealize_translate k hk)
    (fun _ _ h => same_fibre_proximal_of_zero_anchor_common_tile k hk hV hanchor h)
    hzero hadd hequi f hf hf_equiv

end Psc.ParameterFamilyEquicontinuousFactor
