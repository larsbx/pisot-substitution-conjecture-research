import PscVerif.MeasuredPureDiscrete
import PscVerif.PeriodicPartnerSolenoidCharacters

/-!
# The solenoid flow has pure discrete spectrum for every invariant regular measure

The explicit characters of the full-history solenoid are continuous pointwise
eigenfunctions of the flow with dense uniform span. `MeasuredPureDiscrete` turns that into
density of eigenfunctions in `L²(ν; ℂ)` for every finite, weakly regular Borel measure `ν`
preserved by the flow.

The measure is a parameter. Haar measure is not constructed, uniqueness of the invariant
measure is not asserted, and nothing is said about the hull or its fibres.

Source decision: `docs/c4-measured-pure-discrete-2026-11-22.md`.
-/

namespace Psc.PeriodicPartnerSolenoidPureDiscrete

open MeasureTheory Psc.PeriodicPartnerHull Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerSolenoidCharacters Psc.MeasuredPureDiscrete

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  (S : LengthSubst α) (P : PisotData S)
  [MeasurableSpace (Solenoid S)] [BorelSpace (Solenoid S)]

/-- The solenoid flow, as a measured flow for a measure it preserves. -/
noncomputable def solenoidFlow (ν : Measure (Solenoid S))
    (hν : ∀ t, MeasurePreserving (flow P t) ν ν) : MeasuredFlow ν :=
  ⟨flow P, hν⟩

/-- The character phase of `character_flow`, in the normalization of `MeasuredPureDiscrete`. -/
theorem character_phase (ω t : ℝ) :
    Complex.exp (((2 * Real.pi * (t * ω) : ℝ) : ℂ) * Complex.I) =
      MeasuredPureDiscrete.phase ω t := by
  rw [MeasuredPureDiscrete.phase]
  congr 1
  push_cast
  ring

/-- **Pure discrete spectrum of the target.** For every finite weakly regular Borel measure
preserved by the solenoid flow, the flow eigenfunctions span a dense subspace of `L²`. -/
theorem solenoid_pureDiscrete (ν : Measure (Solenoid S)) [IsFiniteMeasure ν] [ν.WeaklyRegular]
    (hν : ∀ t, MeasurePreserving (flow P t) ν ν) :
    PureDiscrete (solenoidFlow S P ν hν) := by
  let _ : T2Space (Solenoid S) := solenoid_t2Space S
  let _ : CompactSpace (Solenoid S) := solenoid_compactSpace S
  refine pureDiscrete_of_continuous_eigen _ (Set.range (character S)) ?_ ?_
  · rintro _ ⟨c, rfl⟩
    refine ⟨frequency S P c, fun t z => ?_⟩
    rw [← character_phase]
    exact character_flow S P c t z
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact span_character_closure_eq_top S

end Psc.PeriodicPartnerSolenoidPureDiscrete
