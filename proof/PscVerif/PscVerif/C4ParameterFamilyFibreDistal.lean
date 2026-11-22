import PscVerif.C4FamilyFiniteProximal
import PscVerif.C4ParameterFamilyZeroFibreControls
import PscVerif.PeriodicPartnerFibreDistal

/-!
# The remaining almost-everywhere singleton-fibre interface

The concrete solenoid fibre relation is now ordinary proximality. Thus a
base point is fibre-distal exactly when it has one preimage. This holds
almost everywhere for an explicitly supplied measure if and only if
almost-everywhere fibre-distality is supplied. The latter geometric
measure statement remains a hypothesis, not a theorem in this module.

The distinct zero-fibre seam pair is a concrete non-distal-fibre control.
Source decision: `docs/c4-fibre-distal-measure-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyFibreDistal

open Function Set MeasureTheory
open Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.C4FamilyFiniteProximal Psc.ParameterFamilyZeroFibreControls
open Psc.PeriodicPartnerRealization (Solenoid)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate ofExact)
open Psc.PeriodicPartnerOrdinaryProximal
open Psc.PeriodicPartnerFibreDistal

variable (k : ℕ) (hk : 1 ≤ k)

/-- Surjectivity and the proved proximal-fibre relation identify the
fibre-distal base points with the points having exactly one preimage. -/
theorem fibreDistal_iff_unique_preimage (hk₂ : 2 ≤ k) (z : Solenoid (geometry k hk)) :
    IsFibreDistal (translate (geometry k hk)) (solenoidRealize k hk) z ↔
      ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z :=
  fibreDistal_iff_existsUnique (translate (geometry k hk)) (solenoidRealize k hk)
    (same_fibre_iff_topologicallyProximal k hk hk₂) z (solenoidRealize_surjective k hk z)

/-- For any explicitly supplied measure, the remaining fibre-distality
input is exactly the almost-everywhere unique-preimage input. This does
not assert that either predicate holds almost everywhere. -/
theorem ae_fibreDistal_iff_ae_unique_preimage (hk₂ : 2 ≤ k)
    [MeasurableSpace (Solenoid (geometry k hk))] (ν : Measure (Solenoid (geometry k hk))) :
    (∀ᵐ z ∂ν, IsFibreDistal (translate (geometry k hk)) (solenoidRealize k hk) z) ↔
      (∀ᵐ z ∂ν, ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z) :=
  ae_fibreDistal_iff_ae_existsUnique (translate (geometry k hk)) (solenoidRealize k hk)
    (solenoidRealize_surjective k hk) (same_fibre_iff_topologicallyProximal k hk hk₂) ν

/-- The one-way consumer keeps almost-everywhere fibre-distality explicit. -/
theorem ae_unique_preimage_of_ae_fibreDistal (hk₂ : 2 ≤ k)
    [MeasurableSpace (Solenoid (geometry k hk))] (ν : Measure (Solenoid (geometry k hk)))
    (hd : ∀ᵐ z ∂ν, IsFibreDistal (translate (geometry k hk)) (solenoidRealize k hk) z) :
    ∀ᵐ z ∂ν, ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z :=
  (ae_fibreDistal_iff_ae_unique_preimage k hk hk₂ ν).mp hd

/-- The actual exceptional zero fibre is not fibre-distal. A full-measure
claim must allow this multiple proximal fibre. -/
theorem zero_not_fibreDistal (hk₂ : 2 ≤ k) :
    ¬ IsFibreDistal (translate (geometry k hk)) (solenoidRealize k hk) 0 := by
  let S := geometry k hk
  obtain ⟨T, U, _, _, hzT, hzU, _, _, hne, _, _⟩ := zero_fibre_seam_control k hk
  have hprox : TopologicallyProximal (translate S) (ofExact S T) (ofExact S U) :=
    same_fibre_topologicallyProximal k hk hk₂ (hzT.trans hzU.symm)
  apply not_fibreDistal_of_distinct_proximal (translate S) (solenoidRealize k hk) hzT hprox
  intro h
  exact hne (congrArg LocalHull.toHull h)

end Psc.ParameterFamilyFibreDistal
