import PscVerif.C4ParameterFamilyInteriorSeed
import PscVerif.C4ParameterFamilyInteriorProximal
import PscVerif.PeriodicPartnerPeriodicZero

/-!
# Interior members of the literal zero fibre

The three-phase singleton seed is an actual legal hull tiling. Its
periodicity and integer length origin invoke the generic stable-series
characterization to prove equality to the full zero solenoid history.
Thus a zero-fibre tiling need not have a vertex at the origin.

Source decision: `docs/c4-zero-fibre-witness-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyInteriorZero

open Function Matrix Set
open Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyRecognizability Psc.ParameterFamilyInteriorSeed
open Psc.ParameterFamilyInteriorProximal Psc.PeriodicPartnerProximal
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerPeriodicZero
open Psc.PeriodicPartnerHull.LengthSubst (inflateH)

variable (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)

include hk₂

/-- All three phases of the literal interior cycle lie over the full
zero history. The first phase has no tile beginning at the origin. -/
theorem interior_zero_cycle :
    ∃ T : (geometry k hk).Hull,
      inflateH^[3] T = T ∧
      origin T = (1, -(geometry k hk).ℓ 0) ∧
      origin (inflateH T) = (1, (geometry k hk).ℓ 0 - (geometry k hk).ℓ 1) ∧
      origin (inflateH^[2] T) = (1, -(geometry k hk).ℓ 2) ∧
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ∧
      realize (pisotData k hk) (inflateH_bijective k hk) (inflateH T) = 0 ∧
      realize (pisotData k hk) (inflateH_bijective k hk) (inflateH^[2] T) = 0 ∧
      ¬ ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1 := by
  obtain ⟨T, hperiod, h₀, h₁, h₂⟩ := interior_periodic_origins k hk hk₂
  have hz : realize (pisotData k hk) (inflateH_bijective k hk) T = 0 := by
    apply realize_zero_of_periodic_lattice_origin (pisotData k hk)
      (inflateH_bijective k hk) (by decide : 0 < 3) hperiod (single_mem_lattice (0 : Fin 3))
    simpa only [dotProduct_single, mul_one] using congrArg Prod.snd h₀
  have hz₁ : realize (pisotData k hk) (inflateH_bijective k hk) (inflateH T) = 0 := by
    rw [realize_inflate, hz, shiftS_zero]
  have hz₂ : realize (pisotData k hk) (inflateH_bijective k hk) (inflateH^[2] T) = 0 := by
    change realize (pisotData k hk) (inflateH_bijective k hk) (inflateH (inflateH T)) = 0
    rw [realize_inflate, hz₁, shiftS_zero]
  exact ⟨T, hperiod, h₀, h₁, h₂, hz, hz₁, hz₂, no_origin_vertex k hk h₀⟩

/-- The proposed shortcut “every zero-fibre tiling has an origin
vertex” is false for every literal family member with `k ≥ 2`. -/
theorem zero_fibre_not_all_vertices :
    ¬ ∀ T : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
      ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1 := by
  obtain ⟨T, _, _, _, _, hz, _, _, hnv⟩ := interior_zero_cycle k hk hk₂
  exact fun h => hnv (h T hz)

/-- A genuine seam anchor and a genuine interior zero-fibre tiling
admit arbitrary-radius exact common-shift witnesses. Every phase of
the interior orbit uses the same anchor. No exhaustion of the zero
fibre by these constructed tilings is asserted. -/
theorem seam_and_interior_zero_witnesses :
    ∃ V T : (geometry k hk).Hull,
      (1, 0) ∈ V.1 ∧ inflateH^[2] V = V ∧ inflateH^[3] T = T ∧
      realize (pisotData k hk) (inflateH_bijective k hk) V = 0 ∧
      origin T = (1, -(geometry k hk).ℓ 0) ∧
      (¬ ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1) ∧
      ∀ i : ℕ,
        realize (pisotData k hk) (inflateH_bijective k hk) (inflateH^[i] T) = 0 ∧
        ExactProximal (geometry k hk) V (inflateH^[i] T) := by
  obtain ⟨V, hleft, hright, hV⟩ := fixed_hull_tiling k hk
  obtain ⟨T, hT, horigin, _, _, hz, _, _, hnv⟩ := interior_zero_cycle k hk hk₂
  have hzV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0 := by
    apply realize_r4 (pisotData k hk) (inflateH_bijective k hk) (b := 1)
    · exact ⟨2, by decide, hV⟩
    · exact (show (1, 0 - (geometry k hk).ℓ 1) ∈ V.1 by simpa using hleft)
  have htile : (1, -(geometry k hk).ℓ 0) ∈ T.1 := by
    rw [← horigin]
    exact (tileAt_spec T 0).1
  refine ⟨V, T, hright, hV, hT, hzV, horigin, hnv, fun i => ⟨?_, ?_⟩⟩
  · induction i with
    | zero => exact hz
    | succ i ih => rw [iterate_succ_apply', realize_inflate, ih, shiftS_zero]
  · exact seam_interior_orbit_exactProximal k hk hk₂ hright hV htile hT i

end Psc.ParameterFamilyInteriorZero
