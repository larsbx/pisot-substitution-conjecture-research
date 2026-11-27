import PscVerif.C4ParameterFamilySolenoid
import PscVerif.PeriodicPartnerSolenoidCharacters

/-!
# Explicit continuous eigenfunctions for the literal parameter family

Finite integer certificates on compatible history coordinates pull back along
the actual geometric realization. Their exact translation eigenfunction law
and their ability to distinguish distinct factor images are unconditional for
`k ≥ 1`. Density is on the solenoid. Density in the hull's measured `L²` space
still needs the almost-everywhere singleton-fibre and measure-transport work.

The final control constructs two actual family solenoid histories with equal
zeroth coordinates and a different first coordinate. It prevents replacing
the nonunit solenoid by its zeroth-coordinate torus.

Source decision: `docs/c4-finite-fibre-obligations-2026-11-21.md`.
-/

namespace Psc.C4FamilySolenoidCharacters

open Function Set Matrix Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.PeriodicPartnerLocalTopology Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerSolenoidCharacters
open scoped Topology

variable (k : ℕ) (hk : 1 ≤ k)

/-- The actual ordinary-hull continuous eigenfunction replayed from a finite certificate. -/
noncomputable def eigenfunction (c : Certificate (Fin 3)) :
    C(LocalHull (geometry k hk), ℂ) :=
  (character (geometry k hk) c).comp
    ⟨solenoidRealize k hk, continuous_solenoidRealize k hk⟩

@[simp]
theorem eigenfunction_apply (c : Certificate (Fin 3)) (T : LocalHull (geometry k hk)) :
    eigenfunction k hk c T = character (geometry k hk) c (solenoidRealize k hk T) := rfl

theorem eigenfunction_norm (c : Certificate (Fin 3)) (T : LocalHull (geometry k hk)) :
    ‖eigenfunction k hk c T‖ = 1 := character_norm _ _ _

/-- The finite character frequency belongs to the specified, actual family realization. -/
theorem eigenfunction_translate (c : Certificate (Fin 3)) (t : ℝ)
    (T : LocalHull (geometry k hk)) :
    eigenfunction k hk c (translate (geometry k hk) t T) =
      Complex.exp (((2 * Real.pi *
        (t * frequency (geometry k hk) (pisotData k hk) c) : ℝ) : ℂ) * Complex.I) *
          eigenfunction k hk c T := by
  simp only [eigenfunction_apply, solenoidRealize_translate]
  exact character_flow _ _ _ _ _

/-- The finite eigenfunctions distinguish exactly the concrete factor images.
This does not assert that they distinguish different tilings in one fibre. -/
theorem eigenfunctions_eq_iff (T U : LocalHull (geometry k hk)) :
    (∀ c : Certificate (Fin 3), eigenfunction k hk c T = eigenfunction k hk c U) ↔
      solenoidRealize k hk T = solenoidRealize k hk U := by
  constructor
  · exact character_ext _
  · intro h c
    simp only [eigenfunction_apply, h]

/-- Uniform density on the actual full compatible-history solenoid. -/
theorem solenoid_character_span_dense :
    (Submodule.span ℂ (range (character (geometry k hk)))).topologicalClosure = ⊤ :=
  span_character_closure_eq_top _

/-! ## The nonunit history control -/

/-- An exact right inverse of the family's real incidence matrix. -/
noncomputable def predecessor (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 1 - (k : ℝ) * v 2 - (v 0 - v 2) / 2, v 2, (v 0 - v 2) / 2]

theorem mat_predecessor (v : Fin 3 → ℝ) :
    mat (geometry k hk) *ᵥ predecessor k v = v := by
  rw [mat_eq, Psc.ParameterFamilyPisot.incidenceQ_eq]
  ext a
  fin_cases a <;>
    simp [predecessor, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.map_apply]
  ring

/-- A history over zero whose first prehistory has a half-integer coordinate.
Each compatibility equation is the finite incidence identity above. -/
noncomputable def nonunitHistory : Solenoid (geometry k hk) :=
  ⟨fun n => (((predecessor k)^[n] ![1, 0, 0] : Fin 3 → ℝ) : Torus (Fin 3)), fun n => by
    rw [torusMap_mk, iterate_succ_apply', mat_predecessor]⟩

theorem nonunitHistory_coord_zero : (nonunitHistory k hk).1 0 = 0 := by
  change ((![(1 : ℝ), 0, 0] : Fin 3 → ℝ) : Torus (Fin 3)) = 0
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  intro a
  fin_cases a
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

theorem nonunitHistory_coord_one_two :
    torusCoordinate (2 : Fin 3) ((nonunitHistory k hk).1 1) = ((1 / 2 : ℝ) : UnitAddCircle) := by
  simp [nonunitHistory, predecessor]

/-- The first-level coordinate character detects the omitted prehistory. -/
theorem nonunitHistory_character :
    character (geometry k hk) (Finsupp.single (1, (2 : Fin 3)) 1)
      (nonunitHistory k hk) = -1 := by
  simp only [character_apply, phase_single, one_zsmul, nonunitHistory_coord_one_two,
    AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one]
  convert Complex.exp_pi_mul_I using 1
  congr 1
  push_cast
  ring

theorem nonunitHistory_ne_zero : nonunitHistory k hk ≠ 0 := by
  intro h
  have hc := nonunitHistory_character k hk
  rw [h, character_at_zero] at hc
  norm_num at hc

/-- Zeroth-coordinate projection really is noninjective for every member of this family. -/
theorem coord_zero_not_injective :
    ¬ Injective (fun z : Solenoid (geometry k hk) => z.1 0) := by
  intro h
  exact nonunitHistory_ne_zero k hk (h (nonunitHistory_coord_zero k hk))

end Psc.C4FamilySolenoidCharacters
