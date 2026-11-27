import PscVerif.PeriodicPartnerRealizationFinite

/-!
# Finite origin displacements in an actual realization fibre

The existing uniform bound on vector lifts puts equal-torus differences in
one finite integer set. Its length image contains every origin displacement,
so the nonzero displacements have a positive finite minimum. No sequence or
compactness argument is added here; the previously proved lift bound is an
explicit input. Source decision: `docs/c4-finite-fibre-obligations-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerOriginSeparation

open Function Matrix Set
open Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerRealizationFinite

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))

/-- A single finite set contains all origin displacements of all pairs
with equal zeroth torus coordinates. -/
theorem exists_finite_origin_displacements :
    ∃ D : Set ℝ, D.Finite ∧ ∀ T U : S.Hull,
      torusRealize P hR T = torusRealize P hR U →
      (origin T).2 - (origin U).2 ∈ D := by
  obtain ⟨K, hK⟩ := exists_realVec_bound P hR
  let A : Set (α → ℝ) := {v | v ∈ lattice α ∧ ‖v‖ ≤ 2 * K}
  refine ⟨(fun v => S.ℓ ⬝ᵥ v) '' A, (finite_lattice_ball (α := α) (2 * K)).image _, ?_⟩
  intro T U hTU
  let v := realVec P hR U - realVec P hR T
  have hv : v ∈ A := by
    refine ⟨QuotientAddGroup.eq_iff_sub_mem.mp hTU.symm, ?_⟩
    exact (norm_sub_le _ _).trans (by linarith [hK U, hK T])
  refine ⟨v, hv, ?_⟩
  simp only [v, dotProduct_sub, dot_realVec]
  ring

/-- Finite induction supplies a positive lower bound for the nonzero
absolute values in a finite real set; the empty case uses the bound one. -/
theorem finite_nonzero_gap {D : Set ℝ} (hD : D.Finite) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ D, d ≠ 0 → ε ≤ |d| := by
  classical
  induction D, hD using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a D ha hD ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      by_cases hzero : a = 0
      · refine ⟨ε, hε, ?_⟩
        intro d hd hd0
        rcases mem_insert_iff.mp hd with h | h
        · exact (hd0 (h.trans hzero)).elim
        · exact hbound d h hd0
      · refine ⟨min ε |a|, lt_min hε (abs_pos.mpr hzero), ?_⟩
        intro d hd hd0
        rcases mem_insert_iff.mp hd with h | h
        · simpa only [h] using min_le_right ε |a|
        · exact (min_le_left ε |a|).trans (hbound d h hd0)

/-- Equal-torus origin starts cannot differ by an arbitrarily small
nonzero displacement. The bound is uniform over all actual hull pairs. -/
theorem exists_origin_separation :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T U : S.Hull,
      torusRealize P hR T = torusRealize P hR U →
      |(origin T).2 - (origin U).2| < ε → (origin T).2 = (origin U).2 := by
  obtain ⟨D, hD, hmem⟩ := exists_finite_origin_displacements P hR
  obtain ⟨ε, hε, hbound⟩ := finite_nonzero_gap hD
  refine ⟨ε, hε, fun T U hTU hsmall => ?_⟩
  by_contra hne
  exact (not_lt_of_ge (hbound _ (hmem T U hTU) (sub_ne_zero.mpr hne))) hsmall

end Psc.PeriodicPartnerOriginSeparation
