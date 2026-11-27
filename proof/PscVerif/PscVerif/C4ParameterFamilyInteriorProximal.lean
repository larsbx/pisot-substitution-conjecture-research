import PscVerif.C4ParameterFamilySolenoid
import PscVerif.PeriodicPartnerProximal

/-!
# Exact coincidence between the seam and a period-three interior tiling

For `k ≥ 2`, the literal second `1` child places a shared type-`0` tile
between any period-two seam tiling starting in `1` at zero and any
period-three tiling containing `1` at `-ℓ 0`. This local calculation
does not assert that those tilings exhaust the zero fibre.

Source decision: `docs/c4-zero-fibre-witness-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyInteriorProximal

open Function Set Psc.ParameterFamilyTiling Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (inflateH)
open Psc.PeriodicPartnerProximal

/-- A concrete shared tile, proved from three levels of literal child placement.
Its coordinate is `ℓ 1 + β * ℓ 1` in both original tilings. -/
theorem seam_interior_common_tile (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
    {T U : (geometry k hk).Hull}
    (hT0 : (1, 0) ∈ T.1) (hT : inflateH^[2] T = T)
    (hU0 : (1, -(geometry k hk).ℓ 0) ∈ U.1) (hU : inflateH^[3] U = U) :
    (0, (geometry k hk).ℓ 1 + (geometry k hk).β * (geometry k hk).ℓ 1) ∈
      T.1 ∩ U.1 := by
  let S := geometry k hk
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
  have hσ : S.σ 1 = 0 :: 1 :: 1 :: (Psc.ParameterFamilyWords.ones j ++ [2]) := by
    change Psc.ParameterFamilyRows.substitution k 1 = _
    rw [hj]
    simp [Psc.ParameterFamilyRows.substitution, Psc.ParameterFamilyWords.ones,
      List.replicate_succ]
  have first_zero (V : S.Hull) (x : ℝ) (hx : (1, x) ∈ V.1) :
      (0, S.β * x) ∈ (inflateH V).1 := by
    refine ⟨(1, x), hx, ?_⟩
    change (0, S.β * x) ∈ S.place (S.σ 1) (S.β * x)
    simp [hσ, LengthSubst.place]
  have first_one (V : S.Hull) (x : ℝ) (hx : (1, x) ∈ V.1) :
      (1, S.β * x + S.ℓ 0) ∈ (inflateH V).1 := by
    refine ⟨(1, x), hx, ?_⟩
    change (1, S.β * x + S.ℓ 0) ∈ S.place (S.σ 1) (S.β * x)
    simp [hσ, LengthSubst.place]
  have second_one (V : S.Hull) (x : ℝ) (hx : (1, x) ∈ V.1) :
      (1, S.β * x + S.ℓ 0 + S.ℓ 1) ∈ (inflateH V).1 := by
    refine ⟨(1, x), hx, ?_⟩
    change (1, S.β * x + S.ℓ 0 + S.ℓ 1) ∈ S.place (S.σ 1) (S.β * x)
    simp [hσ, LengthSubst.place]
  have hlength : S.β * S.ℓ 0 = S.ℓ 1 := by
    dsimp [S, geometry]
    ring
  have hT1 : (1, S.ℓ 0 + S.ℓ 1) ∈ (inflateH T).1 := by
    simpa only [mul_zero, zero_add] using second_one T 0 hT0
  have hT2 := first_zero (inflateH T) (S.ℓ 0 + S.ℓ 1) hT1
  change inflateH (inflateH T) = T at hT
  rw [hT, mul_add, hlength] at hT2
  have hU1 : (1, S.ℓ 0) ∈ (inflateH U).1 := by
    have h := second_one U (-S.ℓ 0) hU0
    rw [mul_neg, hlength] at h
    convert h using 2
    ring
  have hU2 := first_one (inflateH U) (S.ℓ 0) hU1
  have hU3 := first_zero (inflateH (inflateH U)) (S.β * S.ℓ 0 + S.ℓ 0) hU2
  change inflateH (inflateH (inflateH U)) = U at hU
  rw [hU, mul_add, hlength, add_comm] at hU3
  exact ⟨hT2, hU3⟩

/-- The interior tiling and the seam tiling admit arbitrary-radius exact
agreement after a common shift. Their original origin patches need not agree. -/
theorem seam_interior_exactProximal (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
    {T U : (geometry k hk).Hull}
    (hT0 : (1, 0) ∈ T.1) (hT : inflateH^[2] T = T)
    (hU0 : (1, -(geometry k hk).ℓ 0) ∈ U.1) (hU : inflateH^[3] U = U) :
    ExactProximal (geometry k hk) T U :=
  exactProximal_of_periodic_common_tile _ (expansion_gt_one k hk)
    (by decide : 0 < 2) (by decide : 0 < 3) hT hU
    ⟨_, seam_interior_common_tile k hk hk₂ hT0 hT hU0 hU⟩

/-- Every phase of the period-three interior orbit has arbitrary-radius
exact common-shift agreement with the same period-two seam anchor. At
depth `4*i`, the anchor returns and the interior phase advances by `i`. -/
theorem seam_interior_orbit_exactProximal (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
    {T U : (geometry k hk).Hull}
    (hT0 : (1, 0) ∈ T.1) (hT : inflateH^[2] T = T)
    (hU0 : (1, -(geometry k hk).ℓ 0) ∈ U.1) (hU : inflateH^[3] U = U)
    (i : ℕ) : ExactProximal (geometry k hk) T (inflateH^[i] U) := by
  have h := (seam_interior_exactProximal k hk hk₂ hT0 hT hU0 hU).inflate_iterate _ (4 * i)
  have hT' : inflateH^[4 * i] T = T := by
    rw [show 4 * i = 2 * (2 * i) by omega, iterate_mul]
    exact IsFixedPt.iterate hT _
  have hUi : inflateH^[3 * i] U = U := by
    rw [iterate_mul]
    exact IsFixedPt.iterate hU _
  have hU' : inflateH^[4 * i] U = inflateH^[i] U := by
    rw [show 4 * i = i + 3 * i by omega, iterate_add_apply, hUi]
  rwa [hT', hU'] at h

end Psc.ParameterFamilyInteriorProximal
