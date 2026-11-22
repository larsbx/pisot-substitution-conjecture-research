import PscVerif.C4ParameterFamilySolenoid
import PscVerif.PeriodicPartnerProximal

/-!
# Literal zero-fibre controls

The seam `1.1` and its one-step inflation both realize to zero. Their
right tiles at the origin have different labels. Thus equal solenoid
histories do not give direct exact agreement of the original tilings.

This does not refute the existential common-shift witnesses: those
allow two auxiliary legal tilings. Nor does a multiple exceptional
fibre refute coincidence rank one or almost-everywhere injectivity.

Source decision: `docs/c4-zero-fibre-witness-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyZeroFibreControls

open Function Set Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyRecognizability Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (inflateH Agree)
open Psc.PeriodicPartnerLegalCoincidence (originPatch)
open Psc.PeriodicPartnerLocalTopology
open Psc.PeriodicPartnerProximal

/-- The literal seam tiling and its inflation give distinct zero-fibre
members, with different closed origin patches and no direct radius-one
agreement, for every `k ≥ 1`. -/
theorem zero_fibre_seam_control (k : ℕ) (hk : 1 ≤ k) :
    ∃ T U : (geometry k hk).Hull,
      inflateH T = U ∧ inflateH^[2] T = T ∧
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ∧
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 ∧
      (1, 0) ∈ T.1 ∧ (0, 0) ∈ U.1 ∧ T ≠ U ∧
      originPatch (geometry k hk) T.1 ≠ originPatch (geometry k hk) U.1 ∧
      ¬ Agree 1 T U := by
  let S := geometry k hk
  obtain ⟨T, hleft, hright, hperiod⟩ := fixed_hull_tiling k hk
  let U := inflateH T
  have hzT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0 := by
    apply realize_r4 (pisotData k hk) (inflateH_bijective k hk) (b := 1)
    · exact ⟨2, by decide, hperiod⟩
    · exact (show (1, 0 - S.ℓ 1) ∈ T.1 by simpa using hleft)
  have hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0 := by
    change realize (pisotData k hk) (inflateH_bijective k hk) (inflateH T) = 0
    rw [realize_inflate, hzT, shiftS_zero]
  have hzero : (0, (0 : ℝ)) ∈ U.1 := by
    refine ⟨(1, 0), hright, ?_⟩
    change (0, (0 : ℝ)) ∈ S.place (Psc.ParameterFamilyRows.substitution k 1) (S.β * 0)
    simp [Psc.ParameterFamilyRows.substitution, LengthSubst.place]
  have hnot : (1, (0 : ℝ)) ∉ U.1 := by
    intro h
    have h₁ : (0 : ℝ) ∈ S.supp (1, 0) := ⟨le_rfl, by simpa using S.ℓ_pos 1⟩
    have h₀ : (0 : ℝ) ∈ S.supp (0, 0) := ⟨le_rfl, by simpa using S.ℓ_pos 0⟩
    have hlabels := congrArg Prod.fst ((U.2.1 0).unique ⟨h, h₁⟩ ⟨hzero, h₀⟩)
    norm_num at hlabels
  have hne : T ≠ U := by
    intro h
    exact hnot (h ▸ hright)
  have horigin : originPatch S T.1 ≠ originPatch S U.1 := by
    intro h
    have hm : (1, (0 : ℝ)) ∈ originPatch S T.1 :=
      ⟨hright, le_rfl, by simpa using (S.ℓ_pos 1).le⟩
    rw [h] at hm
    exact hnot hm.1
  have hdisagree : ¬ Agree 1 T U := by
    intro h
    have hmeet : (S.supp (1, (0 : ℝ)) ∩ Ioo (-1) 1).Nonempty :=
      ⟨0, ⟨le_rfl, by simpa using S.ℓ_pos 1⟩, by constructor <;> norm_num⟩
    exact hnot ((h (1, 0) hmeet).mp hright)
  exact ⟨T, U, rfl, hperiod, hzT, hzU, hright, hzero, hne, horigin, hdisagree⟩

/-- The constructed ordinary-hull solenoid realization is not globally
injective, even though the intended spectral conclusion concerns almost
everywhere injectivity. -/
theorem solenoidRealize_not_injective (k : ℕ) (hk : 1 ≤ k) :
    ¬ Injective (solenoidRealize k hk) := by
  obtain ⟨T, U, _, _, hzT, hzU, _, _, hne, _, _⟩ := zero_fibre_seam_control k hk
  intro hinj
  apply hne
  have heq : solenoidRealize k hk (ofExact (geometry k hk) T) =
      solenoidRealize k hk (ofExact (geometry k hk) U) := hzT.trans hzU.symm
  exact congrArg LocalHull.toHull (hinj heq)

/-- In the literal seam pair, the right words `101` and `011` place the
same type-`1` tile after the equal-length prefixes `10` and `01`. This
positive control needs `k ≥ 2`. -/
theorem seam_pair_common_tile (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
    {T : (geometry k hk).Hull} (hright : (1, 0) ∈ T.1)
    (hperiod : inflateH^[2] T = T) :
    (1, (geometry k hk).ℓ 0 + (geometry k hk).ℓ 1) ∈
      T.1 ∩ (inflateH T).1 := by
  let S := geometry k hk
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
  have hσ : S.σ 1 = 0 :: 1 :: 1 :: (Psc.ParameterFamilyWords.ones j ++ [2]) := by
    change Psc.ParameterFamilyRows.substitution k 1 = _
    rw [hj]
    simp [Psc.ParameterFamilyRows.substitution, Psc.ParameterFamilyWords.ones,
      List.replicate_succ]
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
  have hfirst : (1, S.ℓ 0) ∈ (inflateH T).1 := by
    simpa only [mul_zero, zero_add] using first_one T 0 hright
  have hsecond : (1, S.ℓ 0 + S.ℓ 1) ∈ (inflateH T).1 := by
    simpa only [mul_zero, zero_add] using second_one T 0 hright
  have hlength : S.β * S.ℓ 0 = S.ℓ 1 := by
    dsimp [S, geometry]
    ring
  have hT := first_one (inflateH T) (S.ℓ 0) hfirst
  change inflateH (inflateH T) = T at hperiod
  rw [hperiod, hlength, add_comm (S.ℓ 1) (S.ℓ 0)] at hT
  exact ⟨hT, hsecond⟩

/-- An actual nontrivial zero-fibre pair admits exact common-shift
agreements at every positive radius, despite having unequal origin
patches before translation. This establishes genuine witnesses for the
literal seam pair; it does not quantify over every zero-fibre pair. -/
theorem zero_fibre_pair_with_exact_shifts (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) :
    ∃ T U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ∧
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 ∧
      originPatch (geometry k hk) T.1 ≠ originPatch (geometry k hk) U.1 ∧
      ExactProximal (geometry k hk) T U := by
  obtain ⟨T, U, hTU, hperiod, hzT, hzU, hright, _, _, horigin, _⟩ :=
    zero_fibre_seam_control k hk
  refine ⟨T, U, hzT, hzU, horigin, ?_⟩
  have hperiodU : inflateH^[2] U = U := by
    rw [← hTU]
    exact congrArg inflateH hperiod
  have hc : (T.1 ∩ U.1).Nonempty := by
    rw [← hTU]
    exact ⟨_, seam_pair_common_tile k hk hk₂ hright hperiod⟩
  exact exactProximal_of_periodic_common_tile (geometry k hk)
    (expansion_gt_one k hk) (by decide : 0 < 2) (by decide : 0 < 2)
    hperiod hperiodU hc

end Psc.ParameterFamilyZeroFibreControls
