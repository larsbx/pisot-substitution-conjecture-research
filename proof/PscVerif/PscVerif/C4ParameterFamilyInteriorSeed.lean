import PscVerif.C4ParameterFamilySolenoid

/-!
# A literal interior periodic seed

For `k ≥ 2`, the type-`1` tile at `-ℓ 0` follows a three-step inflation
cycle through the starts `ℓ 0 - ℓ 1` and `-ℓ 2`. The seed covers an open
neighborhood of zero and is contained in its cubed inflation, so the
existing growing-seed theorem supplies a legal periodic tiling.

This module establishes the actual hull construction and its origin
tiles. Membership in the zero fibre is a separate realization argument.
Source decision: `docs/c4-zero-fibre-witness-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyInteriorSeed

open Function Set Psc.ParameterFamilyTiling Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (inflateH)
open Psc.PeriodicPartnerRealization
open Psc.ParameterFamilyRows (substitution)
open Psc.ParameterFamilyWords (ones)
open Psc.PeriodicPartnerEvenTails (place_append)

variable (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)

include hk₂

/-- Three selected children of the type-`1` image. -/
theorem interior_child_positions (x : ℝ) :
    let S := geometry k hk
    (1, S.β * x + S.ℓ 0) ∈ S.place (S.σ 1) (S.β * x) ∧
    (1, S.β * x + S.ℓ 0 + ((k - 1 : ℕ) : ℝ) * S.ℓ 1) ∈
      S.place (S.σ 1) (S.β * x) ∧
    (1, S.β * x + S.ℓ 0 + S.ℓ 1) ∈ S.place (S.σ 1) (S.β * x) := by
  intro S
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
  have hσ : S.σ 1 = 0 :: 1 :: 1 :: (ones j ++ [2]) := by
    change substitution k 1 = _
    rw [hj]
    simp [substitution, ones, List.replicate_succ]
  have hlast : S.σ 1 = ([0] ++ ones (k - 1)) ++ [1, 2] := by
    change substitution k 1 = _
    have hon : ones k = ones (k - 1) ++ [1] := by
      unfold ones
      rw [show ([1] : List (Fin 3)) = List.replicate 1 1 by rfl,
        List.replicate_append_replicate]
      congr 1
      omega
    simp [substitution, hon, List.append_assoc]
  refine ⟨by simp [hσ, LengthSubst.place], ?_, by simp [hσ, LengthSubst.place]⟩
  rw [hlast, place_append]
  apply List.mem_append_right
  simp [LengthSubst.place, ones, nsmul_eq_mul, add_assoc]

/-- The three-step origin-tile cycle holds inside the literal inflation
of any patch containing the initial tile. -/
theorem interior_cycle_tiles {P : Set (Fin 3 × ℝ)}
    (hp : (1, -(geometry k hk).ℓ 0) ∈ P) :
    let S := geometry k hk
    (1, S.ℓ 0 - S.ℓ 1) ∈ S.inflate P ∧
    (1, -S.ℓ 2) ∈ S.inflate^[2] P ∧
    (1, -S.ℓ 0) ∈ S.inflate^[3] P := by
  intro S
  have e₀ : S.β * S.ℓ 0 = S.ℓ 1 := by
    dsimp [S, geometry]
    ring
  have e₁ : S.β * S.ℓ 1 = S.ℓ 0 + (k : ℝ) * S.ℓ 1 + S.ℓ 2 := by
    have h := S.eigen 1
    simpa [S, substitution, ones, nsmul_eq_mul, add_assoc] using h.symm
  have e₂ : S.β * S.ℓ 2 = 2 * S.ℓ 0 + S.ℓ 1 := by
    have h := S.eigen 2
    simpa [S, substitution, two_mul, add_assoc] using h.symm
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  have h₁ : (1, S.ℓ 0 - S.ℓ 1) ∈ S.inflate P := by
    refine ⟨(1, -S.ℓ 0), hp, ?_⟩
    convert (interior_child_positions k hk hk₂ (-S.ℓ 0)).1 using 1
    congr 1
    rw [mul_neg, e₀]
    ring
  have h₂ : (1, -S.ℓ 2) ∈ S.inflate^[2] P := by
    change (1, -S.ℓ 2) ∈ S.inflate (S.inflate P)
    refine ⟨(1, S.ℓ 0 - S.ℓ 1), h₁, ?_⟩
    have h := (interior_child_positions k hk hk₂ (S.ℓ 0 - S.ℓ 1)).2.1
    convert h using 1
    congr 1
    rw [mul_sub, e₀, e₁, hcast]
    ring
  have h₃ : (1, -S.ℓ 0) ∈ S.inflate^[3] P := by
    change (1, -S.ℓ 0) ∈ S.inflate (S.inflate^[2] P)
    refine ⟨(1, -S.ℓ 2), h₂, ?_⟩
    have h := (interior_child_positions k hk hk₂ (-S.ℓ 2)).2.2
    convert h using 1
    congr 1
    rw [mul_neg, e₂]
    ring
  exact ⟨h₁, h₂, h₃⟩

/-- The initial singleton seed extends to a legal tiling fixed by cubed
inflation. This assertion does not assume a geometric-factor property. -/
theorem interior_periodic_tiling :
    ∃ T : (geometry k hk).Hull,
      (1, -(geometry k hk).ℓ 0) ∈ T.1 ∧ inflateH^[3] T = T := by
  let S := geometry k hk
  let P : Set (Fin 3 × ℝ) := {(1, -S.ℓ 0)}
  have hβ := two_lt_expansion k hk
  have hy : 0 < -S.ℓ 0 + S.ℓ 1 := by
    dsimp [S, geometry]
    nlinarith
  have htiles : S.TilesOn (Ico (-S.ℓ 0) (-S.ℓ 0 + S.ℓ 1)) P := by
    simpa [P, LengthSubst.place] using S.tilesOn_place [1] (-S.ℓ 0)
  have hgrow : P ⊆ S.inflate^[3] P := by
    intro p hp
    have heq : p = (1, -S.ℓ 0) := hp
    subst p
    exact (interior_cycle_tiles k hk hk₂ (P := P) (by rfl)).2.2
  have hlegal : ∃ c n t, P ⊆ LengthSubst.shift t (S.supertile c n) := by
    refine ⟨1, 0, S.ℓ 0, ?_⟩
    rintro p (rfl : p = (1, -S.ℓ 0))
    simp [LengthSubst.shift, LengthSubst.supertile]
  obtain ⟨T, hP, hperiod⟩ := S.periodic_hull_of_seed (expansion_gt_one k hk)
    (by decide : 0 < 3) (neg_lt_zero.mpr (S.ℓ_pos 0)) hy htiles hgrow hlegal
  exact ⟨T, hP (by rfl), hperiod⟩

/-- The actual origin tile in all three phases of the interior cycle. -/
theorem interior_periodic_origins :
    ∃ T : (geometry k hk).Hull,
      inflateH^[3] T = T ∧
      origin T = (1, -(geometry k hk).ℓ 0) ∧
      origin (inflateH T) = (1, (geometry k hk).ℓ 0 - (geometry k hk).ℓ 1) ∧
      origin (inflateH^[2] T) = (1, -(geometry k hk).ℓ 2) := by
  let S := geometry k hk
  obtain ⟨T, hT, hperiod⟩ := interior_periodic_tiling k hk hk₂
  obtain ⟨h₁, h₂, _⟩ := interior_cycle_tiles k hk hk₂ hT
  have hβ := two_lt_expansion k hk
  have h01 : S.ℓ 0 < S.ℓ 1 := by dsimp [S, geometry]; nlinarith
  have h21 : S.ℓ 2 < S.ℓ 1 := by dsimp [S, geometry]; nlinarith
  refine ⟨T, hperiod, tileAt_eq hT ?_, tileAt_eq h₁ ?_, tileAt_eq h₂ ?_⟩
  · change 0 ∈ Ico (-S.ℓ 0) (-S.ℓ 0 + S.ℓ 1)
    constructor <;> linarith [S.ℓ_pos 0]
  · change 0 ∈ Ico (S.ℓ 0 - S.ℓ 1) (S.ℓ 0 - S.ℓ 1 + S.ℓ 1)
    constructor <;> linarith [S.ℓ_pos 0]
  · change 0 ∈ Ico (-S.ℓ 2) (-S.ℓ 2 + S.ℓ 1)
    constructor <;> linarith [S.ℓ_pos 2]

omit hk₂ in
/-- The interior seed's first phase has no tile beginning at zero. -/
theorem no_origin_vertex {T : (geometry k hk).Hull}
    (hT : origin T = (1, -(geometry k hk).ℓ 0)) :
    ¬ ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1 := by
  rintro ⟨a, ha⟩
  have hz : (0 : ℝ) ∈ (geometry k hk).supp (a, 0) :=
    ⟨le_rfl, by simpa using (geometry k hk).ℓ_pos a⟩
  have htile : origin T = (a, 0) := tileAt_eq ha hz
  have hstart := congrArg Prod.snd (hT.symm.trans htile)
  have hp := (geometry k hk).ℓ_pos 0
  change -(geometry k hk).ℓ 0 = 0 at hstart
  linarith

end Psc.ParameterFamilyInteriorSeed
