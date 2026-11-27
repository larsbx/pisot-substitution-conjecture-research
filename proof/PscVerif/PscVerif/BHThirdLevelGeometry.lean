import PscVerif.BHWindowChoice
import PscVerif.BHDiagonalLiteral

/-!
# A shared clean window for two separated obstruction sets

Three length-`4β` windows with gaps `3β` fit into a length-`18β`
interval. On each track, starts separated by at least `β³` can obstruct
at most one of those windows using conservative intervals of length `2β`.
The conclusion retains closed endpoints and excludes only intersections
of interiors. Actual substitution ancestry supplies the separation input.

This is the geometric part of the already reviewed construction in
`docs/bh-third-level-windows-2026-11-24.md`.
-/

namespace Psc.BHThirdLevelGeometry

def windowStart (β L : ℝ) (i : Fin 3) : ℝ := L+7*(i.val : ℝ)*β

def Blocks (β L : ℝ) (B : Set ℝ) (i : Fin 3) : Prop :=
  ∃ b ∈ B, windowStart β L i < b+2*β ∧ b < windowStart β L i+4*β

theorem window_bounds {β L : ℝ} (hβ : 0 < β) (i : Fin 3) :
    L ≤ windowStart β L i ∧ windowStart β L i+4*β ≤ L+18*β := by
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi2 : (i.val : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
  dsimp [windowStart]
  constructor <;> nlinarith

theorem cube_spacing {β : ℝ} (hβ : 12 < β) : 20*β < β^3 := by
  have hβ0 : 0 < β := by linarith
  have hs : (20 : ℝ) < β^2 := by nlinarith [sq_nonneg (β-12)]
  have hm := mul_lt_mul_of_pos_right hs hβ0
  nlinarith only [hm]

theorem one_interval_one_slot {β L b : ℝ} (hβ : 0 < β)
    (i j : Fin 3)
    (hi : windowStart β L i < b+2*β ∧ b < windowStart β L i+4*β)
    (hj : windowStart β L j < b+2*β ∧ b < windowStart β L j+4*β) : i = j := by
  fin_cases i <;> fin_cases j <;> norm_num [windowStart] at * <;>
    first | rfl | linarith

theorem separated_one_slot {β L : ℝ} (hβ : 12 < β) (B : Set ℝ)
    (hsep : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → β^3 ≤ |b-c|)
    (i j : Fin 3) (hi : Blocks β L B i) (hj : Blocks β L B j) : i = j := by
  obtain ⟨b, hb, hbi, hib⟩ := hi
  obtain ⟨c, hc, hcj, hjc⟩ := hj
  have hβ0 : 0 < β := by linarith
  obtain ⟨hli, hui⟩ := window_bounds (L := L) hβ0 i
  obtain ⟨hlj, huj⟩ := window_bounds (L := L) hβ0 j
  have hbc : b = c := by
    by_contra hne
    have hdist : |b-c| < 20*β := by
      apply abs_lt.mpr
      constructor <;> linarith
    exact (not_lt_of_ge (hsep b hb c hc hne)) (hdist.trans (cube_spacing hβ))
  subst c
  exact one_interval_one_slot hβ0 i j ⟨hbi, hib⟩ ⟨hcj, hjc⟩

/-- Two tracks leave a common clean window. No finiteness or attainment
assumption on either obstruction set is needed. -/
theorem exists_clean_window (β L : ℝ) (B₀ B₁ : Set ℝ) (hβ : 12 < β)
    (hsep₀ : ∀ b ∈ B₀, ∀ c ∈ B₀, b ≠ c → β^3 ≤ |b-c|)
    (hsep₁ : ∀ b ∈ B₁, ∀ c ∈ B₁, b ≠ c → β^3 ≤ |b-c|) :
    ∃ a : ℝ, L ≤ a ∧ a+4*β ≤ L+18*β ∧
      (∀ b ∈ B₀, b+2*β ≤ a ∨ a+4*β ≤ b) ∧
      (∀ b ∈ B₁, b+2*β ≤ a ∨ a+4*β ≤ b) := by
  obtain ⟨i, hi₀, hi₁⟩ := Psc.BHWindowChoice.exists_clean_slot
    (Blocks β L B₀) (Blocks β L B₁)
    (separated_one_slot hβ B₀ hsep₀) (separated_one_slot hβ B₁ hsep₁)
  obtain ⟨hlo, hhi⟩ := window_bounds (L := L) (by linarith : 0 < β) i
  refine ⟨windowStart β L i, hlo, hhi, ?_, ?_⟩
  · intro b hb
    by_cases hleft : b+2*β ≤ windowStart β L i
    · exact Or.inl hleft
    · exact Or.inr (le_of_not_gt (fun hright => hi₀ ⟨b, hb, lt_of_not_ge hleft, hright⟩))
  · intro b hb
    by_cases hleft : b+2*β ≤ windowStart β L i
    · exact Or.inl hleft
    · exact Or.inr (le_of_not_gt (fun hright => hi₁ ⟨b, hb, lt_of_not_ge hleft, hright⟩))

end Psc.BHThirdLevelGeometry
