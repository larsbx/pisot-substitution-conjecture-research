import PscVerif.BHDiagonalLiteral
import Mathlib.Topology.Order.IntermediateValue

/-! Algebraic existence and uniqueness for the diagonal parameter root.
The bracketed root is constructed for every integer parameter `r ≥ 12`;
it is not retained as an extra existence premise in the family endpoint.
-/

namespace Psc.BHDiagonalParameters

open Psc.BHDiagonalLiteral

theorem bracketed_root_exists (r k : ℕ) (hr : 12 ≤ r) (hk : r ≤ k) :
    ∃ β : ℝ, (k : ℝ) < β ∧ β < (k : ℝ)+1 ∧
      β^3 = (k : ℝ)*β^2+2*β+r := by
  let f : ℝ → ℝ := fun x => x^3-(k : ℝ)*x^2-2*x-r
  have hrR : (12 : ℝ) ≤ r := by exact_mod_cast hr
  have hkR : (r : ℝ) ≤ k := by exact_mod_cast hk
  have hlo : f k < 0 := by dsimp [f]; nlinarith
  have hhi : 0 < f ((k : ℝ)+1) := by
    have he : f ((k : ℝ)+1) = (k : ℝ)^2-r-1 := by dsimp [f]; ring
    rw [he]
    nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hc : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨β, hβ, hf⟩ := intermediate_value_Ioo
    (show (k : ℝ) ≤ (k : ℝ)+1 by linarith) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (f k) (f ((k : ℝ)+1)) from ⟨hlo, hhi⟩)
  refine ⟨β, hβ.1, hβ.2, ?_⟩
  dsimp [f] at hf
  linarith

theorem family_root_exists (r : ℕ) (hr : 12 ≤ r) :
    ∃ β : ℝ, Family r β := by
  obtain ⟨β, hlo, hhi, hc⟩ := bracketed_root_exists r r hr le_rfl
  exact ⟨β, hr, hlo, hhi, hc⟩

theorem near_diagonal_root_exists (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r+1 ≤ k) (hkhi : k ≤ r+2) :
    ∃ β : ℝ, Psc.BHNearDiagonalLiteral.Family r k β := by
  obtain ⟨β, hlo, hhi, hc⟩ := bracketed_root_exists r k hr (by omega)
  exact ⟨β, hr, hklo, hkhi, hlo, hhi, hc⟩

theorem cubic_factor {r β} (h : Family r β) (x : ℝ) :
    (x-β)*(x^2+(β-r)*x+r/β) = x^3-(r : ℝ)*x^2-2*x-r := by
  have ha := a_identity h
  have hb : β*((r : ℝ)/β) = r := mul_div_cancel₀ _ (beta_pos h).ne'
  have hax := congrArg (fun v : ℝ => v*x) ha
  nlinarith only [hb, hax]

/-- The required root is unique even among all positive real roots. -/
theorem positive_root_unique {r β} (h : Family r β) {x : ℝ}
    (hx : 0 < x) (hroot : x^3-(r : ℝ)*x^2-2*x-r = 0) : x = β := by
  have hfactor : (x-β)*(x^2+(β-r)*x+r/β) = 0 := by
    rw [cubic_factor h, hroot]
  have hquad : 0 < x^2+(β-r)*x+r/β := by
    have hp := mul_pos (a_pos h) hx
    nlinarith only [sq_nonneg x, hp, b_pos h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hquad.ne')

theorem family_root_unique {r β γ} (hβ : Family r β) (hγ : Family r γ) :
    γ = β :=
  positive_root_unique hβ (beta_pos hγ) (by linarith [hγ.cubic])

theorem quadratic_factor_pos {r β} (h : Family r β) (x : ℝ) :
    0 < x^2+(β-r)*x+r/β := by
  have hs := mul_pos (a_pos h) (sub_pos.mpr (a_small h))
  nlinarith only [hs, a_small h, b_large h, sq_nonneg (x+(β-r)/2)]

/-- The other two roots cannot be real; the full cubic has a unique real root. -/
theorem real_root_unique {r β} (h : Family r β) {x : ℝ}
    (hroot : x^3-(r : ℝ)*x^2-2*x-r = 0) : x = β := by
  have hfactor : (x-β)*(x^2+(β-r)*x+r/β) = 0 := by
    rw [cubic_factor h, hroot]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_right (quadratic_factor_pos h x).ne')

theorem root_not_integer {r β} (h : Family r β) (z : ℤ) : (z : ℝ) ≠ β := by
  intro hz
  have hlo : (r : ℤ) < z := by exact_mod_cast (hz ▸ h.lower)
  have hhi : z < (r : ℤ)+1 := by exact_mod_cast (hz ▸ h.upper)
  omega

theorem no_integer_root {r β} (h : Family r β) (z : ℤ) :
    (z : ℝ)^3-(r : ℝ)*(z : ℝ)^2-2*(z : ℝ)-r ≠ 0 := by
  intro hz
  exact root_not_integer h z (real_root_unique h hz)

end Psc.BHDiagonalParameters
