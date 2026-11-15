/-
# The actual literal incidence cubic and its dominant root

The displayed cubic is the characteristic polynomial of the literal
substitution incidence matrix. Its bracketed real root is greater than one;
every other complex root has norm less than one. Together with the explicit
positive normalized scaling row, this identifies the algebraic Perron root
without invoking a substitution dynamical or spectral conclusion.

Pre-code scope: `docs/bh-class-a-literal-lean-stop-go-2026-11-14.md`.
-/
import PscVerif.ClassAMinusNoHalfUnit
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace Psc.ClassAMinusRootSpectrum

open Polynomial Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusLiteralArithmetic Psc.ClassAMinusNoHalfUnit Matrix

def literalMatrix (n d : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (incidenceZ (sigma n d)).map (fun z => (z : ℚ))

theorem literal_matrix_entries (n d : ℕ) (hn : 1 ≤ n) :
    literalMatrix n d = !![2, 1, 1; 0, 1, 1; (n : ℚ)+d, n, (n : ℚ)-1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [literalMatrix, incidenceZ, inc, sigma, first, last, runLength,
      List.count_replicate, Nat.cast_sub hn]

/-- This polynomial binding is derived from literal word counts. -/
theorem literal_charpoly (n d : ℕ) (hn : 1 ≤ n) :
    (literalMatrix n d).charpoly = polyQ n d := by
  rw [literal_matrix_entries n d hn, Matrix.charpoly, Matrix.det_fin_three]
  simp [polyQ]
  simp only [map_ofNat]
  ring

/-- The normalized positive row is an eigenrow of the actual incidence matrix. -/
theorem literal_positive_eigenrow (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) :
    (∀ a, 0 < lengths n β a) ∧
      lengths n β ᵥ* (literalMatrix n d).map (fun z => (z : ℝ)) = β • lengths n β := by
  refine ⟨literal_lengths_pos n d hd hn β hroot, ?_⟩
  funext a
  have hh := literal_length_scaling n d hd hn β hroot a
  simpa [literalMatrix, Matrix.vecMul, dotProduct, incidenceZ, inc, physicalLength,
    Pi.smul_apply, smul_eq_mul] using hh

theorem cubic_continuous (n d : ℕ) : Continuous (cubic n d) := by
  unfold cubic
  fun_prop

theorem negative_root_exists (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n) :
    ∃ r ∈ Set.Ioo (-1 : ℝ) 0, cubic n d r = 0 := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (d : ℝ)+1 ≤ n := by exact_mod_cast hn
  apply intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num)
    (cubic_continuous n d).continuousOn
  constructor
  · norm_num [cubic]
    linarith
  · norm_num [cubic]

theorem small_positive_root_exists (n d : ℕ) (hd : 5 ≤ d) :
    ∃ r ∈ Set.Ioo (0 : ℝ) 1, cubic n d r = 0 := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  apply intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by norm_num)
    (cubic_continuous n d).continuousOn
  constructor
  · norm_num [cubic]
    linarith
  · norm_num [cubic]

/-- The divided-difference identity for three distinct roots of this cubic. -/
theorem sum_of_distinct_roots {K : Type*} [Field K] (n d : ℕ) {a b c : K}
    (ha : a^3-((n : K)+2)*a^2+((n : K)-(d : K)-1)*a+2 = 0)
    (hb : b^3-((n : K)+2)*b^2+((n : K)-(d : K)-1)*b+2 = 0)
    (hc : c^3-((n : K)+2)*c^2+((n : K)-(d : K)-1)*c+2 = 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : a+b+c = (n : K)+2 := by
  have qab : a^2+a*b+b^2-((n : K)+2)*(a+b)+((n : K)-(d : K)-1) = 0 := by
    have hh : (a-b)*(a^2+a*b+b^2-((n : K)+2)*(a+b)+((n : K)-(d : K)-1)) = 0 := by
      linear_combination ha-hb
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hab)
  have qac : a^2+a*c+c^2-((n : K)+2)*(a+c)+((n : K)-(d : K)-1) = 0 := by
    have hh : (a-c)*(a^2+a*c+c^2-((n : K)+2)*(a+c)+((n : K)-(d : K)-1)) = 0 := by
      linear_combination ha-hc
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hac)
  have hh : (b-c)*(a+b+c-((n : K)+2)) = 0 := by
    linear_combination qab-qac
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hbc))

theorem aeval_polyQ {K : Type*} [CommRing K] [Algebra ℚ K]
    (n d : ℕ) (z : K) :
    aeval z (polyQ n d) = z^3-((n : K)+2)*z^2+((n : K)-(d : K)-1)*z+2 := by
  simp [polyQ, map_ofNat]

/-- Every other complex characteristic root is strictly inside the unit disk. -/
theorem literal_other_roots (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) :
    1 < β ∧ aeval (β : ℂ) (literalMatrix n d).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (literalMatrix n d).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1 := by
  have hn1 : 1 ≤ n := by omega
  rw [literal_charpoly n d hn1]
  have hβ1 : 1 < β := by linarith [hroot.lower, Nat.cast_nonneg (α := ℝ) n]
  have hcβ : (β : ℂ)^3-((n : ℂ)+2)*(β : ℂ)^2+
      ((n : ℂ)-(d : ℂ)-1)*(β : ℂ)+2 = 0 := by
    have hh := hroot.cubic_eq_zero
    dsimp [cubic] at hh
    exact_mod_cast hh
  have hbroot : aeval (β : ℂ) (polyQ n d) = 0 := by
    rw [aeval_polyQ]
    exact hcβ
  obtain ⟨r₁, ⟨h₁l, h₁u⟩, hr₁⟩ := negative_root_exists n d hd hn
  obtain ⟨r₂, ⟨h₂l, h₂u⟩, hr₂⟩ := small_positive_root_exists n d hd
  have hc₁ : (r₁ : ℂ)^3-((n : ℂ)+2)*(r₁ : ℂ)^2+
      ((n : ℂ)-(d : ℂ)-1)*(r₁ : ℂ)+2 = 0 := by
    dsimp [cubic] at hr₁
    exact_mod_cast hr₁
  have hc₂ : (r₂ : ℂ)^3-((n : ℂ)+2)*(r₂ : ℂ)^2+
      ((n : ℂ)-(d : ℂ)-1)*(r₂ : ℂ)+2 = 0 := by
    dsimp [cubic] at hr₂
    exact_mod_cast hr₂
  have h₁₂ : (r₁ : ℂ) ≠ r₂ := by exact_mod_cast (show r₁ ≠ r₂ by linarith)
  have hb₁ : (β : ℂ) ≠ r₁ := by exact_mod_cast (show β ≠ r₁ by linarith)
  have hb₂ : (β : ℂ) ≠ r₂ := by exact_mod_cast (show β ≠ r₂ by linarith)
  have hsβ := sum_of_distinct_roots n d hcβ hc₁ hc₂ hb₁ hb₂ h₁₂
  refine ⟨hβ1, hbroot, ?_⟩
  intro z hz hzb
  rw [aeval_polyQ] at hz
  by_cases he₁ : z = r₁
  · rw [he₁, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  by_cases he₂ : z = r₂
  · rw [he₂, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hsz := sum_of_distinct_roots n d hz hc₁ hc₂ he₁ he₂ h₁₂
  exact absurd (by linear_combination hsz-hsβ) hzb

/-- Existence and literal binding of the dominant Pisot characteristic root.
No substitution dynamical consequence is part of this algebraic endpoint. -/
theorem literal_pisot_root_exists (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n) :
    ∃ β : ℝ, RootData n d β ∧ (∀ a, 0 < lengths n β a) ∧
      lengths n β ᵥ* (literalMatrix n d).map (fun z => (z : ℝ)) = β • lengths n β ∧
      1 < β ∧ aeval (β : ℂ) (literalMatrix n d).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (literalMatrix n d).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1 := by
  obtain ⟨β, hroot⟩ := root_exists n d hd hn
  have hrow := literal_positive_eigenrow n d hd hn β hroot
  exact ⟨β, hroot, hrow.1, hrow.2, literal_other_roots n d hd hn β hroot⟩

end Psc.ClassAMinusRootSpectrum
