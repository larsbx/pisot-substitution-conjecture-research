/-
# `M0 = [[5,21,1],[6,26,1],[6,24,1]]` has an irreducible Pisot characteristic polynomial

`docs/c4-concentration-attack-2026-11-06.md` §§2, 3, 8.  `PscVerif.ConcentrationControls`
records `χ(x) = x³ - 32x² + 5x + 2 = det(xI - M0)` and its values at `±1, ±2, 0, 32`, but
leaves the two standard inferences (rational root theorem, intermediate value theorem) to
prose.  This module formalizes them.  With `f = X³ - 32X² + 5X + 2 : ℚ[X]` it proves:

* `f_irreducible : Irreducible f` -- `f` has degree 3, so irreducibility over `ℚ` is
  equivalent to having no rational root; a rational root of the monic integer cubic is an
  integer dividing `2` (`exists_integer_of_is_root_of_monic`), and `f(±1), f(±2) ≠ 0`.
* `f_is_charpoly : M0.charpoly = f`, for `M0 : Matrix (Fin 3) (Fin 3) ℚ` with rows
  `[5,21,1], [6,26,1], [6,24,1]`; `M0_eq_m0` identifies `M0` entrywise with the integer
  matrix `Psc.ConcentrationControls.m0`.
* `m0_pisot : ∃ b : ℝ, 1 < b ∧ aeval (b : ℂ) f = 0 ∧ ∀ z : ℂ, aeval z f = 0 → z ≠ b → ‖z‖ < 1`
  -- the intermediate value theorem gives real roots in `(-1,0)`, `(0,1)`, `(1,32)`; any
  three pairwise distinct roots of the cubic sum to `32` (`sum_of_distinct_roots`, a
  divided-difference identity valid in any field), so every complex root is one of the three.

Hypotheses: none -- all three theorems are about the fixed matrix/polynomial.  The auxiliary
lemma `sum_of_distinct_roots` assumes three roots in a field that are pairwise distinct;
both assumptions are needed (a repeated root gives no constraint on the third).

Not formalized here: any eigenvalue/eigenvector statement about `M0` beyond
`M0.charpoly = f` (e.g. that `b` is the Perron--Frobenius eigenvalue with a positive
eigenvector), any
statement about the substitution realizing `M0`, the unimodularity question (`det M0 = -2`,
so `M0` is *not* unimodular; see `ConcentrationControls.m0_det`), and any consequence for
the Pisot substitution conjecture.
-/
import Mathlib
import PscVerif.ConcentrationControls

namespace Psc.M0Pisot

open Polynomial

/-- `f = X³ - 32X² + 5X + 2`. -/
noncomputable def f : ℚ[X] := X ^ 3 - C 32 * X ^ 2 + C 5 * X + C 2

/-- The same cubic over `ℤ`, used for the rational root theorem. -/
noncomputable def fZ : ℤ[X] := X ^ 3 - C 32 * X ^ 2 + C 5 * X + C 2

def M0 : Matrix (Fin 3) (Fin 3) ℚ := !![5, 21, 1; 6, 26, 1; 6, 24, 1]

theorem M0_eq_m0 : ∀ i j, M0 i j = (Psc.ConcentrationControls.m0 i j : ℚ) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [M0, Psc.ConcentrationControls.m0]

theorem aeval_f {A : Type*} [CommRing A] [Algebra ℚ A] (z : A) :
    aeval z f = z ^ 3 - 32 * z ^ 2 + 5 * z + 2 := by
  simp [f, map_ofNat]

theorem aeval_fZ {A : Type*} [CommRing A] [Algebra ℤ A] (z : A) :
    aeval z fZ = z ^ 3 - 32 * z ^ 2 + 5 * z + 2 := by
  simp [fZ, map_ofNat]

theorem natDegree_f : f.natDegree = 3 := by
  unfold f; compute_degree!

theorem monic_fZ : fZ.Monic := by
  unfold fZ; monicity!

theorem coeff_zero_fZ : fZ.coeff 0 = 2 := by
  simp [fZ]

/-- `f` is the image of the monic integer polynomial `fZ`: its roots are
algebraic integers. -/
theorem f_eq_map : f = fZ.map (Int.castRingHom ℚ) := by
  simp [f, fZ, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    map_ofNat]

theorem f_monic : f.Monic := by
  rw [f_eq_map]; exact monic_fZ.map _

theorem f_irreducible : Irreducible f := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_f]; decide
  · intro x hx
    have hx' : aeval x fZ = 0 := by
      have h0 : eval x f = 0 := hx
      rw [aeval_fZ]; simpa [f] using h0
    obtain ⟨n, rfl, hn⟩ := exists_integer_of_is_root_of_monic monic_fZ hx'
    rw [coeff_zero_fZ] at hn
    have hroot : n ^ 3 - 32 * n ^ 2 + 5 * n + 2 = 0 := by
      rw [aeval_fZ, algebraMap_int_eq, eq_intCast] at hx'
      exact_mod_cast hx'
    have hb : n.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr hn)
    have h1 : -2 ≤ n := by omega
    have h2 : n ≤ 2 := by omega
    interval_cases n <;> norm_num at hroot

theorem f_is_charpoly : M0.charpoly = f := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [M0, f]
  simp only [map_ofNat]
  ring

/-- Three pairwise distinct roots of `x³ - 32x² + 5x + 2` in a field sum to `32`. -/
theorem sum_of_distinct_roots {K : Type*} [Field K] {a b c : K}
    (ha : a ^ 3 - 32 * a ^ 2 + 5 * a + 2 = 0) (hb : b ^ 3 - 32 * b ^ 2 + 5 * b + 2 = 0)
    (hc : c ^ 3 - 32 * c ^ 2 + 5 * c + 2 = 0) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a + b + c = 32 := by
  have qab : a ^ 2 + a * b + b ^ 2 - 32 * (a + b) + 5 = 0 := by
    have h : (a - b) * (a ^ 2 + a * b + b ^ 2 - 32 * (a + b) + 5) = 0 := by
      linear_combination ha - hb
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hab
    · exact h
  have qac : a ^ 2 + a * c + c ^ 2 - 32 * (a + c) + 5 = 0 := by
    have h : (a - c) * (a ^ 2 + a * c + c ^ 2 - 32 * (a + c) + 5) = 0 := by
      linear_combination ha - hc
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hac
    · exact h
  have h : (b - c) * (a + b + c - 32) = 0 := by linear_combination qab - qac
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) hbc
  · exact sub_eq_zero.1 h

/-- The real cubic `g(x) = x³ - 32x² + 5x + 2`. -/
def g (x : ℝ) : ℝ := x ^ 3 - 32 * x ^ 2 + 5 * x + 2

theorem g_continuous : Continuous g := by unfold g; fun_prop

theorem exists_root_neg : ∃ r ∈ Set.Ioo (-1 : ℝ) 0, g r = 0 := by
  have := intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num) g_continuous.continuousOn
  exact this ⟨by norm_num [g], by norm_num [g]⟩

theorem exists_root_small : ∃ r ∈ Set.Ioo (0 : ℝ) 1, g r = 0 := by
  have := intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by norm_num) g_continuous.continuousOn
  exact this ⟨by norm_num [g], by norm_num [g]⟩

theorem exists_root_big : ∃ r ∈ Set.Ioo (1 : ℝ) 32, g r = 0 := by
  have := intermediate_value_Ioo (show (1 : ℝ) ≤ 32 by norm_num) g_continuous.continuousOn
  exact this ⟨by norm_num [g], by norm_num [g]⟩

theorem aeval_ofReal_f (r : ℝ) (hr : g r = 0) : aeval (r : ℂ) f = 0 := by
  rw [aeval_f]
  have := congrArg (fun x : ℝ => (x : ℂ)) hr
  simp only [g] at this
  push_cast at this
  exact this

/-- `f` is a Pisot polynomial: it has a real root `b > 1` and every other complex root has
modulus `< 1`. -/
theorem m0_pisot : ∃ b : ℝ, 1 < b ∧ aeval (b : ℂ) f = 0 ∧
    ∀ z : ℂ, aeval z f = 0 → z ≠ b → ‖z‖ < 1 := by
  obtain ⟨r1, ⟨h1l, h1u⟩, h1⟩ := exists_root_neg
  obtain ⟨r2, ⟨h2l, h2u⟩, h2⟩ := exists_root_small
  obtain ⟨r3, ⟨h3l, h3u⟩, h3⟩ := exists_root_big
  have c1 := aeval_ofReal_f r1 h1
  have c2 := aeval_ofReal_f r2 h2
  have c3 := aeval_ofReal_f r3 h3
  rw [aeval_f] at c1 c2 c3
  have n12 : (r1 : ℂ) ≠ r2 := by exact_mod_cast (show r1 ≠ r2 by linarith)
  have n13 : (r1 : ℂ) ≠ r3 := by exact_mod_cast (show r1 ≠ r3 by linarith)
  have n23 : (r2 : ℂ) ≠ r3 := by exact_mod_cast (show r2 ≠ r3 by linarith)
  have s123 := sum_of_distinct_roots c1 c2 c3 n12 n13 n23
  refine ⟨r3, h3l, aeval_ofReal_f r3 h3, fun z hz hz3 => ?_⟩
  rw [aeval_f] at hz
  by_cases e1 : z = r1
  · rw [e1, Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  by_cases e2 : z = r2
  · rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have sz := sum_of_distinct_roots hz c1 c2 e1 e2 n12
  exact absurd (by linear_combination sz - s123) hz3

end Psc.M0Pisot
