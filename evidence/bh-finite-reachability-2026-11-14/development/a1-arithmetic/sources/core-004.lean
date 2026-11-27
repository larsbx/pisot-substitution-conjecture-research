import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PscVerif.Incidence

/-!
# Primitive irreducible Pisot arithmetic for the A1′ tail family

The matrix is bound to the actual words of both boundary layers.
The common arithmetic covers j=1 and j=2. Its square is positive, its
characteristic polynomial is irreducible, and a quadratic-factor argument
controls real and nonreal contracting roots separately.
Pre-code decision: docs/p1a-minimal-z3-tail-stop-go-2026-11-14.md.

The reconstruction history after the executor changed environments is
recorded separately; acceptance is tracked by the focused source gate.
-/

namespace Psc.A1PrimeTailPisot

open Matrix Polynomial
open Psc.Incidence (inc)

def matrix (e j : ℕ) : Matrix (Fin 3) (Fin 3) ℕ :=
  !![0, 2, 2; 1, 2 * e + j, e; 0, 4, 3]

theorem matrix_sq (e j : ℕ) :
    matrix e j ^ 2 =
      !![2, 2 * (2 * e + j) + 8, 2 * e + 6;
        2 * e + j, (2 * e + j) ^ 2 + 4 * e + 2, e * (2 * e + j) + 3 * e + 2;
        4, 4 * (2 * e + j) + 12, 4 * e + 9] := by
  rw [pow_two]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem matrix_primitive (e j : ℕ) (hj : j = 1 ∨ j = 2) :
    ∃ n ≥ 1, ∀ a c, 0 < (matrix e j ^ n) a c := by
  have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> omega
  refine ⟨2, by omega, ?_⟩
  rw [matrix_sq]
  intro a c
  fin_cases a <;> fin_cases c <;> simp <;> omega

noncomputable def matrixQ (e j : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (matrix e j).map (Nat.cast : ℕ → ℚ)

theorem matrixQ_eq (e j : ℕ) :
    matrixQ e j = !![0, 2, 2; 1, 2 * (e : ℚ) + (j : ℚ), (e : ℚ); 0, 4, 3] := by
  ext a c
  fin_cases a <;> fin_cases c <;> simp [matrixQ, matrix]

theorem matrix_determinant (e j : ℕ) : (matrixQ e j).det = 2 := by
  rw [matrixQ_eq, Matrix.det_fin_three]
  simp
  ring

noncomputable def polynomial (e j : ℕ) : ℚ[X] :=
  X ^ 3 - C (2 * (e : ℚ) + (j : ℚ) + 3) * X ^ 2 +
    C (2 * (e : ℚ) + 3 * (j : ℚ) - 2) * X - C 2

noncomputable def integerPolynomial (e j : ℕ) : ℤ[X] :=
  X ^ 3 - C (2 * (e : ℤ) + (j : ℤ) + 3) * X ^ 2 +
    C (2 * (e : ℤ) + 3 * (j : ℤ) - 2) * X - C 2

theorem matrix_charpoly (e j : ℕ) : (matrixQ e j).charpoly = polynomial e j := by
  rw [matrixQ_eq, Matrix.charpoly, Matrix.det_fin_three]
  simp [polynomial, map_ofNat]
  ring

theorem polynomial_natDegree (e j : ℕ) : (polynomial e j).natDegree = 3 := by
  unfold polynomial
  compute_degree!

theorem integerPolynomial_monic (e j : ℕ) : (integerPolynomial e j).Monic := by
  unfold integerPolynomial
  monicity!

theorem polynomial_eq_map (e j : ℕ) :
    polynomial e j = (integerPolynomial e j).map (Int.castRingHom ℚ) := by
  simp [polynomial, integerPolynomial, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_ofNat]

theorem polynomial_monic (e j : ℕ) : (polynomial e j).Monic := by
  rw [polynomial_eq_map]
  exact (integerPolynomial_monic e j).map _

theorem aeval_polynomial {A : Type*} [CommRing A] [Algebra ℚ A] (e j : ℕ) (z : A) :
    aeval z (polynomial e j) =
      z ^ 3 - (2 * (e : A) + (j : A) + 3) * z ^ 2 +
        (2 * (e : A) + 3 * (j : A) - 2) * z - 2 := by
  simp [polynomial, map_ofNat]

theorem aeval_integerPolynomial {A : Type*} [CommRing A] [Algebra ℤ A]
    (e j : ℕ) (z : A) :
    aeval z (integerPolynomial e j) =
      z ^ 3 - (2 * (e : A) + (j : A) + 3) * z ^ 2 +
        (2 * (e : A) + 3 * (j : A) - 2) * z - 2 := by
  simp [integerPolynomial, map_ofNat]

theorem no_rational_root (e j : ℕ) (hj : j = 1 ∨ j = 2) (x : ℚ) :
    ¬ (polynomial e j).IsRoot x := by
  intro hx
  have hx' : aeval x (integerPolynomial e j) = 0 := by
    have h0 : eval x (polynomial e j) = 0 := hx
    rw [aeval_integerPolynomial]
    simpa [polynomial] using h0
  obtain ⟨n, rfl, hn⟩ := exists_integer_of_is_root_of_monic
    (integerPolynomial_monic e j) hx'
  have hroot : n ^ 3 - (2 * (e : ℤ) + (j : ℤ) + 3) * n ^ 2 +
      (2 * (e : ℤ) + 3 * (j : ℤ) - 2) * n - 2 = 0 := by
    rw [aeval_integerPolynomial, algebraMap_int_eq, eq_intCast] at hx'
    exact_mod_cast hx'
  have hb : n.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num)
    (show n.natAbs ∣ 2 by
      simpa [integerPolynomial] using Int.natAbs_dvd_natAbs.mpr hn)
  have h1 : -2 ≤ n := by omega
  have h2 : n ≤ 2 := by omega
  have hez : (0 : ℤ) ≤ e := by omega
  rcases hj with rfl | rfl <;>
    interval_cases n <;> norm_num at hroot <;> omega

theorem polynomial_irreducible (e j : ℕ) (hj : j = 1 ∨ j = 2) :
    Irreducible (polynomial e j) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [polynomial_natDegree]; decide
  · exact no_rational_root e j hj

theorem matrix_irreducible (e j : ℕ) (hj : j = 1 ∨ j = 2) :
    Irreducible (matrixQ e j).charpoly := by
  rw [matrix_charpoly]
  exact polynomial_irreducible e j hj

theorem real_root (e j : ℕ) (hj : j = 1 ∨ j = 2) :
    ∃ b : ℝ, 2 * (e : ℝ) + (j : ℝ) + 2 < b ∧
      b < 2 * (e : ℝ) + (j : ℝ) + 3 ∧
      b ^ 3 - (2 * (e : ℝ) + (j : ℝ) + 3) * b ^ 2 +
        (2 * (e : ℝ) + 3 * (j : ℝ) - 2) * b - 2 = 0 := by
  have heR : (0 : ℝ) ≤ e := by positivity
  have hc : Continuous fun x : ℝ =>
      x ^ 3 - (2 * (e : ℝ) + (j : ℝ) + 3) * x ^ 2 +
        (2 * (e : ℝ) + 3 * (j : ℝ) - 2) * x - 2 := by
    fun_prop
  obtain ⟨b, ⟨h1, h2⟩, hb⟩ := intermediate_value_Ioo
    (show 2 * (e : ℝ) + (j : ℝ) + 2 ≤ 2 * (e : ℝ) + (j : ℝ) + 3 by linarith)
    hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo
      ((fun x : ℝ => x ^ 3 - (2 * (e : ℝ) + (j : ℝ) + 3) * x ^ 2 +
        (2 * (e : ℝ) + 3 * (j : ℝ) - 2) * x - 2)
        (2 * (e : ℝ) + (j : ℝ) + 2))
      ((fun x : ℝ => x ^ 3 - (2 * (e : ℝ) + (j : ℝ) + 3) * x ^ 2 +
        (2 * (e : ℝ) + 3 * (j : ℝ) - 2) * x - 2)
        (2 * (e : ℝ) + (j : ℝ) + 3)) by
      rcases hj with rfl | rfl <;>
        constructor <;> norm_num <;> nlinarith [sq_nonneg (e : ℝ)])
  exact ⟨b, h1, h2, hb⟩

theorem other_root (e j : ℕ) (hj : j = 1 ∨ j = 2) {b : ℝ} (hb2 : 2 < b)
    (hbA : b < 2 * (e : ℝ) + (j : ℝ) + 3)
    (hb : b ^ 3 - (2 * (e : ℝ) + (j : ℝ) + 3) * b ^ 2 +
      (2 * (e : ℝ) + 3 * (j : ℝ) - 2) * b - 2 = 0)
    {z : ℂ} (hz : z ^ 3 - (2 * (e : ℂ) + (j : ℂ) + 3) * z ^ 2 +
      (2 * (e : ℂ) + 3 * (j : ℂ) - 2) * z - 2 = 0)
    (hzb : z ≠ b) : ‖z‖ < 1 := by
  let p : ℝ := b ^ 2 - (2 * (e : ℝ) + (j : ℝ) + 3) * b +
    (2 * (e : ℝ) + 3 * (j : ℝ) - 2)
  let d : ℝ := b - (2 * (e : ℝ) + (j : ℝ) + 3)
  have hprod : b * p = 2 := by dsimp [p]; nlinarith [hb]
  have hp : 0 < p := by nlinarith
  have hp1 : p < 1 := by nlinarith
  have hd : d < 0 := by dsimp [d]; linarith
  have hq1prod : (b - 1) * (1 + d + p) = 6 - 2 * (j : ℝ) := by
    dsimp [d, p]
    nlinarith [hb]
  have hq1 : 0 < 1 + d + p := by
    rcases hj with rfl | rfl <;> norm_num at hq1prod <;> nlinarith
  have hq : z ^ 2 + (d : ℂ) * z + (p : ℂ) = 0 := by
    have hbC : (b : ℂ) ^ 3 - (2 * (e : ℂ) + (j : ℂ) + 3) * b ^ 2 +
        (2 * (e : ℂ) + 3 * (j : ℂ) - 2) * b - 2 = 0 := by exact_mod_cast hb
    have h : (z - b) * (z ^ 2 + (d : ℂ) * z + (p : ℂ)) = 0 := by
      dsimp [d, p]
      push_cast
      linear_combination hz - hbC
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hzb)
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im] at hre him
  set x := z.re
  set y := z.im
  by_cases hy : y = 0
  · have hx0 : 0 < x := by
      by_contra! hn
      have hdx : 0 ≤ d * x := mul_nonneg_of_nonpos_of_nonpos (le_of_lt hd) hn
      rw [hy] at hre
      nlinarith [sq_nonneg x]
    have hx1 : x < 1 := by
      by_contra! hn
      have hpos : 0 < x * (1 + d + p) := mul_pos hx0 hq1
      have hnonneg : 0 ≤ (x - 1) * (x - p) :=
        mul_nonneg (by linarith) (by linarith)
      rw [hy] at hre
      nlinarith
    have hn : ‖z‖ ^ 2 = x ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      change x * x + y * y = x ^ 2
      rw [hy]
      ring
    nlinarith [norm_nonneg z]
  · have hx : 2 * x + d = 0 := by
      have : y * (2 * x + d) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hy
    have hn : ‖z‖ ^ 2 = p := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      linear_combination (-1 : ℝ) * hre + x * hx
    nlinarith [norm_nonneg z]

theorem matrix_pisot (e j : ℕ) (hj : j = 1 ∨ j = 2) :
    ∃ b : ℝ, 2 * (e : ℝ) + (j : ℝ) + 2 < b ∧
      b < 2 * (e : ℝ) + (j : ℝ) + 3 ∧
      aeval (b : ℂ) (matrixQ e j).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (matrixQ e j).charpoly = 0 → z ≠ b → ‖z‖ < 1 := by
  obtain ⟨b, hbL, hbU, hb⟩ := real_root e j hj
  have hb2 : 2 < b := by
    have heR : (0 : ℝ) ≤ e := by positivity
    have hjR : (1 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
    linarith
  refine ⟨b, hbL, hbU, ?_, ?_⟩
  · rw [matrix_charpoly, aeval_polynomial]
    exact_mod_cast hb
  · intro z hz hzb
    rw [matrix_charpoly, aeval_polynomial] at hz
    exact other_root e j hj hb2 hbU hb hz hzb

theorem root_irrational (e j : ℕ) (hj : j = 1 ∨ j = 2) {b : ℝ}
    (hb : b ^ 3 - (2 * (e : ℝ) + (j : ℝ) + 3) * b ^ 2 +
      (2 * (e : ℝ) + 3 * (j : ℝ) - 2) * b - 2 = 0) : Irrational b := by
  rintro ⟨q, hq⟩
  apply no_rational_root e j hj q
  change eval q (polynomial e j) = 0
  simp only [polynomial, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  rw [← hq] at hb
  exact_mod_cast hb

theorem matrix_positive_left_eigenvector (e j : ℕ) {b : ℝ} (hb3 : 3 < b)
    (hb : b ^ 3 - (2 * (e : ℝ) + (j : ℝ) + 3) * b ^ 2 +
      (2 * (e : ℝ) + 3 * (j : ℝ) - 2) * b - 2 = 0) :
    ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
      w ᵥ* (matrix e j).map (Nat.cast : ℕ → ℝ) = b • w := by
  refine ⟨![b - 3, b * (b - 3), 2 + (e : ℝ) * b], ?_, ?_⟩
  · have heR : (0 : ℝ) ≤ e := by positivity
    intro a
    fin_cases a <;> simp <;> nlinarith
  · ext c
    fin_cases c <;>
      simp [matrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> nlinarith [hb]

theorem third_layer_unit_root (e : ℕ) :
    aeval (1 : ℂ) (matrixQ e 3).charpoly = 0 := by
  rw [matrix_charpoly, aeval_polynomial]
  norm_num
  ring

theorem third_layer_no_pisot_above_two (e : ℕ) :
    ¬ ∃ b : ℝ, 2 < b ∧ aeval (b : ℂ) (matrixQ e 3).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (matrixQ e 3).charpoly = 0 → z ≠ b → ‖z‖ < 1 := by
  rintro ⟨b, hb, _, hroots⟩
  have hne : (1 : ℂ) ≠ b := by
    intro h
    have hR := congrArg Complex.re h
    simp at hR
    linarith
  have h := hroots 1 (third_layer_unit_root e) hne
  norm_num at h


end Psc.A1PrimeTailPisot
