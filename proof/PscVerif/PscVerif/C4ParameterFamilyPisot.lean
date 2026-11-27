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
import PscVerif.C4ParameterFamilyWords

/-!
# Primitive irreducible Pisot arithmetic for the literal parameter family

The substitution is the existing `0 ↦ 1`, `1 ↦ 0 1^k 2`, `2 ↦ 001`.
Every matrix below is identified with its actual image-letter counts. For
`k ≥ 1` its incidence square is positive, its rational characteristic polynomial
is irreducible, and it has a real root `β > 2` with every other complex root of
modulus less than one. The explicit positive left eigenvector binds this root
to the same incidence matrix. No finite parameter sample supplies these results.

The proof uses the standard rational-root and quadratic-root arguments already
used in `M0Pisot` and `Degree3Sector`, with the parameter retained. The pre-code
scope decision is `docs/c4-family-pisot-bridge-stop-go-2026-11-14.md`.
No spectral-dynamical theorem or universal PSC conclusion is asserted here.
-/

namespace Psc.ParameterFamilyPisot

open Matrix Polynomial
open Psc.Incidence (inc)
open Psc.ParameterFamilyRows (substitution)

/-- The literal image-letter counts, with source letters indexing columns. -/
theorem incidence_eq (k : ℕ) :
    inc (substitution k) = !![0, 1, 2; 1, k, 1; 0, 1, 0] := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Psc.Incidence.inc_apply, substitution, Psc.ParameterFamilyWords.ones,
      List.count_replicate]

/-- The positive square is computed on the actual incidence matrix. -/
theorem incidence_sq (k : ℕ) :
    inc (substitution k) ^ 2 =
      !![1, k + 2, 1; k, k ^ 2 + 2, k + 2; 1, k, 1] := by
  rw [incidence_eq, pow_two]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem primitive (k : ℕ) (hk : 1 ≤ k) :
    ∃ n ≥ 1, ∀ a c, 0 < (inc (substitution k) ^ n) a c := by
  refine ⟨2, by omega, ?_⟩
  rw [incidence_sq]
  intro a c
  fin_cases a <;> fin_cases c <;> simp <;> omega

/-- Rational cast of the actual incidence matrix. -/
noncomputable def incidenceQ (k : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (inc (substitution k)).map (Nat.cast : ℕ → ℚ)

theorem incidenceQ_eq (k : ℕ) :
    incidenceQ k = !![0, 1, 2; 1, (k : ℚ), 1; 0, 1, 0] := by
  rw [incidenceQ, incidence_eq]
  ext a c
  fin_cases a <;> fin_cases c <;> simp

/-- In particular this family is nonunimodular. -/
theorem determinant (k : ℕ) : (incidenceQ k).det = 2 := by
  rw [incidenceQ_eq, Matrix.det_fin_three]
  simp

noncomputable def polynomial (k : ℕ) : ℚ[X] :=
  X ^ 3 - C (k : ℚ) * X ^ 2 - C 2 * X - C 2

noncomputable def integerPolynomial (k : ℕ) : ℤ[X] :=
  X ^ 3 - C (k : ℤ) * X ^ 2 - C 2 * X - C 2

theorem charpoly_eq (k : ℕ) : (incidenceQ k).charpoly = polynomial k := by
  rw [incidenceQ_eq, Matrix.charpoly, Matrix.det_fin_three]
  simp [polynomial, map_ofNat]
  ring

theorem polynomial_natDegree (k : ℕ) : (polynomial k).natDegree = 3 := by
  unfold polynomial
  compute_degree!

theorem integerPolynomial_monic (k : ℕ) : (integerPolynomial k).Monic := by
  unfold integerPolynomial
  monicity!

theorem polynomial_eq_map (k : ℕ) :
    polynomial k = (integerPolynomial k).map (Int.castRingHom ℚ) := by
  simp [polynomial, integerPolynomial, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_ofNat]

theorem polynomial_monic (k : ℕ) : (polynomial k).Monic := by
  rw [polynomial_eq_map]
  exact (integerPolynomial_monic k).map _

theorem aeval_polynomial {A : Type*} [CommRing A] [Algebra ℚ A] (k : ℕ) (z : A) :
    aeval z (polynomial k) = z ^ 3 - (k : A) * z ^ 2 - 2 * z - 2 := by
  simp [polynomial, map_ofNat]

theorem aeval_integerPolynomial {A : Type*} [CommRing A] [Algebra ℤ A]
    (k : ℕ) (z : A) :
    aeval z (integerPolynomial k) = z ^ 3 - (k : A) * z ^ 2 - 2 * z - 2 := by
  simp [integerPolynomial, map_ofNat]

/-- A rational root would be an integer dividing two; each candidate fails. -/
theorem no_rational_root (k : ℕ) (hk : 1 ≤ k) (x : ℚ) :
    ¬ (polynomial k).IsRoot x := by
  intro hx
  have hx' : aeval x (integerPolynomial k) = 0 := by
    have h0 : eval x (polynomial k) = 0 := hx
    rw [aeval_integerPolynomial]
    simpa [polynomial] using h0
  obtain ⟨n, rfl, hn⟩ := exists_integer_of_is_root_of_monic
    (integerPolynomial_monic k) hx'
  have hroot : n ^ 3 - (k : ℤ) * n ^ 2 - 2 * n - 2 = 0 := by
    rw [aeval_integerPolynomial, algebraMap_int_eq, eq_intCast] at hx'
    exact_mod_cast hx'
  have hb : n.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num)
    (show n.natAbs ∣ 2 by
      simpa [integerPolynomial] using Int.natAbs_dvd_natAbs.mpr hn)
  have h1 : -2 ≤ n := by omega
  have h2 : n ≤ 2 := by omega
  have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
  interval_cases n <;> norm_num at hroot <;> omega

theorem polynomial_irreducible (k : ℕ) (hk : 1 ≤ k) :
    Irreducible (polynomial k) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [polynomial_natDegree]; decide
  · exact no_rational_root k hk

theorem irreducible (k : ℕ) (hk : 1 ≤ k) :
    Irreducible (incidenceQ k).charpoly := by
  rw [charpoly_eq]
  exact polynomial_irreducible k hk

/-- A uniform intermediate-value bracket, with no numerical root approximation. -/
theorem real_root (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℝ, 2 < b ∧ b < (k : ℝ) + 2 ∧
      b ^ 3 - (k : ℝ) * b ^ 2 - 2 * b - 2 = 0 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : Continuous fun x : ℝ => x ^ 3 - (k : ℝ) * x ^ 2 - 2 * x - 2 := by
    fun_prop
  obtain ⟨b, ⟨h1, h2⟩, hb⟩ := intermediate_value_Ioo
    (show (2 : ℝ) ≤ (k : ℝ) + 2 by linarith) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo
      ((fun x : ℝ => x ^ 3 - (k : ℝ) * x ^ 2 - 2 * x - 2) 2)
      ((fun x : ℝ => x ^ 3 - (k : ℝ) * x ^ 2 - 2 * x - 2) ((k : ℝ) + 2)) by
        constructor <;> nlinarith [sq_nonneg (k : ℝ)])
  exact ⟨b, h1, h2, hb⟩

/-- Factoring out the root above two leaves a quadratic with product `2/b < 1`.
Its discriminant is negative, so each other root has exactly that squared norm. -/
theorem other_root (k : ℕ) {b : ℝ} (hb2 : 2 < b)
    (hb : b ^ 3 - (k : ℝ) * b ^ 2 - 2 * b - 2 = 0)
    {z : ℂ} (hz : z ^ 3 - (k : ℂ) * z ^ 2 - 2 * z - 2 = 0)
    (hzb : z ≠ b) : ‖z‖ ^ 2 = 2 / b ∧ z.im ≠ 0 ∧ ‖z‖ < 1 := by
  let p : ℝ := b ^ 2 - (k : ℝ) * b - 2
  let d : ℝ := b - k
  have hb0 : 0 < b := by linarith
  have hprod : b * p = 2 := by dsimp [p]; nlinarith [hb]
  have hbd : b * d = p + 2 := by dsimp [p, d]; ring
  have hp : 0 < p := by nlinarith
  have hp1 : p < 1 := by nlinarith
  have hd : 0 < d := by nlinarith
  have hdp : 2 * d = p * (p + 2) := by
    calc
      2 * d = (b * p) * d := by rw [hprod]
      _ = p * (b * d) := by ring
      _ = p * (p + 2) := by rw [hbd]
  have hd1 : d < 3 / 2 := by nlinarith
  have hd2 : 2 * d ≤ 3 * p := by nlinarith
  have hdisc : d ^ 2 < 4 * p := by
    nlinarith [mul_nonneg (le_of_lt hd) (le_of_lt (sub_pos.mpr hd1))]
  have hq : z ^ 2 + (d : ℂ) * z + (p : ℂ) = 0 := by
    have hbC : (b : ℂ) ^ 3 - (k : ℂ) * b ^ 2 - 2 * b - 2 = 0 := by
      exact_mod_cast hb
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
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at hre
    nlinarith [sq_nonneg (2 * x + d)]
  have hx : 2 * x + d = 0 := by
    have : y * (2 * x + d) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hy
  have hn : ‖z‖ ^ 2 = p := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    linear_combination (-1 : ℝ) * hre + x * hx
  have hpdiv : p = 2 / b := (eq_div_iff (ne_of_gt hb0)).2 (by nlinarith [hprod])
  refine ⟨hn.trans hpdiv, hy, ?_⟩
  nlinarith [norm_nonneg z]

/-- Primitive irreducible Pisot arithmetic, tied to the literal incidence. -/
theorem pisot (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℝ, 2 < b ∧ aeval (b : ℂ) (incidenceQ k).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (incidenceQ k).charpoly = 0 → z ≠ b → ‖z‖ < 1 := by
  obtain ⟨b, hb2, _, hb⟩ := real_root k hk
  refine ⟨b, hb2, ?_, ?_⟩
  · rw [charpoly_eq, aeval_polynomial]
    exact_mod_cast hb
  · intro z hz hzb
    rw [charpoly_eq, aeval_polynomial] at hz
    exact (other_root k hb2 hb hz hzb).2.2

/-- The same real root is irrational; in particular its expansion cannot be rational. -/
theorem root_irrational (k : ℕ) (hk : 1 ≤ k) {b : ℝ}
    (hb : b ^ 3 - (k : ℝ) * b ^ 2 - 2 * b - 2 = 0) : Irrational b := by
  rintro ⟨q, hq⟩
  apply no_rational_root k hk q
  change eval q (polynomial k) = 0
  simp only [polynomial, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
  rw [← hq] at hb
  exact_mod_cast hb

/-- Positive left eigenvector with no division: `(b,b²,b+2)`.
Together with `pisot`, this identifies the expanding root of the actual matrix. -/
theorem positive_left_eigenvector (k : ℕ) {b : ℝ} (hb2 : 2 < b)
    (hb : b ^ 3 - (k : ℝ) * b ^ 2 - 2 * b - 2 = 0) :
    ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
      w ᵥ* (inc (substitution k)).map (Nat.cast : ℕ → ℝ) = b • w := by
  refine ⟨![b, b ^ 2, b + 2], ?_, ?_⟩
  · intro a
    fin_cases a <;> simp <;> nlinarith
  · rw [incidence_eq]
    ext c
    fin_cases c <;>
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> nlinarith [hb]

/-- The boundary `k=0` cannot satisfy the expanding-root conclusion above two. -/
theorem zero_no_root_above_two {b : ℝ} (hb : 2 < b) :
    aeval (b : ℂ) (incidenceQ 0).charpoly ≠ 0 := by
  rw [charpoly_eq, aeval_polynomial]
  intro h
  simp only [Nat.cast_zero, zero_mul, sub_zero] at h
  have hR : b ^ 3 - 2 * b - 2 = 0 := by exact_mod_cast h
  nlinarith [mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ b ^ 2 - 4 by nlinarith)]

end Psc.ParameterFamilyPisot
