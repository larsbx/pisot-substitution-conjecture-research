import PscVerif.BHNearDiagonalPisot

/-!
# Actual Pisot arithmetic throughout the higher-determinant parameter domain

For the original literal words `(1, 0 1^k 2, 0^r 1)`, every pair
`4 ≤ r ≤ k` has primitive incidence, irreducible characteristic polynomial
`X^3-k*X^2-2*X-r`, and a constructed expanding root in `(k,k+1)`.
The other complex roots have squared norm exactly `r/beta < 1`.

The source decision and written calculation are Section 2 of
`docs/bh-three-band-spectral-transfer-2026-11-27.md`, continuing the
actual-arithmetic decision of the same date. This module adds arithmetic
and literal length scaling only. It asserts no spectral theorem.
-/

namespace Psc.BHHigherDeterminantPisot

open Matrix Polynomial
open Psc.Incidence (inc)
open Psc.BHNearDiagonalLiteral (sigma lengths RunFamily)
open Psc.BHNearDiagonalPisot
  (incidenceQ incidence_eq polynomial integerPolynomial
    charpoly_eq polynomial_natDegree integerPolynomial_monic
    aeval_polynomial aeval_integerPolynomial)

/-- The full domain uses the existing literal scaling data. No adjacent-band
window, discriminant conclusion or root-existence premise is added. -/
structure Family (r k : ℕ) (β : ℝ) : Prop extends RunFamily r k β where
  large : 4 ≤ r
  above : r ≤ k
  upper : β < (k : ℝ) + 1

/-- Opposite endpoint signs construct the root on the entire domain. -/
theorem bracketed_root_exists (r k : ℕ) (hr : 4 ≤ r) (hk : r ≤ k) :
    ∃ β : ℝ, (k : ℝ) < β ∧ β < (k : ℝ)+1 ∧
      β^3 = (k : ℝ)*β^2+2*β+r := by
  let f : ℝ → ℝ := fun x => x^3-(k : ℝ)*x^2-2*x-r
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
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

theorem family_root_exists (r k : ℕ) (hr : 4 ≤ r) (hk : r ≤ k) :
    ∃ β : ℝ, Family r k β := by
  obtain ⟨β, hlo, hhi, hc⟩ := bracketed_root_exists r k hr hk
  exact ⟨β, ⟨⟨by omega, hlo, hc⟩, hr, hk, hhi⟩⟩

theorem beta_gt_four {r k : ℕ} {β : ℝ} (h : Family r k β) : 4 < β := by
  have hk : (4 : ℝ) ≤ k := by exact_mod_cast (h.large.trans h.above)
  exact hk.trans_lt h.lower

theorem a_identity {r k : ℕ} {β : ℝ} (h : RunFamily r k β) :
    (β-k)*β = 2+r/β := by
  nlinarith only [h.quadratic_eq]

theorem b_pos {r k : ℕ} {β : ℝ} (h : Family r k β) :
    0 < (r : ℝ)/β := by
  exact div_pos (by exact_mod_cast (show 0 < r by have := h.large; omega))
    h.toRunFamily.beta_pos

theorem b_lt_one {r k : ℕ} {β : ℝ} (h : Family r k β) :
    (r : ℝ)/β < 1 := by
  apply (div_lt_one h.toRunFamily.beta_pos).mpr
  exact (by exact_mod_cast h.above : (r : ℝ) ≤ k).trans_lt h.lower

/-- The discriminant estimate uses only `4 ≤ r ≤ k`: after multiplying by
`beta^2`, its two sides are `(2+B)^2 < 9 < 4*r*beta`. -/
theorem quadratic_discriminant {r k : ℕ} {β : ℝ} (h : Family r k β) :
    (β-k)^2 < 4*((r : ℝ)/β) := by
  let a : ℝ := β-k
  let b : ℝ := r/β
  have hβ := h.toRunFamily.beta_pos
  have hb0 : 0 < b := b_pos h
  have hb1 : b < 1 := b_lt_one h
  have ha : a*β = 2+b := a_identity h.toRunFamily
  have hb : b*β = r := div_mul_cancel₀ _ hβ.ne'
  have hsmall : (2+b)^2 < 9 := by
    nlinarith only [hb0, hb1, mul_pos hb0 (sub_pos.mpr hb1)]
  have hr : (4 : ℝ) ≤ r := by exact_mod_cast h.large
  have hlarge : 9 < 4*(r : ℝ)*β := by
    have hm := mul_le_mul_of_nonneg_right hr hβ.le
    nlinarith only [hm, beta_gt_four h]
  have ha2 : a^2*β^2 = (2+b)^2 := by
    calc
      a^2*β^2 = (a*β)^2 := by ring
      _ = (2+b)^2 := by rw [ha]
  have hb2 : (4*b)*β^2 = 4*(r : ℝ)*β := by
    calc
      (4*b)*β^2 = 4*(b*β)*β := by ring
      _ = 4*(r : ℝ)*β := by rw [hb]
  have hprod : a^2*β^2 < (4*b)*β^2 := by
    rw [ha2, hb2]
    exact hsmall.trans hlarge
  exact lt_of_mul_lt_mul_right hprod (sq_nonneg β)

theorem cubic_factor {r k : ℕ} {β : ℝ} (h : RunFamily r k β) (x : ℝ) :
    (x-β)*(x^2+(β-k)*x+r/β) = x^3-(k : ℝ)*x^2-2*x-r := by
  have ha := a_identity h
  have hb : β*((r : ℝ)/β) = r := mul_div_cancel₀ _ h.beta_pos.ne'
  have hax := congrArg (fun v : ℝ => v*x) ha
  nlinarith only [hb, hax]

theorem quadratic_factor_pos {r k : ℕ} {β : ℝ} (h : Family r k β) (x : ℝ) :
    0 < x^2+(β-k)*x+r/β := by
  nlinarith only [quadratic_discriminant h, sq_nonneg (2*x+(β-k))]

/-- The actual cubic has exactly one real root. -/
theorem real_root_unique {r k : ℕ} {β : ℝ} (h : Family r k β) {x : ℝ}
    (hroot : x^3-(k : ℝ)*x^2-2*x-r = 0) : x = β := by
  have hfactor : (x-β)*(x^2+(β-k)*x+r/β) = 0 := by
    rw [cubic_factor h.toRunFamily, hroot]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_right (quadratic_factor_pos h x).ne')

theorem family_root_unique {r k : ℕ} {β γ : ℝ}
    (hβ : Family r k β) (hγ : Family r k γ) : γ = β :=
  real_root_unique hβ (by linarith [hγ.cubic])

theorem root_not_integer {r k : ℕ} {β : ℝ} (h : Family r k β) (z : ℤ) :
    (z : ℝ) ≠ β := by
  intro hz
  have hlo : (k : ℤ) < z := by exact_mod_cast (hz ▸ h.lower)
  have hhi : z < (k : ℤ)+1 := by exact_mod_cast (hz ▸ h.upper)
  omega

theorem no_integer_root {r k : ℕ} {β : ℝ} (h : Family r k β) (z : ℤ) :
    (z : ℝ)^3-(k : ℝ)*(z : ℝ)^2-2*(z : ℝ)-r ≠ 0 := by
  intro hz
  exact root_not_integer h z (real_root_unique h hz)

/-- A rational root of the actual monic cubic would be integral, while its
unique real root lies strictly between consecutive integers. -/
theorem no_rational_root (r k : ℕ) (hr : 4 ≤ r) (hk : r ≤ k) (x : ℚ) :
    ¬ (polynomial r k).IsRoot x := by
  intro hx
  obtain ⟨β, hβ⟩ := family_root_exists r k hr hk
  have hx' : aeval x (integerPolynomial r k) = 0 := by
    have h0 : eval x (polynomial r k) = 0 := hx
    rw [aeval_integerPolynomial]
    simpa [polynomial] using h0
  obtain ⟨n, rfl, _⟩ := exists_integer_of_is_root_of_monic
    (integerPolynomial_monic r k) hx'
  have hn : (n : ℝ)^3-(k : ℝ)*(n : ℝ)^2-2*(n : ℝ)-r = 0 := by
    rw [aeval_integerPolynomial, algebraMap_int_eq, eq_intCast] at hx'
    exact_mod_cast hx'
  exact no_integer_root hβ n hn

theorem polynomial_irreducible (r k : ℕ) (hr : 4 ≤ r) (hk : r ≤ k) :
    Irreducible (polynomial r k) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [polynomial_natDegree]; decide
  · exact no_rational_root r k hr hk

/-- Irreducibility belongs to the original image-letter incidence matrix. -/
theorem irreducible (r k : ℕ) (hr : 4 ≤ r) (hk : r ≤ k) :
    Irreducible (incidenceQ r k).charpoly := by
  rw [charpoly_eq]
  exact polynomial_irreducible r k hr hk

theorem complex_cubic_factor {r k : ℕ} {β : ℝ} (h : RunFamily r k β) (z : ℂ) :
    (z-(β : ℂ))*(z^2+((β-k : ℝ) : ℂ)*z+(((r : ℝ)/β : ℝ) : ℂ)) =
      z^3-(k : ℂ)*z^2-2*z-r := by
  have ha : ((β-k : ℝ) : ℂ)*(β : ℂ) = 2+(((r : ℝ)/β : ℝ) : ℂ) := by
    exact_mod_cast a_identity h
  have hb : (β : ℂ)*(((r : ℝ)/β : ℝ) : ℂ) = (r : ℂ) := by
    exact_mod_cast (mul_div_cancel₀ (r : ℝ) h.beta_pos.ne')
  push_cast at ha hb ⊢
  linear_combination -z*ha-hb

/-- Every other complex root is nonreal, with exact squared norm r/beta. -/
theorem other_root {r k : ℕ} {β : ℝ} (h : Family r k β) {z : ℂ}
    (hz : z^3-(k : ℂ)*z^2-2*z-r = 0) (hzb : z ≠ (β : ℂ)) :
    ‖z‖^2 = (r : ℝ)/β ∧ z.im ≠ 0 ∧ ‖z‖ < 1 := by
  let a : ℝ := β-k
  let b : ℝ := r/β
  have hb' : b < 1 := b_lt_one h
  have hdisc : a^2 < 4*b := quadratic_discriminant h
  have hquad : z^2+(a : ℂ)*z+(b : ℂ) = 0 := by
    have hf : (z-(β : ℂ))*(z^2+(a : ℂ)*z+(b : ℂ)) = 0 := by
      rw [complex_cubic_factor h.toRunFamily, hz]
    exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hzb)
  have hre := congrArg Complex.re hquad
  have him := congrArg Complex.im hquad
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im] at hre him
  set x := z.re
  set y := z.im
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at hre
    nlinarith [sq_nonneg (2*x+a)]
  have hx : 2*x+a = 0 := by
    have hp : y*(2*x+a) = 0 := by linarith
    exact (mul_eq_zero.mp hp).resolve_left hy
  have hn : ‖z‖^2 = b := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    linear_combination (-1 : ℝ)*hre+x*hx
  refine ⟨hn, hy, ?_⟩
  nlinarith [norm_nonneg z]

/-- The parameter-only Pisot endpoint constructs its root. -/
theorem pisot (r k : ℕ) (hr : 4 ≤ r) (hk : r ≤ k) :
    ∃ β : ℝ, Family r k β ∧ 1 < β ∧
      aeval (β : ℂ) (incidenceQ r k).charpoly = 0 ∧
      ∀ z : ℂ, aeval z (incidenceQ r k).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1 := by
  obtain ⟨β, hβ⟩ := family_root_exists r k hr hk
  refine ⟨β, hβ, ?_, ?_, ?_⟩
  · linarith [beta_gt_four hβ]
  · rw [charpoly_eq, aeval_polynomial]
    exact_mod_cast (show β^3-(k : ℝ)*β^2-2*β-r = 0 by linarith [hβ.cubic])
  · intro z hz hzb
    rw [charpoly_eq, aeval_polynomial] at hz
    exact (other_root hβ hz hzb).2.2

theorem root_not_rational {r k : ℕ} {β : ℝ} (h : Family r k β) (q : ℚ) :
    (q : ℝ) ≠ β := by
  intro hq
  apply no_rational_root r k h.large h.above q
  change eval q (polynomial r k) = 0
  simp only [polynomial, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
  have hb : β^3-(k : ℝ)*β^2-2*β-r = 0 := by linarith [h.cubic]
  rw [← hq] at hb
  exact_mod_cast hb

theorem positive_literal_lengths {r k : ℕ} {β : ℝ} (h : RunFamily r k β) :
    ∀ a, 0 < lengths r β a :=
  fun a => zero_lt_one.trans_le (h.lengths_ge_one a)

/-- The literal normalized length row is an eigenrow of the actual incidence. -/
theorem literal_left_eigenvector {r k : ℕ} {β : ℝ} (h : RunFamily r k β) :
    lengths r β ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) =
      β • lengths r β := by
  have hb : β*((r : ℝ)/β) = r := mul_div_cancel₀ _ h.beta_pos.ne'
  rw [incidence_eq]
  ext c
  fin_cases c <;> simp [lengths, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
    nlinarith only [h.quadratic_eq, hb]

/-- The same equality stated on the original literal image words. -/
theorem literal_lengths_scale {r k : ℕ} {β : ℝ} (h : RunFamily r k β) :
    ∀ a, Psc.OccurrenceNewborn.physicalLength (lengths r β) (sigma r k a) =
      β * lengths r β a := by
  intro a
  have he := congrFun (literal_left_eigenvector h) a
  simpa [Matrix.vecMul, dotProduct, Matrix.map_apply,
    Psc.OccurrenceNewborn.physicalLength, Psc.Incidence.inc_apply] using he

/-- A division-free positive eigenvector is also available. -/
theorem positive_left_eigenvector {r k : ℕ} {β : ℝ} (h : RunFamily r k β) :
    ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
      w ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) = β • w := by
  refine ⟨![β,β^2,β+r], ?_, ?_⟩
  · intro a
    fin_cases a <;> simp <;>
      nlinarith [h.beta_pos, show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  · rw [incidence_eq]
    ext c
    fin_cases c <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
      nlinarith [h.cubic]

/-- Actual primitive irreducible Pisot arithmetic for every `4 ≤ r ≤ k`,
including the positive literal eigenlengths and exact image scaling.
The expanding root is constructed, not supplied as an extra input. -/
theorem primitive_irreducible_pisot (r k : ℕ) (hr : 4 ≤ r) (hk : r ≤ k) :
    (∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r k)^n) a c) ∧
    Irreducible (incidenceQ r k).charpoly ∧
    ∃ β : ℝ, Family r k β ∧ 1 < β ∧
      aeval (β : ℂ) (incidenceQ r k).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (incidenceQ r k).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1) ∧
      (∀ a, 0 < lengths r β a) ∧
      lengths r β ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) =
        β • lengths r β ∧
      (∀ a, Psc.OccurrenceNewborn.physicalLength (lengths r β) (sigma r k a) =
        β * lengths r β a) := by
  obtain ⟨β, hβ, hβ1, hroot, hother⟩ := pisot r k hr hk
  exact ⟨BHNearDiagonalPisot.primitive r k (by omega), irreducible r k hr hk,
    β, hβ, hβ1, hroot, hother, positive_literal_lengths hβ.toRunFamily,
    literal_left_eigenvector hβ.toRunFamily, literal_lengths_scale hβ.toRunFamily⟩

end Psc.BHHigherDeterminantPisot
