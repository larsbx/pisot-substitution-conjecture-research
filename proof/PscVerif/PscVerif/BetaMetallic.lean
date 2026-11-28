import PscVerif.BetaNumeration
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# The metallic bases `β_m² = m β_m + 1`

`beta m = (m + √(m² + 4))/2` is the positive root of `x² = m x + 1`; `beta 1 = φ`.
With the full alphabet `{0,…,m}` the representable interval is `[0, m/(β-1)]`
and `m/(β-1) - 1 = β⁻¹` (`top_sub_one`), so the uniqueness criterion of
`PscVerif.BetaNumeration` reads: a digit below `m` needs its tail below `1`, a
positive digit needs its tail above `β⁻¹`.

Proved here, for `m ≥ 2`:

* `isUnique_of_low`: a stream with digits in `{0,…,m-1}` in which no positive digit
  is ever followed by a zero is the only `{0,…,m}` stream with its value. This
  covers `0^∞` and every `0^r B^ℕ`, `B = {1,…,m-1}`;
* `isUnique_interior`: in particular every stream in `B^ℕ`;
* `value_lt_one_of_low`, `interior_value_pos`: such values lie in `[0, 1)`, and
  interior values in `(β⁻¹, 1)`;
* `isPisot`: `beta m` is Pisot for `m ≥ 1`, its conjugate being `m - β = -β⁻¹`.

This is a specialization of the classical classification (de Vries–Komornik;
Glendinning–Sidorov for `m = 1`), formalized without a novelty claim.
Source decision: `docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaMetallic

open Psc.BetaNumeration Polynomial

/-- The metallic mean `(m + √(m² + 4))/2`. -/
noncomputable def beta (m : ℕ) : ℝ := ((m : ℝ) + √((m : ℝ) ^ 2 + 4)) / 2

theorem sqrt_sq (m : ℕ) : √((m : ℝ) ^ 2 + 4) ^ 2 = (m : ℝ) ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

theorem beta_sq (m : ℕ) : beta m ^ 2 = m * beta m + 1 := by
  unfold beta
  linear_combination (1 / 4 : ℝ) * sqrt_sq m

theorem lt_beta (m : ℕ) : (m : ℝ) < beta m := by
  have hs := sqrt_sq m
  have h0 := Real.sqrt_nonneg ((m : ℝ) ^ 2 + 4)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : (m : ℝ) < √((m : ℝ) ^ 2 + 4) := by nlinarith
  unfold beta
  linarith

theorem one_lt_beta {m : ℕ} (hm : 1 ≤ m) : 1 < beta m :=
  lt_of_le_of_lt (by exact_mod_cast hm) (lt_beta m)

theorem beta_pos {m : ℕ} (hm : 1 ≤ m) : 0 < beta m := by linarith [one_lt_beta hm]

/-- `β - m = β⁻¹`: the conjugate root is `m - β = -β⁻¹`. -/
theorem beta_sub (m : ℕ) (hm : 1 ≤ m) : beta m - m = (beta m)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  linear_combination beta_sq m

/-- The top of the representable interval minus one is `β⁻¹`. -/
theorem top_sub_one {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) / (beta m - 1) - 1 = (beta m)⁻¹ := by
  have hne : beta m - 1 ≠ 0 := by linarith [one_lt_beta hm]
  rw [div_sub_one hne, div_eq_iff hne, ← beta_sub m hm]
  linear_combination (-1 : ℝ) * beta_sq m

theorem beta_one : beta 1 = Real.goldenRatio := by
  simp only [beta]
  norm_num [Real.goldenRatio]

/-! ## Pisot property -/

/-- `x² - m x - 1`. -/
noncomputable def poly (m : ℕ) : ℤ[X] := X ^ 2 - C (m : ℤ) * X - 1

theorem poly_monic (m : ℕ) : (poly m).Monic := by
  unfold poly
  monicity!

theorem aeval_poly {A : Type*} [CommRing A] [Algebra ℤ A] (m : ℕ) (z : A) :
    aeval z (poly m) = z ^ 2 - (m : A) * z - 1 := by
  simp [poly]

theorem isPisot {m : ℕ} (hm : 1 ≤ m) : IsPisot (beta m) := by
  refine ⟨one_lt_beta hm, poly m, poly_monic m, ?_, fun z hz hne => ?_⟩
  · rw [aeval_poly]
    linear_combination beta_sq m
  · rw [aeval_poly] at hz
    have hb : ((beta m : ℝ) : ℂ) ^ 2 = (m : ℂ) * (beta m : ℂ) + 1 := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (beta_sq m)
    have hprod : (z - (beta m : ℂ)) * (z - ((m : ℂ) - (beta m : ℂ))) = 0 := by
      linear_combination hz - hb
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · have hz' : z = (((m : ℝ) - beta m : ℝ) : ℂ) := by
        push_cast
        linear_combination h
      rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, beta_sub m hm,
        abs_of_pos (inv_pos.mpr (beta_pos hm))]
      exact inv_lt_one_of_one_lt₀ (one_lt_beta hm)

/-! ## Unique streams -/

theorem low_top_lt_one {m : ℕ} (hm : 1 ≤ m) : ((m - 1 : ℕ) : ℝ) / (beta m - 1) < 1 := by
  have hpos : 0 < beta m - 1 := by linarith [one_lt_beta hm]
  rw [div_lt_one hpos, Nat.cast_sub hm, Nat.cast_one]
  linarith [lt_beta m]

/-- Digits at most `m - 1` give a value below `1`. -/
theorem value_lt_one_of_low {m : ℕ} (hm : 1 ≤ m) {d : ℕ → ℕ} (hd : Bounded (m - 1) d) :
    value (beta m) d < 1 :=
  lt_of_le_of_lt (value_le_of_le (one_lt_beta hm) hd) (low_top_lt_one hm)

/-- Positive digits give a value above `β⁻¹`. -/
theorem inv_lt_value_of_pos {m : ℕ} (hm : 1 ≤ m) {d : ℕ → ℕ} (hd : Bounded m d)
    (hpos : ∀ n, 1 ≤ d n) : (beta m)⁻¹ < value (beta m) d := by
  have hβ := one_lt_beta hm
  have h1 := le_value_of_le hβ hd hpos
  have h2 : (beta m)⁻¹ < ((1 : ℕ) : ℝ) / (beta m - 1) := by
    rw [Nat.cast_one, one_div]
    exact inv_strictAnti₀ (by linarith) (by linarith)
  linarith

/-- Digits in `{0,…,m-1}`, no positive digit ever followed by a zero: unique. -/
theorem isUnique_of_low {m : ℕ} (hm : 2 ≤ m) {d : ℕ → ℕ} (hd : Bounded (m - 1) d)
    (hpos : ∀ n, 0 < d n → ∀ k, 1 ≤ d (k + (n + 1))) : IsUnique (beta m) m d := by
  have hm1 : 1 ≤ m := by omega
  have hβ := one_lt_beta hm1
  have hdm : Bounded m d := fun n => by have := hd n; omega
  refine isUnique_of_tails hβ hdm (fun n _ => value_lt_one_of_low hm1 (hd.shift _))
    (fun n hn => ?_)
  rw [top_sub_one hm1]
  exact inv_lt_value_of_pos hm1 (hdm.shift _) (hpos n hn)

/-- Every interior stream (digits in `{1,…,m-1}`) is uniquely represented. -/
theorem isUnique_interior {m : ℕ} (hm : 2 ≤ m) {d : ℕ → ℕ}
    (hd : ∀ n, 1 ≤ d n ∧ d n + 1 ≤ m) : IsUnique (beta m) m d :=
  isUnique_of_low hm (fun n => by have := hd n; omega)
    (fun _ _ k => (hd _).1)

/-- Interior values lie in `(β⁻¹, 1)`. -/
theorem interior_value_mem {m : ℕ} (hm : 2 ≤ m) {d : ℕ → ℕ}
    (hd : ∀ n, 1 ≤ d n ∧ d n + 1 ≤ m) :
    (beta m)⁻¹ < value (beta m) d ∧ value (beta m) d < 1 := by
  have hm1 : 1 ≤ m := by omega
  exact ⟨inv_lt_value_of_pos hm1 (fun n => by have := hd n; omega) (fun n => (hd n).1),
    value_lt_one_of_low hm1 (fun n => by have := hd n; omega)⟩

/-- Interior streams are greedy: they are the Rényi expansion of their value. -/
theorem interior_renyi {m : ℕ} (hm : 2 ≤ m) {d : ℕ → ℕ}
    (hd : ∀ n, 1 ≤ d n ∧ d n + 1 ≤ m) : renyiExpansion (beta m) (value (beta m) d) = d :=
  renyiExpansion_value (one_lt_beta (by omega)) (m := m) (fun n => by have := hd n; omega)
    (fun n => value_lt_one_of_low (by omega)
      (fun k => show d (k + n) ≤ m - 1 by have := hd (k + n); omega))

end Psc.BetaMetallic
