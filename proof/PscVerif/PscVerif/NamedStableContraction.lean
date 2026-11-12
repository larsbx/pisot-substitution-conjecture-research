module

public import PscVerif.NamedStableChart
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Strict contraction of the named stable chart at block twelve

The norm on `Stable = Fin 2 → ℝ` is the sup norm. The estimate below uses
absolute row sums of the actual twelfth matrix power. It does not use the
entrywise maximum matrix norm, a floating-point root, or sampled vectors.

The period-two action is deliberately retained as a negative control:
its value at `(1,-1)` is `(2*a,2*b)`, so the useful bound cannot be moved
from block twelve to block two.

Pre-code gate: `docs/c4-named-stable-chart-literature-2026-11-11.md`.
-/

@[expose] public section

namespace Psc.NamedStableContraction

open Psc.NamedStableChart Matrix

/-- A small rational enclosure, derived from the authenticated native
root bracket, keeps the subsequent chart bounds elementary. -/
theorem beta_coarse_bounds :
    (226953084 : ℝ) / 100000000 ≤ beta ∧ beta ≤ 226953085 / 100000000 := by
  constructor
  · exact (show (226953084 : ℝ) / 100000000 ≤ betaLo by norm_num [betaLo]).trans
      beta_ge_lo
  · exact beta_le_hi.trans
      (show betaHi ≤ (226953085 : ℝ) / 100000000 by norm_num [betaHi])

/-- Both chart coordinates have rigorously proved rational bounds. -/
theorem chart_coarse_bounds :
    ((8289111 : ℝ) / 10000000 ≤ a ∧ a ≤ 8289112 / 10000000) ∧
    ((4406196 : ℝ) / 10000000 ≤ b ∧ b ≤ 4406198 / 10000000) := by
  obtain ⟨hl, hu⟩ := beta_coarse_bounds
  have hb : 0 ≤ beta := by linarith
  have hsl := mul_self_le_mul_self
    (by norm_num : (0 : ℝ) ≤ 226953084 / 100000000) hl
  have hsu := mul_self_le_mul_self hb hu
  unfold a b
  constructor <;> constructor <;> nlinarith

/-- Convenient exact ceilings for the four genuine block entries. -/
theorem twelfth_entry_bounds :
    |3941 - 4755 * a| ≤ (19 : ℝ) / 40 ∧
    |7415 - 8945 * a| ≤ (2 : ℝ) / 5 ∧
    |2095 - 4755 * b| ≤ (3 : ℝ) / 20 ∧
    |3941 - 8945 * b| ≤ (7 : ℝ) / 20 := by
  obtain ⟨⟨hal, hau⟩, ⟨hbl, hbu⟩⟩ := chart_coarse_bounds
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

/-- Every absolute row sum is at most `7/8`; the second is already at
most `1/2`. The matrix entries are bound to the actual twelfth power. -/
theorem twelfth_row_bounds (i : Fin 2) :
    ‖(Bmat ^ 12) i 0‖ + ‖(Bmat ^ 12) i 1‖ ≤ (7 : ℝ) / 8 := by
  obtain ⟨h00, h01, h10, h11⟩ := twelfth_entry_bounds
  rw [Bmat_pow_twelve]
  fin_cases i
  · change ‖3941 - 4755 * a‖ + ‖7415 - 8945 * a‖ ≤ (7 : ℝ) / 8
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  · change ‖2095 - 4755 * b‖ + ‖3941 - 8945 * b‖ ≤ (7 : ℝ) / 8
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith

/-- The two-dimensional row-sum estimate for the actual vector sup norm.
No matrix norm instance is selected or silently changed here. -/
theorem norm_mulVec_le_of_row_bound (C : Matrix (Fin 2) (Fin 2) ℝ)
    (q : ℝ) (hq : 0 ≤ q) (rows : ∀ i, ‖C i 0‖ + ‖C i 1‖ ≤ q)
    (x : Fin 2 → ℝ) : ‖C *ᵥ x‖ ≤ q * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg x))).mpr
  intro i
  calc
    ‖(C *ᵥ x) i‖ = ‖C i 0 * x 0 + C i 1 * x 1‖ := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    _ ≤ ‖C i 0 * x 0‖ + ‖C i 1 * x 1‖ := norm_add_le _ _
    _ = ‖C i 0‖ * ‖x 0‖ + ‖C i 1‖ * ‖x 1‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖C i 0‖ * ‖x‖ + ‖C i 1‖ * ‖x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_le_pi_norm x 0) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm x 1) (norm_nonneg _))
    _ = (‖C i 0‖ + ‖C i 1‖) * ‖x‖ := by ring
    _ ≤ q * ‖x‖ := mul_le_mul_of_nonneg_right (rows i) (norm_nonneg _)

/-- The named composition power contracts every real vector in the
declared sup norm, with no remaining numerical or geometric premise. -/
theorem B_pow_twelve_contract (x : Stable) :
    ‖(B ^ 12) x‖ ≤ (7 / 8 : ℝ) * ‖x‖ := by
  rw [B_pow_apply_eq_matrix]
  exact norm_mulVec_le_of_row_bound (Bmat ^ 12) (7 / 8) (by norm_num)
    twelfth_row_bounds x

/-- A concrete vector distinguishes the short action from its useful
contracting block. -/
theorem B_test_vector : B (![1, -1] : Stable) = ![-2, 0] := by
  rw [B_apply, Bmat_mulVec]
  ext i
  fin_cases i <;> simp <;> ring

theorem B_pow_two_test_vector : (B ^ 2) (![1, -1] : Stable) = ![2 * a, 2 * b] := by
  rw [pow_two]
  change B (B (![1, -1] : Stable)) = _
  rw [B_test_vector]
  rw [B_apply, Bmat_mulVec]
  ext i
  fin_cases i <;> simp <;> ring

/-- Literal word period two does not supply a block-two contraction in
these stable coordinates. -/
theorem not_B_pow_two_contract :
    ¬ (∀ x : Stable, ‖(B ^ 2) x‖ ≤ (7 / 8 : ℝ) * ‖x‖) := by
  intro contract
  have hx : ‖(![1, -1] : Stable)‖ ≤ (1 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> norm_num
  have h := (contract (![1, -1] : Stable)).trans
    (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 7 / 8))
  rw [B_pow_two_test_vector] at h
  have hc : ‖(2 : ℝ) * a‖ ≤ ‖(![2 * a, 2 * b] : Stable)‖ :=
    norm_le_pi_norm (![2 * a, 2 * b] : Stable) 0
  rw [Real.norm_eq_abs] at hc
  have ha := chart_coarse_bounds.1.1
  have hle := le_abs_self ((2 : ℝ) * a)
  linarith

end Psc.NamedStableContraction
