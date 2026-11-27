import PscVerif.BetaFamilyComplexity

/-!
# The Adamczewski–Bugeaud inputs for `ξ_{k,m}`

For `k ≥ 1`, `m ≥ 4` and a base with `β² = mβ + 1`, let
`ξ_{k,m} = Σ_{n ≥ 1} (w_n + 1) β^{-n}` with `w` the fixed word of `σ_k²`.
This module proves every hypothesis that Adamczewski–Bugeaud, *Dynamics for
β-shifts and Diophantine approximation* (ETDS 2007), Corollary 1, places on
`β` and on the expansion:

* `β > 1` is a root of `X² - mX - 1` whose other root `-β⁻¹` has modulus
  below `1`, so `β` is a quadratic Pisot number (`pisot_facts`);
* `w + 1` is the greedy `β`-expansion of `ξ_{k,m} ∈ (β⁻¹, 1)`: every digit is
  the floor of `β` times the current remainder, and every remainder lies in
  `[0, 1)` (`greedy`);
* the expansion is not eventually periodic and has at most `27 (k² + 2)² n`
  factors of length `n` (`xi_inputs`).

The corollary then says an algebraic `ξ ∈ [0, 1]` has greedy complexity that is
either bounded or satisfies `liminf p(n)/n = ∞`. A non-eventually-periodic
stream has `p(n) ≥ n + 1` (Morse–Hedlund), so it is not bounded, and the linear
bound excludes the other case. So `ξ_{k,m}` is transcendental.

That implication is external and is **not** formalized: no axiom or hypothesis
standing for the corollary is introduced, and neither the Morse–Hedlund step nor
transcendence is a Lean declaration here. Whether `ξ_{k,m}` is new is not
addressed. Source decision: `docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaFamilyXi

open Psc.BetaMetallicUnique
open Psc.BetaFamilyFixedWord
open Psc.BetaFamilyComplexity (factors E)

variable {m : ℕ}

/-- The quadratic Pisot facts for `β = r⁻¹`: a root of `X² - mX - 1` above `1`,
with conjugate `-r` of modulus below `1`. -/
theorem pisot_facts (B : Base m) :
    1 < B.r⁻¹ ∧ B.r⁻¹ ^ 2 = (m : ℝ) * B.r⁻¹ + 1 ∧
      (-B.r) ^ 2 = (m : ℝ) * (-B.r) + 1 ∧ |-B.r| < 1 ∧
      B.r⁻¹ + -B.r = m ∧ B.r⁻¹ * -B.r = -1 := by
  have hr := B.r_pos
  have h1 : B.r⁻¹ * B.r = 1 := inv_mul_cancel₀ hr.ne'
  have hc := B.carry
  refine ⟨one_lt_inv_iff₀.mpr ⟨hr, B.r_lt_one⟩, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (-(B.r⁻¹ ^ 2)) * hc + ((m : ℝ) * B.r⁻¹ + B.r⁻¹ * B.r + 1) * h1
  · linear_combination hc
  · rw [abs_neg, abs_of_pos hr]; exact B.r_lt_one
  · have : B.r⁻¹ = m + B.r := by
      field_simp
      linear_combination -hc
    linarith
  · linear_combination -h1

/-- `ξ_{k,m}` with its digit stream `w + 1`. -/
noncomputable def xi (k : ℕ) (hm : 4 ≤ m) (B : Base m) : ℝ := B.value (shifted k m (by omega))

/-- **Greedy digits.** Every remainder of `w + 1` lies in `[0, 1)`, and every
digit is the floor of `β` times the preceding remainder. -/
theorem greedy (k : ℕ) (hm : 4 ≤ m) (B : Base m) (n : ℕ) :
    0 ≤ B.value (shift (shifted k m (by omega)) n) ∧
      B.value (shift (shifted k m (by omega)) n) < 1 ∧
      ((shifted k m (by omega) n : ℕ) : ℤ) =
        ⌊B.r⁻¹ * B.value (shift (shifted k m (by omega)) n)⌋ := by
  set d := shifted k m (by omega)
  have lt : ∀ j, B.value (shift d j) < 1 := fun j =>
    B.value_lt_one fun i => (shifted_interior k m hm (j + i)).2
  refine ⟨B.value_nonneg _, lt n, ?_⟩
  have step := B.value_eq_step (shift d n)
  have h0 : shift d n 0 = d n := by simp [shift]
  have ht : tail (shift d n) = shift d (n + 1) := (shift_succ d n).symm
  rw [h0, ht] at step
  have hr := B.r_pos
  have e : B.r⁻¹ * B.value (shift d n) = ((d n : ℕ) : ℝ) + B.value (shift d (n + 1)) := by
    rw [step]; field_simp
  rw [e, eq_comm, Int.floor_eq_iff]
  constructor
  · push_cast; linarith [B.value_nonneg (shift d (n + 1))]
  · push_cast; linarith [lt (n + 1)]

/-- **The Adamczewski–Bugeaud inputs for `ξ_{k,m}`**, assembled. -/
theorem xi_inputs (k : ℕ) (hk : 1 ≤ k) (hm : 4 ≤ m) (B : Base m) :
    B.IsUnique (shifted k m (by omega)) ∧ B.r < xi k hm B ∧ xi k hm B < 1 ∧
      (∀ n, ((shifted k m (by omega) n : ℕ) : ℤ) =
        ⌊B.r⁻¹ * B.value (shift (shifted k m (by omega)) n)⌋) ∧
      ¬ EventuallyPeriodic (shifted k m (by omega)) ∧
      (∀ n, 1 ≤ n → (factors (shifted k m (by omega)) n).Finite ∧
        (factors (shifted k m (by omega)) n).ncard ≤ 27 * E k ^ 2 * n) := by
  obtain ⟨hu, hlo, hhi, hnp⟩ := xi_unique k m hk hm B
  exact ⟨hu, hlo, hhi, fun n => (greedy k hm B n).2.2, hnp,
    fun n hn => Psc.BetaFamilyComplexity.shifted_factors_linear k m hk (by omega) n hn⟩

end Psc.BetaFamilyXi
