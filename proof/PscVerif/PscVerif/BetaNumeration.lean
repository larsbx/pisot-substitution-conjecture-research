import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PscVerif.WordComplexity

/-!
# Real bases, greedy expansions and the Adamczewski–Bugeaud dichotomy

For a real base `β > 1` and a digit stream `d : ℕ → ℕ` bounded by `m`, the
valuation is `value β d = ∑_{n ≥ 0} d n β^{-(n+1)}`.

Proved here:

* `value_step`, `value_le_of_le`, `le_value_of_le`: one-step recursion and the
  geometric bounds `a/(β-1) ≤ value ≤ b/(β-1)` for digits in `[a, b]`;
* `renyiExpansion_value` (**greedy binding**): if every tail value of `d` lies
  below `1`, then `d` *is* the Rényi expansion of its value, with digits
  `⌊β Tⁿ x⌋` and `T x = {β x}` — the `β`-expansion used by Adamczewski–Bugeaud;
* `isUnique_of_tails` (**uniqueness criterion**, sufficient direction): if every
  digit below `m` is followed by a tail value below `1` and every positive digit
  by a tail value above `m/(β-1) - 1`, then `d` is the only `{0,…,m}` stream with
  its value. The quantifier ranges over *all* bounded streams.

The deep input is imported, not proved: `ABCorollary1` states Corollary 1 of
Adamczewski–Bugeaud, *Dynamics for β-shifts and some Diophantine approximation
problems*, ETDS 27 (2007), restricted to Pisot bases (the paper also allows Salem
bases). It is a hypothesis of `transcendental_of_greedy`, never an axiom.
`IsPisot` asks for some monic integer polynomial vanishing at `β` whose other
complex roots lie in the open unit disc; this is equivalent to the usual
definition, since the minimal polynomial divides any such polynomial and is one.
Source decision: `docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaNumeration

open Psc.WordComplexity

/-- Digits bounded by `m`. -/
def Bounded (m : ℕ) (d : ℕ → ℕ) : Prop := ∀ n, d n ≤ m

/-- The tail of `d` after its first `n` digits. -/
def shift (d : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun k => d (k + n)

/-- The valuation `∑_{n ≥ 0} d n β^{-(n+1)}`. -/
noncomputable def value (β : ℝ) (d : ℕ → ℕ) : ℝ := ∑' n, (d n : ℝ) * β⁻¹ ^ (n + 1)

@[simp] theorem shift_apply (d : ℕ → ℕ) (n k : ℕ) : shift d n k = d (k + n) := rfl

@[simp] theorem shift_zero (d : ℕ → ℕ) : shift d 0 = d := by
  funext k; simp [shift]

theorem shift_shift (d : ℕ → ℕ) (n k : ℕ) : shift (shift d n) k = shift d (k + n) := by
  funext i; simp only [shift]; congr 1; omega

theorem shift_shift_one (d : ℕ → ℕ) (n : ℕ) : shift (shift d n) 1 = shift d (n + 1) := by
  rw [shift_shift, Nat.add_comm]

theorem Bounded.shift {m : ℕ} {d : ℕ → ℕ} (hd : Bounded m d) (n : ℕ) :
    Bounded m (shift d n) := fun k => hd (k + n)

section Base

variable {β : ℝ} (hβ : 1 < β)
include hβ

theorem rinv_pos : 0 < β⁻¹ := inv_pos.mpr (by linarith)

theorem rinv_lt_one : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ

theorem summable_rpow : Summable fun n : ℕ => β⁻¹ ^ (n + 1) :=
  (summable_nat_add_iff 1).mpr
    (summable_rpowetric_of_lt_one (rinv_pos hβ).le (rinv_lt_one hβ))

/-- `∑ c β^{-(n+1)} = c/(β-1)`. -/
theorem tsum_const_rpow (c : ℝ) : ∑' n : ℕ, c * β⁻¹ ^ (n + 1) = c / (β - 1) := by
  have hr0 := (rinv_pos hβ).le
  have hr1 := rinv_lt_one hβ
  have h : ∀ n : ℕ, c * β⁻¹ ^ (n + 1) = (c * β⁻¹) * β⁻¹ ^ n := fun n => by ring
  simp_rw [h]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hβ0 : β ≠ 0 := (by linarith : (0 : ℝ) < β).ne'
  have hβ1 : β - 1 ≠ 0 := by linarith
  field_simp
  try ring

theorem term_nonneg (d : ℕ → ℕ) (n : ℕ) : 0 ≤ (d n : ℝ) * β⁻¹ ^ (n + 1) :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (rinv_pos hβ).le _)

theorem summable_value {m : ℕ} {d : ℕ → ℕ} (hd : Bounded m d) :
    Summable fun n => (d n : ℝ) * β⁻¹ ^ (n + 1) :=
  Summable.of_nonneg_of_le (term_nonneg hβ d)
    (fun n => mul_le_mul_of_nonneg_right (by exact_mod_cast hd n)
      (pow_nonneg (rinv_pos hβ).le _))
    ((summable_rpow hβ).mul_left (m : ℝ))

theorem value_nonneg (d : ℕ → ℕ) : 0 ≤ value β d := tsum_nonneg (term_nonneg hβ d)

/-- Digits at most `b` give a value at most `b/(β-1)`. -/
theorem value_le_of_le {b : ℕ} {d : ℕ → ℕ} (hd : Bounded b d) :
    value β d ≤ b / (β - 1) := by
  rw [← tsum_const_rpow hβ]
  exact (summable_value hβ hd).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (by exact_mod_cast hd n)
      (pow_nonneg (rinv_pos hβ).le _))
    ((summable_rpow hβ).mul_left (b : ℝ))

/-- Digits at least `a` (and at most `m`) give a value at least `a/(β-1)`. -/
theorem le_value_of_le {a m : ℕ} {d : ℕ → ℕ} (hd : Bounded m d) (ha : ∀ n, a ≤ d n) :
    (a : ℝ) / (β - 1) ≤ value β d := by
  rw [← tsum_const_rpow hβ]
  exact ((summable_rpow hβ).mul_left (a : ℝ)).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (by exact_mod_cast ha n)
      (pow_nonneg (rinv_pos hβ).le _))
    (summable_value hβ hd)

/-- One step: `value d = β⁻¹ (d 0 + value (shift d 1))`. -/
theorem value_step {m : ℕ} {d : ℕ → ℕ} (hd : Bounded m d) :
    value β d = β⁻¹ * (d 0 + value β (shift d 1)) := by
  unfold value
  rw [(summable_value hβ hd).tsum_eq_zero_add, mul_add, ← tsum_mul_left]
  simp only [zero_add, pow_one, shift_apply]
  congr 1
  · ring
  · refine tsum_congr fun n => ?_
    ring

/-- `β · value (shift d n) = d n + value (shift d (n+1))`. -/
theorem mul_value_shift {m : ℕ} {d : ℕ → ℕ} (hd : Bounded m d) (n : ℕ) :
    β * value β (shift d n) = d n + value β (shift d (n + 1)) := by
  rw [value_step hβ (hd.shift n), shift_shift_one]
  have hβ0 : β ≠ 0 := (by linarith : (0 : ℝ) < β).ne'
  simp only [shift_apply, zero_add]
  rw [← mul_assoc, mul_inv_cancel₀ hβ0, one_mul]

/-! ## Greedy (Rényi) expansions -/

end Base

/-- The Rényi map `T x = {β x}`. -/
noncomputable def renyiMap (β x : ℝ) : ℝ := Int.fract (β * x)

/-- The Rényi `β`-expansion: `xₙ = ⌊β Tⁿ x⌋`. For `x < 1` this is the greedy
expansion; it is the expansion `d_β(x)` of Adamczewski–Bugeaud. -/
noncomputable def renyiExpansion (β x : ℝ) (n : ℕ) : ℕ := ⌊β * (renyiMap β)^[n] x⌋₊

section Greedy

variable {β : ℝ} (hβ : 1 < β)
include hβ

/-- **Greedy binding.** A bounded stream all of whose tail values lie below `1`
is the Rényi expansion of its value. -/
theorem renyiExpansion_value {m : ℕ} {d : ℕ → ℕ} (hd : Bounded m d)
    (htail : ∀ n, value β (shift d n) < 1) : renyiExpansion β (value β d) = d := by
  have horbit : ∀ n, (renyiMap β)^[n] (value β d) = value β (shift d n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, renyiMap, mul_value_shift hβ hd]
      rw [Int.fract_eq_iff]
      refine ⟨value_nonneg hβ _, htail (n + 1), d n, ?_⟩
      push_cast
      ring
  funext n
  rw [renyiExpansion, horbit, mul_value_shift hβ hd, Nat.floor_eq_iff
    (add_nonneg (Nat.cast_nonneg _) (value_nonneg hβ _))]
  exact ⟨le_add_of_nonneg_right (value_nonneg hβ _), by linarith [htail (n + 1)]⟩

end Greedy

/-! ## Unique representation -/

/-- `d` is the only `{0,…,m}` stream with its value. -/
def IsUnique (β : ℝ) (m : ℕ) (d : ℕ → ℕ) : Prop :=
  Bounded m d ∧ ∀ e, Bounded m e → value β e = value β d → e = d

section Unique

variable {β : ℝ} (hβ : 1 < β)
include hβ

/-- **Uniqueness criterion** (sufficient direction). -/
theorem isUnique_of_tails {m : ℕ} {d : ℕ → ℕ} (hd : Bounded m d)
    (hup : ∀ n, d n < m → value β (shift d (n + 1)) < 1)
    (hdown : ∀ n, 0 < d n → (m : ℝ) / (β - 1) - 1 < value β (shift d (n + 1))) :
    IsUnique β m d := by
  refine ⟨hd, fun e he hv => ?_⟩
  -- Equal tails force equal digits, and equal digits pass equality to the next tail.
  have hdigit : ∀ n, value β (shift e n) = value β (shift d n) → e n = d n := by
    intro n hn
    have key : (e n : ℝ) + value β (shift e (n + 1)) = d n + value β (shift d (n + 1)) := by
      rw [← mul_value_shift hβ he, ← mul_value_shift hβ hd, hn]
    rcases lt_trichotomy (e n) (d n) with hlt | heq | hgt
    · exfalso
      have h1 : (e n : ℝ) + 1 ≤ d n := by exact_mod_cast hlt
      have hlow := hdown n (by omega)
      have hup' := value_le_of_le hβ (he.shift (n + 1))
      linarith
    · exact heq
    · exfalso
      have h1 : (d n : ℝ) + 1 ≤ e n := by exact_mod_cast hgt
      have hlt := hup n (lt_of_lt_of_le hgt (he n))
      have := value_nonneg hβ (shift e (n + 1))
      linarith
  have htails : ∀ n, value β (shift e n) = value β (shift d n) := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      have key : (e n : ℝ) + value β (shift e (n + 1)) = d n + value β (shift d (n + 1)) := by
        rw [← mul_value_shift hβ he, ← mul_value_shift hβ hd, ih]
      rw [hdigit n ih] at key
      linarith
  funext n
  exact hdigit n (htails n)

end Unique

/-! ## The imported dichotomy and the transcendence step -/

/-- Pisot numbers, via any annihilating monic integer polynomial. -/
def IsPisot (β : ℝ) : Prop :=
  1 < β ∧ ∃ P : Polynomial ℤ, P.Monic ∧ Polynomial.aeval β P = 0 ∧
    ∀ z : ℂ, Polynomial.aeval z P = 0 → z ≠ (β : ℂ) → ‖z‖ < 1

/-- **Adamczewski–Bugeaud (2007), Corollary 1**, restricted to Pisot bases: for
algebraic `α ∈ [0, 1]` the complexity of the `β`-expansion of `α` is bounded or
satisfies `liminf p(n)/n = +∞`. Imported as a hypothesis, never as an axiom. -/
def ABCorollary1 : Prop :=
  ∀ β : ℝ, IsPisot β → ∀ α : ℝ, IsAlgebraic ℚ α → 0 ≤ α → α ≤ 1 →
    (∃ B : ℕ, ∀ n, complexity (renyiExpansion β α) n ≤ B) ∨
      (∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n < complexity (renyiExpansion β α) n)

/-- A greedy, non-eventually-periodic expansion whose complexity is at most
linear along a subsequence has transcendental value, given `ABCorollary1`. -/
theorem transcendental_of_greedy (hAB : ABCorollary1) {β : ℝ} (hP : IsPisot β)
    {m : ℕ} {d : ℕ → ℕ} (hd : Bounded m d) (htail : ∀ n, value β (shift d n) < 1)
    (hper : ¬ EventuallyPeriodic d)
    (hlin : ∃ C : ℕ, ∀ N, ∃ n, N ≤ n ∧ complexity d n ≤ C * n) :
    Transcendental ℚ (value β d) := by
  intro halg
  have hβ := hP.1
  have h0 : 0 ≤ value β d := value_nonneg hβ d
  have h1 : value β d ≤ 1 := by simpa using (htail 0).le
  have hR := renyiExpansion_value hβ hd htail
  rcases hAB β hP _ halg h0 h1 with ⟨B, hB⟩ | hinf
  · rw [hR] at hB
    have := succ_le_complexity d (factors_finite_of_bounded hd) hper B
    have := hB B
    omega
  · rw [hR] at hinf
    obtain ⟨C, hC⟩ := hlin
    obtain ⟨N, hN⟩ := hinf C
    obtain ⟨n, hn, hle⟩ := hC N
    have := hN n hn
    omega

end Psc.BetaNumeration
