import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Golden-base endpoint theorem

For `β = φ`, digits `{0,1}` and valuation `π(d) = ∑_{n ≥ 1} d_n φ^{-n}`, a digit
stream is the only representation of its value among *all* `{0,1}` streams iff
it is constant. The represented values are then `0` and `φ`, the endpoints of
the representable interval `[0, φ]`.

This is the classical classification (Glendinning–Sidorov 2001), formalized
here as a specialization; no novelty is claimed. The proof is the direct one:
`φ² = φ + 1` exchanges `100` and `011`, so a unique stream alternates after its
first change of digit, and `(01)^∞` has the value of `1000…`.

Uniqueness is unrestricted: it quantifies over every stream, not over a greedy
or otherwise selected language. Source decision:
`docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaGoldenEndpoint

open scoped goldenRatio

/-- The contraction `φ⁻¹`. -/
noncomputable def r : ℝ := φ⁻¹

/-- A binary digit as a real number. -/
def digit (b : Bool) : ℝ := if b then 1 else 0

/-- The valuation `π(d) = ∑_{n ≥ 1} d_n φ^{-n}`, indexed from zero. -/
noncomputable def value (d : ℕ → Bool) : ℝ := ∑' n, digit (d n) * r ^ (n + 1)

/-- `d` is the only `{0,1}` stream with its value. -/
def IsUnique (d : ℕ → Bool) : Prop := ∀ e : ℕ → Bool, value e = value d → e = d

/-- Prepend a digit. -/
def cons (b : Bool) (t : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | k + 1 => t k

/-- Drop the first digit. -/
def tail (d : ℕ → Bool) : ℕ → Bool := fun k => d (k + 1)

@[simp] theorem digit_true : digit true = 1 := rfl
@[simp] theorem digit_false : digit false = 0 := rfl
@[simp] theorem cons_zero (b : Bool) (t : ℕ → Bool) : cons b t 0 = b := rfl
@[simp] theorem cons_succ (b : Bool) (t : ℕ → Bool) (k : ℕ) : cons b t (k + 1) = t k := rfl
@[simp] theorem tail_apply (d : ℕ → Bool) (k : ℕ) : tail d k = d (k + 1) := rfl

theorem digit_nonneg (b : Bool) : 0 ≤ digit b := by cases b <;> simp
theorem digit_le_one (b : Bool) : digit b ≤ 1 := by cases b <;> simp

theorem cons_head_tail (d : ℕ → Bool) : cons (d 0) (tail d) = d := by
  funext k; cases k <;> rfl

@[simp] theorem tail_cons (b : Bool) (t : ℕ → Bool) : tail (cons b t) = t := rfl

theorem r_pos : 0 < r := inv_pos.mpr Real.goldenRatio_pos

theorem r_lt_one : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

/-- The carry identity `φ⁻² + φ⁻¹ = 1`, i.e. `φ² = φ + 1`. -/
theorem r_sq_add : r ^ 2 + r = 1 := by
  have h1 : φ * r = 1 := mul_inv_cancel₀ Real.goldenRatio_pos.ne'
  have h := Real.goldenRatio_sq
  linear_combination (-r + φ * r + 1) * h1 - r ^ 2 * h

theorem summable_pow : Summable fun n : ℕ => r ^ (n + 1) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one r_pos.le r_lt_one)

theorem term_nonneg (d : ℕ → Bool) (n : ℕ) : 0 ≤ digit (d n) * r ^ (n + 1) :=
  mul_nonneg (digit_nonneg _) (pow_nonneg r_pos.le _)

theorem summable_value (d : ℕ → Bool) : Summable fun n => digit (d n) * r ^ (n + 1) :=
  Summable.of_nonneg_of_le (term_nonneg d)
    (fun _ => mul_le_of_le_one_left (pow_nonneg r_pos.le _) (digit_le_one _)) summable_pow

/-- One step of the valuation: `π(b t) = b φ⁻¹ + φ⁻¹ π(t)`. -/
theorem value_cons (b : Bool) (t : ℕ → Bool) :
    value (cons b t) = digit b * r + r * value t := by
  unfold value
  rw [(summable_value (cons b t)).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [cons_zero, cons_succ, zero_add, pow_one]
  congr 1
  refine tsum_congr fun n => ?_
  ring

theorem value_eq_step (d : ℕ → Bool) :
    value d = digit (d 0) * r + r * value (tail d) := by
  conv_lhs => rw [← cons_head_tail d]
  exact value_cons _ _

@[simp] theorem value_zero : value (fun _ => false) = 0 := by
  simp [value]

theorem value_nonneg (d : ℕ → Bool) : 0 ≤ value d := tsum_nonneg (term_nonneg d)

/-- The all-ones stream has value `φ`, the top of the representable interval. -/
theorem value_one : value (fun _ => true) = φ := by
  have hstep := value_eq_step (fun _ => true)
  have htail : tail (fun _ : ℕ => true) = fun _ => true := rfl
  rw [htail] at hstep
  simp only [digit_true, one_mul] at hstep
  -- `V = r + r V` and `1 - r = r²` give `V r = 1`.
  have hV : value (fun _ => true) * r = 1 := by
    have hr := r_sq_add
    have : r * (value (fun _ => true) * r - 1) = 0 := by
      linear_combination hstep + value (fun _ => true) * hr
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h r_pos.ne'
    · linarith
  have hφr : φ * r = 1 := mul_inv_cancel₀ Real.goldenRatio_pos.ne'
  exact mul_right_cancel₀ r_pos.ne' (hV.trans hφr.symm)

/-- Every value lies in `[0, φ]`. -/
theorem value_le (d : ℕ → Bool) : value d ≤ φ := by
  rw [← value_one]
  exact (summable_value d).tsum_le_tsum
    (fun n => by simpa using mul_le_of_le_one_left (pow_nonneg r_pos.le (n + 1)) (digit_le_one (d n)))
    (summable_value _)

/-! ## The two collisions (negative controls for unrestricted uniqueness) -/

/-- `100 t` and `011 t` have the same value. -/
theorem value_100_eq_011 (t : ℕ → Bool) :
    value (cons true (cons false (cons false t))) =
      value (cons false (cons true (cons true t))) := by
  simp only [value_cons, digit_true, digit_false]
  linear_combination (-r) * r_sq_add

/-- A stream that starts at `0` and changes digit at every step has value `φ⁻¹`. -/
theorem value_alternating {v : ℕ → Bool} (h0 : v 0 = false)
    (halt : ∀ k, v k ≠ v (k + 1)) : value v = r := by
  have h1 : v 1 = true := by
    have := halt 0
    rw [h0] at this
    cases h : v 1 <;> simp_all
  have hper : tail (tail v) = v := by
    funext k
    have a := halt k
    have b := halt (k + 1)
    simp only [tail_apply]
    cases hk : v k <;> cases hk1 : v (k + 1) <;> cases hk2 : v (k + 1 + 1) <;> simp_all
  have hstep : value v = r * (r + r * value v) := by
    have e1 := value_eq_step v
    have e2 := value_eq_step (tail v)
    rw [hper] at e2
    rw [e2] at e1
    simpa [h0, h1] using e1
  -- `V (1 - r²) = r²` and `1 - r² = r`.
  have : r * (value v - r) = 0 := by
    linear_combination hstep + value v * r_sq_add
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h r_pos.ne'
  · linarith

/-- `1000…` has value `φ⁻¹`. -/
theorem value_one_zeros : value (cons true fun _ => false) = r := by
  simp [value_cons]

/-- `(01)^∞` and `1000…` have the same value. -/
theorem value_01_periodic_eq_one_zeros {v : ℕ → Bool} (h0 : v 0 = false)
    (halt : ∀ k, v k ≠ v (k + 1)) : value v = value (cons true fun _ => false) :=
  (value_alternating h0 halt).trans value_one_zeros.symm

/-! ## Uniqueness passes to tails -/

theorem IsUnique.tail {d : ℕ → Bool} (h : IsUnique d) : IsUnique (tail d) := by
  intro e he
  have hv : value (cons (d 0) e) = value d := by
    rw [value_cons, he, ← value_eq_step]
  have := congrArg Psc.BetaGoldenEndpoint.tail (h _ hv)
  simpa using this

theorem IsUnique.shift {d : ℕ → Bool} (h : IsUnique d) (n : ℕ) :
    IsUnique (fun k => d (k + n)) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have : (fun k => d (k + (n + 1))) = Psc.BetaGoldenEndpoint.tail (fun k => d (k + n)) := by
      funext k
      simp only [tail_apply]
      congr 1
      omega
    rw [this]
    exact ih.tail

/-- A unique stream contains neither `100` nor `011` at its head. -/
theorem IsUnique.head_change {u : ℕ → Bool} (h : IsUnique u) (h01 : u 0 ≠ u 1) :
    u 1 ≠ u 2 := by
  intro h12
  have key : ∀ a : Bool, u 0 = a → u 1 = !a → u 2 = !a → False := by
    intro a h0 h1 h2
    have hu : u = cons a (cons (!a) (cons (!a) fun k => u (k + 3))) := by
      funext k
      match k with
      | 0 => exact h0
      | 1 => exact h1
      | 2 => exact h2
      | k + 3 => rfl
    cases a
    · have hv : value (cons true (cons false (cons false fun k => u (k + 3)))) = value u :=
        (value_100_eq_011 _).trans (congrArg value hu.symm)
      have := congrFun (h _ hv) 0
      simp [h0] at this
    · have hv : value (cons false (cons true (cons true fun k => u (k + 3)))) = value u :=
        (value_100_eq_011 _).symm.trans (congrArg value hu.symm)
      have := congrFun (h _ hv) 0
      simp [h0] at this
  have e1 : u 1 = !u 0 := by
    cases h0 : u 0 <;> cases h1 : u 1 <;> simp_all
  exact key (u 0) rfl e1 (h12 ▸ e1)

/-- A unique stream contains neither `100` nor `011` anywhere. -/
theorem IsUnique.change_at {d : ℕ → Bool} (h : IsUnique d) (m : ℕ) (hm : d m ≠ d (m + 1)) :
    d (m + 1) ≠ d (m + 2) := by
  have hs : d (1 + m) ≠ d (2 + m) :=
    (h.shift m).head_change (show d (0 + m) ≠ d (1 + m) by
      rw [Nat.zero_add, Nat.add_comm 1 m]; exact hm)
  rwa [Nat.add_comm 1 m, Nat.add_comm 2 m] at hs

/-- A unique stream does not start at `0` and alternate forever. -/
theorem IsUnique.not_alternating {v : ℕ → Bool} (h : IsUnique v) (h0 : v 0 = false) :
    ¬ ∀ k, v k ≠ v (k + 1) := by
  intro halt
  have := congrFun (h _ (value_01_periodic_eq_one_zeros h0 halt).symm) 0
  simp [h0] at this

/-- No tail of a unique stream starts at `0` and alternates forever. -/
theorem IsUnique.not_alternating_from {d : ℕ → Bool} (h : IsUnique d) (m : ℕ)
    (h0 : d m = false) : ¬ ∀ k, d (m + k) ≠ d (m + k + 1) := by
  intro halt
  refine (h.shift m).not_alternating (show d (0 + m) = false by rw [Nat.zero_add]; exact h0)
    (fun k => show d (k + m) ≠ d (k + 1 + m) from ?_)
  have e1 : k + m = m + k := Nat.add_comm _ _
  have e2 : k + 1 + m = m + k + 1 := by omega
  rw [e1, e2]
  exact halt k

/-! ## The classification -/

/-- A stream with unrestricted unique representation is constant. -/
theorem IsUnique.constant {d : ℕ → Bool} (h : IsUnique d) : ∀ n, d n = d 0 := by
  by_contra hne
  have hchange : ∃ n, d n ≠ d (n + 1) := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    apply hne
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← hno n, ih]
  obtain ⟨n, hn⟩ := hchange
  -- After the first change the digits alternate.
  have halt : ∀ k, d (n + k) ≠ d (n + k + 1) := by
    intro k
    induction k with
    | zero => exact hn
    | succ k ih => exact h.change_at (n + k) ih
  -- Start the alternating tail at a zero digit.
  cases hdn : d n with
  | false => exact h.not_alternating_from n hdn halt
  | true =>
    have hn1 : d (n + 1) = false := by
      cases h1 : d (n + 1) <;> simp_all
    refine h.not_alternating_from (n + 1) hn1 (fun k => ?_)
    have := halt (k + 1)
    rwa [show n + (k + 1) = n + 1 + k by omega] at this

theorem isUnique_zero : IsUnique (fun _ => false) := by
  intro e he
  rw [value_zero] at he
  have hs : HasSum (fun n => digit (e n) * r ^ (n + 1)) (value e) := (summable_value e).hasSum
  rw [he] at hs
  have hz := (hasSum_zero_iff_of_nonneg (term_nonneg e)).mp hs
  funext n
  have hn := congrFun hz n
  cases hen : e n
  · rfl
  · rw [hen] at hn
    exact absurd (by simpa using hn) (pow_pos r_pos (n + 1)).ne'

theorem isUnique_one : IsUnique (fun _ => true) := by
  intro e he
  have hsub : HasSum (fun n => (1 - digit (e n)) * r ^ (n + 1)) 0 := by
    have h1 : HasSum (fun n => digit true * r ^ (n + 1)) (value fun _ => true) :=
      (summable_value (fun _ => true)).hasSum
    have h2 : HasSum (fun n => digit (e n) * r ^ (n + 1)) (value e) := (summable_value e).hasSum
    have := h1.sub h2
    rw [he, sub_self] at this
    have hfun : (fun n => (1 - digit (e n)) * r ^ (n + 1)) =
        fun n => digit true * r ^ (n + 1) - digit (e n) * r ^ (n + 1) := by
      funext n
      rw [digit_true, sub_mul]
    rw [hfun]
    exact this
  have hz := (hasSum_zero_iff_of_nonneg (fun n =>
    mul_nonneg (sub_nonneg.mpr (digit_le_one _)) (pow_nonneg r_pos.le _))).mp hsub
  funext n
  have hn := congrFun hz n
  cases hen : e n
  · rw [hen] at hn
    exact absurd (by simpa using hn) (pow_pos r_pos (n + 1)).ne'
  · rfl

/-- **Golden-base endpoint theorem.** Among all `{0,1}` streams, exactly the
two constant streams are the only representation of their value. -/
theorem isUnique_iff (d : ℕ → Bool) :
    IsUnique d ↔ d = (fun _ => false) ∨ d = (fun _ => true) := by
  constructor
  · intro h
    have hc := h.constant
    cases h0 : d 0
    · exact Or.inl (funext fun n => (hc n).trans h0)
    · exact Or.inr (funext fun n => (hc n).trans h0)
  · rintro (rfl | rfl)
    · exact isUnique_zero
    · exact isUnique_one

/-- The uniquely represented values are exactly the endpoints `0` and `φ`. -/
theorem value_of_isUnique {d : ℕ → Bool} (h : IsUnique d) : value d = 0 ∨ value d = φ := by
  rcases (isUnique_iff d).mp h with rfl | rfl
  · exact Or.inl value_zero
  · exact Or.inr value_one

/-- On `[0,1)` the only uniquely represented value is zero. -/
theorem eq_zero_of_isUnique_of_lt_one {d : ℕ → Bool} (h : IsUnique d) (hlt : value d < 1) :
    d = fun _ => false := by
  rcases (isUnique_iff d).mp h with rfl | rfl
  · rfl
  · rw [value_one] at hlt
    exact absurd hlt (not_lt.mpr Real.one_lt_goldenRatio.le)

end Psc.BetaGoldenEndpoint
