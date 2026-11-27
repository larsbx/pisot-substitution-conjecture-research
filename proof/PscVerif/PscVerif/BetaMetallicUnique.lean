import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Unique expansions in the metallic quadratic bases

Let `β > 1` be the positive root of `β² = mβ + 1`, `m ≥ 1`, with the full
alphabet `{0, …, m}` and valuation `π(d) = ∑_{n ≥ 1} d_n β^{-n}`. A stream is
the only representation of its value among *all* streams over the alphabet iff
its endpoint digits occur only in an initial constant run:

* a digit `0` is preceded only by `0`, and
* a digit `m` is preceded only by `m`.

Equivalently the stream is `0^∞`, `m^∞`, `0^r w` or `m^r w` with every digit
of `w` in `{1, …, m-1}`. At `m = 1` this is the golden-base endpoint theorem.

This is a specialization of the known theory of unique expansions; no novelty
is claimed. Uniqueness is unrestricted: it quantifies over every stream, not
over a greedy or otherwise selected language. Source decision:
`docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaMetallicUnique

/-- A metallic base, by its contraction `r = β⁻¹`: `m r + r² = 1`. -/
structure Base (m : ℕ) where
  r : ℝ
  r_pos : 0 < r
  one_le : 1 ≤ m
  carry : (m : ℝ) * r + r ^ 2 = 1

variable {m : ℕ}

/-- Prepend a digit. -/
def cons (b : Fin (m + 1)) (t : ℕ → Fin (m + 1)) : ℕ → Fin (m + 1)
  | 0 => b
  | k + 1 => t k

/-- Drop the first digit. -/
def tail (d : ℕ → Fin (m + 1)) : ℕ → Fin (m + 1) := fun k => d (k + 1)

/-- Drop the first `n` digits. -/
def shift (d : ℕ → Fin (m + 1)) (n : ℕ) : ℕ → Fin (m + 1) := fun k => d (n + k)

/-- Endpoint digits occur only in an initial constant run. -/
def EndpointsInitial (d : ℕ → Fin (m + 1)) : Prop :=
  (∀ n, (d (n + 1) : ℕ) = 0 → (d n : ℕ) = 0) ∧ (∀ n, (d (n + 1) : ℕ) = m → (d n : ℕ) = m)

@[simp] theorem cons_zero (b : Fin (m + 1)) (t : ℕ → Fin (m + 1)) : cons b t 0 = b := rfl
@[simp] theorem cons_succ (b : Fin (m + 1)) (t : ℕ → Fin (m + 1)) (k : ℕ) :
    cons b t (k + 1) = t k := rfl
@[simp] theorem tail_apply (d : ℕ → Fin (m + 1)) (k : ℕ) : tail d k = d (k + 1) := rfl
@[simp] theorem tail_cons (b : Fin (m + 1)) (t : ℕ → Fin (m + 1)) : tail (cons b t) = t := rfl

theorem cons_head_tail (d : ℕ → Fin (m + 1)) : cons (d 0) (tail d) = d := by
  funext k; cases k <;> rfl

theorem shift_zero (d : ℕ → Fin (m + 1)) : shift d 0 = d := by
  funext k; simp [shift]

theorem shift_succ (d : ℕ → Fin (m + 1)) (n : ℕ) : shift d (n + 1) = tail (shift d n) := by
  funext k
  simp only [shift, tail]
  congr 1
  omega

theorem digit_le (a : Fin (m + 1)) : ((a : ℕ) : ℝ) ≤ m := by
  exact_mod_cast Nat.lt_succ_iff.mp a.2

namespace Base

variable (B : Base m)

theorem m_pos (B : Base m) : (0 : ℝ) < m := by exact_mod_cast B.one_le

theorem r_lt_one : B.r < 1 := by
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast B.one_le
  have h2 := mul_le_mul_of_nonneg_right h1 B.r_pos.le
  have h3 := pow_pos B.r_pos 2
  linarith [B.carry]

/-- The valuation `π(d) = ∑_{n ≥ 1} d_n β^{-n}`, indexed from zero. -/
noncomputable def value (d : ℕ → Fin (m + 1)) : ℝ := ∑' n, ((d n : ℕ) : ℝ) * B.r ^ (n + 1)

/-- `d` is the only stream over `{0, …, m}` with its value. -/
def IsUnique (d : ℕ → Fin (m + 1)) : Prop := ∀ e : ℕ → Fin (m + 1), B.value e = B.value d → e = d

/-- The value of the all-ones stream. -/
noncomputable def G : ℝ := ∑' n : ℕ, B.r ^ (n + 1)

theorem summable_pow : Summable fun n : ℕ => B.r ^ (n + 1) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one B.r_pos.le B.r_lt_one)

theorem term_nonneg (d : ℕ → Fin (m + 1)) (n : ℕ) : 0 ≤ ((d n : ℕ) : ℝ) * B.r ^ (n + 1) :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg B.r_pos.le _)

theorem summable_value (d : ℕ → Fin (m + 1)) :
    Summable fun n => ((d n : ℕ) : ℝ) * B.r ^ (n + 1) :=
  Summable.of_nonneg_of_le (B.term_nonneg d)
    (fun _ => mul_le_mul_of_nonneg_right (digit_le _) (pow_nonneg B.r_pos.le _))
    (B.summable_pow.mul_left _)

/-- One step of the valuation: `π(b t) = b β⁻¹ + β⁻¹ π(t)`. -/
theorem value_cons (b : Fin (m + 1)) (t : ℕ → Fin (m + 1)) :
    B.value (cons b t) = ((b : ℕ) : ℝ) * B.r + B.r * B.value t := by
  unfold value
  rw [(B.summable_value (cons b t)).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [cons_zero, cons_succ, zero_add, pow_one]
  congr 1
  refine tsum_congr fun n => ?_
  ring

theorem value_eq_step (d : ℕ → Fin (m + 1)) :
    B.value d = ((d 0 : ℕ) : ℝ) * B.r + B.r * B.value (tail d) := by
  conv_lhs => rw [← cons_head_tail d]
  exact B.value_cons _ _

theorem value_const (a : Fin (m + 1)) : B.value (fun _ => a) = ((a : ℕ) : ℝ) * B.G := by
  unfold value G
  rw [tsum_mul_left]

theorem value_nonneg (d : ℕ → Fin (m + 1)) : 0 ≤ B.value d := tsum_nonneg (B.term_nonneg d)

theorem G_step : B.G = B.r + B.r * B.G := by
  have h := B.summable_pow.tsum_eq_zero_add
  have h2 : (∑' n : ℕ, B.r ^ (n + 1 + 1)) = B.r * ∑' n : ℕ, B.r ^ (n + 1) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  rw [h2, zero_add, pow_one] at h
  exact h

theorem G_pos : 0 < B.G := by
  have h0 : 0 ≤ B.G := tsum_nonneg fun n => pow_nonneg B.r_pos.le _
  have := B.G_step
  nlinarith [mul_nonneg B.r_pos.le h0, B.r_pos]

theorem r_lt_G : B.r < B.G := by
  have := B.G_step
  nlinarith [mul_pos B.r_pos B.G_pos]

/-- The top of the representable interval: `m/(β - 1) = 1 + β⁻¹`. -/
theorem top : (m : ℝ) * B.G = 1 + B.r := by
  have h : (1 - B.r) * ((m : ℝ) * B.G - (1 + B.r)) = 0 := by
    linear_combination (m : ℝ) * B.G_step + B.carry
  rcases mul_eq_zero.mp h with h | h
  · linarith [B.r_lt_one]
  · linarith

theorem const_mul_G : (m : ℝ) * B.G = ∑' n : ℕ, (m : ℝ) * B.r ^ (n + 1) := by
  unfold G
  rw [tsum_mul_left]

/-- Every value lies in `[0, 1 + β⁻¹]`. -/
theorem value_le_top (d : ℕ → Fin (m + 1)) : B.value d ≤ 1 + B.r := by
  rw [← B.top, B.const_mul_G]
  exact (B.summable_value d).tsum_le_tsum
    (fun _ => mul_le_mul_of_nonneg_right (digit_le _) (pow_nonneg B.r_pos.le _))
    (B.summable_pow.mul_left _)

/-- A stream with no digit `m` has value below `1`. -/
theorem value_lt_one {t : ℕ → Fin (m + 1)} (h : ∀ k, (t k : ℕ) < m) : B.value t < 1 := by
  have e : B.value t + B.G = ∑' n, (((t n : ℕ) : ℝ) + 1) * B.r ^ (n + 1) := by
    unfold value G
    rw [← (B.summable_value t).tsum_add B.summable_pow]
    exact tsum_congr fun n => by ring
  have s : Summable fun n => (((t n : ℕ) : ℝ) + 1) * B.r ^ (n + 1) :=
    ((B.summable_value t).add B.summable_pow).congr fun n => by ring
  have hle : B.value t + B.G ≤ (m : ℝ) * B.G := by
    rw [e, B.const_mul_G]
    exact s.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_right (by exact_mod_cast h n) (pow_nonneg B.r_pos.le _))
      (B.summable_pow.mul_left _)
  linarith [B.top, B.r_lt_G]

/-- A stream with no digit `0` has value above `β⁻¹`. -/
theorem lt_value {t : ℕ → Fin (m + 1)} (h : ∀ k, 0 < (t k : ℕ)) : B.r < B.value t := by
  have hle : B.G ≤ B.value t := by
    unfold G value
    exact B.summable_pow.tsum_le_tsum
      (fun n => le_mul_of_one_le_left (pow_nonneg B.r_pos.le _) (by exact_mod_cast h n))
      (B.summable_value t)
  linarith [B.r_lt_G]

/-! ## Collisions -/

/-- The carry `a 0 c ~ (a-1) m (c+1)`, valid before any common tail. -/
theorem value_carry (a a' z l c c' : Fin (m + 1)) (t : ℕ → Fin (m + 1))
    (ha : (a : ℕ) = a' + 1) (hz : (z : ℕ) = 0) (hl : (l : ℕ) = m) (hc : (c' : ℕ) = c + 1) :
    B.value (cons a (cons z (cons c t))) = B.value (cons a' (cons l (cons c' t))) := by
  have ha' : ((a : ℕ) : ℝ) = (a' : ℕ) + 1 := by exact_mod_cast ha
  have hc' : ((c' : ℕ) : ℝ) = (c : ℕ) + 1 := by exact_mod_cast hc
  simp only [value_cons, ha', hc', hz, hl, Nat.cast_zero]
  linear_combination (-B.r) * B.carry

/-- `(0 m)^∞` has value `β⁻¹`, the value of `1 0^∞`. -/
theorem value_zero_top {v : ℕ → Fin (m + 1)}
    (h : ∀ k, (v (2 * k) : ℕ) = 0 ∧ (v (2 * k + 1) : ℕ) = m) : B.value v = B.r := by
  have hper : tail (tail v) = v := by
    funext j
    apply Fin.ext
    show (v (j + 1 + 1) : ℕ) = v j
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, (h (k + 1)).1, (h k).1]
    · rw [show 2 * k + 1 + 1 + 1 = 2 * (k + 1) + 1 by ring, (h (k + 1)).2, (h k).2]
  have e1 := B.value_eq_step v
  have e2 := B.value_eq_step (tail v)
  rw [hper] at e2
  rw [e2] at e1
  have a0 : (v 0 : ℕ) = 0 := (h 0).1
  have a1 : (tail v 0 : ℕ) = m := (h 0).2
  rw [a0, a1, Nat.cast_zero] at e1
  have hz : (m : ℝ) * B.r * (B.value v - B.r) = 0 := by
    linear_combination e1 + B.value v * B.carry
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h (mul_pos B.m_pos B.r_pos).ne'
  · linarith

/-- `(m 0)^∞` has value `1`, the value of `β 0^∞` one place up. -/
theorem value_top_zero {v : ℕ → Fin (m + 1)}
    (h : ∀ k, (v (2 * k) : ℕ) = m ∧ (v (2 * k + 1) : ℕ) = 0) : B.value v = 1 := by
  have hper : tail (tail v) = v := by
    funext j
    apply Fin.ext
    show (v (j + 1 + 1) : ℕ) = v j
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, (h (k + 1)).1, (h k).1]
    · rw [show 2 * k + 1 + 1 + 1 = 2 * (k + 1) + 1 by ring, (h (k + 1)).2, (h k).2]
  have e1 := B.value_eq_step v
  have e2 := B.value_eq_step (tail v)
  rw [hper] at e2
  rw [e2] at e1
  have a0 : (v 0 : ℕ) = m := (h 0).1
  have a1 : (tail v 0 : ℕ) = 0 := (h 0).2
  rw [a0, a1, Nat.cast_zero] at e1
  have hz : (m : ℝ) * B.r * (B.value v - 1) = 0 := by
    linear_combination e1 + B.value v * B.carry
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h (mul_pos B.m_pos B.r_pos).ne'
  · linarith

/-! ## Uniqueness passes to tails -/

variable {B}

theorem IsUnique.of_tail {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) : B.IsUnique (tail d) := by
  intro e he
  have hv : B.value (cons (d 0) e) = B.value d := by
    rw [B.value_cons, he, ← B.value_eq_step]
  have := congrArg tail (h _ hv)
  simpa using this

theorem IsUnique.of_shift {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) (n : ℕ) :
    B.IsUnique (shift d n) := by
  induction n with
  | zero => rw [shift_zero]; exact h
  | succ n ih => rw [shift_succ]; exact ih.of_tail

/-! ## Necessity -/

/-- In a unique stream, `a 0` with `a > 0` is followed by `m`. -/
theorem IsUnique.head_zero {u : ℕ → Fin (m + 1)} (h : B.IsUnique u) (h0 : 0 < (u 0 : ℕ))
    (h1 : (u 1 : ℕ) = 0) : (u 2 : ℕ) = m := by
  by_contra h2
  have h2' : (u 2 : ℕ) < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp (u 2).2) h2
  have hu0 := (u 0).2
  let a' : Fin (m + 1) := ⟨(u 0 : ℕ) - 1, by omega⟩
  let c' : Fin (m + 1) := ⟨(u 2 : ℕ) + 1, by omega⟩
  have hu : u = cons (u 0) (cons (u 1) (cons (u 2) fun k => u (k + 3))) := by
    funext k
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | k + 3 => rfl
  have hv : B.value (cons a' (cons (Fin.last m) (cons c' fun k => u (k + 3)))) = B.value u := by
    rw [← B.value_carry (u 0) a' (u 1) (Fin.last m) (u 2) c' _
      (show (u 0 : ℕ) = (u 0 : ℕ) - 1 + 1 by omega) h1 (Fin.val_last m) rfl]
    exact congrArg B.value hu.symm
  have := congrArg Fin.val (congrFun (h _ hv) 0)
  change (u 0 : ℕ) - 1 = (u 0 : ℕ) at this
  omega

/-- In a unique stream, `a m` with `a < m` is followed by `0`. -/
theorem IsUnique.head_top {u : ℕ → Fin (m + 1)} (h : B.IsUnique u) (h0 : (u 0 : ℕ) < m)
    (h1 : (u 1 : ℕ) = m) : (u 2 : ℕ) = 0 := by
  by_contra h2
  have hu2 := (u 2).2
  let a' : Fin (m + 1) := ⟨(u 0 : ℕ) + 1, by omega⟩
  let c' : Fin (m + 1) := ⟨(u 2 : ℕ) - 1, by omega⟩
  let z : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
  have hu : u = cons (u 0) (cons (u 1) (cons (u 2) fun k => u (k + 3))) := by
    funext k
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | k + 3 => rfl
  have hv : B.value (cons a' (cons z (cons c' fun k => u (k + 3)))) = B.value u := by
    rw [B.value_carry a' (u 0) z (u 1) c' (u 2) _ rfl rfl h1
      (show (u 2 : ℕ) = (u 2 : ℕ) - 1 + 1 by omega)]
    exact congrArg B.value hu.symm
  have := congrArg Fin.val (congrFun (h _ hv) 0)
  change (u 0 : ℕ) + 1 = (u 0 : ℕ) at this
  omega

theorem IsUnique.zero_at {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) (n : ℕ)
    (h0 : 0 < (d n : ℕ)) (h1 : (d (n + 1) : ℕ) = 0) : (d (n + 2) : ℕ) = m :=
  (h.of_shift n).head_zero h0 h1

theorem IsUnique.top_at {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) (n : ℕ)
    (h0 : (d n : ℕ) < m) (h1 : (d (n + 1) : ℕ) = m) : (d (n + 2) : ℕ) = 0 :=
  (h.of_shift n).head_top h0 h1

/-- In a unique stream a digit `0` is preceded only by `0`. -/
theorem IsUnique.zero_pred {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) (n : ℕ)
    (h1 : (d (n + 1) : ℕ) = 0) : (d n : ℕ) = 0 := by
  by_contra hne
  have h0 : 0 < (d n : ℕ) := Nat.pos_of_ne_zero hne
  have hm := B.one_le
  have hdn := (d n).2
  -- The tail after `d n` is `(0 m)^∞`.
  have alt : ∀ k, (d (n + 1 + 2 * k) : ℕ) = 0 ∧ (d (n + 1 + 2 * k + 1) : ℕ) = m := by
    intro k
    induction k with
    | zero => exact ⟨h1, h.zero_at n h0 h1⟩
    | succ k ih =>
      have z : (d (n + 1 + 2 * k + 2) : ℕ) = 0 := h.top_at (n + 1 + 2 * k) (by omega) ih.2
      have t : (d (n + 1 + 2 * k + 1 + 2) : ℕ) = m :=
        h.zero_at (n + 1 + 2 * k + 1) (by omega) z
      rw [show n + 1 + 2 * (k + 1) = n + 1 + 2 * k + 2 by ring]
      exact ⟨z, t⟩
  have hr : B.value (tail (shift d n)) = B.r := by
    refine B.value_zero_top (fun k => ?_)
    show (d (n + (2 * k + 1)) : ℕ) = 0 ∧ (d (n + (2 * k + 1 + 1)) : ℕ) = m
    have := alt k
    rwa [show n + 1 + 2 * k = n + (2 * k + 1) by omega,
      show n + (2 * k + 1) + 1 = n + (2 * k + 1 + 1) by omega] at this
  -- `a (0 m)^∞` and `(a-1) m^∞` have the same value.
  let a' : Fin (m + 1) := ⟨(d n : ℕ) - 1, by omega⟩
  have ha : ((a' : ℕ) : ℝ) = ((d n : ℕ) : ℝ) - 1 := by
    show (((d n : ℕ) - 1 : ℕ) : ℝ) = _
    rw [Nat.cast_sub h0, Nat.cast_one]
  have e1 : B.value (shift d n) =
      ((d n : ℕ) : ℝ) * B.r + B.r * B.value (tail (shift d n)) :=
    B.value_eq_step _
  have hv : B.value (cons a' fun _ => Fin.last m) = B.value (shift d n) := by
    rw [B.value_cons, B.value_const, e1, hr, ha, Fin.val_last, B.top]
    ring
  have := congrArg Fin.val (congrFun ((h.of_shift n) _ hv) 0)
  change (d n : ℕ) - 1 = (d n : ℕ) at this
  omega

/-- In a unique stream a digit `m` is preceded only by `m`. -/
theorem IsUnique.top_pred {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) (n : ℕ)
    (h1 : (d (n + 1) : ℕ) = m) : (d n : ℕ) = m := by
  by_contra hne
  have h0 : (d n : ℕ) < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp (d n).2) hne
  have hm := B.one_le
  -- The tail after `d n` is `(m 0)^∞`.
  have alt : ∀ k, (d (n + 1 + 2 * k) : ℕ) = m ∧ (d (n + 1 + 2 * k + 1) : ℕ) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨h1, h.top_at n h0 h1⟩
    | succ k ih =>
      have z : (d (n + 1 + 2 * k + 2) : ℕ) = m := h.zero_at (n + 1 + 2 * k) (by omega) ih.2
      have t : (d (n + 1 + 2 * k + 1 + 2) : ℕ) = 0 :=
        h.top_at (n + 1 + 2 * k + 1) (by omega) z
      rw [show n + 1 + 2 * (k + 1) = n + 1 + 2 * k + 2 by ring]
      exact ⟨z, t⟩
  have hr : B.value (tail (shift d n)) = 1 := by
    refine B.value_top_zero (fun k => ?_)
    show (d (n + (2 * k + 1)) : ℕ) = m ∧ (d (n + (2 * k + 1 + 1)) : ℕ) = 0
    have := alt k
    rwa [show n + 1 + 2 * k = n + (2 * k + 1) by omega,
      show n + (2 * k + 1) + 1 = n + (2 * k + 1 + 1) by omega] at this
  -- `a (m 0)^∞` and `(a+1) 0^∞` have the same value.
  let a' : Fin (m + 1) := ⟨(d n : ℕ) + 1, by omega⟩
  let z : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
  have ha : ((a' : ℕ) : ℝ) = ((d n : ℕ) : ℝ) + 1 := by
    show (((d n : ℕ) + 1 : ℕ) : ℝ) = _
    rw [Nat.cast_add, Nat.cast_one]
  have hz : ((z : ℕ) : ℝ) = 0 := Nat.cast_zero
  have e1 : B.value (shift d n) =
      ((d n : ℕ) : ℝ) * B.r + B.r * B.value (tail (shift d n)) :=
    B.value_eq_step _
  have hv : B.value (cons a' fun _ => z) = B.value (shift d n) := by
    rw [B.value_cons, B.value_const, e1, hr, ha, hz]
    ring
  have := congrArg Fin.val (congrFun ((h.of_shift n) _ hv) 0)
  change (d n : ℕ) + 1 = (d n : ℕ) at this
  omega

theorem IsUnique.endpointsInitial {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) :
    EndpointsInitial d := ⟨h.zero_pred, h.top_pred⟩

/-! ## Sufficiency -/

variable (B)

theorem value_shift_eq {d e : ℕ → Fin (m + 1)} (n : ℕ) (hpre : ∀ k < n, e k = d k)
    (he : B.value e = B.value d) : B.value (shift e n) = B.value (shift d n) := by
  induction n with
  | zero => rw [shift_zero, shift_zero]; exact he
  | succ n ih =>
    have hn := ih fun k hk => hpre k (Nat.lt_succ_of_lt hk)
    have h0 : shift e n 0 = shift d n 0 := hpre n (Nat.lt_succ_self n)
    rw [B.value_eq_step (shift e n), B.value_eq_step (shift d n), h0] at hn
    rw [shift_succ, shift_succ]
    exact mul_left_cancel₀ B.r_pos.ne' (add_left_cancel hn)

end Base

theorem EndpointsInitial.lt_top_from {d : ℕ → Fin (m + 1)} (S : EndpointsInitial d) {n : ℕ}
    (h : (d n : ℕ) < m) : ∀ k, (d (n + k) : ℕ) < m := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    by_contra hk
    have hle := Nat.lt_succ_iff.mp (d (n + (k + 1))).2
    have := S.2 (n + k) (by show (d (n + (k + 1)) : ℕ) = m; omega)
    omega

theorem EndpointsInitial.pos_from {d : ℕ → Fin (m + 1)} (S : EndpointsInitial d) {n : ℕ}
    (h : 0 < (d n : ℕ)) : ∀ k, 0 < (d (n + k) : ℕ) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    by_contra hk
    have := S.1 (n + k) (by show (d (n + (k + 1)) : ℕ) = 0; omega)
    omega

/-- After leaving its endpoint run, a stream has only interior digits. -/
theorem EndpointsInitial.interior_from {d : ℕ → Fin (m + 1)} (S : EndpointsInitial d) {n : ℕ}
    (h0 : 0 < (d n : ℕ)) (h1 : (d n : ℕ) < m) (k : ℕ) :
    0 < (d (n + k) : ℕ) ∧ (d (n + k) : ℕ) < m := ⟨S.pos_from h0 k, S.lt_top_from h1 k⟩

/-- At `m = 1` the condition says the stream is constant. -/
theorem EndpointsInitial.const_of_one {d : ℕ → Fin (m + 1)} (S : EndpointsInitial d)
    (hm : m = 1) (n : ℕ) : d n = d (n + 1) := by
  apply Fin.ext
  have h1 := (d (n + 1)).2
  have a := S.1 n
  have b := S.2 n
  omega

namespace Base

variable {B : Base m}

theorem tail_lt_one {d : ℕ → Fin (m + 1)} (S : EndpointsInitial d) {n : ℕ}
    (h : (d n : ℕ) < m) : B.value (tail (shift d n)) < 1 :=
  B.value_lt_one fun k => S.lt_top_from h (k + 1)

theorem lt_tail {d : ℕ → Fin (m + 1)} (S : EndpointsInitial d) {n : ℕ}
    (h : 0 < (d n : ℕ)) : B.r < B.value (tail (shift d n)) :=
  B.lt_value fun k => S.pos_from h (k + 1)

/-- A stream whose endpoint digits occur only in an initial constant run is unique. -/
theorem isUnique_of_endpointsInitial {d : ℕ → Fin (m + 1)} (S : EndpointsInitial d) :
    B.IsUnique d := by
  intro e he
  by_contra hne
  have hex : ∃ n, e n ≠ d n := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    exact hne (funext hno)
  obtain ⟨n, hn, hmin⟩ : ∃ n, e n ≠ d n ∧ ∀ k < n, e k = d k := by
    classical
    exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_not.mp (Nat.find_min hex hk)⟩
  have hval := B.value_shift_eq n hmin he
  have e1 : B.value (shift d n) = ((d n : ℕ) : ℝ) * B.r + B.r * B.value (tail (shift d n)) :=
    B.value_eq_step _
  have e2 : B.value (shift e n) = ((e n : ℕ) : ℝ) * B.r + B.r * B.value (tail (shift e n)) :=
    B.value_eq_step _
  have key : ((d n : ℕ) : ℝ) + B.value (tail (shift d n)) =
      ((e n : ℕ) : ℝ) + B.value (tail (shift e n)) := by
    have : B.r * (((d n : ℕ) : ℝ) + B.value (tail (shift d n))) =
        B.r * (((e n : ℕ) : ℝ) + B.value (tail (shift e n))) := by
      linear_combination e2 - e1 - hval
    exact mul_left_cancel₀ B.r_pos.ne' this
  rcases lt_or_gt_of_ne (show (d n : ℕ) ≠ e n from fun h => hn (Fin.ext h.symm)) with hlt | hgt
  · have b := tail_lt_one (B := B) S (lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp (e n).2))
    have c : ((d n : ℕ) : ℝ) + 1 ≤ (e n : ℕ) := by exact_mod_cast hlt
    linarith [B.value_nonneg (tail (shift e n))]
  · have b := lt_tail (B := B) S (Nat.lt_of_le_of_lt (Nat.zero_le _) hgt)
    have c : ((e n : ℕ) : ℝ) + 1 ≤ (d n : ℕ) := by exact_mod_cast hgt
    linarith [B.value_le_top (tail (shift e n))]

/-- **Metallic unique-expansion theorem.** Among all streams over `{0, …, m}`,
exactly those whose endpoint digits occur only in an initial constant run are
the only representation of their value. -/
theorem isUnique_iff (d : ℕ → Fin (m + 1)) : B.IsUnique d ↔ EndpointsInitial d :=
  ⟨IsUnique.endpointsInitial, isUnique_of_endpointsInitial⟩

/-- A stream with every digit in `{1, …, m-1}` is unique and has value in
`(β⁻¹, 1)`. -/
theorem interior {d : ℕ → Fin (m + 1)} (h : ∀ n, 0 < (d n : ℕ) ∧ (d n : ℕ) < m) :
    B.IsUnique d ∧ B.r < B.value d ∧ B.value d < 1 :=
  ⟨isUnique_of_endpointsInitial
      ⟨fun n hz => absurd hz (h (n + 1)).1.ne', fun n ht => absurd ht (h (n + 1)).2.ne⟩,
    B.lt_value fun k => (h k).1, B.value_lt_one fun k => (h k).2⟩

/-- At `m = 1` a unique stream is constant. -/
theorem IsUnique.const_of_one {d : ℕ → Fin (m + 1)} (h : B.IsUnique d) (hm : m = 1) (n : ℕ) :
    d n = d (n + 1) := h.endpointsInitial.const_of_one hm n

/-! ## The bases exist -/

/-- The base attached to a positive root of `β² = mβ + 1`. -/
noncomputable def ofRoot (hm : 1 ≤ m) (β : ℝ) (hpos : 0 < β) (hsq : β ^ 2 = (m : ℝ) * β + 1) :
    Base m where
  r := β⁻¹
  r_pos := inv_pos.mpr hpos
  one_le := hm
  carry := by
    have h1 : β * β⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    linear_combination (-(β⁻¹) ^ 2) * hsq + (β * β⁻¹ + 1 - (m : ℝ) * β⁻¹) * h1

/-- The metallic base with `β⁻¹ = (√(m² + 4) - m)/2`. -/
noncomputable def metallic (hm : 1 ≤ m) : Base m where
  r := (√((m : ℝ) ^ 2 + 4) - m) / 2
  r_pos := by
    have : (m : ℝ) < √((m : ℝ) ^ 2 + 4) :=
      (Real.lt_sqrt (Nat.cast_nonneg m)).mpr (by linarith)
    linarith
  one_le := hm
  carry := by
    have hs : √((m : ℝ) ^ 2 + 4) ^ 2 = (m : ℝ) ^ 2 + 4 := Real.sq_sqrt (by positivity)
    linear_combination (1 / 4 : ℝ) * hs

end Base

end Psc.BetaMetallicUnique
