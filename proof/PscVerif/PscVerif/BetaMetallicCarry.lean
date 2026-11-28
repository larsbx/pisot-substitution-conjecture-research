import PscVerif.BetaFamilyXi

/-!
# The finite-state carry criterion for equal metallic values

For a base `β² = mβ + 1` (`r = β⁻¹`) and two streams `d, e` over `{0, …, m}`,
let `δ_n = d_n - e_n` and define the integer carry `(a_n, b_n)` by
`(a_0, b_0) = (0, 0)` and `(a_{n+1}, b_{n+1}) = (b_n + δ_n, a_n + m b_n)`.
Its value `z_n = a_n + b_n β` satisfies `z_{n+1} = β z_n + δ_n`, and its
conjugate `z'_n = a_n - b_n r` satisfies `z'_{n+1} = -r z'_n + δ_n`.

* `value_eq_iff_bounded`: `value d = value e` iff `|z_n| ≤ 1 + r` for every `n`,
  iff `z_n` is bounded;
* `conj_bound`: always `|z'_n| ≤ m / (1 - r)`;
* `value_eq_iff_states`: `value d = value e` iff every carry lies in the
  finite set `states B` of integer pairs in an explicit box with
  `|a + bβ| ≤ 1 + r` (`states_finite`).

So equality of values is decided by a finite automaton reading `(d_n, e_n)`
with integer transitions. This is the Pisot finite-state normalization
principle (Frougny) specialized to the metallic quadratic family; no novelty is
claimed, and the exact state count per `m` is left to the Quint replay.
Source decision: `docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaMetallicUnique

variable {m : ℕ}

/-- The digit difference. -/
def delta (d e : ℕ → Fin (m + 1)) (n : ℕ) : ℤ := (d n : ℤ) - (e n : ℤ)

/-- The integer carry. -/
def carryPair (d e : ℕ → Fin (m + 1)) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => ((carryPair d e n).2 + delta d e n, (carryPair d e n).1 + m * (carryPair d e n).2)

namespace Base

variable (B : Base m)

/-- The base `β = r⁻¹`. -/
noncomputable def beta : ℝ := B.r⁻¹

theorem beta_sq : B.beta ^ 2 = m * B.beta + 1 := (Psc.BetaFamilyXi.pisot_facts B).2.1

theorem beta_r : B.beta * B.r = 1 := inv_mul_cancel₀ B.r_pos.ne'

theorem one_lt_beta : 1 < B.beta := (Psc.BetaFamilyXi.pisot_facts B).1

/-- The value of a carry pair. -/
noncomputable def zval (p : ℤ × ℤ) : ℝ := p.1 + p.2 * B.beta

/-- Its conjugate under `β ↦ -r`. -/
noncomputable def zconj (p : ℤ × ℤ) : ℝ := p.1 - p.2 * B.r

theorem zval_succ (d e : ℕ → Fin (m + 1)) (n : ℕ) :
    B.zval (carryPair d e (n + 1)) = B.beta * B.zval (carryPair d e n) + delta d e n := by
  simp only [zval, carryPair]
  push_cast
  linear_combination (-((carryPair d e n).2 : ℝ)) * B.beta_sq

theorem zconj_succ (d e : ℕ → Fin (m + 1)) (n : ℕ) :
    B.zconj (carryPair d e (n + 1)) = -B.r * B.zconj (carryPair d e n) + delta d e n := by
  simp only [zconj, carryPair]
  push_cast
  linear_combination (-((carryPair d e n).2 : ℝ)) * B.carry

theorem abs_delta_le (d e : ℕ → Fin (m + 1)) (n : ℕ) : |(delta d e n : ℝ)| ≤ m := by
  unfold delta
  have h1 := digit_le (d n)
  have h2 := digit_le (e n)
  push_cast
  rw [abs_le]
  constructor <;> linarith [(Nat.cast_nonneg (d n : ℕ) : (0 : ℝ) ≤ _),
    (Nat.cast_nonneg (e n : ℕ) : (0 : ℝ) ≤ _)]

/-- The partial sums `Σ_{j<n} d_j r^{j+1}`. -/
noncomputable def psumB (d : ℕ → Fin (m + 1)) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ((d j : ℕ) : ℝ) * B.r ^ (j + 1)

theorem value_split (d : ℕ → Fin (m + 1)) (n : ℕ) :
    B.value d = B.psumB d n + B.r ^ n * B.value (shift d n) := by
  induction n with
  | zero => simp [psumB, shift_zero]
  | succ n ih =>
    have step := B.value_eq_step (shift d n)
    have h0 : shift d n 0 = d n := by simp [shift]
    rw [h0, ← shift_succ] at step
    rw [ih, step]
    unfold psumB
    rw [Finset.sum_range_succ]
    ring

theorem psum_diff (d e : ℕ → Fin (m + 1)) (n : ℕ) :
    B.psumB d n - B.psumB e n = B.r ^ n * B.zval (carryPair d e n) := by
  induction n with
  | zero => simp [psumB, zval, carryPair]
  | succ n ih =>
    unfold psumB at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ, B.zval_succ, pow_succ]
    have hb := B.beta_r
    unfold delta
    push_cast
    linear_combination ih - (B.r ^ n * B.zval (carryPair d e n)) * hb

/-- **Carry criterion.** Equal values iff the carry stays bounded by `1 + r`,
iff it stays bounded at all. -/
theorem value_eq_iff_bounded (d e : ℕ → Fin (m + 1)) :
    (B.value d = B.value e ↔ ∀ n, |B.zval (carryPair d e n)| ≤ 1 + B.r) ∧
      (B.value d = B.value e ↔ ∃ C, ∀ n, |B.zval (carryPair d e n)| ≤ C) := by
  have hr := B.r_pos
  have fwd : B.value d = B.value e → ∀ n, |B.zval (carryPair d e n)| ≤ 1 + B.r := by
    intro h n
    have h1 := B.value_split d n
    have h2 := B.value_split e n
    have h3 := B.psum_diff d e n
    have hz : B.zval (carryPair d e n) = B.value (shift e n) - B.value (shift d n) := by
      have hrn : 0 < B.r ^ n := pow_pos hr n
      have : B.r ^ n * (B.zval (carryPair d e n) - (B.value (shift e n) - B.value (shift d n))) = 0 := by
        linear_combination -h3 - h1 + h2 + h
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hrn.ne')
    rw [hz, abs_le]
    have a1 := B.value_nonneg (shift d n)
    have a2 := B.value_nonneg (shift e n)
    have b1 := B.value_le_top (shift d n)
    have b2 := B.value_le_top (shift e n)
    constructor <;> linarith
  have bwd : (∃ C, ∀ n, |B.zval (carryPair d e n)| ≤ C) → B.value d = B.value e := by
    rintro ⟨C, hC⟩
    have hd := (B.summable_value d).hasSum.tendsto_sum_nat
    have he := (B.summable_value e).hasSum.tendsto_sum_nat
    have hdiff := hd.sub he
    have hzero : Filter.Tendsto (fun n => B.psumB d n - B.psumB e n) Filter.atTop (nhds 0) := by
      simp_rw [B.psum_diff]
      have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le B.r_lt_one
      refine squeeze_zero_norm (fun n => ?_) (by simpa using hpow.mul_const C)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hr n)]
      exact mul_le_mul_of_nonneg_left (hC n) (pow_pos hr n).le
    have := tendsto_nhds_unique hdiff hzero
    exact sub_eq_zero.mp this
  exact ⟨⟨fwd, fun h => bwd ⟨_, h⟩⟩, ⟨fun h => ⟨_, fwd h⟩, bwd⟩⟩

/-- The conjugate carry is always bounded by `m / (1 - r)`. -/
theorem conj_bound (d e : ℕ → Fin (m + 1)) (n : ℕ) :
    |B.zconj (carryPair d e n)| ≤ m / (1 - B.r) := by
  have hr := B.r_pos
  have h1r : 0 < 1 - B.r := sub_pos.mpr B.r_lt_one
  induction n with
  | zero => simp [zconj, carryPair]; positivity
  | succ n ih =>
    rw [B.zconj_succ]
    calc |-B.r * B.zconj (carryPair d e n) + delta d e n|
        ≤ |-B.r * B.zconj (carryPair d e n)| + |(delta d e n : ℝ)| := abs_add_le _ _
      _ = B.r * |B.zconj (carryPair d e n)| + |(delta d e n : ℝ)| := by
          rw [abs_mul, abs_neg, abs_of_pos hr]
      _ ≤ B.r * (m / (1 - B.r)) + m := by
          gcongr
          exact abs_delta_le d e n
      _ = m / (1 - B.r) := by field_simp; ring

/-- The side of the integer box. -/
noncomputable def side : ℕ := ⌈1 + B.r + 2 * (m / (1 - B.r))⌉₊

/-- The finite state set: box pairs with `|a + bβ| ≤ 1 + r`. -/
noncomputable def states : Set (ℤ × ℤ) :=
  {p | p ∈ Finset.Icc (-(B.side : ℤ)) B.side ×ˢ Finset.Icc (-(B.side : ℤ)) B.side ∧
    |B.zval p| ≤ 1 + B.r}

theorem states_finite : B.states.Finite :=
  (Finset.finite_toSet _).subset fun _ hp => hp.1

theorem mem_box (p : ℤ × ℤ) (hz : |B.zval p| ≤ 1 + B.r) (hc : |B.zconj p| ≤ m / (1 - B.r)) :
    p ∈ Finset.Icc (-(B.side : ℤ)) B.side ×ˢ Finset.Icc (-(B.side : ℤ)) B.side := by
  have hr := B.r_pos
  have hβ := B.one_lt_beta
  have hM : 0 ≤ (m : ℝ) / (1 - B.r) := div_nonneg (Nat.cast_nonneg m) (sub_pos.mpr B.r_lt_one).le
  have hK : 1 + B.r + 2 * (m / (1 - B.r)) ≤ (B.side : ℝ) := Nat.le_ceil _
  obtain ⟨z1, z2⟩ := abs_le.mp hz
  obtain ⟨c1, c2⟩ := abs_le.mp hc
  simp only [zval, zconj] at z1 z2 c1 c2
  -- `b (β + r) = z - z'` and `a = z' + b r`.
  have hb : |(p.2 : ℝ)| ≤ 1 + B.r + m / (1 - B.r) := by
    have e : (p.2 : ℝ) * (B.beta + B.r) = (p.1 + p.2 * B.beta) - (p.1 - p.2 * B.r) := by ring
    have hpos : 1 ≤ B.beta + B.r := by linarith
    rw [abs_le]
    constructor <;> nlinarith
  have ha : |(p.1 : ℝ)| ≤ 1 + B.r + 2 * (m / (1 - B.r)) := by
    obtain ⟨b1, b2⟩ := abs_le.mp hb
    rw [abs_le]
    constructor <;> nlinarith [B.r_lt_one]
  obtain ⟨a1, a2⟩ := abs_le.mp ha
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  simp only [Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : -(B.side : ℝ) ≤ p.1 := by linarith
    exact_mod_cast this
  · have : (p.1 : ℝ) ≤ B.side := by linarith
    exact_mod_cast this
  · have : -(B.side : ℝ) ≤ p.2 := by linarith
    exact_mod_cast this
  · have : (p.2 : ℝ) ≤ B.side := by linarith
    exact_mod_cast this

/-- **Finite-state equality criterion.** Equal values iff every carry lies in
the finite set `states B`. -/
theorem value_eq_iff_states (d e : ℕ → Fin (m + 1)) :
    B.value d = B.value e ↔ ∀ n, carryPair d e n ∈ B.states := by
  rw [(B.value_eq_iff_bounded d e).1]
  constructor
  · intro h n
    exact ⟨B.mem_box _ (h n) (B.conj_bound d e n), h n⟩
  · intro h n
    exact (h n).2

/-- Negative control: `1 0 0 …` and `0 m 1 0 …`-type carries. At `m = 1`
the prefixes `100` and `011` leave the carry at `0` after three digits. -/
theorem carry_100_011 (t : ℕ → Fin 2) :
    carryPair (cons 1 (cons 0 (cons 0 t))) (cons 0 (cons 1 (cons 1 t))) 3 = (0, 0) := by
  simp [carryPair, delta]

end Base

end Psc.BetaMetallicUnique
