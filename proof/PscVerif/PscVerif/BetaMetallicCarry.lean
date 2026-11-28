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


/-! ## The seven-state automaton, uniformly in `m` -/

/-- The seven carries `0, ±1, ±r, ±(1 + r)` in coordinates `a + bβ`. -/
def seven (m : ℕ) : Set (ℤ × ℤ) :=
  {((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((-1 : ℤ), (0 : ℤ)), (-(m : ℤ), (1 : ℤ)),
    (1 - (m : ℤ), (1 : ℤ)), ((m : ℤ), (-1 : ℤ)), ((m : ℤ) - 1, (-1 : ℤ))}

theorem beta_eq : B.beta = m + B.r := by
  have := (Psc.BetaFamilyXi.pisot_facts B).2.2.2.2.1
  unfold beta; linarith

theorem delta_bounds (d e : ℕ → Fin (m + 1)) (n : ℕ) :
    -(m : ℤ) ≤ delta d e n ∧ delta d e n ≤ m := by
  unfold delta
  have h1 := Nat.lt_succ_iff.mp (d n).2
  have h2 := Nat.lt_succ_iff.mp (e n).2
  omega

theorem seven_of_b0 (q : ℤ × ℤ) (hb : q.2 = 0) (hz : |B.zval q| ≤ 1 + B.r) : q ∈ seven m := by
  obtain ⟨a, b⟩ := q
  simp only at hb
  subst hb
  simp only [zval, Int.cast_zero, zero_mul, add_zero] at hz
  obtain ⟨h1, h2⟩ := abs_le.mp hz
  have hr := B.r_lt_one
  have u : a < 2 := by have : (a : ℝ) < 2 := by linarith
                       exact_mod_cast this
  have l : -2 < a := by have : (-2 : ℝ) < a := by linarith
                        exact_mod_cast this
  have : a = 0 ∨ a = 1 ∨ a = -1 := by omega
  rcases this with rfl | rfl | rfl <;> simp [seven]

theorem seven_of_b1 (q : ℤ × ℤ) (hb : q.2 = 1) (ha : -(m : ℤ) ≤ q.1)
    (hz : |B.zval q| ≤ 1 + B.r) : q ∈ seven m := by
  obtain ⟨a, b⟩ := q
  simp only at hb ha
  subst hb
  simp only [zval, Int.cast_one, one_mul, B.beta_eq] at hz
  have h2 := (abs_le.mp hz).2
  have u : a ≤ 1 - m := by
    have : (a : ℝ) ≤ 1 - m := by linarith
    exact_mod_cast this
  have : a = -(m : ℤ) ∨ a = 1 - m := by omega
  rcases this with rfl | rfl <;> simp [seven]

theorem seven_of_bm1 (q : ℤ × ℤ) (hb : q.2 = -1) (ha : q.1 ≤ m)
    (hz : |B.zval q| ≤ 1 + B.r) : q ∈ seven m := by
  obtain ⟨a, b⟩ := q
  simp only at hb ha
  subst hb
  simp only [zval, Int.cast_neg, Int.cast_one, neg_mul, one_mul, B.beta_eq] at hz
  have h1 := (abs_le.mp hz).1
  have l : (m : ℤ) - 1 ≤ a := by
    have : (m : ℝ) - 1 ≤ a := by linarith
    exact_mod_cast this
  have : a = (m : ℤ) ∨ a = m - 1 := by omega
  rcases this with rfl | rfl <;> simp [seven]

/-- A bounded transition from one of the seven carries stays among them. -/
theorem seven_step {p : ℤ × ℤ} (hp : p ∈ seven m) {δ : ℤ} (hδ : -(m : ℤ) ≤ δ ∧ δ ≤ m)
    (hz : |B.zval (p.2 + δ, p.1 + m * p.2)| ≤ 1 + B.r) : (p.2 + δ, p.1 + m * p.2) ∈ seven m := by
  simp only [seven, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B.seven_of_b0 _ (by simp) hz
  · exact B.seven_of_b1 _ (by simp) (by simp; omega) hz
  · exact B.seven_of_bm1 _ (by simp) (by simp; omega) hz
  · exact B.seven_of_b0 _ (by simp) hz
  · exact B.seven_of_b1 _ (by simp) (by simp; omega) hz
  · exact B.seven_of_b0 _ (by simp) hz
  · exact B.seven_of_bm1 _ (by simp; ring) (by simp; omega) hz

theorem seven_bound {q : ℤ × ℤ} (hq : q ∈ seven m) : |B.zval q| ≤ 1 + B.r := by
  have hr := B.r_pos
  have hβ := B.beta_eq
  simp only [seven, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [zval, hβ] <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- **Seven-state equality criterion**, uniformly in `m ≥ 1`. Equal values iff
every carry is one of `0, ±1, ±r, ±(1 + r)`. -/
theorem value_eq_iff_seven (d e : ℕ → Fin (m + 1)) :
    B.value d = B.value e ↔ ∀ n, carryPair d e n ∈ seven m := by
  constructor
  · intro h n
    have hb := (B.value_eq_iff_bounded d e).1.mp h
    induction n with
    | zero => simp [carryPair, seven]
    | succ n ih =>
      have := B.seven_step ih (delta_bounds d e n) (hb (n + 1))
      exact this
  · intro h
    exact (B.value_eq_iff_bounded d e).1.mpr fun n => B.seven_bound (h n)


/-! ## All seven states are reached, uniformly in `m` -/

/-- The carry driven by an integer difference sequence. -/
def carryOf (m : ℕ) (δ : ℕ → ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => ((carryOf m δ n).2 + δ n, (carryOf m δ n).1 + m * (carryOf m δ n).2)

omit B in
theorem carryPair_eq (d e : ℕ → Fin (m + 1)) : carryPair d e = carryOf m (delta d e) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp only [carryPair, carryOf, ih]

/-- Realize a bounded difference sequence by two digit streams. -/
def realD (δ : ℕ → ℤ) (h : ∀ n, -(m : ℤ) ≤ δ n ∧ δ n ≤ m) : ℕ → Fin (m + 1) :=
  fun n => ⟨(δ n).toNat, by have := h n; omega⟩

def realE (δ : ℕ → ℤ) (h : ∀ n, -(m : ℤ) ≤ δ n ∧ δ n ≤ m) : ℕ → Fin (m + 1) :=
  fun n => ⟨(-δ n).toNat, by have := h n; omega⟩

omit B in
theorem delta_real (δ : ℕ → ℤ) (h : ∀ n, -(m : ℤ) ≤ δ n ∧ δ n ≤ m) :
    delta (realD δ h) (realE δ h) = δ := by
  funext n
  simp only [delta, realD, realE]
  omega

omit B in
theorem stay (δ : ℕ → ℤ) {k : ℕ} {q : ℤ × ℤ} {c : ℤ} (hq : (q.2 + c, q.1 + m * q.2) = q)
    (hk : carryOf m δ k = q) (hc : ∀ j, k ≤ j → δ j = c) : ∀ i, carryOf m δ (k + i) = q := by
  intro i
  induction i with
  | zero => exact hk
  | succ i ih =>
    rw [← add_assoc]
    simp only [carryOf, ih, hc (k + i) (by omega)]
    exact hq

/-- A difference sequence whose carry stays among the seven states yields two
streams with equal values. -/
theorem equal_of_walk (δ : ℕ → ℤ) (h : ∀ n, -(m : ℤ) ≤ δ n ∧ δ n ≤ m)
    (hw : ∀ n, carryOf m δ n ∈ seven m) :
    B.value (realD δ h) = B.value (realE δ h) := by
  rw [B.value_eq_iff_seven, carryPair_eq, delta_real]
  exact hw

omit B in
theorem walk_mem (δ : ℕ → ℤ) (k : ℕ) (hlow : ∀ n ≤ k, carryOf m δ n ∈ seven m)
    {q : ℤ × ℤ} {c : ℤ} (hq : (q.2 + c, q.1 + m * q.2) = q) (hqs : q ∈ seven m)
    (hk : carryOf m δ k = q) (hc : ∀ j, k ≤ j → δ j = c) : ∀ n, carryOf m δ n ∈ seven m := by
  intro n
  by_cases hn : n ≤ k
  · exact hlow n hn
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ n by omega)
    rw [stay δ hq hk hc i]; exact hqs

/-- **Every one of the seven carries occurs** for a pair of streams with equal
values, for every `m ≥ 1`. -/
theorem seven_reachable (hm : 1 ≤ m) {q : ℤ × ℤ} (hq : q ∈ seven m) :
    ∃ d e : ℕ → Fin (m + 1), B.value d = B.value e ∧ ∃ n, carryPair d e n = q := by
  -- Four explicit walks, each eventually constant at an absorbing state.
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  let w1 : ℕ → ℤ := fun n => if n = 0 then 1 else if n = 1 then -m else if n = 2 then -1 else 0
  let w2 : ℕ → ℤ := fun n => if n = 0 then 1 else if n = 1 then 1 - m else -m
  let w3 : ℕ → ℤ := fun n => -w1 n
  let w4 : ℕ → ℤ := fun n => -w2 n
  have b1 : ∀ n, -(m : ℤ) ≤ w1 n ∧ w1 n ≤ m := fun n => by
    simp only [w1]; split_ifs <;> omega
  have b2 : ∀ n, -(m : ℤ) ≤ w2 n ∧ w2 n ≤ m := fun n => by
    simp only [w2]; split_ifs <;> omega
  have b3 : ∀ n, -(m : ℤ) ≤ w3 n ∧ w3 n ≤ m := fun n => by
    have := b1 n; simp only [w3]; omega
  have b4 : ∀ n, -(m : ℤ) ≤ w4 n ∧ w4 n ≤ m := fun n => by
    have := b2 n; simp only [w4]; omega
  have c1 : carryOf m w1 1 = (1, 0) ∧ carryOf m w1 2 = (-(m : ℤ), 1) ∧ carryOf m w1 3 = (0, 0) := by
    simp [carryOf, w1]
  have c2 : carryOf m w2 1 = (1, 0) ∧ carryOf m w2 2 = (1 - (m : ℤ), 1) := by
    simp [carryOf, w2]
  have c3 : carryOf m w3 1 = (-1, 0) ∧ carryOf m w3 2 = ((m : ℤ), -1) ∧ carryOf m w3 3 = (0, 0) := by
    simp [carryOf, w3, w1]
  have c4 : carryOf m w4 1 = (-1, 0) ∧ carryOf m w4 2 = ((m : ℤ) - 1, -1) := by
    simp [carryOf, w4, w2]
  have s7 : ∀ q, q ∈ seven m ↔ q = (0, 0) ∨ q = (1, 0) ∨ q = (-1, 0) ∨ q = (-(m : ℤ), 1) ∨
      q = (1 - (m : ℤ), 1) ∨ q = ((m : ℤ), -1) ∨ q = ((m : ℤ) - 1, -1) := fun q => by
    simp [seven]
  have m1 : ∀ n, carryOf m w1 n ∈ seven m := by
    refine walk_mem w1 3 (fun n hn => ?_) (q := (0, 0)) (c := 0) (by simp) ((s7 _).2 (Or.inl rfl))
      c1.2.2 (fun j hj => by simp only [w1]; split_ifs <;> omega)
    interval_cases n
    · exact (s7 _).2 (Or.inl rfl)
    · rw [c1.1]; exact (s7 _).2 (Or.inr (Or.inl rfl))
    · rw [c1.2.1]; exact (s7 _).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rw [c1.2.2]; exact (s7 _).2 (Or.inl rfl)
  have m2 : ∀ n, carryOf m w2 n ∈ seven m := by
    refine walk_mem w2 2 (fun n hn => ?_) (q := (1 - (m : ℤ), 1)) (c := -m) (by ext <;> simp <;> ring)
      ((s7 _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) c2.2
      (fun j hj => by simp only [w2]; split_ifs <;> omega)
    interval_cases n
    · exact (s7 _).2 (Or.inl rfl)
    · rw [c2.1]; exact (s7 _).2 (Or.inr (Or.inl rfl))
    · rw [c2.2]; exact (s7 _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have m3 : ∀ n, carryOf m w3 n ∈ seven m := by
    refine walk_mem w3 3 (fun n hn => ?_) (q := (0, 0)) (c := 0) (by simp) ((s7 _).2 (Or.inl rfl))
      c3.2.2 (fun j hj => by simp only [w3, w1]; split_ifs <;> omega)
    interval_cases n
    · exact (s7 _).2 (Or.inl rfl)
    · rw [c3.1]; exact (s7 _).2 (Or.inr (Or.inr (Or.inl rfl)))
    · rw [c3.2.1]; exact (s7 _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · rw [c3.2.2]; exact (s7 _).2 (Or.inl rfl)
  have m4 : ∀ n, carryOf m w4 n ∈ seven m := by
    refine walk_mem w4 2 (fun n hn => ?_) (q := ((m : ℤ) - 1, -1)) (c := m) (by ext <;> simp <;> ring)
      ((s7 _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) c4.2
      (fun j hj => by simp only [w4, w2]; split_ifs <;> omega)
    interval_cases n
    · exact (s7 _).2 (Or.inl rfl)
    · rw [c4.1]; exact (s7 _).2 (Or.inr (Or.inr (Or.inl rfl)))
    · rw [c4.2]; exact (s7 _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have use : ∀ (δ : ℕ → ℤ) (h : ∀ n, -(m : ℤ) ≤ δ n ∧ δ n ≤ m), (∀ n, carryOf m δ n ∈ seven m) →
      ∀ k, carryOf m δ k = q →
        ∃ d e : ℕ → Fin (m + 1), B.value d = B.value e ∧ ∃ n, carryPair d e n = q :=
    fun δ h hw k hk => ⟨realD δ h, realE δ h, B.equal_of_walk δ h hw,
      k, by rw [carryPair_eq, delta_real]; exact hk⟩
  rcases (s7 q).1 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact use w1 b1 m1 0 rfl
  · exact use w1 b1 m1 1 c1.1
  · exact use w3 b3 m3 1 c3.1
  · exact use w1 b1 m1 2 c1.2.1
  · exact use w2 b2 m2 2 c2.2
  · exact use w3 b3 m3 2 c3.2.1
  · exact use w4 b4 m4 2 c4.2

/-- Negative control: `1 0 0 …` and `0 m 1 0 …`-type carries. At `m = 1`
the prefixes `100` and `011` leave the carry at `0` after three digits. -/
theorem carry_100_011 (t : ℕ → Fin 2) :
    carryPair (cons 1 (cons 0 (cons 0 t))) (cons 0 (cons 1 (cons 1 t))) 3 = (0, 0) := by
  simp [carryPair, delta]

end Base

end Psc.BetaMetallicUnique
