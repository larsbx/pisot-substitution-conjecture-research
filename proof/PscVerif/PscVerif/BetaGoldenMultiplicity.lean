import PscVerif.BetaGoldenCoding
import PscVerif.BetaMetallicNormalForm

/-!
# Multiplicity of golden-base expansions

For `x ∈ (0, φ)` and digits `{0, 1}`, let `E(x)` be the set of all streams `d`
with `Σ_{n ≥ 1} d_n φ^{-n} = x`. Proved here:

* `expansions_countable`, `expansions_infinite`: if `x ∈ ℤ[φ]`, then `E(x)` is
  countably infinite;
* `expansions_not_countable`: if `x ∉ ℤ[φ]`, then `E(x)` is uncountable.

With `isUnique_iff` of the golden endpoint module (`E(0)`, `E(φ)` singletons)
this is the classical Sidorov–Vershik classification, extended from `(0, 1)` to
`(0, φ)`. It is formalized here as a specialization; no novelty is claimed.

Countable case. Along an expansion the remainders `y_n` satisfy
`y_{n+1} = φ y_n - d_n` and stay in `[0, φ]`. For `x = a + bφ` they stay in
`ℤ[φ]`, with integer coordinates following `(a, b) ↦ (b - d, a + b)`; the
conjugates contract by `|1 - φ| = φ⁻¹`. So the coordinates stay in a finite box
and some state repeats. A repeated state has conjugate at most `φ²`, and the
only such states in `[0, φ]` are `0, φ⁻¹, 1, φ, 2 - φ`; the last never returns.
The set `{0, φ⁻¹, 1, φ}` is closed, and on it the remainders, hence the digits,
are eventually `2`-periodic. Eventually periodic streams form a countable set.

Infinite case. Some expansion reaches `φ⁻¹` or `1`, because `0` and `φ` are
entered only from `{0, φ⁻¹}` and `{1, φ}`. From there `(01)^j 1 0^∞` gives
infinitely many continuations.

Uncountable case. A run chooses a digit by a bit stream whenever its remainder
lies in `[φ⁻¹, 1]` and is otherwise forced. For `x ∉ ℤ[φ]` remainders never lie
in `ℤ[φ]`, the run enters `(φ⁻¹, 1)` infinitely often, and distinct bit streams
give distinct expansions.

Source decision: `docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaGoldenMultiplicity

open scoped goldenRatio
open Psc.BetaGoldenEndpoint
open Psc.BetaGoldenCoding (gshift psum value_split)


/-- All `{0,1}` expansions of `x` in base `φ`. -/
def expansions (x : ℝ) : Set (ℕ → Bool) := {d | value d = x}


/-! ## Constants -/

/-- `φ` as an opaque constant, so that `ring`, `linarith` and `interval_cases`
treat it as an atom; Mathlib's `φ` is an abbreviation for `(1 + √5)/2`. -/
noncomputable def ph : ℝ := φ

theorem ph_pos : 0 < ph := Real.goldenRatio_pos

theorem one_lt_ph : 1 < ph := Real.one_lt_goldenRatio

theorem phi_sq : ph ^ 2 = ph + 1 := Real.goldenRatio_sq

theorem phi_r : ph * r = 1 := mul_inv_cancel₀ Real.goldenRatio_pos.ne'

/-- Membership in `ℤ[φ]`. -/
def InZ (x : ℝ) : Prop := ∃ a b : ℤ, x = a + b * ph

theorem r_eq : r = ph - 1 := by
  have h1 := phi_r
  have h := phi_sq
  have : ph * (ph - 1) = 1 := by nlinarith
  exact mul_left_cancel₀ ph_pos.ne' (h1.trans this.symm)

theorem phi_bounds : 1.6 < ph ∧ ph < 1.62 := by
  have h := phi_sq
  have hp := ph_pos
  constructor <;> nlinarith

theorem digit_eq (b : Bool) : digit b = (b.toNat : ℝ) := by cases b <;> simp

/-! ## Remainders of an expansion -/

/-- The remainder after `n` digits. -/
noncomputable def st (d : ℕ → Bool) (n : ℕ) : ℝ := value (gshift d n)

theorem tail_gshift (d : ℕ → Bool) (n : ℕ) : tail (gshift d n) = gshift d (n + 1) := by
  funext i; simp only [tail_apply, gshift]; congr 1; omega

theorem st_zero (d : ℕ → Bool) : st d 0 = value d := by
  unfold st; congr 1; funext i; simp [gshift]

theorem st_succ (d : ℕ → Bool) (n : ℕ) : st d (n + 1) = ph * st d n - digit (d n) := by
  have step := value_eq_step (gshift d n)
  have h0 : gshift d n 0 = d n := by simp [gshift]
  rw [h0, tail_gshift] at step
  unfold st
  rw [step]
  linear_combination (-(digit (d n)) - value (gshift d (n + 1))) * phi_r

theorem st_mem (d : ℕ → Bool) (n : ℕ) : 0 ≤ st d n ∧ st d n ≤ ph :=
  ⟨value_nonneg _, value_le _⟩

/-! ## The closed set `{0, φ⁻¹, 1, φ}` -/

/-- The four states lying on cycles. -/
def IsT (y : ℝ) : Prop := y = 0 ∨ y = r ∨ y = 1 ∨ y = ph

/-- From `0` the next remainder is `0`, with digit `0`. -/
theorem next_of_zero (d : ℕ → Bool) {n : ℕ} (h : st d n = 0) :
    d n = false ∧ st d (n + 1) = 0 := by
  have hs := st_succ d n
  have hm := (st_mem d (n + 1)).1
  rw [h, mul_zero, zero_sub] at hs
  cases hd : d n
  · simp [hd] at hs; exact ⟨rfl, hs⟩
  · rw [hd, digit_true] at hs; linarith

/-- From `φ` the next remainder is `φ`, with digit `1`. -/
theorem next_of_phi (d : ℕ → Bool) {n : ℕ} (h : st d n = ph) :
    d n = true ∧ st d (n + 1) = ph := by
  have hs := st_succ d n
  have hm := (st_mem d (n + 1)).2
  rw [h] at hs
  have hsq := phi_sq
  cases hd : d n
  · rw [hd, digit_false] at hs; nlinarith [ph_pos]
  · rw [hd, digit_true] at hs; exact ⟨rfl, by nlinarith⟩

theorem next_of_r (d : ℕ → Bool) {n : ℕ} (h : st d n = r) :
    (d n = false ∧ st d (n + 1) = 1) ∨ (d n = true ∧ st d (n + 1) = 0) := by
  have hs := st_succ d n
  rw [h, phi_r] at hs
  cases hd : d n
  · left; rw [hd, digit_false] at hs; exact ⟨rfl, by linarith⟩
  · right; rw [hd, digit_true] at hs; exact ⟨rfl, by linarith⟩

theorem next_of_one (d : ℕ → Bool) {n : ℕ} (h : st d n = 1) :
    (d n = false ∧ st d (n + 1) = ph) ∨ (d n = true ∧ st d (n + 1) = r) := by
  have hs := st_succ d n
  rw [h, mul_one] at hs
  cases hd : d n
  · left; rw [hd, digit_false] at hs; exact ⟨rfl, by linarith⟩
  · right; rw [hd, digit_true] at hs; exact ⟨rfl, by rw [r_eq]; linarith⟩

theorem isT_succ (d : ℕ → Bool) {n : ℕ} (h : IsT (st d n)) : IsT (st d (n + 1)) := by
  rcases h with h | h | h | h
  · exact Or.inl (next_of_zero d h).2
  · rcases next_of_r d h with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inl h'
  · rcases next_of_one d h with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact Or.inr (Or.inr (Or.inr h'))
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (Or.inr (next_of_phi d h).2))

theorem isT_add (d : ℕ → Bool) {n : ℕ} (h : IsT (st d n)) : ∀ j, IsT (st d (n + j)) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih => exact isT_succ d ih

/-- On the closed set the digits are eventually `2`-periodic. -/
theorem eventually_two_periodic (d : ℕ → Bool) {n : ℕ} (h : IsT (st d n)) :
    ∃ N, ∀ j, N ≤ j → d (j + 2) = d j := by
  have hT := isT_add d h
  by_cases h0 : ∃ j, n ≤ j ∧ st d j = 0
  · obtain ⟨j, -, hj⟩ := h0
    have hz : ∀ i, st d (j + i) = 0 := by
      intro i
      induction i with
      | zero => simpa using hj
      | succ i ih => exact (next_of_zero d ih).2
    refine ⟨j, fun i hi => ?_⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [(next_of_zero d (hz t)).1, show j + t + 2 = j + (t + 2) by ring,
      (next_of_zero d (hz (t + 2))).1]
  by_cases hph : ∃ j, n ≤ j ∧ st d j = ph
  · obtain ⟨j, -, hj⟩ := hph
    have hz : ∀ i, st d (j + i) = ph := by
      intro i
      induction i with
      | zero => simpa using hj
      | succ i ih => exact (next_of_phi d ih).2
    refine ⟨j, fun i hi => ?_⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [(next_of_phi d (hz t)).1, show j + t + 2 = j + (t + 2) by ring,
      (next_of_phi d (hz (t + 2))).1]
  simp only [not_exists, not_and] at h0 hph
  -- Every later remainder is `φ⁻¹` or `1`, and they alternate.
  have hmid : ∀ j, n ≤ j → st d j = r ∨ st d j = 1 := by
    intro j hj
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
    rcases hT t with h | h | h | h
    · exact absurd h (h0 _ (by omega))
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hph _ (by omega))
  have hstep : ∀ j, n ≤ j → (st d j = r → d j = false ∧ st d (j + 1) = 1) ∧
      (st d j = 1 → d j = true ∧ st d (j + 1) = r) := by
    intro j hj
    constructor
    · intro h
      rcases next_of_r d h with h' | ⟨-, h'⟩
      · exact h'
      · exact absurd h' (h0 _ (by omega))
    · intro h
      rcases next_of_one d h with ⟨-, h'⟩ | h'
      · exact absurd h' (hph _ (by omega))
      · exact h'
  refine ⟨n, fun j hj => ?_⟩
  rcases hmid j hj with h | h
  · have a := (hstep j hj).1 h
    have b := (hstep (j + 1) (by omega)).2 a.2
    rw [a.1, ((hstep (j + 2) (by omega)).1 b.2).1]
  · have a := (hstep j hj).2 h
    have b := (hstep (j + 1) (by omega)).1 a.2
    rw [a.1, ((hstep (j + 2) (by omega)).2 b.2).1]

/-- Eventually `2`-periodic streams form a countable set. -/
theorem countable_eventually_two_periodic :
    {d : ℕ → Bool | ∃ N, ∀ j, N ≤ j → d (j + 2) = d j}.Countable := by
  let F : ℕ × List Bool → (ℕ → Bool) := fun p i =>
    p.2.getD (if i < p.1 + 2 then i else p.1 + (i - p.1) % 2) false
  refine (Set.countable_range F).mono ?_
  rintro d ⟨N, hN⟩
  refine ⟨(N, List.ofFn fun i : Fin (N + 2) => d i), funext fun i => ?_⟩
  have key : ∀ i, N ≤ i → d i = d (N + (i - N) % 2) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h2 : i < N + 2
      · have : (i - N) % 2 = i - N := Nat.mod_eq_of_lt (by omega)
        rw [this]; congr 1; omega
      · have e := hN (i - 2) (by omega)
        rw [show i - 2 + 2 = i by omega] at e
        rw [e, ih (i - 2) (by omega) (by omega)]
        congr 2
        omega
  simp only [F]
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_cond_eq_true (eq_true h)]
    rfl
  · rename_i h
    have hlt : N + (i - N) % 2 < N + 2 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true,
      Option.getD_some]
    exact (key i (by omega)).symm

/-! ## Coordinates in `ℤ[φ]` and the conjugate -/

/-- Integer coordinates of the remainders, from `x = a₀ + b₀ φ`. -/
def pr (d : ℕ → Bool) (a₀ b₀ : ℤ) : ℕ → ℤ × ℤ
  | 0 => (a₀, b₀)
  | n + 1 => ((pr d a₀ b₀ n).2 - (d n).toNat, (pr d a₀ b₀ n).1 + (pr d a₀ b₀ n).2)

/-- The real number with coordinates `p`. -/
noncomputable def ev (p : ℤ × ℤ) : ℝ := p.1 + p.2 * ph

/-- Its conjugate, under `φ ↦ 1 - φ`. -/
noncomputable def cj (p : ℤ × ℤ) : ℝ := p.1 + p.2 * (1 - ph)

theorem st_eq_ev (d : ℕ → Bool) {a₀ b₀ : ℤ} (hx : value d = a₀ + b₀ * ph) (n : ℕ) :
    st d n = ev (pr d a₀ b₀ n) := by
  induction n with
  | zero => rw [st_zero, hx]; rfl
  | succ n ih =>
    rw [st_succ, ih, digit_eq]
    simp only [ev, pr]
    push_cast
    linear_combination ((pr d a₀ b₀ n).2 : ℝ) * phi_sq

theorem cj_succ (d : ℕ → Bool) (a₀ b₀ : ℤ) (n : ℕ) :
    cj (pr d a₀ b₀ (n + 1)) = (1 - ph) * cj (pr d a₀ b₀ n) - digit (d n) := by
  rw [digit_eq]
  simp only [cj, pr]
  push_cast
  linear_combination (-((pr d a₀ b₀ n).2 : ℝ)) * phi_sq

theorem abs_conj : |1 - ph| = r := by
  rw [r_eq, abs_sub_comm, abs_of_pos (by linarith [one_lt_ph])]

theorem cj_step (d : ℕ → Bool) (a₀ b₀ : ℤ) (n : ℕ) :
    |cj (pr d a₀ b₀ (n + 1))| ≤ r * |cj (pr d a₀ b₀ n)| + 1 := by
  rw [cj_succ]
  calc |(1 - ph) * cj (pr d a₀ b₀ n) - digit (d n)|
      ≤ |(1 - ph) * cj (pr d a₀ b₀ n)| + |digit (d n)| := abs_sub _ _
    _ = r * |cj (pr d a₀ b₀ n)| + |digit (d n)| := by rw [abs_mul, abs_conj]
    _ ≤ r * |cj (pr d a₀ b₀ n)| + 1 := by
        gcongr; cases d n <;> simp

theorem cj_iter (d : ℕ → Bool) (a₀ b₀ : ℤ) (m k : ℕ) :
    |cj (pr d a₀ b₀ (m + k))| ≤ r ^ k * |cj (pr d a₀ b₀ m)| + ph ^ 2 * (1 - r ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := cj_step d a₀ b₀ (m + k)
    have hr := r_pos
    have key : ph ^ 2 * r + 1 = ph ^ 2 := by
      have := phi_r; nlinarith [phi_sq]
    calc |cj (pr d a₀ b₀ (m + (k + 1)))|
        ≤ r * |cj (pr d a₀ b₀ (m + k))| + 1 := by rw [← add_assoc]; exact hs
      _ ≤ r * (r ^ k * |cj (pr d a₀ b₀ m)| + ph ^ 2 * (1 - r ^ k)) + 1 := by gcongr
      _ = r ^ (k + 1) * |cj (pr d a₀ b₀ m)| + ph ^ 2 * (1 - r ^ (k + 1)) := by
        rw [pow_succ]; linear_combination key

/-! ## The five candidate cycle states -/

theorem five (a b : ℤ) (hy0 : 0 ≤ (a : ℝ) + b * ph) (hy1 : (a : ℝ) + b * ph ≤ ph)
    (hz : |(a : ℝ) + b * (1 - ph)| ≤ ph ^ 2) :
    (a : ℝ) + b * ph = 0 ∨ (a : ℝ) + b * ph = r ∨ (a : ℝ) + b * ph = 1 ∨
      (a : ℝ) + b * ph = ph ∨ (a : ℝ) + b * ph = 2 - ph := by
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨p1, p2⟩ := phi_bounds
  have hsq := phi_sq
  have hb2 : (b : ℝ) < 2 := by
    by_contra h; push Not at h; nlinarith
  have hb2' : -2 < (b : ℝ) := by
    by_contra h; push Not at h; nlinarith
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    have e1 : (-2 : ℤ) < b := by exact_mod_cast hb2'
    have e2 : b < (2 : ℤ) := by exact_mod_cast hb2
    omega
  have ha3 : (a : ℝ) < 3 := by nlinarith
  have ha2 : -2 < (a : ℝ) := by nlinarith
  have ha : -1 ≤ a ∧ a ≤ 2 := by
    have e1 : (-2 : ℤ) < a := by exact_mod_cast ha2
    have e2 : a < (3 : ℤ) := by exact_mod_cast ha3
    omega
  obtain ⟨ha1, ha2'⟩ := ha
  obtain ⟨hb1, hb1'⟩ := hb
  rw [r_eq]
  interval_cases a <;> interval_cases b <;> push_cast at hy0 hy1 hz1 hz2 ⊢ <;>
    first
    | (left; ring1)
    | (right; left; ring1)
    | (right; right; left; ring1)
    | (right; right; right; left; ring1)
    | (right; right; right; right; ring1)
    | (exfalso; linarith)

/-! ## Countability for `x ∈ ℤ[φ]` -/

section Countable

variable {d : ℕ → Bool} {a₀ b₀ : ℤ}

/-- A repeated coordinate pair lies on the closed set. -/
theorem isT_of_cycle (hx : value d = a₀ + b₀ * ph) {n p : ℕ} (hp : 1 ≤ p)
    (h : pr d a₀ b₀ (n + p) = pr d a₀ b₀ n) : IsT (st d n) := by
  set z := cj (pr d a₀ b₀ n)
  have hit := cj_iter d a₀ b₀ n p
  rw [h] at hit
  have hrp : r ^ p < 1 := pow_lt_one₀ r_pos.le r_lt_one (by omega)
  have hz : |z| ≤ ph ^ 2 := by nlinarith [abs_nonneg z]
  have hev := st_eq_ev d hx n
  obtain ⟨h0, h1⟩ := st_mem d n
  rw [hev] at h0 h1
  rcases five _ _ h0 h1 hz with e | e | e | e | e
  · exact Or.inl (hev.trans e)
  · exact Or.inr (Or.inl (hev.trans e))
  · exact Or.inr (Or.inr (Or.inl (hev.trans e)))
  · exact Or.inr (Or.inr (Or.inr (hev.trans e)))
  · -- `2 - φ` moves to `φ⁻¹`, from which it is never reached again.
    exfalso
    have hev' : st d n = 2 - ph := hev.trans e
    have hs := st_succ d n
    have hm := (st_mem d (n + 1)).1
    rw [hev'] at hs
    have hsq := phi_sq
    obtain ⟨q1, q2⟩ := phi_bounds
    have hnext : st d (n + 1) = r := by
      cases hd : d n
      · rw [hd, digit_false] at hs; rw [hs, r_eq]; linear_combination (-1 : ℝ) * hsq
      · rw [hd, digit_true] at hs; nlinarith
    have hT := isT_add d (n := n + 1) (Or.inr (Or.inl hnext)) (p - 1)
    have hsame : st d (n + p) = st d n := by rw [st_eq_ev d hx, st_eq_ev d hx n, h]
    rw [show n + 1 + (p - 1) = n + p by omega, hsame, hev'] at hT
    unfold IsT at hT
    rw [r_eq] at hT
    rcases hT with h | h | h | h <;> linarith

theorem exists_isT (hx : value d = a₀ + b₀ * ph) : ∃ n, IsT (st d n) := by
  set B := |cj (pr d a₀ b₀ 0)| + ph ^ 2
  have hB : ∀ n, |cj (pr d a₀ b₀ n)| ≤ B := fun n => by
    have := cj_iter d a₀ b₀ 0 n
    rw [zero_add] at this
    have h1 : r ^ n ≤ 1 := pow_le_one₀ r_pos.le r_lt_one.le
    have h2 : 0 ≤ r ^ n := pow_nonneg r_pos.le n
    have h3 : 0 ≤ ph ^ 2 := sq_nonneg _
    nlinarith [abs_nonneg (cj (pr d a₀ b₀ 0))]
  set K : ℕ := ⌈ph + B⌉₊
  have hbox : ∀ n, pr d a₀ b₀ n ∈ (Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K) := by
    intro n
    obtain ⟨y0, y1⟩ := st_mem d n
    rw [st_eq_ev d hx] at y0 y1
    obtain ⟨z1, z2⟩ := abs_le.mp (hB n)
    have hK : ph + B ≤ (K : ℝ) := Nat.le_ceil _
    obtain ⟨p1, p2⟩ := phi_bounds
    simp only [ev, cj] at y0 y1 z1 z2
    set a := (pr d a₀ b₀ n).1
    set b := (pr d a₀ b₀ n).2
    have hb1 : (b : ℝ) ≤ K := by nlinarith
    have hb2 : -(K : ℝ) ≤ b := by nlinarith
    have ha1 : (a : ℝ) ≤ K := by nlinarith
    have ha2 : -(K : ℝ) ≤ a := by nlinarith
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by exact_mod_cast ha2, by exact_mod_cast ha1⟩,
      ⟨by exact_mod_cast hb2, by exact_mod_cast hb1⟩⟩
  let S := (Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K)
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n => (⟨pr d a₀ b₀ n, hbox n⟩ : S))
  have heq' : pr d a₀ b₀ n₁ = pr d a₀ b₀ n₂ := congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨n₁, isT_of_cycle hx (p := n₂ - n₁) (by omega)
      (by rw [show n₁ + (n₂ - n₁) = n₂ by omega]; exact heq'.symm)⟩
  · exact ⟨n₂, isT_of_cycle hx (p := n₁ - n₂) (by omega)
      (by rw [show n₂ + (n₁ - n₂) = n₁ by omega]; exact heq')⟩

end Countable

/-- **Countable case.** Every value in `ℤ[φ]` has countably many expansions. -/
theorem expansions_countable {x : ℝ} (hx : InZ x) : (expansions x).Countable := by
  obtain ⟨a₀, b₀, rfl⟩ := hx
  refine countable_eventually_two_periodic.mono fun d hd => ?_
  obtain ⟨n, hn⟩ := exists_isT (d := d) hd
  exact eventually_two_periodic d hn

/-! ## A run with chosen digits -/

/-- The digit chosen at a remainder `y`: forced off `[φ⁻¹, 1]`, `bit` on it. -/
noncomputable def rule (y : ℝ) (bit : Bool) : Bool := if y < r then false else if 1 < y then true
  else bit

/-- Remainder and number of choices made so far. -/
noncomputable def run (x : ℝ) (b : ℕ → Bool) : ℕ → ℝ × ℕ
  | 0 => (x, 0)
  | n + 1 =>
    ((ph * (run x b n).1 - digit (rule (run x b n).1 (b (run x b n).2))),
      if r ≤ (run x b n).1 ∧ (run x b n).1 ≤ 1 then (run x b n).2 + 1 else (run x b n).2)

/-- The digit stream of a run. -/
noncomputable def runD (x : ℝ) (b : ℕ → Bool) (n : ℕ) : Bool :=
  rule (run x b n).1 (b (run x b n).2)

theorem run_snd_succ (x : ℝ) (b : ℕ → Bool) (n : ℕ) :
    (run x b (n + 1)).2 = if r ≤ (run x b n).1 ∧ (run x b n).1 ≤ 1 then (run x b n).2 + 1
      else (run x b n).2 := rfl

theorem run_succ_fst (x : ℝ) (b : ℕ → Bool) (n : ℕ) :
    (run x b (n + 1)).1 = ph * (run x b n).1 - digit (runD x b n) := rfl

theorem run_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ ph) (b : ℕ → Bool) :
    ∀ n, 0 ≤ (run x b n).1 ∧ (run x b n).1 ≤ ph := by
  intro n
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ n ih =>
    rw [run_succ_fst]
    obtain ⟨y0, y1⟩ := ih
    set y := (run x b n).1
    have hsq := phi_sq
    have hre := r_eq
    have hp := ph_pos
    unfold runD rule
    split
    · rename_i h; simp only [digit_false, sub_zero]
      constructor
      · positivity
      · nlinarith [r_lt_one]
    · split
      · rename_i h h'; simp only [digit_true]
        constructor <;> nlinarith
      · rename_i h h'
        push Not at h h'
        cases b (run x b n).2
        · simp only [digit_false, sub_zero]; constructor <;> nlinarith
        · simp only [digit_true]; constructor <;> nlinarith

theorem run_value {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ ph) (b : ℕ → Bool) :
    value (runD x b) = x := by
  have hsplit : ∀ n, x = psum (runD x b) n + r ^ n * (run x b n).1 := by
    intro n
    induction n with
    | zero => simp [psum, run]
    | succ n ih =>
      have hps : psum (runD x b) (n + 1) =
          psum (runD x b) n + digit (runD x b n) * r ^ (n + 1) := Finset.sum_range_succ _ _
      rw [hps, run_succ_fst, pow_succ]
      linear_combination ih - (r ^ n * (run x b n).1) * phi_r
  have hlim : Filter.Tendsto (fun n => psum (runD x b) n) Filter.atTop (nhds x) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one r_pos.le r_lt_one
    have : Filter.Tendsto (fun n => x - r ^ n * (run x b n).1) Filter.atTop (nhds x) := by
      have hb : Filter.Tendsto (fun n => r ^ n * (run x b n).1) Filter.atTop (nhds 0) := by
        refine squeeze_zero (fun n => mul_nonneg (pow_nonneg r_pos.le n)
          (run_mem h0 h1 b n).1) (fun n => mul_le_mul_of_nonneg_left
          (run_mem h0 h1 b n).2 (pow_nonneg r_pos.le n) |>.trans (le_of_eq (mul_comm _ _)))
          (by simpa using hpow.const_mul ph)
      simpa using tendsto_const_nhds.sub hb
    refine this.congr fun n => ?_
    have := hsplit n
    linarith
  exact tendsto_nhds_unique (summable_value (runD x b)).hasSum.tendsto_sum_nat hlim

/-! ## Uncountability for `x ∉ ℤ[φ]` -/

theorem inZ_of_succ {y y' : ℝ} (b : Bool) (h : y' = ph * y - digit b) (hz : InZ y') : InZ y := by
  obtain ⟨a, c, rfl⟩ := hz
  have hy : y = r * (a + c * ph + digit b) := by
    linear_combination (-r) * h - y * phi_r
  rw [hy, r_eq, digit_eq]
  refine ⟨c - (a + (b.toNat : ℤ)), a + (b.toNat : ℤ), ?_⟩
  push_cast
  linear_combination (c : ℝ) * phi_sq

theorem isT_inZ {y : ℝ} (h : IsT y) : InZ y := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by simp⟩
  · exact ⟨-1, 1, by rw [r_eq]; push_cast; ring⟩
  · exact ⟨1, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩

section Uncountable

variable {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ ph) (hx : ¬ InZ x)
include h0 h1 hx

omit h0 h1 in
theorem run_not_inZ (b : ℕ → Bool) : ∀ n, ¬ InZ (run x b n).1 := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih => exact fun hz => ih (inZ_of_succ _ (run_succ_fst x b n) hz)

/-- The run enters `(φ⁻¹, 1)` after every time. -/
theorem run_branches (b : ℕ → Bool) (n : ℕ) :
    ∃ m, n ≤ m ∧ r < (run x b m).1 ∧ (run x b m).1 < 1 := by
  by_contra hno
  push Not at hno
  have hnz := run_not_inZ hx b
  have hmem := run_mem h0 h1 b
  have hne : ∀ m, (run x b m).1 ≠ r ∧ (run x b m).1 ≠ 1 ∧ (run x b m).1 ≠ 0 ∧
      (run x b m).1 ≠ ph := fun m => by
    refine ⟨fun e => hnz m ?_, fun e => hnz m ?_, fun e => hnz m ?_, fun e => hnz m ?_⟩ <;>
      rw [e]
    · exact isT_inZ (Or.inr (Or.inl rfl))
    · exact isT_inZ (Or.inr (Or.inr (Or.inl rfl)))
    · exact isT_inZ (Or.inl rfl)
    · exact isT_inZ (Or.inr (Or.inr (Or.inr rfl)))
  have hsq := phi_sq
  have hre := r_eq
  have hp1 := one_lt_ph
  set y := (run x b n).1
  by_cases hlow : y < r
  · -- Below `φ⁻¹` the digit is `0` and the remainder grows by `φ`.
    have key : ∀ j, (run x b (n + j)).1 = ph ^ j * y ∧ (run x b (n + j)).1 < r := by
      intro j
      induction j with
      | zero => simp [y, hlow]
      | succ j ih =>
        have hs := run_succ_fst x b (n + j)
        have hd : runD x b (n + j) = false := by
          unfold runD rule; rw [if_pos ih.2]
        rw [hd, digit_false, sub_zero, ih.1] at hs
        rw [← add_assoc, hs]
        refine ⟨by ring, ?_⟩
        have hlt1 : ph * (ph ^ j * y) < 1 := by
          rw [← ih.1]; nlinarith [phi_r, r_pos]
        have hnb := hno (n + (j + 1)) (by omega)
        rw [← add_assoc, hs] at hnb
        have hneq := (hne (n + j + 1)).1
        rw [hs] at hneq
        rcases lt_or_gt_of_ne hneq with h | h
        · exact h
        · exact absurd (hnb h) (not_le.mpr hlt1)
    have hy0 : 0 < y := lt_of_le_of_ne (hmem n).1 (hne n).2.2.1.symm
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (r / y) hp1
    have := (key j).2
    rw [(key j).1] at this
    rw [div_lt_iff₀ hy0] at hj
    linarith
  · by_cases hhigh : 1 < y
    · -- Above `1` the digit is `1` and the distance to `φ` grows by `φ`.
      have key : ∀ j, ph - (run x b (n + j)).1 = ph ^ j * (ph - y) ∧ 1 < (run x b (n + j)).1 := by
        intro j
        induction j with
        | zero => simp [y, hhigh]
        | succ j ih =>
          have hs := run_succ_fst x b (n + j)
          have hd : runD x b (n + j) = true := by
            unfold runD rule
            rw [if_neg (by linarith [ih.2, r_lt_one]), if_pos ih.2]
          rw [hd, digit_true] at hs
          rw [← add_assoc, hs]
          refine ⟨by rw [pow_succ]; nlinarith [ih.1], ?_⟩
          have hgt : r < ph * (run x b (n + j)).1 - 1 := by rw [hre]; nlinarith [ih.2]
          have hnb := hno (n + (j + 1)) (by omega)
          rw [← add_assoc, hs] at hnb
          have hneq := (hne (n + j + 1)).2.1
          rw [hs] at hneq
          rcases lt_or_gt_of_ne hneq with h | h
          · exact absurd h (not_lt.mpr (hnb hgt))
          · exact h
      have hd0 : 0 < ph - y := sub_pos.mpr (lt_of_le_of_ne (hmem n).2 (hne n).2.2.2)
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (ph / (ph - y)) hp1
      have hk := (key j).1
      have hm := (hmem (n + j)).1
      rw [div_lt_iff₀ hd0] at hj
      linarith
    · push Not at hlow hhigh
      exact absurd (hno n le_rfl (lt_of_le_of_ne hlow (hne n).1.symm))
        (not_le.mpr (lt_of_le_of_ne hhigh (hne n).2.1))

omit h0 h1 hx in
theorem count_mono (b : ℕ → Bool) (n : ℕ) : (run x b n).2 ≤ (run x b (n + 1)).2 := by
  rw [run_snd_succ]
  split_ifs <;> omega

theorem count_unbounded (b : ℕ → Bool) : ∀ K, ∃ n, K < (run x b n).2 := by
  have mono : ∀ n m, n ≤ m → (run x b n).2 ≤ (run x b m).2 := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact ih.trans (count_mono b m)
  have jump : ∀ n, ∃ m, n ≤ m ∧ (run x b n).2 < (run x b (m + 1)).2 := by
    intro n
    obtain ⟨m, hm, hl, hu⟩ := run_branches h0 h1 hx b n
    refine ⟨m, hm, ?_⟩
    rw [run_snd_succ, if_pos ⟨hl.le, hu.le⟩]
    exact Nat.lt_succ_of_le (mono n m hm)
  intro K
  induction K with
  | zero =>
    obtain ⟨m, -, hm⟩ := jump 0
    exact ⟨m + 1, by simp [run] at hm ⊢; omega⟩
  | succ K ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, -, hm⟩ := jump n
    exact ⟨m + 1, by omega⟩

omit h0 h1 hx in
theorem run_agree {b b' : ℕ → Bool} {K : ℕ} (hb : ∀ i < K, b i = b' i) :
    ∀ n, (run x b n).2 ≤ K → run x b n = run x b' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hK
    have hle : (run x b n).2 ≤ K := by
      have : (run x b n).2 ≤ (run x b (n + 1)).2 := by
        rw [run_snd_succ]; split_ifs <;> omega
      omega
    have e := ih hle
    have hrule : rule (run x b n).1 (b (run x b n).2) = rule (run x b n).1 (b' (run x b n).2) := by
      by_cases hbr : r ≤ (run x b n).1 ∧ (run x b n).1 ≤ 1
      · have : (run x b n).2 < K := by
          have h2 : (run x b (n + 1)).2 = (run x b n).2 + 1 := by
            rw [run_snd_succ, if_pos hbr]
          omega
        rw [hb _ this]
      · unfold rule
        rcases not_and_or.mp hbr with h | h
        · push Not at h; simp [h]
        · push Not at h
          have : ¬ (run x b n).1 < r := by linarith [r_lt_one]
          simp [this, h]
    show ((ph * (run x b n).1 - digit (rule (run x b n).1 (b (run x b n).2))),
        if r ≤ (run x b n).1 ∧ (run x b n).1 ≤ 1 then (run x b n).2 + 1 else (run x b n).2) =
      ((ph * (run x b' n).1 - digit (rule (run x b' n).1 (b' (run x b' n).2))),
        if r ≤ (run x b' n).1 ∧ (run x b' n).1 ≤ 1 then (run x b' n).2 + 1 else (run x b' n).2)
    rw [hrule, e]

theorem runD_injective : Function.Injective (runD x) := by
  intro b b' hbb
  by_contra hne
  have hex : ∃ i, b i ≠ b' i := by
    by_contra h; push Not at h; exact hne (funext h)
  classical
  set K := Nat.find hex
  have hK : b K ≠ b' K := Nat.find_spec hex
  have hlt : ∀ i < K, b i = b' i := fun i hi => not_not.mp (Nat.find_min hex hi)
  have hcount := count_unbounded h0 h1 hx b K
  set n₀ := Nat.find hcount
  have hn₀ : K < (run x b n₀).2 := Nat.find_spec hcount
  have hpos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · rw [h] at hn₀; simp [run] at hn₀
    · exact h
  set m := n₀ - 1
  have hm : (run x b m).2 ≤ K := not_lt.mp (Nat.find_min hcount (by omega))
  have hsucc : (run x b (m + 1)).2 = (run x b n₀).2 := by rw [show m + 1 = n₀ by omega]
  have hbr : r ≤ (run x b m).1 ∧ (run x b m).1 ≤ 1 := by
    by_contra hbr
    have : (run x b (m + 1)).2 = (run x b m).2 := by
      rw [run_snd_succ, if_neg hbr]
    omega
  have hcK : (run x b m).2 = K := by
    have : (run x b (m + 1)).2 = (run x b m).2 + 1 := by
      rw [run_snd_succ, if_pos hbr]
    omega
  have e := run_agree hlt m hm
  have hnz := run_not_inZ hx b m
  have hlo : ¬ (run x b m).1 < r := not_lt.mpr hbr.1
  have hhi : ¬ 1 < (run x b m).1 := not_lt.mpr hbr.2
  have hd := congrFun hbb m
  unfold runD rule at hd
  rw [← e] at hd
  simp only [hlo, hhi, if_false, hcK] at hd
  exact hK hd

end Uncountable

/-- **Uncountable case.** A value in `[0, φ]` outside `ℤ[φ]` has uncountably many
expansions. -/
theorem expansions_not_countable {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ ph) (hx : ¬ InZ x) :
    ¬ (expansions x).Countable := by
  intro hc
  have hmem : ∀ b, runD x b ∈ expansions x := fun b => run_value h0 h1 b
  have hinj : Function.Injective fun b => (⟨runD x b, hmem b⟩ : expansions x) := fun b b' h =>
    runD_injective h0 h1 hx (congrArg Subtype.val h)
  have : Countable (expansions x) := hc.to_subtype
  exact Psc.BetaMetallicUnique.not_countable_bool_seq hinj.countable

/-! ## Infinitely many expansions for `x ∈ ℤ[φ] ∩ (0, φ)` -/

/-- `(01)^j 1 0^∞`, an expansion of `φ⁻¹`. -/
def altR : ℕ → (ℕ → Bool)
  | 0 => cons true fun _ => false
  | j + 1 => cons false (cons true (altR j))

theorem value_altR (j : ℕ) : value (altR j) = r := by
  induction j with
  | zero => exact value_one_zeros
  | succ j ih =>
    simp only [altR, value_cons, ih, digit_false, digit_true]
    linear_combination r * r_sq_add

theorem altR_even (j : ℕ) : altR j (2 * j) = true ∧ ∀ i < j, altR j (2 * i) = false := by
  induction j with
  | zero => exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
    refine ⟨by rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]; exact ih.1, fun i hi => ?_⟩
    rcases i with _ | i
    · rfl
    · rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]; exact ih.2 i (by omega)

theorem altR_injective : Function.Injective altR := by
  intro j j' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have a := (altR_even j).1
    rw [h, (altR_even j').2 j hlt] at a
    exact Bool.noConfusion a
  · have a := (altR_even j').1
    rw [← h, (altR_even j).2 j' hlt] at a
    exact Bool.noConfusion a

/-- Prefix `d` up to `n`, then continue with `e`. -/
def splice (d : ℕ → Bool) (n : ℕ) (e : ℕ → Bool) : ℕ → Bool := fun i =>
  if i < n then d i else e (i - n)

theorem value_splice (d : ℕ → Bool) (n : ℕ) (e : ℕ → Bool) :
    value (splice d n e) = psum d n + r ^ n * value e := by
  rw [value_split (splice d n e) n]
  have hs : gshift (splice d n e) n = e := by
    funext i; simp [gshift, splice]
  have hp : psum (splice d n e) n = psum d n := by
    unfold psum
    exact Finset.sum_congr rfl fun i hi => by
      simp [splice, Finset.mem_range.mp hi]
  rw [hs, hp]

theorem splice_injective (d : ℕ → Bool) (n : ℕ) : Function.Injective (splice d n) := by
  intro e e' h
  funext i
  have := congrFun h (n + i)
  simpa [splice] using this

/-- **Infinite case.** Every value in `ℤ[φ] ∩ (0, φ)` has infinitely many expansions. -/
theorem expansions_infinite {x : ℝ} (hx : InZ x) (h0 : 0 < x) (h1 : x < ph) :
    (expansions x).Infinite := by
  set d := runD x fun _ => false
  have hd : value d = x := run_value h0.le h1.le _
  obtain ⟨a₀, b₀, hab⟩ := hx
  have hex : ∃ n, IsT (st d n) := exists_isT (d := d) (hd.trans hab)
  classical
  set n₁ := Nat.find hex
  have hT : IsT (st d n₁) := Nat.find_spec hex
  -- The first visit to the closed set is at `φ⁻¹` or `1`.
  have hmid : st d n₁ = r ∨ st d n₁ = 1 := by
    rcases Nat.eq_zero_or_pos n₁ with hz | hpos
    · rw [hz, st_zero, hd] at hT
      rw [hz, st_zero, hd]
      rcases hT with h | h | h | h
      · linarith
      · exact Or.inl h
      · exact Or.inr h
      · linarith
    · have hprev : ¬ IsT (st d (n₁ - 1)) := Nat.find_min hex (by omega)
      have hs := st_succ d (n₁ - 1)
      rw [show n₁ - 1 + 1 = n₁ by omega] at hs
      rcases hT with h | h | h | h
      · exfalso; apply hprev
        rw [h] at hs
        set s0 := st d (n₁ - 1)
        cases hdn : d (n₁ - 1)
        · rw [hdn, digit_false, sub_zero] at hs
          have : ph * s0 = 0 := hs.symm
          exact Or.inl ((mul_eq_zero.mp this).resolve_left ph_pos.ne')
        · rw [hdn, digit_true] at hs
          have : ph * (s0 - r) = 0 := by linear_combination (-1 : ℝ) * hs - phi_r
          exact Or.inr (Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ph_pos.ne')))
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; apply hprev
        rw [h] at hs
        set s0 := st d (n₁ - 1)
        cases hdn : d (n₁ - 1)
        · rw [hdn, digit_false, sub_zero] at hs
          have : ph * (s0 - 1) = 0 := by linear_combination (-1 : ℝ) * hs
          exact Or.inr (Or.inr (Or.inl
            (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ph_pos.ne'))))
        · rw [hdn, digit_true] at hs
          have : ph * (s0 - ph) = 0 := by linear_combination (-1 : ℝ) * hs - phi_sq
          exact Or.inr (Or.inr (Or.inr
            (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ph_pos.ne'))))
  -- Continue from that state with infinitely many tails.
  let tails : ℕ → (ℕ → Bool) := fun j =>
    if st d n₁ = r then altR j else cons true (altR j)
  have htails : ∀ j, value (tails j) = st d n₁ := by
    intro j
    simp only [tails]
    split
    · rename_i h; rw [value_altR, h]
    · rename_i h
      rw [value_cons, value_altR, digit_true, one_mul]
      rcases hmid with h' | h'
      · exact absurd h' h
      · rw [h']; linear_combination r_sq_add
  have htinj : Function.Injective tails := by
    intro j j' h
    simp only [tails] at h
    split at h
    · exact altR_injective h
    · exact altR_injective (by
        funext i; have := congrFun h (i + 1); simpa [cons] using this)
  refine Set.infinite_of_injective_forall_mem (f := fun j => splice d n₁ (tails j))
    ((splice_injective d n₁).comp htinj) fun j => ?_
  show value (splice d n₁ (tails j)) = x
  rw [value_splice, htails, ← hd, value_split d n₁]
  rfl

/-- **Golden-base multiplicity**, stated with Mathlib's `φ`. For `0 < x < φ`,
the set of `{0,1}` expansions of `x` is countably infinite if `x ∈ ℤ[φ]` and
uncountable otherwise. -/
theorem golden_classification {x : ℝ} (h0 : 0 < x) (h1 : x < φ) :
    ((∃ a b : ℤ, x = a + b * φ) →
        {d : ℕ → Bool | value d = x}.Countable ∧ {d : ℕ → Bool | value d = x}.Infinite) ∧
      (¬ (∃ a b : ℤ, x = a + b * φ) → ¬ {d : ℕ → Bool | value d = x}.Countable) :=
  ⟨fun hz => ⟨expansions_countable hz, expansions_infinite hz h0 h1⟩,
    fun hz => expansions_not_countable h0.le h1.le hz⟩

end Psc.BetaGoldenMultiplicity
