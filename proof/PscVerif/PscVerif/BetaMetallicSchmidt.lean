import PscVerif.BetaMetallicCarry
import PscVerif.BetaGoldenCoding

/-!
# Greedy expansions of elements of `ℚ(β)` in metallic bases are eventually periodic

The quadratic metallic case of K. Schmidt, *On periodic expansions of Pisot and
Salem numbers* (1980). Let `β² = mβ + 1`, `m ≥ 1`, and let `d` be a stream over
`{0, …, m}` all of whose remainders `R_n = Σ_{j≥1} d_{n+j-1} β^{-j}` lie in `[0, 1)`,
so that `d` is the greedy expansion of `R_0`. If `q R_0 = a + bβ` with integers
`a, b, q`, `q > 0`, then `d` is eventually periodic (`eventuallyPeriodic_of_mem`).

Every element of `ℚ(β)` has this form, because `β` is quadratic.

Proof. `q R_n = a_n + b_n β` with integer coordinates following
`(a, b) ↦ (b - q d_n, a + m b)`. The conjugate `a_n - b_n β⁻¹` contracts by
`β⁻¹`, so it stays bounded, and `q R_n ∈ [0, q)`. Hence the coordinates lie in a
finite box and some remainder repeats. Greedy digits are `⌊β R_n⌋`, functions of
the remainder, so the digits repeat with it.

Corollaries:

* `xi_not_mem`, `xi_irrational`: `ξ_{k,m} ∉ ℚ(β_m)`, in particular `ξ_{k,m}` is
  irrational, for `k ≥ 1`, `m ≥ 4`;
* `golden_code_not_mem`: the value of the golden block coding is not in `ℚ(φ)`.

This closes the internal half of the second transcendence route in
`docs/beta-xi-novelty-stop-go-2026-11-28.md`; transcendence itself remains the
external Adamczewski–Bugeaud (or Kebis–Luca–Ouaknine–Scoones–Worrell) step.
-/

set_option autoImplicit false

namespace Psc.BetaMetallicUnique

open Psc.BetaFamilyFixedWord (EventuallyPeriodic)

variable {m : ℕ}

namespace Base

variable (B : Base m)

/-- Remainders of a stream. -/
noncomputable def rem (d : ℕ → Fin (m + 1)) (n : ℕ) : ℝ := B.value (shift d n)

theorem rem_succ (d : ℕ → Fin (m + 1)) (n : ℕ) :
    B.rem d (n + 1) = B.beta * B.rem d n - ((d n : ℕ) : ℝ) := by
  have step := B.value_eq_step (shift d n)
  have h0 : shift d n 0 = d n := by simp [shift]
  rw [h0, ← shift_succ] at step
  unfold rem
  rw [step]
  linear_combination (-((d n : ℕ) : ℝ) - B.value (shift d (n + 1))) * B.beta_r

/-- Greedy digits are the floor of `β` times the remainder. -/
theorem digit_eq_floor (d : ℕ → Fin (m + 1)) (hg : ∀ n, B.rem d n < 1) (n : ℕ) :
    ((d n : ℕ) : ℤ) = ⌊B.beta * B.rem d n⌋ := by
  have e : B.beta * B.rem d n = ((d n : ℕ) : ℝ) + B.rem d (n + 1) := by
    rw [B.rem_succ]; ring
  rw [e, eq_comm, Int.floor_eq_iff]
  have h0 := B.value_nonneg (shift d (n + 1))
  have h1 := hg (n + 1)
  unfold rem at *
  push_cast
  constructor <;> linarith

/-- Integer coordinates of `q R_n`. -/
def coords (d : ℕ → Fin (m + 1)) (a₀ b₀ q : ℤ) : ℕ → ℤ × ℤ
  | 0 => (a₀, b₀)
  | n + 1 => ((coords d a₀ b₀ q n).2 - q * (d n : ℕ), (coords d a₀ b₀ q n).1 + m * (coords d a₀ b₀ q n).2)

theorem rem_coords (d : ℕ → Fin (m + 1)) {a₀ b₀ q : ℤ}
    (h0 : (q : ℝ) * B.value d = a₀ + b₀ * B.beta) (n : ℕ) :
    (q : ℝ) * B.rem d n = B.zval (coords d a₀ b₀ q n) := by
  induction n with
  | zero =>
    simp only [rem, coords, zval]
    rw [show shift d 0 = d from shift_zero d, h0]
  | succ n ih =>
    rw [B.rem_succ]
    simp only [coords, zval] at ih ⊢
    push_cast
    linear_combination B.beta * ih + ((coords d a₀ b₀ q n).2 : ℝ) * B.beta_sq

theorem conj_coords_step (d : ℕ → Fin (m + 1)) (a₀ b₀ q : ℤ) (n : ℕ) :
    B.zconj (coords d a₀ b₀ q (n + 1)) = -B.r * B.zconj (coords d a₀ b₀ q n) - q * (d n : ℕ) := by
  simp only [zconj, coords]
  push_cast
  linear_combination (-((coords d a₀ b₀ q n).2 : ℝ)) * B.carry

theorem conj_coords_bound (d : ℕ → Fin (m + 1)) (a₀ b₀ q : ℤ) (hq : 0 < q) (n : ℕ) :
    |B.zconj (coords d a₀ b₀ q n)| ≤ |B.zconj (a₀, b₀)| + q * m / (1 - B.r) := by
  have hr := B.r_pos
  have h1r : 0 < 1 - B.r := sub_pos.mpr B.r_lt_one
  have hqm : 0 ≤ (q : ℝ) * m / (1 - B.r) := by
    have : (0 : ℝ) ≤ q := by exact_mod_cast hq.le
    positivity
  induction n with
  | zero => simp only [coords]; linarith
  | succ n ih =>
    rw [B.conj_coords_step]
    have hd : |(q : ℝ) * (d n : ℕ)| ≤ q * m := by
      rw [abs_mul, abs_of_pos (by exact_mod_cast hq : (0 : ℝ) < q), Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (digit_le _) (by exact_mod_cast hq.le)
    calc |-B.r * B.zconj (coords d a₀ b₀ q n) - q * (d n : ℕ)|
        ≤ |-B.r * B.zconj (coords d a₀ b₀ q n)| + |(q : ℝ) * (d n : ℕ)| := abs_sub _ _
      _ = B.r * |B.zconj (coords d a₀ b₀ q n)| + |(q : ℝ) * (d n : ℕ)| := by
          rw [abs_mul, abs_neg, abs_of_pos hr]
      _ ≤ B.r * (|B.zconj (a₀, b₀)| + q * m / (1 - B.r)) + q * m := by gcongr
      _ ≤ |B.zconj (a₀, b₀)| + q * m / (1 - B.r) := by
          have e : B.r * ((q : ℝ) * m / (1 - B.r)) + q * m = q * m / (1 - B.r) := by
            field_simp; ring
          nlinarith [abs_nonneg (B.zconj (a₀, b₀)), B.r_lt_one]

/-- **Schmidt, quadratic metallic case.** A greedy expansion of an element of
`ℚ(β)` is eventually periodic. -/
theorem eventuallyPeriodic_of_mem (d : ℕ → Fin (m + 1)) (hg : ∀ n, B.rem d n < 1)
    {a₀ b₀ q : ℤ} (hq : 0 < q) (h0 : (q : ℝ) * B.value d = a₀ + b₀ * B.beta) :
    EventuallyPeriodic d := by
  set C := |B.zconj (a₀, b₀)| + q * m / (1 - B.r)
  have hr := B.r_pos
  have hβ := B.one_lt_beta
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set K : ℕ := ⌈(q : ℝ) + 2 * C + 1⌉₊
  have hC0 : 0 ≤ C := by
    have : (0 : ℝ) ≤ q * m / (1 - B.r) :=
      div_nonneg (mul_nonneg hqR.le (Nat.cast_nonneg m)) (sub_pos.mpr B.r_lt_one).le
    positivity
  have hbox : ∀ n, coords d a₀ b₀ q n ∈
      Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K := by
    intro n
    have hz := B.rem_coords d h0 n
    have hc : |B.zconj (coords d a₀ b₀ q n)| ≤ C := B.conj_coords_bound d a₀ b₀ q hq n
    have hR0 := B.value_nonneg (shift d n)
    have hR1 := hg n
    unfold rem at hz hR1
    have hK : (q : ℝ) + 2 * C + 1 ≤ K := Nat.le_ceil _
    set a := (coords d a₀ b₀ q n).1
    set b := (coords d a₀ b₀ q n).2
    have hzv : B.zval (coords d a₀ b₀ q n) = a + b * B.beta := rfl
    have hcv : B.zconj (coords d a₀ b₀ q n) = a - b * B.r := rfl
    rw [hzv] at hz
    rw [hcv] at hc
    obtain ⟨c1, c2⟩ := abs_le.mp hc
    have hqv0 : 0 ≤ (q : ℝ) * B.value (shift d n) := mul_nonneg hqR.le hR0
    have hqv1 : (q : ℝ) * B.value (shift d n) ≤ q := by nlinarith
    have hpos : 1 ≤ B.beta + B.r := by linarith
    have e : (b : ℝ) * (B.beta + B.r) = q * B.value (shift d n) - (a - b * B.r) := by
      rw [hz]; ring
    have hbm : |(b : ℝ) * (B.beta + B.r)| ≤ q + C := by
      rw [e, abs_le]; constructor <;> linarith
    have hbabs : |(b : ℝ)| ≤ q + C := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < B.beta + B.r)] at hbm
      nlinarith [abs_nonneg (b : ℝ)]
    have hbr : |(b : ℝ) * B.r| ≤ q + C := by
      rw [abs_mul, abs_of_pos hr]; nlinarith [abs_nonneg (b : ℝ), B.r_lt_one]
    obtain ⟨bb1, bb2⟩ := abs_le.mp hbabs
    obtain ⟨br1, br2⟩ := abs_le.mp hbr
    have ha1 : (a : ℝ) ≤ K := by linarith
    have ha2 : -(K : ℝ) ≤ a := by linarith
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨by exact_mod_cast ha2, by exact_mod_cast ha1⟩, ⟨?_, ?_⟩⟩
    · have : -(K : ℝ) ≤ b := by linarith
      exact_mod_cast this
    · have : (b : ℝ) ≤ K := by linarith
      exact_mod_cast this
  let S := Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n => (⟨coords d a₀ b₀ q n, hbox n⟩ : S))
  have heq' : coords d a₀ b₀ q n₁ = coords d a₀ b₀ q n₂ := congrArg Subtype.val heq
  have hrem : ∀ {i j}, coords d a₀ b₀ q i = coords d a₀ b₀ q j → B.rem d i = B.rem d j := by
    intro i j h
    have hi := B.rem_coords d h0 i
    have hj := B.rem_coords d h0 j
    rw [h] at hi
    exact mul_left_cancel₀ hqR.ne' (hi.trans hj.symm)
  -- Equal remainders propagate, and digits are functions of remainders.
  have prop : ∀ {i j}, B.rem d i = B.rem d j → ∀ t, B.rem d (i + t) = B.rem d (j + t) ∧
      d (i + t) = d (j + t) := by
    intro i j h t
    induction t with
    | zero =>
      refine ⟨h, Fin.ext ?_⟩
      have e1 := B.digit_eq_floor d hg i
      have e2 := B.digit_eq_floor d hg j
      rw [h] at e1
      exact_mod_cast e1.trans e2.symm
    | succ t ih =>
      have hr' : B.rem d (i + (t + 1)) = B.rem d (j + (t + 1)) := by
        rw [← add_assoc, ← add_assoc, B.rem_succ, B.rem_succ, ih.1, ih.2]
      refine ⟨hr', Fin.ext ?_⟩
      have e1 := B.digit_eq_floor d hg (i + (t + 1))
      have e2 := B.digit_eq_floor d hg (j + (t + 1))
      rw [hr'] at e1
      exact_mod_cast e1.trans e2.symm
  have per : ∀ {i j}, i < j → B.rem d i = B.rem d j → EventuallyPeriodic d := by
    intro i j hij h
    refine ⟨i, j - i, by omega, fun n hn => ?_⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show i + t + (j - i) = j + t by omega]
    exact ((prop h t).2).symm
  rcases lt_or_gt_of_ne hne with h | h
  · exact per h (hrem heq')
  · exact per h (hrem heq'.symm)

end Base

/-- **`ξ_{k,m}` is not in `ℚ(β_m)`**: no integers `a, b, q` with `q > 0` and
`q ξ = a + bβ`. -/
theorem xi_not_mem (k m : ℕ) (hk : 1 ≤ k) (hm : 4 ≤ m) (B : Base m) :
    ¬ ∃ a b q : ℤ, 0 < q ∧ (q : ℝ) * Psc.BetaFamilyXi.xi k hm B = a + b * B.beta := by
  rintro ⟨a, b, q, hq, h⟩
  have hg : ∀ n, B.rem (Psc.BetaFamilyFixedWord.shifted k m (by omega)) n < 1 :=
    fun n => (Psc.BetaFamilyXi.greedy k hm B n).2.1
  exact Psc.BetaFamilyFixedWord.shifted_not_eventuallyPeriodic k m hk (by omega)
    (B.eventuallyPeriodic_of_mem _ hg hq h)

/-- In particular `ξ_{k,m}` is irrational. -/
theorem xi_irrational (k m : ℕ) (hk : 1 ≤ k) (hm : 4 ≤ m) (B : Base m) :
    Irrational (Psc.BetaFamilyXi.xi k hm B) := by
  rintro ⟨p, hp⟩
  apply xi_not_mem k m hk hm B
  refine ⟨p.num, 0, p.den, by exact_mod_cast p.den_pos, ?_⟩
  rw [← hp]
  push_cast
  have hd : (p.den : ℝ) ≠ 0 := by exact_mod_cast p.den_pos.ne'
  rw [zero_mul, add_zero, Rat.cast_def]
  field_simp

/-! ## The golden block coding -/

open scoped goldenRatio

/-- The golden base as a metallic base with `m = 1`. -/
noncomputable def goldenBase : Base 1 :=
  Base.ofRoot le_rfl φ Real.goldenRatio_pos (by rw [Real.goldenRatio_sq]; ring)

/-- A `{0,1}` stream as a stream over `Fin 2`. -/
def toFin (c : ℕ → Bool) : ℕ → Fin (1 + 1) := fun n => if c n then 1 else 0

theorem goldenBase_value (c : ℕ → Bool) :
    goldenBase.value (toFin c) = Psc.BetaGoldenEndpoint.value c := by
  unfold Base.value Psc.BetaGoldenEndpoint.value
  refine tsum_congr fun n => ?_
  simp only [toFin, goldenBase, Base.ofRoot, Psc.BetaGoldenEndpoint.r]
  cases c n <;> simp

theorem shift_toFin (c : ℕ → Bool) (n : ℕ) :
    shift (toFin c) n = toFin (Psc.BetaGoldenCoding.gshift c n) := rfl

/-- **The golden coding's value is not in `ℚ(φ)`.** -/
theorem golden_code_not_mem (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ a b q : ℤ, 0 < q ∧
      (q : ℝ) * Psc.BetaGoldenEndpoint.value (Psc.BetaGoldenCoding.code k) = a + b * φ := by
  rintro ⟨a, b, q, hq, h⟩
  have hβ : goldenBase.beta = φ := by simp [Base.beta, goldenBase, Base.ofRoot]
  have hg : ∀ n, goldenBase.rem (toFin (Psc.BetaGoldenCoding.code k)) n < 1 := fun n => by
    unfold Base.rem
    rw [shift_toFin, goldenBase_value]
    exact (Psc.BetaGoldenCoding.code_greedy k n).2.1
  have hv : (q : ℝ) * goldenBase.value (toFin (Psc.BetaGoldenCoding.code k)) =
      a + b * goldenBase.beta := by rw [goldenBase_value, hβ]; exact h
  obtain ⟨N, p, hp, hper⟩ := goldenBase.eventuallyPeriodic_of_mem _ hg hq hv
  refine Psc.BetaGoldenCoding.code_not_eventuallyPeriodic k hk ⟨N, p, hp, fun i hi => ?_⟩
  have := congrArg Fin.val (hper i hi)
  simp only [toFin] at this
  cases h1 : Psc.BetaGoldenCoding.code k (i + p) <;>
    cases h2 : Psc.BetaGoldenCoding.code k i <;> simp_all

end Psc.BetaMetallicUnique
