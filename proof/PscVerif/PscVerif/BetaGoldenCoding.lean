import PscVerif.BetaGoldenEndpoint
import PscVerif.BetaFamilyComplexity
import PscVerif.BetaFactorBounded
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The golden-ratio block coding of the `σ_k²` fixed word

Code the fixed word `w` of `σ_k²` by the injective constant-width blocks
`0 ↦ 0000`, `1 ↦ 0010`, `2 ↦ 0100` to a stream `c` over `{0, 1}` and read it in
base `φ`. Proved here, for `k ≥ 1`:

* `code_no_one_one`: `c` has no two adjacent ones;
* `tail_lt_one`: every tail of a no-`11` stream containing `00` has value below
  `1`; hence (`code_greedy`) every remainder of `c` lies in `[0, 1)` and every
  digit is `⌊φ · remainder⌋`: `c` is the greedy `φ`-expansion of its value;
* `code_not_eventuallyPeriodic`, `code_factors_linear`: `c` is not eventually
  periodic and has at most `108 (k²+2)² (⌊n/4⌋ + 2)` factors of length `n`;
* `code_not_unique`: `c` is not the unique `{0,1}` expansion of its value
  (only constant streams are), so this is a canonical candidate, never a
  globally unique representation;
* `golden_pisot`: `φ` and its conjugate `1 - φ` are the roots of `X² - X - 1`
  and `|1 - φ| < 1`.

These are the hypotheses Adamczewski–Bugeaud Corollary 1 places on the greedy
`φ`-expansion; that corollary is not formalized. Source decision:
`docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaGoldenCoding

open scoped goldenRatio
open Psc.BetaGoldenEndpoint
open Psc.BetaFamilyFixedWord (word EventuallyPeriodic)
open Psc.BetaFamilyComplexity (factor factors E)

/-! ## No-`11` streams have tails below `1` -/

/-- Drop the first `j` digits. -/
def gshift (t : ℕ → Bool) (j : ℕ) : ℕ → Bool := fun i => t (j + i)

/-- No two adjacent ones. -/
def NoOneOne (t : ℕ → Bool) : Prop := ∀ n, t n = true → t (n + 1) = false

/-- The partial valuation `Σ_{n<N} t_n φ^{-(n+1)}`. -/
noncomputable def psum (t : ℕ → Bool) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, digit (t n) * r ^ (n + 1)

theorem partial_succ (t : ℕ → Bool) (N : ℕ) :
    psum t (N + 1) = digit (t 0) * r + r * psum (tail t) N := by
  unfold psum
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [zero_add, pow_one, tail_apply]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

theorem partial_le (N : ℕ) : ∀ t : ℕ → Bool, NoOneOne t → psum t N ≤ 1 - r ^ (N + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t ht
    have hr := r_pos
    have hr1 := r_lt_one
    have hc := r_sq_add
    rcases N with _ | N
    · simp [psum]; linarith
    · have htail : NoOneOne (tail t) := fun n h => ht (n + 1) h
      rw [partial_succ]
      cases h0 : t 0
      · have := ih N (by omega) (tail t) htail
        simp only [digit_false, zero_mul, zero_add]
        have hpow : 0 ≤ r ^ (N + 1) := pow_nonneg hr.le _
        nlinarith [pow_succ r (N + 1)]
      · have h1 : t 1 = false := ht 0 h0
        rcases N with _ | N
        · simp [psum]; linarith
        · rw [partial_succ]
          have htt : NoOneOne (tail (tail t)) := fun n h => htail (n + 1) h
          have := ih N (by omega) (tail (tail t)) htt
          simp only [digit_true, tail_apply, h1, digit_false, zero_mul, zero_add, one_mul]
          have e : r ^ (N + 1 + 1 + 1) = r ^ 2 * r ^ (N + 1) := by ring
          rw [e]
          nlinarith [pow_nonneg hr.le (N + 1)]

theorem value_le_one {t : ℕ → Bool} (ht : NoOneOne t) : value t ≤ 1 :=
  Real.tsum_le_of_sum_range_le (term_nonneg t) fun N => by
    have := partial_le N t ht
    have : 0 ≤ r ^ (N + 1) := pow_nonneg r_pos.le _
    unfold psum at *
    linarith

theorem value_split (t : ℕ → Bool) (j : ℕ) :
    value t = psum t j + r ^ j * value (gshift t j) := by
  induction j with
  | zero =>
    have : gshift t 0 = t := by funext i; simp [gshift]
    simp [psum, this]
  | succ j ih =>
    have step := value_eq_step (gshift t j)
    have h0 : gshift t j 0 = t j := by simp [gshift]
    have ht : tail (gshift t j) = gshift t (j + 1) := by
      funext i; simp only [tail_apply, gshift]; congr 1; omega
    rw [h0, ht] at step
    rw [ih, step]
    unfold psum
    rw [Finset.sum_range_succ]
    ring

theorem noOneOne_gshift {t : ℕ → Bool} (ht : NoOneOne t) (j : ℕ) : NoOneOne (gshift t j) :=
  fun n h => by
    have := ht (j + n) h
    simpa [gshift, add_assoc] using this

/-- A no-`11` stream containing `00` has value below `1`. -/
theorem tail_lt_one {t : ℕ → Bool} (ht : NoOneOne t) {j : ℕ} (hj0 : t j = false)
    (hj1 : t (j + 1) = false) : value t < 1 := by
  have hr := r_pos
  have hc := r_sq_add
  have hs := value_split t j
  have hP := partial_le j t ht
  have hstep := value_eq_step (gshift t j)
  have hstep2 := value_eq_step (tail (gshift t j))
  have e0 : gshift t j 0 = false := by simpa [gshift] using hj0
  have e1 : tail (gshift t j) 0 = false := by simpa [gshift] using hj1
  rw [e0] at hstep
  rw [e1] at hstep2
  have hle := value_le_one (noOneOne_gshift (noOneOne_gshift ht j) 1 |> fun h => by
    have : gshift (gshift t j) 1 = tail (gshift t j) := by
      funext i; simp [gshift, tail, add_comm]
    exact this ▸ h)
  -- The second tail is again no-`11`.
  have htt : NoOneOne (tail (tail (gshift t j))) := fun n h => by
    have := noOneOne_gshift ht j (n + 2) (by simpa [tail] using h)
    simpa [tail] using this
  have hle2 := value_le_one htt
  simp only [digit_false, zero_mul, zero_add] at hstep hstep2
  have hrj : 0 < r ^ j := pow_pos hr j
  have hV : value (gshift t j) ≤ r ^ 2 := by
    rw [hstep, hstep2]; nlinarith
  have : r ^ j * value (gshift t j) ≤ r ^ j * r ^ 2 := mul_le_mul_of_nonneg_left hV hrj.le
  have hgap : r ^ (j + 1) - r ^ j * r ^ 2 = r ^ j * (r - r ^ 2) := by ring
  have hpos : 0 < r - r ^ 2 := by nlinarith [r_lt_one]
  have : 0 < r ^ j * (r - r ^ 2) := mul_pos hrj hpos
  linarith

/-! ## The coding -/

/-- The block of a letter: `0 ↦ 0000`, `1 ↦ 0010`, `2 ↦ 0100`. -/
def block (a : Fin 3) (o : ℕ) : Bool := (a = 1 ∧ o = 2) ∨ (a = 2 ∧ o = 1)

/-- The coded stream `c`. -/
noncomputable def code (k : ℕ) (n : ℕ) : Bool := block (word k (n / 4)) (n % 4)

theorem block_ends (a : Fin 3) : block a 0 = false ∧ block a 3 = false := by
  fin_cases a <;> simp [block]

theorem code_no_one_one (k : ℕ) : NoOneOne (code k) := by
  intro n h
  unfold code at *
  have h4 := Nat.mod_lt n (show 0 < 4 by norm_num)
  by_cases h3 : n % 4 = 3
  · rw [h3] at h; simp [block] at h
  · have e1 : (n + 1) / 4 = n / 4 := by omega
    have e2 : (n + 1) % 4 = n % 4 + 1 := by omega
    rw [e1, e2]
    revert h
    generalize word k (n / 4) = a
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 := by omega
    fin_cases a <;> rcases this with h | h | h <;> simp [block, h]

/-- Every block contains `00` at offset `0` or `2`. -/
theorem code_zero_zero (k : ℕ) (n : ℕ) :
    ∃ j, n ≤ j ∧ code k j = false ∧ code k (j + 1) = false := by
  set i := n / 4 + 1
  have hb : ∀ a : Fin 3, (block a 0 = false ∧ block a 1 = false) ∨
      (block a 2 = false ∧ block a 3 = false) := by
    intro a; fin_cases a <;> simp [block]
  have hcode : ∀ o < 4, code k (4 * i + o) = block (word k i) o := by
    intro o ho
    unfold code
    rw [show (4 * i + o) / 4 = i by omega, show (4 * i + o) % 4 = o by omega]
  rcases hb (word k i) with ⟨h0, h1⟩ | ⟨h2, h3⟩
  · exact ⟨4 * i, by omega, by rw [show 4 * i = 4 * i + 0 by rfl, hcode 0 (by norm_num)]; exact h0,
      by rw [hcode 1 (by norm_num)]; exact h1⟩
  · exact ⟨4 * i + 2, by omega, by rw [hcode 2 (by norm_num)]; exact h2,
      by rw [show 4 * i + 2 + 1 = 4 * i + 3 by rfl, hcode 3 (by norm_num)]; exact h3⟩

/-- **Greedy `φ`-expansion.** Every remainder of `c` lies in `[0, 1)` and every
digit is the floor of `φ` times the preceding remainder. -/
theorem code_greedy (k n : ℕ) :
    0 ≤ value (gshift (code k) n) ∧ value (gshift (code k) n) < 1 ∧
      ((code k n).toNat : ℤ) = ⌊φ * value (gshift (code k) n)⌋ := by
  have lt : ∀ j, value (gshift (code k) j) < 1 := fun j => by
    obtain ⟨i, hi, h0, h1⟩ := code_zero_zero k j
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact tail_lt_one (noOneOne_gshift (code_no_one_one k) j)
      (show code k (j + l) = false from h0) (show code k (j + (l + 1)) = false from h1)
  refine ⟨value_nonneg _, lt n, ?_⟩
  have step := value_eq_step (gshift (code k) n)
  have h0 : gshift (code k) n 0 = code k n := by simp [gshift]
  have ht : tail (gshift (code k) n) = gshift (code k) (n + 1) := by
    funext i; simp only [tail_apply, gshift]; congr 1; omega
  rw [h0, ht] at step
  have hφr : φ * r = 1 := mul_inv_cancel₀ Real.goldenRatio_pos.ne'
  have e : φ * value (gshift (code k) n) = digit (code k n) + value (gshift (code k) (n + 1)) := by
    rw [step]
    linear_combination (digit (code k n) + value (gshift (code k) (n + 1))) * hφr
  rw [e]
  have hnn := value_nonneg (gshift (code k) (n + 1))
  have hlt := lt (n + 1)
  rw [eq_comm, Int.floor_eq_iff]
  cases code k n
  · simp only [digit_false, Bool.toNat_false, Nat.cast_zero, Int.cast_zero, zero_add]
    constructor <;> linarith
  · simp only [digit_true, Bool.toNat_true, Nat.cast_one, Int.cast_one]
    constructor <;> linarith

/-! ## Non-periodicity -/

/-- Decode a block from its middle digits. -/
def decode (b1 b2 : Bool) : Fin 3 := if b2 then 1 else if b1 then 2 else 0

theorem decode_code (k i : ℕ) : decode (code k (4 * i + 1)) (code k (4 * i + 2)) = word k i := by
  unfold code
  rw [show (4 * i + 1) / 4 = i by omega, show (4 * i + 1) % 4 = 1 by omega,
    show (4 * i + 2) / 4 = i by omega, show (4 * i + 2) % 4 = 2 by omega]
  generalize word k i = a
  fin_cases a <;> simp [decode, block]

theorem code_not_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) : ¬ EventuallyPeriodic (code k) := by
  rintro ⟨N, p, hp, hper⟩
  have hmul : ∀ j i, N ≤ i → code k (i + j * p) = code k i := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro i hi
      rw [show i + (j + 1) * p = (i + j * p) + p by ring, hper _ (by omega), ih i hi]
  refine Psc.BetaFamilyFixedWord.word_not_eventuallyPeriodic k hk ⟨N, p, hp, fun i hi => ?_⟩
  rw [← decode_code, ← decode_code]
  have e1 : 4 * (i + p) + 1 = (4 * i + 1) + 4 * p := by ring
  have e2 : 4 * (i + p) + 2 = (4 * i + 2) + 4 * p := by ring
  rw [e1, e2, hmul 4 _ (by omega), hmul 4 _ (by omega)]

/-! ## Linear complexity -/

/-- Rebuild a coded factor from a factor of `w` and an offset. -/
def rebuild (n : ℕ) (x : List (Fin 3) × ℕ) : List Bool :=
  List.ofFn fun t : Fin n => block ((x.1[(x.2 + t) / 4]?).getD 0) ((x.2 + t) % 4)

theorem factor_code (k s n : ℕ) :
    factor (code k) s n = rebuild n (factor (word k) (s / 4) (n / 4 + 2), s % 4) := by
  unfold factor rebuild
  congr 1
  funext t
  have ht := t.2
  have hidx : (s % 4 + t) / 4 < n / 4 + 2 := by omega
  simp only [code, List.getElem?_ofFn, hidx, dite_true, Option.getD_some]
  rw [show (s + t) / 4 = s / 4 + (s % 4 + t) / 4 by omega,
    show (s + t) % 4 = (s % 4 + t) % 4 by omega]

theorem code_factors_linear (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    (factors (code k) n).Finite ∧
      (factors (code k) n).ncard ≤ 108 * E k ^ 2 * (n / 4 + 2) := by
  obtain ⟨hfin, hcard⟩ :=
    Psc.BetaFamilyComplexity.factors_finite_and_linear k hk (n / 4 + 2) (by omega)
  have hsub : factors (code k) n ⊆
      rebuild n '' (factors (word k) (n / 4 + 2) ×ˢ Set.Iio 4) := by
    rintro u ⟨s, rfl⟩
    exact ⟨_, ⟨⟨s / 4, rfl⟩, Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))⟩,
      (factor_code k s n).symm⟩
  have hprod : (factors (word k) (n / 4 + 2) ×ˢ Set.Iio 4).Finite :=
    hfin.prod (Set.finite_Iio 4)
  refine ⟨(hprod.image _).subset hsub, ?_⟩
  calc (factors (code k) n).ncard
      ≤ (rebuild n '' (factors (word k) (n / 4 + 2) ×ˢ Set.Iio 4)).ncard :=
        Set.ncard_le_ncard hsub (hprod.image _)
    _ ≤ (factors (word k) (n / 4 + 2) ×ˢ Set.Iio 4).ncard := Set.ncard_image_le hprod
    _ = (factors (word k) (n / 4 + 2)).ncard * 4 := by
        rw [Set.ncard_prod, Set.ncard_eq_toFinset_card' (Set.Iio 4)]; simp
    _ ≤ 27 * E k ^ 2 * (n / 4 + 2) * 4 := Nat.mul_le_mul_right _ hcard
    _ = 108 * E k ^ 2 * (n / 4 + 2) := by ring

/-! ## Non-uniqueness and the base -/

theorem word_one (k : ℕ) (hk : 1 ≤ k) : word k 1 = 1 := by
  have h := Psc.BetaFamilyFixedWord.word_prefix k 1
  have hlen : 1 < ((Psc.Binomial.subst (Psc.ParameterFamilyRows.substitution k))^[2 * 1]
      [0]).length := by
    rw [show 2 * 1 = 2 by rfl, Psc.BetaFamilyFixedWord.square_zero]; simp; try omega
  have := congrArg (fun l => l[1]?) h
  simp only [Psc.BetaFamilyFixedWord.pref, List.getElem?_ofFn, hlen, dite_true] at this
  rw [show 2 * 1 = 2 by rfl, Psc.BetaFamilyFixedWord.square_zero] at this
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa [Psc.ParameterFamilyWords.ones, List.replicate_succ] using this

/-- The coded stream is not the unique expansion of its value. -/
theorem code_not_unique (k : ℕ) (hk : 1 ≤ k) : ¬ IsUnique (code k) := by
  intro h
  have h6 : code k 6 = true := by
    unfold code; rw [show 6 / 4 = 1 by rfl, show 6 % 4 = 2 by rfl, word_one k hk]; simp [block]
  have h0 : code k 0 = false := by unfold code; exact (block_ends _).1
  rcases (isUnique_iff _).mp h with he | he
  · have := congrFun he 6; rw [h6] at this; exact Bool.noConfusion this
  · have := congrFun he 0; rw [h0] at this; exact Bool.noConfusion this

/-- `φ` is a quadratic Pisot number: its conjugate `1 - φ` has modulus below `1`. -/
theorem golden_pisot :
    1 < φ ∧ φ ^ 2 = φ + 1 ∧ (1 - φ) ^ 2 = (1 - φ) + 1 ∧ |1 - φ| < 1 := by
  have h := Real.goldenRatio_sq
  refine ⟨Real.one_lt_goldenRatio, h, by linear_combination h, ?_⟩
  rw [abs_sub_comm, abs_of_pos (by linarith [Real.one_lt_goldenRatio])]
  linarith [Real.goldenRatio_lt_two]

/-- The factor counts of the coded stream are unbounded. -/
theorem code_complexity_unbounded (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ C, ∀ n, (factors (code k) n).Finite ∧ (factors (code k) n).ncard ≤ C := by
  rintro ⟨C, hC⟩
  exact code_not_eventuallyPeriodic k hk
    (Psc.BetaFactorBounded.eventuallyPeriodic_of_bounded _ hC)

end Psc.BetaGoldenCoding
