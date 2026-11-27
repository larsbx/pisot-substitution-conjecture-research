import PscVerif.FixedPointLimit
import PscVerif.C4ParameterFamilyPisot
import PscVerif.BetaMetallicUnique
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The fixed word of `σ_k²` and its non-eventual periodicity

`σ_k = (0 ↦ 1, 1 ↦ 0 1^k 2, 2 ↦ 001)` is the literal substitution
`Psc.ParameterFamilyRows.substitution k`. Since `σ_k²(0) = 0 1^k 2` begins with
`0`, the chain `σ_k^{2n}(0)` is increasing in the prefix order and its limit is
the one-sided fixed word `w` of `σ_k²` beginning at `0`.

Proved here:

* `word_prefix`: every iterate `σ_k^{2n}(0)` is a literal prefix of `w`;
  `word_fixed`: `σ_k²` maps each prefix of `w` to a prefix of `w`.
* `word_not_eventuallyPeriodic` (`k ≥ 1`): `w` is not eventually periodic.
* `xi_unique`: for `m ≥ 4` the stream `w + 1` over `{0, …, m}` is the unique
  representation of its value in every metallic base `β² = mβ + 1`, that value
  lies in `(β⁻¹, 1)`, and the stream is not eventually periodic.

The non-periodicity argument is algebraic and avoids letter frequencies. An
eventually periodic word gives a nonzero integer functional `y`, orthogonal to
the letter counts of one period, whose values on prefix counts are bounded.
On the prefixes `σ_k^{2n}(0)` these values are `yᵀ M^{2n} e₀`, a bounded integer
sequence. Pigeonhole and the independence of `e₀, M²e₀, M⁴e₀` give
`yᵀ (M^{2T} - 1) = 0` with `T ≥ 1`. Irreducibility of the characteristic
polynomial then forces `M^{2T} = 1`, which `det M = 2` refutes.

Not proved here: linear factor complexity, greedy admissibility of any coding,
any transcendence statement, or that `ξ_{k,m}` is new. Source decision:
`docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaFamilyFixedWord

open Matrix Polynomial
open Psc.Binomial (subst)
open Psc.ParameterFamilyRows (substitution)
open Psc.ParameterFamilyPisot (incidenceQ)

/-- A one-sided sequence is eventually periodic. -/
def EventuallyPeriodic {β : Type*} (x : ℕ → β) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ i, N ≤ i → x (i + p) = x i

/-! ## The fixed word -/

theorem substitution_ne_nil (k : ℕ) (a : Fin 3) : substitution k a ≠ [] := by
  fin_cases a <;> simp [substitution]

theorem square_zero (k : ℕ) :
    (subst (substitution k))^[2] [0] = 0 :: (Psc.ParameterFamilyWords.ones k ++ [2]) := by
  simp [subst, substitution]

theorem seed_prefix (k : ℕ) : [0] <+: (subst (substitution k))^[2] [0] := by
  rw [square_zero]
  exact ⟨_, rfl⟩

theorem seed_grows (k : ℕ) : [0].length < ((subst (substitution k))^[2] [0]).length := by
  rw [square_zero]
  simp

theorem growth (k : ℕ) :
    ∀ m, ∃ n, m < ((subst (substitution k))^[2 * n] [0]).length :=
  Psc.FixedPointLimit.grow_of_nonerasing _ (substitution_ne_nil k) (seed_prefix k)
    (seed_grows k)

/-- The one-sided fixed word of `σ_k²` beginning at `0`. -/
noncomputable def word (k : ℕ) : ℕ → Fin 3 :=
  Psc.FixedPointLimit.limit (substitution k) [0] 2 (growth k)

/-- The length-`L` prefix of the fixed word. -/
noncomputable def pref (k L : ℕ) : List (Fin 3) := List.ofFn fun i : Fin L => word k i

theorem word_zero (k : ℕ) : word k 0 = 0 :=
  Psc.FixedPointLimit.limit_zero _ (seed_prefix k) (growth k) (List.cons_ne_nil _ _)

/-- Every literal iterate `σ_k^{2n}(0)` is the prefix of `w` of its length. -/
theorem word_prefix (k n : ℕ) :
    pref k ((subst (substitution k))^[2 * n] [0]).length =
      (subst (substitution k))^[2 * n] [0] :=
  Psc.FixedPointLimit.ofFn_limit_of_prefix _ (seed_prefix k) (growth k) (List.prefix_refl _)

/-- `σ_k²` maps each prefix of `w` onto the prefix of `w` of the image length. -/
theorem word_fixed (k L : ℕ) :
    pref k ((subst (substitution k))^[2] (pref k L)).length =
      (subst (substitution k))^[2] (pref k L) :=
  Psc.FixedPointLimit.limit_fixed_eq _ (seed_prefix k) (growth k) L

/-! ## Prefix letter counts -/

theorem pref_succ (k L : ℕ) : pref k (L + 1) = pref k L ++ [word k L] := by
  unfold pref
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

theorem count_pref_succ (k L : ℕ) (a : Fin 3) :
    (pref k (L + 1)).count a = (pref k L).count a + if word k L = a then 1 else 0 := by
  rw [pref_succ, List.count_append, List.count_singleton]
  simp [beq_iff_eq]

/-- Letter counts of the iterates are columns of the incidence powers. -/
theorem count_iterate (k n : ℕ) (a : Fin 3) :
    ((subst (substitution k))^[2 * n] [0]).count a =
      (Psc.Incidence.inc (substitution k) ^ (2 * n)) a 0 :=
  Psc.Incidence.count_iterate_subst _ _ _ _

/-! ## An eventually periodic word has a bounded orthogonal functional -/

section Periodic

variable {k : ℕ}

/-- Counts in the window `[L, L + p)`. -/
noncomputable def window (k p L : ℕ) (a : Fin 3) : ℤ :=
  ((pref k (L + p)).count a : ℤ) - (pref k L).count a

theorem window_succ {N p : ℕ} (hper : ∀ i, N ≤ i → word k (i + p) = word k i) {L : ℕ}
    (hL : N ≤ L) (a : Fin 3) : window k p (L + 1) a = window k p L a := by
  unfold window
  rw [show L + 1 + p = L + p + 1 by omega, count_pref_succ, count_pref_succ, hper L hL]
  push_cast
  ring

theorem window_const {N p : ℕ} (hper : ∀ i, N ≤ i → word k (i + p) = word k i) (a : Fin 3) :
    ∀ L, N ≤ L → window k p L a = window k p N a := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => rfl
  | succ L hL ih => rw [window_succ hper hL, ih]

/-- The functional `L ↦ Σ_a y_a |w[0,L)|_a`. -/
noncomputable def functional (k : ℕ) (y : Fin 3 → ℤ) (L : ℕ) : ℤ :=
  ∑ a, y a * (pref k L).count a

theorem functional_periodic {N p : ℕ} (hper : ∀ i, N ≤ i → word k (i + p) = word k i)
    {y : Fin 3 → ℤ} (hy : ∑ a, y a * window k p N a = 0) {L : ℕ} (hL : N ≤ L) :
    functional k y (L + p) = functional k y L := by
  have h : functional k y (L + p) - functional k y L = ∑ a, y a * window k p L a := by
    unfold functional window
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [Finset.sum_congr rfl fun a _ => by rw [window_const hper a L hL]] at h
  linarith

/-- An eventually periodic integer sequence is bounded. -/
theorem bounded_of_periodic (f : ℕ → ℤ) {N p : ℕ} (hp : 0 < p)
    (hf : ∀ L, N ≤ L → f (L + p) = f L) :
    ∀ L, |f L| ≤ ∑ j ∈ Finset.range (N + p), |f j| := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    by_cases hL : L < N + p
    · exact Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr hL)
    · have e : L = (L - p) + p := by omega
      rw [e, hf (L - p) (by omega)]
      exact ih _ (by omega)

/-- A nonzero integer vector orthogonal to a given one. -/
theorem exists_orthogonal (q : Fin 3 → ℤ) : ∃ y : Fin 3 → ℤ, y ≠ 0 ∧ ∑ a, y a * q a = 0 := by
  by_cases h : q 0 = 0
  · refine ⟨![1, 0, 0], fun h1 => by simpa using congrFun h1 0, ?_⟩
    simp [Fin.sum_univ_three, h]
  · refine ⟨![q 1, -q 0, 0], fun h1 => h (by simpa using congrFun h1 1), ?_⟩
    simp [Fin.sum_univ_three]
    ring

end Periodic

/-! ## The incidence matrix has no root-of-unity eigenvalue -/

theorem det_pow_sub_one_ne_zero (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (hN : 1 ≤ N) :
    (incidenceQ k ^ N - 1).det ≠ 0 := by
  set M := incidenceQ k
  have hχ := Psc.ParameterFamilyPisot.irreducible k hk
  intro hdet
  by_cases hdvd : M.charpoly ∣ X ^ N - 1
  · obtain ⟨g, hg⟩ := hdvd
    have h1 : M ^ N - 1 = 0 := by
      have := congrArg (aeval M) hg
      simpa [aeval_self_charpoly] using this
    have h2 : (M ^ N).det = 1 := by rw [sub_eq_zero.mp h1, det_one]
    rw [det_pow, Psc.ParameterFamilyPisot.determinant] at h2
    have : (1 : ℚ) < 2 ^ N := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  · obtain ⟨a, b, hab⟩ := (hχ.coprime_iff_not_dvd).mpr hdvd
    have h1 : aeval M b * (M ^ N - 1) = 1 := by
      have := congrArg (aeval M) hab
      have hc : aeval M (incidenceQ k).charpoly = 0 := aeval_self_charpoly M
      simp only [map_add, map_mul, map_one, map_sub, map_pow, aeval_X, hc, mul_zero,
        zero_add] at this
      exact this
    have h2 := congrArg Matrix.det h1
    rw [det_mul, hdet, mul_zero, det_one] at h2
    exact zero_ne_one h2

/-! ## The fixed word is not eventually periodic -/

theorem incidenceQ_pow (k n : ℕ) :
    incidenceQ k ^ n = (Psc.Incidence.inc (substitution k) ^ n).map (Nat.cast : ℕ → ℚ) := by
  unfold incidenceQ
  exact (Matrix.map_pow _ (Nat.castRingHom ℚ) n).symm

theorem sq_col (k : ℕ) (b : Fin 3) :
    (incidenceQ k ^ 2) b 0 = ![1, (k : ℚ), 1] b := by
  rw [incidenceQ_pow, Matrix.map_apply, Psc.ParameterFamilyPisot.incidence_sq]
  fin_cases b <;> simp

theorem fourth_col (k : ℕ) (b : Fin 3) :
    (incidenceQ k ^ 4) b 0 =
      ![(k : ℚ) ^ 2 + 2 * k + 2, (k : ℚ) ^ 3 + 4 * k + 2, (k : ℚ) ^ 2 + 2] b := by
  rw [show 4 = 2 + 2 by rfl, pow_add, Matrix.mul_apply, Fin.sum_univ_three, sq_col, sq_col,
    sq_col]
  rw [incidenceQ_pow, Psc.ParameterFamilyPisot.incidence_sq]
  fin_cases b <;> simp <;> ring

/-- Three consecutive samples `r ⬝ M^{2j} e₀`, `j = 0, 1, 2`, determine `r`. -/
theorem samples_determine (k : ℕ) {d : Fin 3 → ℚ}
    (h : ∀ j < 3, ∑ b, d b * (incidenceQ k ^ (2 * j)) b 0 = 0) : d = 0 := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  simp only [Nat.mul_zero, pow_zero, Nat.mul_one, show 2 * 2 = 4 by rfl,
    Fin.sum_univ_three] at h0 h1 h2
  rw [sq_col, sq_col, sq_col] at h1
  rw [fourth_col, fourth_col, fourth_col] at h2
  simp at h0 h1 h2
  have hkpos : (0 : ℚ) < 2 * k + 2 := by positivity
  have e1 : d 1 * (2 * k + 2) = 0 := by
    linear_combination h2 - ((k : ℚ) ^ 2 + 2) * h1 - (2 * (k : ℚ)) * h0
  have d1 : d 1 = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact h
    · linarith
  have d2 : d 2 = 0 := by linear_combination h1 - h0 - (k : ℚ) * d1
  funext b
  fin_cases b
  · simpa using h0
  · simpa using d1
  · simpa using d2

theorem vecMul_pow_eq (k : ℕ) (y : Fin 3 → ℚ) {n n' : ℕ}
    (h : ∀ j < 3, ∑ b, (y ᵥ* incidenceQ k ^ (2 * n)) b * (incidenceQ k ^ (2 * j)) b 0 =
      ∑ b, (y ᵥ* incidenceQ k ^ (2 * n')) b * (incidenceQ k ^ (2 * j)) b 0) :
    y ᵥ* incidenceQ k ^ (2 * n) = y ᵥ* incidenceQ k ^ (2 * n') := by
  have := samples_determine k (d := y ᵥ* incidenceQ k ^ (2 * n) - y ᵥ* incidenceQ k ^ (2 * n'))
    fun j hj => by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [h j hj, sub_self]
  exact sub_eq_zero.mp this

theorem sample_eq (k : ℕ) (y : Fin 3 → ℚ) (n j : ℕ) :
    ∑ b, (y ᵥ* incidenceQ k ^ (2 * n)) b * (incidenceQ k ^ (2 * j)) b 0 =
      (y ᵥ* incidenceQ k ^ (2 * (n + j))) 0 := by
  rw [show 2 * (n + j) = 2 * n + 2 * j by ring, pow_add, ← Matrix.vecMul_vecMul]
  rfl

/-- **The fixed word of `σ_k²` is not eventually periodic** (`k ≥ 1`). -/
theorem word_not_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) : ¬ EventuallyPeriodic (word k) := by
  rintro ⟨N, p, hp, hper⟩
  obtain ⟨y, hy0, hy⟩ := exists_orthogonal (window k p N)
  set U : ℕ → List (Fin 3) := fun n => (subst (substitution k))^[2 * n] [0]
  set a : ℕ → ℤ := fun n => functional k y (U n).length
  set B := ∑ j ∈ Finset.range (N + p), |functional k y j|
  have hbound : ∀ n, |a n| ≤ B := fun n =>
    bounded_of_periodic (functional k y) hp (fun L hL => functional_periodic hper hy hL) _
  -- `a n = yᵀ M^{2n} e₀`.
  have ha : ∀ n, (a n : ℚ) = ((fun b => (y b : ℚ)) ᵥ* incidenceQ k ^ (2 * n)) 0 := by
    intro n
    show ((∑ b, y b * ((pref k (U n).length).count b : ℤ) : ℤ) : ℚ) = _
    rw [word_prefix]
    simp only [Matrix.vecMul, dotProduct, incidenceQ_pow, Matrix.map_apply]
    push_cast
    exact Finset.sum_congr rfl fun b _ => by rw [count_iterate]
  -- Pigeonhole on three consecutive bounded integer samples.
  let I := Set.Icc (-B) B
  have hmem : ∀ n, a n ∈ I := fun n => abs_le.mp (hbound n)
  let f : ℕ → I × I × I := fun n => (⟨a n, hmem n⟩, ⟨a (n + 1), hmem _⟩, ⟨a (n + 2), hmem _⟩)
  have : Finite I := (Set.finite_Icc (-B) B).to_subtype
  obtain ⟨n₁, n₂, hne, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ {n n' : ℕ}, f n = f n' → n < n' → False := by
    intro n n' hf hlt
    have hs : ∀ j < 3, a (n + j) = a (n' + j) := by
      intro j hj
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hf
      interval_cases j
      · exact hf.1
      · exact hf.2.1
      · exact hf.2.2
    set yq : Fin 3 → ℚ := fun b => (y b : ℚ)
    have hv := vecMul_pow_eq k yq (n := n) (n' := n') fun j hj => by
      rw [sample_eq, sample_eq, ← ha, ← ha, hs j hj]
    set T := n' - n
    have hT : 1 ≤ 2 * T := by omega
    have hpow : incidenceQ k ^ (2 * n') = incidenceQ k ^ (2 * T) * incidenceQ k ^ (2 * n) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, ← Matrix.vecMul_vecMul] at hv
    have hz : (yq ᵥ* incidenceQ k ^ (2 * T) - yq) ᵥ* incidenceQ k ^ (2 * n) = 0 := by
      rw [Matrix.sub_vecMul, ← hv, sub_self]
    have hinv : (incidenceQ k ^ (2 * n)).det ≠ 0 := by
      rw [det_pow, Psc.ParameterFamilyPisot.determinant]; positivity
    have h1 : yq ᵥ* incidenceQ k ^ (2 * T) - yq = 0 := by
      by_contra hne'
      exact hinv (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne', hz⟩)
    have h2 : yq ᵥ* (incidenceQ k ^ (2 * T) - 1) = 0 := by
      rw [Matrix.vecMul_sub, Matrix.vecMul_one]; exact h1
    have hyq : yq ≠ 0 := by
      intro h0
      apply hy0
      funext b
      have := congrFun h0 b
      simp only [yq, Pi.zero_apply, Int.cast_eq_zero] at this
      exact this
    exact det_pow_sub_one_ne_zero k hk hT (Matrix.exists_vecMul_eq_zero_iff.mp ⟨yq, hyq, h2⟩)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key hf h
  · exact key hf.symm h

/-! ## The coded stream `w + 1` in a metallic base -/

/-- The digit stream `w_n + 1` over `{0, …, m}`, for `m ≥ 3`. -/
noncomputable def shifted (k m : ℕ) (hm : 3 ≤ m) : ℕ → Fin (m + 1) :=
  fun n => ⟨(word k n : ℕ) + 1, by have := (word k n).2; omega⟩

theorem shifted_not_eventuallyPeriodic (k m : ℕ) (hk : 1 ≤ k) (hm : 3 ≤ m) :
    ¬ EventuallyPeriodic (shifted k m hm) := by
  rintro ⟨N, p, hp, hper⟩
  refine word_not_eventuallyPeriodic k hk ⟨N, p, hp, fun i hi => Fin.ext ?_⟩
  have := congrArg Fin.val (hper i hi)
  simp only [shifted] at this
  omega

/-- For `m ≥ 4`, every digit of `w + 1` lies in `{1, …, m - 1}`. -/
theorem shifted_interior (k m : ℕ) (hm : 4 ≤ m) (n : ℕ) :
    0 < (shifted k m (by omega) n : ℕ) ∧ (shifted k m (by omega) n : ℕ) < m := by
  have := (word k n).2
  simp only [shifted]
  omega

/-- **`ξ_{k,m}` is uniquely represented.** In every base with `β² = mβ + 1`,
`m ≥ 4`, the stream `w + 1` is the only expansion of its value over the full
alphabet `{0, …, m}`, the value lies in `(β⁻¹, 1)`, and the stream is not
eventually periodic. -/
theorem xi_unique (k m : ℕ) (hk : 1 ≤ k) (hm : 4 ≤ m) (B : Psc.BetaMetallicUnique.Base m) :
    B.IsUnique (shifted k m (by omega)) ∧ B.r < B.value (shifted k m (by omega)) ∧
      B.value (shifted k m (by omega)) < 1 ∧
      ¬ EventuallyPeriodic (shifted k m (by omega)) :=
  let h := Psc.BetaMetallicUnique.Base.interior (B := B) (shifted_interior k m hm)
  ⟨h.1, h.2.1, h.2.2, shifted_not_eventuallyPeriodic k m hk (by omega)⟩

end Psc.BetaFamilyFixedWord
