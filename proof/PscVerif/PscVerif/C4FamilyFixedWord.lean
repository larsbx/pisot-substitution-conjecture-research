import PscVerif.C4ParameterFamilyPisot
import PscVerif.Incidence
import PscVerif.WordComplexity
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Data.List.GetD
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The fixed word of `σ_k²` from `0`: aperiodicity and linear complexity

For the literal family `σ_k = (0 ↦ 1, 1 ↦ 0 1^k 2, 2 ↦ 0 0 1)` put `τ = σ_k²`.
Since `τ(0) = 0 1^k 2` begins with `0`, the words `τʲ(0)` form a prefix chain and
define the one-sided fixed word `fixedWord k : ℕ → Fin 3`.

Proved here, for `k ≥ 1`:

* `fixedWord_eq`, `block_eq`: every prefix of `fixedWord k` is read off a literal
  iterate `τʲ(0)`;
* `not_eventuallyPeriodic`: `fixedWord k` is not eventually periodic;
* `frequently_linear`: `p(n) ≤ 12 (k² + 2k + 4) n` for infinitely many `n`.

**Aperiodicity.** For an eventually periodic word the discrepancies
`p · |u_{[0,N)}|_a - N c_a` take finitely many values. Along `N = |τʲ(0)|` the
Parikh vectors are the columns `A^j e₀` of `A = M_σ²`, which obey
`A³ = (k²+4) A² + (4k-4) A + 4` (`charpoly_identity`). Pigeonhole then makes the
difference vectors parallel to the period vector; either two prefix lengths
coincide, contradicting strict growth, or `A` has a rational eigenvalue, a rational
root of `x³ - (k²+4) x² - (4k-4) x - 4`, of which there is none (`no_rational_root`).
No frequency limit or Perron–Frobenius convergence is used.

**Complexity.** A factor of length `n = min_a |τ^{j+1}(a)|` starts inside some
block `τ^{j+1}(a)` of the decomposition of a long prefix and ends in the next one
(`Psc.WordComplexity.window_flatten`), so it is fixed by the two letters and an
offset below `max_a |τ^{j+1}(a)| ≤ (k²+2k+4) n` (`len_le`).
Source decision: `docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.ParameterFamilyFixedWord

open Psc.Binomial (subst power subst_power subst_prefix)
open Psc.Incidence (inc count_iterate_subst subst_cons)
open Psc.ParameterFamilyRows (substitution)
open Psc.WordComplexity
open Matrix Polynomial

variable (k : ℕ)

/-- `τ = σ_k²` acting on words. -/
def tau (w : List (Fin 3)) : List (Fin 3) := (subst (substitution k))^[2] w

/-- The literal iterate `τʲ(0) = σ_k^{2j}(0)`. -/
def iter (j : ℕ) : List (Fin 3) := (subst (substitution k))^[2 * j] [0]

/-- `|τʲ(a)|`. -/
def len (j : ℕ) (a : Fin 3) : ℕ := (power (substitution k) (2 * j) a).length

/-- The largest image length `|τ(1)| = k² + 2k + 4`. -/
def L : ℕ := k ^ 2 + 2 * k + 4

/-! ## Letter images of `τ` -/

theorem tau_zero : tau k [0] = [0] ++ Psc.ParameterFamilyWords.ones k ++ [2] := by
  show subst (substitution k) (subst (substitution k) [0]) = _
  simp [Psc.Binomial.subst, substitution]

/-- Letter counts of `τ(a)` are the entries of the squared incidence matrix. -/
theorem count_tau (a b : Fin 3) :
    (tau k [a]).count b = (!![1, k + 2, 1; k, k ^ 2 + 2, k + 2; 1, k, 1] : Matrix (Fin 3) (Fin 3) ℕ) b a := by
  rw [tau, count_iterate_subst, Psc.ParameterFamilyPisot.incidence_sq]

theorem length_eq_counts (w : List (Fin 3)) : w.length = w.count 0 + w.count 1 + w.count 2 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    fin_cases x <;> simp [List.count_cons, ih] <;> omega

theorem length_tau (a : Fin 3) :
    (tau k [a]).length = (![k + 2, k ^ 2 + 2 * k + 4, k + 4] : Fin 3 → ℕ) a := by
  rw [length_eq_counts, count_tau, count_tau, count_tau]
  fin_cases a <;> simp <;> ring

theorem two_le_length_tau (a : Fin 3) : 2 ≤ (tau k [a]).length := by
  rw [length_tau]; fin_cases a <;> simp <;> nlinarith

theorem length_tau_le (a : Fin 3) : (tau k [a]).length ≤ L k := by
  rw [length_tau, L]; fin_cases a <;> simp <;> nlinarith

theorem mem_tau (hk : 1 ≤ k) (a b : Fin 3) : b ∈ tau k [a] := by
  apply List.count_pos_iff.mp
  rw [count_tau]
  fin_cases a <;> fin_cases b <;> simp <;> first | omega | positivity | nlinarith

/-! ## Words under powers -/

theorem tau_eq_subst (w : List (Fin 3)) : tau k w = subst (power (substitution k) 2) w := by
  show (subst (substitution k))^[2] w = _
  rw [subst_power]

theorem length_le_length_subst (P : Fin 3 → List (Fin 3)) {w : List (Fin 3)} {b : Fin 3}
    (hb : b ∈ w) : (P b).length ≤ (subst P w).length := by
  induction w with
  | nil => simp at hb
  | cons c w ih =>
    rw [subst_cons, List.length_append]
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · have := ih hb; omega

theorem length_subst_le (P : Fin 3 → List (Fin 3)) (w : List (Fin 3)) (K : ℕ)
    (hK : ∀ c ∈ w, (P c).length ≤ K) : (subst P w).length ≤ w.length * K := by
  induction w with
  | nil => simp [Psc.Binomial.subst]
  | cons c w ih =>
    rw [subst_cons, List.length_append, List.length_cons]
    have h1 := hK c List.mem_cons_self
    have h2 := ih fun x hx => hK x (List.mem_cons_of_mem _ hx)
    nlinarith

theorem two_mul_length_le (w : List (Fin 3)) : 2 * w.length ≤ (tau k w).length := by
  rw [tau_eq_subst]
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [subst_cons, List.length_append, List.length_cons]
    have h2 : 2 ≤ (power (substitution k) 2 c).length := two_le_length_tau k c
    omega

/-! ## The prefix chain and the fixed word -/

theorem iter_succ (j : ℕ) : iter k (j + 1) = tau k (iter k j) := by
  unfold iter tau
  rw [show 2 * (j + 1) = 2 + 2 * j by ring, Function.iterate_add_apply]

theorem tau_prefix {x y : List (Fin 3)} (h : x <+: y) : tau k x <+: tau k y :=
  subst_prefix _ (subst_prefix _ h)

theorem iter_prefix_succ (j : ℕ) : iter k j <+: iter k (j + 1) := by
  induction j with
  | zero =>
    rw [iter_succ]
    show [0] <+: tau k [0]
    rw [tau_zero, List.append_assoc]
    exact List.prefix_append _ _
  | succ j ih =>
    have h := tau_prefix k ih
    rwa [← iter_succ, ← iter_succ] at h

theorem iter_prefix {j J : ℕ} (h : j ≤ J) : iter k j <+: iter k J := by
  induction J, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ J _ ih => exact ih.trans (iter_prefix_succ k J)

theorem length_iter_pos (j : ℕ) : 0 < (iter k j).length := by
  induction j with
  | zero => simp [iter]
  | succ j ih => rw [iter_succ]; have := two_mul_length_le k (iter k j); omega

theorem length_iter_lt (j : ℕ) : (iter k j).length < (iter k (j + 1)).length := by
  rw [iter_succ]
  have h := two_mul_length_le k (iter k j)
  have hpos := length_iter_pos k j
  omega

theorem length_iter_strictMono : StrictMono fun j => (iter k j).length :=
  strictMono_nat_of_lt_succ (length_iter_lt k)

theorem le_length_iter (j : ℕ) : j + 1 ≤ (iter k j).length := by
  induction j with
  | zero => simp [iter]
  | succ j ih => have := length_iter_lt k j; omega

/-- The one-sided fixed word of `τ` starting at `0`. -/
def fixedWord (i : ℕ) : Fin 3 := (iter k (i + 1)).getD i 0

theorem fixedWord_eq (J i : ℕ) (h : i < (iter k J).length) :
    fixedWord k i = (iter k J)[i] := by
  have h1 : i < (iter k (i + 1)).length := by have := le_length_iter k (i + 1); omega
  rw [fixedWord, List.getD_eq_getElem _ _ h1]
  rcases le_total (i + 1) J with hle | hle
  · exact (iter_prefix k hle).getElem h1
  · exact ((iter_prefix k hle).getElem h).symm

theorem block_eq (J i n : ℕ) (h : i + n ≤ (iter k J).length) :
    block (fixedWord k) i n = ((iter k J).drop i).take n := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [getElem_block, List.getElem_take, List.getElem_drop]
  exact fixedWord_eq k J (i + j) (by simp at h1; omega)

theorem block_zero_iter (j : ℕ) : block (fixedWord k) 0 (iter k j).length = iter k j := by
  rw [block_eq k j 0 (iter k j).length (by simp)]
  simp

/-! ## Linear complexity along a subsequence -/

theorem iter_split (j t : ℕ) :
    iter k (j + t) = ((iter k t).map (power (substitution k) (2 * j))).flatten := by
  unfold iter
  rw [mul_add, Function.iterate_add_apply, ← subst_power (substitution k) (2 * j)]
  rfl

theorem power_succ (j : ℕ) (a : Fin 3) :
    power (substitution k) (2 * (j + 1)) a = subst (power (substitution k) (2 * j)) (tau k [a]) := by
  show (subst (substitution k))^[2 * (j + 1)] [a] =
    subst (power (substitution k) (2 * j)) ((subst (substitution k))^[2] [a])
  rw [subst_power, show 2 * (j + 1) = 2 * j + 2 by ring, Function.iterate_add_apply]

theorem power_succ' (j : ℕ) (a : Fin 3) :
    power (substitution k) (2 * (j + 1)) a = tau k (power (substitution k) (2 * j) a) := by
  show (subst (substitution k))^[2 * (j + 1)] [a] =
    (subst (substitution k))^[2] ((subst (substitution k))^[2 * j] [a])
  rw [show 2 * (j + 1) = 2 + 2 * j by ring, Function.iterate_add_apply]

theorem le_len (j : ℕ) (a : Fin 3) : j + 1 ≤ len k j a := by
  induction j with
  | zero => simp [len, power]
  | succ j ih =>
    unfold len at ih ⊢
    rw [power_succ']
    have := two_mul_length_le k (power (substitution k) (2 * j) a)
    omega

/-- Ratios of image lengths are bounded by `L`. -/
theorem len_le (hk : 1 ≤ k) (j : ℕ) (a b : Fin 3) : len k (j + 1) a ≤ L k * len k (j + 1) b := by
  unfold len
  rw [power_succ k j a]
  calc (subst (power (substitution k) (2 * j)) (tau k [a])).length
      ≤ (tau k [a]).length * (power (substitution k) (2 * (j + 1)) b).length := by
        apply length_subst_le
        intro c hc
        rw [power_succ k j b]
        exact length_le_length_subst _ (mem_tau k hk b c)
    _ ≤ L k * (power (substitution k) (2 * (j + 1)) b).length :=
        Nat.mul_le_mul_right _ (length_tau_le k a)

theorem complexity_le (hk : 1 ≤ k) (j : ℕ) (a₀ : Fin 3) (hmin : ∀ c, len k (j + 1) a₀ ≤ len k (j + 1) c) :
    complexity (fixedWord k) (len k (j + 1) a₀) ≤ 12 * (L k * len k (j + 1) a₀) := by
  set n := len k (j + 1) a₀ with hn
  set P := power (substitution k) (2 * (j + 1)) with hP
  set K := L k * n with hK
  let g : Fin 3 × Option (Fin 3) × Fin K → List (Fin 3) := fun x =>
    ((P x.1 ++ x.2.1.elim [] P).drop x.2.2).take n
  have hsub : Factors (fixedWord k) n ⊆ Set.range g := by
    rintro _ ⟨i, rfl⟩
    show block (fixedWord k) i n ∈ Set.range g
    have hlen := le_length_iter k ((j + 1) + (i + n))
    rw [block_eq k ((j + 1) + (i + n)) i n (by omega), iter_split k (j + 1) (i + n)]
    rw [iter_split k (j + 1) (i + n), ← hP] at hlen
    have hmem : ∀ w ∈ (iter k (i + n)).map P, n ≤ w.length := by
      intro w hw
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hw
      exact hmin c
    obtain ⟨w, hw, w', hw', o, ho, heq⟩ := window_flatten _ n hmem i (by omega)
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hw
    have hoK : o < K := lt_of_lt_of_le ho (len_le k hk j a a₀)
    rcases hw' with hw' | rfl
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hw'
      exact ⟨(a, some b, ⟨o, hoK⟩), heq.symm⟩
    · exact ⟨(a, none, ⟨o, hoK⟩), heq.symm⟩
  calc complexity (fixedWord k) n ≤ (Set.range g).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range g)
    _ ≤ Nat.card (Fin 3 × Option (Fin 3) × Fin K) := by
        rw [← Set.image_univ, ← Set.ncard_univ]
        exact Set.ncard_image_le Set.finite_univ
    _ = 12 * K := by
        rw [Nat.card_eq_fintype_card]
        simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
        ring

/-- `p(n) ≤ 12 L n` for infinitely many `n`. -/
theorem frequently_linear (hk : 1 ≤ k) :
    ∃ C : ℕ, ∀ N, ∃ n, N ≤ n ∧ complexity (fixedWord k) n ≤ C * n := by
  refine ⟨12 * L k, fun N => ?_⟩
  obtain ⟨a₀, ha₀⟩ := Finite.exists_min (len k (N + 1))
  refine ⟨len k (N + 1) a₀, by have := le_len k (N + 1) a₀; omega, ?_⟩
  have := complexity_le k hk N a₀ ha₀
  calc complexity (fixedWord k) (len k (N + 1) a₀) ≤ 12 * (L k * len k (N + 1) a₀) := this
    _ = 12 * L k * len k (N + 1) a₀ := by ring

/-! ## Parikh vectors along the prefix chain -/

/-- The squared incidence matrix over `ℚ`. -/
noncomputable def A : Matrix (Fin 3) (Fin 3) ℚ := (inc (substitution k) ^ 2).map (Nat.castRingHom ℚ)

theorem A_eq : A k = !![1, (k : ℚ) + 2, 1; (k : ℚ), (k : ℚ) ^ 2 + 2, (k : ℚ) + 2; 1, (k : ℚ), 1] := by
  rw [A, Psc.ParameterFamilyPisot.incidence_sq]
  ext a c
  fin_cases a <;> fin_cases c <;> simp

/-- Cayley–Hamilton for `A`, written as a three-term recurrence. -/
theorem charpoly_identity :
    A k ^ 3 = ((k : ℚ) ^ 2 + 4) • A k ^ 2 + (4 * (k : ℚ) - 4) • A k ^ 1 + (4 : ℚ) • A k ^ 0 := by
  rw [A_eq]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [pow_succ, pow_zero, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.add_apply, Matrix.smul_apply] <;> ring

/-- Column `0` of `A^j`: the Parikh vector of `τʲ(0)`. -/
noncomputable def x (j : ℕ) (a : Fin 3) : ℚ := (A k ^ j) a 0

theorem count_iter (j : ℕ) (a : Fin 3) : ((iter k j).count a : ℚ) = x k j a := by
  rw [iter, count_iterate_subst, pow_mul, x, A, ← Matrix.map_pow]
  simp

theorem length_iter (j : ℕ) : ((iter k j).length : ℚ) = x k j 0 + x k j 1 + x k j 2 := by
  rw [length_eq_counts]
  push_cast
  rw [count_iter, count_iter, count_iter]

theorem x_rec (j : ℕ) (a : Fin 3) :
    x k (j + 3) a = ((k : ℚ) ^ 2 + 4) * x k (j + 2) a + (4 * (k : ℚ) - 4) * x k (j + 1) a +
      4 * x k j a := by
  have h := congrArg (· * A k ^ j) (charpoly_identity k)
  simp only [add_mul, smul_mul_assoc, ← pow_add] at h
  have h' := congrFun (congrFun h a) 0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h'
  unfold x
  rw [show j + 3 = 3 + j by ring, show j + 2 = 2 + j by ring, show j + 1 = 1 + j by ring]
  simpa using h'

theorem x_succ (j : ℕ) (a : Fin 3) :
    x k (j + 1) a = A k a 0 * x k j 0 + A k a 1 * x k j 1 + A k a 2 * x k j 2 := by
  unfold x
  rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_three]

/-! ## No rational eigenvalue -/

/-- `x³ - (k²+4) x² - (4k-4) x - 4`, the characteristic polynomial of `A`. -/
noncomputable def gPoly : ℤ[X] := X ^ 3 - C ((k : ℤ) ^ 2 + 4) * X ^ 2 - C (4 * (k : ℤ) - 4) * X - C 4

theorem gPoly_monic : (gPoly k).Monic := by
  unfold gPoly
  monicity!

theorem aeval_gPoly {R : Type*} [CommRing R] [Algebra ℤ R] (z : R) :
    aeval z (gPoly k) = z ^ 3 - ((k : R) ^ 2 + 4) * z ^ 2 - (4 * (k : R) - 4) * z - 4 := by
  simp [gPoly, map_ofNat]

/-- A rational root would be an integer dividing four; each candidate fails. -/
theorem no_rational_root (hk : 1 ≤ k) (μ : ℚ) :
    μ ^ 3 - ((k : ℚ) ^ 2 + 4) * μ ^ 2 - (4 * (k : ℚ) - 4) * μ - 4 ≠ 0 := by
  intro hμ
  have hx' : aeval μ (gPoly k) = 0 := by rw [aeval_gPoly]; exact hμ
  obtain ⟨n, rfl, hn⟩ := exists_integer_of_is_root_of_monic (gPoly_monic k) hx'
  have hroot : n ^ 3 - ((k : ℤ) ^ 2 + 4) * n ^ 2 - (4 * (k : ℤ) - 4) * n - 4 = 0 := by
    rw [aeval_gPoly, algebraMap_int_eq, eq_intCast] at hx'
    exact_mod_cast hx'
  have hb : n.natAbs ≤ 4 := Nat.le_of_dvd (by norm_num)
    (show n.natAbs ∣ 4 by simpa [gPoly] using Int.natAbs_dvd_natAbs.mpr hn)
  have h1 : -4 ≤ n := by omega
  have h2 : n ≤ 4 := by omega
  have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
  interval_cases n <;> norm_num at hroot <;>
    nlinarith [sq_nonneg ((k : ℤ) - 1), sq_nonneg ((k : ℤ) - 2), sq_nonneg (2 * (k : ℤ) - 1)]

/-! ## Aperiodicity -/

/-- Along an eventually periodic word, letter counts grow by a fixed amount per period. -/
theorem count_block_add_period {u : ℕ → Fin 3} {q p : ℕ} (hu : ∀ n, q ≤ n → u (n + p) = u n)
    (a : Fin 3) (N : ℕ) (hN : q ≤ N) :
    (block u 0 (N + p)).count a + (block u 0 q).count a =
      (block u 0 N).count a + (block u 0 (q + p)).count a := by
  induction N, hN using Nat.le_induction with
  | base => ring
  | succ N hqN ih =>
    rw [show N + 1 + p = N + p + 1 by ring, block_succ, block_succ, List.count_append,
      List.count_append, zero_add, zero_add, hu N hqN]
    omega

theorem not_eventuallyPeriodic (hk : 1 ≤ k) : ¬ EventuallyPeriodic (fixedWord k) := by
  rintro ⟨q, p, hp, hu⟩
  let cnt : Fin 3 → ℕ → ℚ := fun a N => ((block (fixedWord k) 0 N).count a : ℚ)
  let c : Fin 3 → ℚ := fun a => cnt a (q + p) - cnt a q
  -- The discrepancy vector `p · count - N · c` is periodic beyond `q`.
  let D : ℕ → Fin 3 → ℚ := fun N a => (p : ℚ) * cnt a N - (N : ℚ) * c a
  have hDper : ∀ N, q ≤ N → D (N + p) = D N := by
    intro N hN
    funext a
    have h := count_block_add_period hu a N hN
    have h' : cnt a (N + p) + cnt a q = cnt a N + cnt a (q + p) := by
      simp only [cnt]; exact_mod_cast h
    simp only [D, c]
    push_cast
    linear_combination (p : ℚ) * h'
  have hres : ∀ N, q ≤ N → ∃ s : Fin p, D N = D (q + s) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro hN
      by_cases hlt : N < q + p
      · refine ⟨⟨N - q, by omega⟩, ?_⟩
        simp only [Fin.val_mk]
        congr 1
        omega
      · obtain ⟨s, hs⟩ := ih (N - p) (by omega) (by omega)
        refine ⟨s, ?_⟩
        rw [← hs, ← hDper (N - p) (by omega)]
        congr 1
        omega
  -- The same vector along the prefix lengths `|τʲ(0)|`.
  let y : ℕ → Fin 3 → ℚ := fun j a =>
    (p : ℚ) * x k j a - (x k j 0 + x k j 1 + x k j 2) * c a
  have hy : ∀ j, y j = D (iter k j).length := by
    intro j
    funext a
    simp only [y, D, cnt]
    rw [block_zero_iter, count_iter, length_iter]
  have hyrec : ∀ j a, y (j + 3) a = ((k : ℚ) ^ 2 + 4) * y (j + 2) a +
      (4 * (k : ℚ) - 4) * y (j + 1) a + 4 * y j a := by
    intro j a
    simp only [y, x_rec]
    ring
  -- Finitely many states: pigeonhole on consecutive triples.
  let R : Set ((Fin 3 → ℚ) × (Fin 3 → ℚ) × (Fin 3 → ℚ)) :=
    Set.range fun s : Fin p × Fin p × Fin p => (D (q + s.1), D (q + s.2.1), D (q + s.2.2))
  have hRfin : R.Finite := Set.finite_range _
  have hmemD : ∀ j, q ≤ j → ∃ s : Fin p, y j = D (q + s) := by
    intro j hj
    rw [hy]
    exact hres _ (by have := le_length_iter k j; omega)
  have hR : ∀ t, (y (q + t), y (q + t + 1), y (q + t + 2)) ∈ R := by
    intro t
    obtain ⟨s0, h0⟩ := hmemD (q + t) (by omega)
    obtain ⟨s1, h1⟩ := hmemD (q + t + 1) (by omega)
    obtain ⟨s2, h2⟩ := hmemD (q + t + 2) (by omega)
    exact ⟨(s0, s1, s2), by simp only [h0, h1, h2]⟩
  obtain ⟨t1, t2, ht, htrip⟩ := hRfin.exists_lt_map_eq_of_forall_mem
    (f := fun t => (y (q + t), y (q + t + 1), y (q + t + 2))) hR
  obtain ⟨P, rfl⟩ : ∃ P, t2 = t1 + P := ⟨t2 - t1, by omega⟩
  have hP : 0 < P := by omega
  simp only [Prod.mk.injEq] at htrip
  obtain ⟨e0, e1, e2⟩ := htrip
  -- The triples agree from `q + t1` on, hence so does `y`.
  have htriple : ∀ t, y (q + t1 + t) = y (q + t1 + P + t) ∧
      y (q + t1 + t + 1) = y (q + t1 + P + t + 1) ∧
      y (q + t1 + t + 2) = y (q + t1 + P + t + 2) := by
    intro t
    induction t with
    | zero =>
      simp only [Nat.add_zero]
      rw [show q + t1 + P = q + (t1 + P) by omega]
      exact ⟨e0, e1, e2⟩
    | succ t ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      funext a
      show y (q + t1 + t + 3) a = y (q + t1 + P + t + 3) a
      rw [hyrec, hyrec, ih.1, ih.2.1, ih.2.2]
  -- Difference vectors lie on the line through `c`.
  let w : ℕ → Fin 3 → ℚ := fun t a => x k (q + t1 + P + t) a - x k (q + t1 + t) a
  let S : ℕ → ℚ := fun t => w t 0 + w t 1 + w t 2
  have hline : ∀ t a, (p : ℚ) * w t a = S t * c a := by
    intro t a
    have h := congrFun (htriple t).1 a
    simp only [y] at h
    simp only [w, S]
    linear_combination -h
  have hwsucc : ∀ t a, w (t + 1) a = A k a 0 * w t 0 + A k a 1 * w t 1 + A k a 2 * w t 2 := by
    intro t a
    simp only [w]
    rw [show q + t1 + P + (t + 1) = q + t1 + P + t + 1 by ring,
      show q + t1 + (t + 1) = q + t1 + t + 1 by ring, x_succ, x_succ]
    ring
  have hwrec : ∀ a, w 3 a = ((k : ℚ) ^ 2 + 4) * w 2 a + (4 * (k : ℚ) - 4) * w 1 a + 4 * w 0 a := by
    intro a
    simp only [w, Nat.add_zero]
    rw [x_rec k (q + t1 + P) a, x_rec k (q + t1) a]
    ring
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  by_cases hS0 : S 0 = 0
  · -- Two prefix lengths coincide, contradicting strict growth.
    have hw0 : ∀ a, w 0 a = 0 := by
      intro a
      have h := hline 0 a
      rw [hS0, zero_mul] at h
      exact (mul_eq_zero.mp h).resolve_left hpq.ne'
    have hlen : ((iter k (q + t1 + P)).length : ℚ) = (iter k (q + t1)).length := by
      rw [length_iter, length_iter]
      have h0 := hw0 0
      have h1 := hw0 1
      have h2 := hw0 2
      simp only [w, Nat.add_zero] at h0 h1 h2
      linarith
    have hlt : (iter k (q + t1)).length < (iter k (q + t1 + P)).length :=
      length_iter_strictMono k (by omega)
    have hcast : (iter k (q + t1 + P)).length = (iter k (q + t1)).length := by
      exact_mod_cast hlen
    omega
  · -- Otherwise `A` has the rational eigenvalue `S 1 / S 0`.
    have hc : ∀ a, c a = (p : ℚ) * w 0 a / S 0 := by
      intro a
      rw [hline 0 a, mul_div_cancel_left₀ _ hS0]
    have hw1 : ∀ a, w 1 a = S 1 / S 0 * w 0 a := by
      intro a
      have h := hline 1 a
      rw [hc a] at h
      apply mul_left_cancel₀ hpq.ne'
      rw [h]
      ring
    have hw2 : ∀ a, w 2 a = (S 1 / S 0) ^ 2 * w 0 a := by
      intro a
      have e2 : w 2 a = A k a 0 * w 1 0 + A k a 1 * w 1 1 + A k a 2 * w 1 2 := hwsucc 1 a
      have e1 : w 1 a = A k a 0 * w 0 0 + A k a 1 * w 0 1 + A k a 2 * w 0 2 := hwsucc 0 a
      rw [hw1 a] at e1
      rw [e2, hw1 0, hw1 1, hw1 2]
      linear_combination (-(S 1 / S 0)) * e1
    have hw3 : ∀ a, w 3 a = (S 1 / S 0) ^ 3 * w 0 a := by
      intro a
      have e3 : w 3 a = A k a 0 * w 2 0 + A k a 1 * w 2 1 + A k a 2 * w 2 2 := hwsucc 2 a
      have e1 : w 1 a = A k a 0 * w 0 0 + A k a 1 * w 0 1 + A k a 2 * w 0 2 := hwsucc 0 a
      rw [hw1 a] at e1
      rw [e3, hw2 0, hw2 1, hw2 2]
      linear_combination (-(S 1 / S 0) ^ 2) * e1
    obtain ⟨a, ha⟩ : ∃ a, w 0 a ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hS0 (by simp only [S, hall]; ring)
    have hroot : ((S 1 / S 0) ^ 3 - ((k : ℚ) ^ 2 + 4) * (S 1 / S 0) ^ 2 -
        (4 * (k : ℚ) - 4) * (S 1 / S 0) - 4) * w 0 a = 0 := by
      have h := hwrec a
      rw [hw3, hw2, hw1] at h
      linear_combination h
    exact no_rational_root k hk _ ((mul_eq_zero.mp hroot).resolve_right ha)

end Psc.ParameterFamilyFixedWord
