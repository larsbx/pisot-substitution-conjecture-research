import PscVerif.BetaFamilyFixedWord
import Mathlib.Data.Set.Card

/-!
# Linear factor complexity of the fixed word of `σ_k²`

For `k ≥ 1` the fixed word `w` of `σ_k²` beginning at `0` has at most
`27 (k² + 2)² n` distinct factors of each length `n ≥ 1`. The same bound holds
for the coded stream `w + 1`.

The argument is the standard one for primitive substitutions, made elementary
by the explicit square of the incidence matrix. Write `ℓ_J(a) = |σ^{2J}(a)|` and
`S_J = Σ_a ℓ_J(a)`. Every entry of `M²` lies in `[1, k² + 2]`, hence
`S_J ≤ ℓ_{J+1}(a) ≤ (k² + 2) S_J`. Choose the least `j` with `n ≤ S_j` and put
`J = j + 1`. Every level-`J` block of `w = σ^{2J}(w)` then has length at least
`n` and at most `3 (k² + 2)² n`, so a factor of length `n` starts inside some
block `σ^{2J}(a)` and ends inside the next one. It is therefore determined by
the two letters `a b` and an offset smaller than `|σ^{2J}(a)|`.

Not proved here: greedy admissibility, a Pisot statement for the metallic
bases, or any transcendence statement. Source decision:
`docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.BetaFamilyComplexity

open Psc.Binomial (subst)
open Psc.ParameterFamilyRows (substitution)
open Psc.BetaFamilyFixedWord

/-! ## Factors and complexity -/

/-- The factor of length `n` at position `s`. -/
def factor {β : Type*} (x : ℕ → β) (s n : ℕ) : List β := List.ofFn fun t : Fin n => x (s + t)

/-- The set of factors of length `n`. -/
def factors {β : Type*} (x : ℕ → β) (n : ℕ) : Set (List β) := Set.range fun s => factor x s n

/-! ## Level-`J` blocks -/

/-- `σ^{2J}`. -/
def it (k J : ℕ) : List (Fin 3) → List (Fin 3) := (subst (substitution k))^[2 * J]

/-- `ℓ_J(a) = |σ^{2J}(a)|`. -/
def blockLen (k J : ℕ) (a : Fin 3) : ℕ := (it k J [a]).length

/-- `S_J = Σ_a ℓ_J(a)`. -/
def total (k J : ℕ) : ℕ := ∑ a, blockLen k J a

theorem it_append (k J : ℕ) (x y : List (Fin 3)) : it k J (x ++ y) = it k J x ++ it k J y :=
  Psc.Binomial.iterate_subst_append _ _ _ _

theorem it_nil (k J : ℕ) : it k J [] = [] := Psc.Binomial.iterate_subst_nil _ _

theorem it_succ (k J : ℕ) (u : List (Fin 3)) :
    it k (J + 1) u = it k J ((subst (substitution k))^[2] u) := by
  unfold it
  rw [show 2 * (J + 1) = 2 * J + 2 by ring, Function.iterate_add_apply]

theorem it_succ_outer (k J : ℕ) (u : List (Fin 3)) :
    it k (J + 1) u = (subst (substitution k))^[2] (it k J u) := by
  unfold it
  rw [show 2 * (J + 1) = 2 + 2 * J by ring, Function.iterate_add_apply]

theorem length_it (k J : ℕ) (u : List (Fin 3)) :
    (it k J u).length = ∑ c, u.count c * blockLen k J c := by
  induction u with
  | nil => simp [it_nil]
  | cons a u ih =>
    rw [show a :: u = [a] ++ u from rfl, it_append, List.length_append, ih]
    simp only [List.singleton_append, List.count_cons, beq_iff_eq, add_mul,
      Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    simp [blockLen]

theorem blockLen_zero (k : ℕ) (a : Fin 3) : blockLen k 0 a = 1 := rfl

theorem total_zero (k : ℕ) : total k 0 = 3 := rfl

theorem blockLen_succ (k J : ℕ) (a : Fin 3) :
    blockLen k (J + 1) a =
      ∑ c, (Psc.Incidence.inc (substitution k) ^ 2) c a * blockLen k J c := by
  rw [blockLen, it_succ, length_it]
  exact Finset.sum_congr rfl fun c _ => by rw [Psc.Incidence.count_iterate_subst]

/-- The constant `E = k² + 2`, the largest entry of `M²`. -/
def E (k : ℕ) : ℕ := k ^ 2 + 2

theorem entry_bounds (k : ℕ) (hk : 1 ≤ k) (c a : Fin 3) :
    1 ≤ (Psc.Incidence.inc (substitution k) ^ 2) c a ∧
      (Psc.Incidence.inc (substitution k) ^ 2) c a ≤ E k := by
  rw [Psc.ParameterFamilyPisot.incidence_sq]
  have : k ≤ k ^ 2 := by nlinarith
  fin_cases c <;> fin_cases a <;> simp [E] <;> omega

theorem total_le_blockLen (k J : ℕ) (hk : 1 ≤ k) (a : Fin 3) :
    total k J ≤ blockLen k (J + 1) a := by
  rw [blockLen_succ, total]
  exact Finset.sum_le_sum fun c _ =>
    Nat.le_mul_of_pos_left _ (entry_bounds k hk c a).1

theorem blockLen_le_total (k J : ℕ) (hk : 1 ≤ k) (a : Fin 3) :
    blockLen k (J + 1) a ≤ E k * total k J := by
  rw [blockLen_succ, total, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ =>
    Nat.mul_le_mul_right _ (entry_bounds k hk c a).2

theorem total_succ_le (k J : ℕ) (hk : 1 ≤ k) : total k (J + 1) ≤ 3 * E k * total k J := by
  have h := fun a => blockLen_le_total k J hk a
  unfold total at *
  simp only [Fin.sum_univ_three] at *
  linarith [h 0, h 1, h 2]

theorem blockLen_pos (k J : ℕ) (a : Fin 3) : 0 < blockLen k J a :=
  List.length_pos_of_ne_nil
    (Psc.FixedPointLimit.iterate_subst_ne_nil _ (substitution_ne_nil k) _ (by simp))

theorem le_total (k J : ℕ) (hk : 1 ≤ k) : J ≤ total k J := by
  induction J with
  | zero => exact Nat.zero_le _
  | succ J ih =>
    have h0 := total_le_blockLen k J hk 0
    have h1 := blockLen_pos k (J + 1) 1
    have h2 := blockLen_pos k (J + 1) 2
    have e : total k (J + 1) =
        blockLen k (J + 1) 0 + blockLen k (J + 1) 1 + blockLen k (J + 1) 2 := by
      simp [total, Fin.sum_univ_three]
    omega

/-! ## Block positions in the fixed word -/

/-- `σ^{2J}` of a prefix of `w` is the prefix of `w` of its length. -/
theorem pref_it (k J L : ℕ) : pref k (it k J (pref k L)).length = it k J (pref k L) := by
  induction J with
  | zero =>
    simp only [it, Nat.mul_zero, Function.iterate_zero, id_eq]
    rw [show (pref k L).length = L from List.length_ofFn]
  | succ J ih =>
    have h := word_fixed k (it k J (pref k L)).length
    rw [ih] at h
    rw [it_succ_outer]
    exact h

/-- Start of the `i`-th level-`J` block. -/
noncomputable def pos (k J i : ℕ) : ℕ := (it k J (pref k i)).length

theorem pos_zero (k J : ℕ) : pos k J 0 = 0 := by
  simp [pos, pref, it_nil]

theorem pos_succ (k J i : ℕ) : pos k J (i + 1) = pos k J i + blockLen k J (word k i) := by
  rw [pos, pref_succ, it_append, List.length_append]
  rfl

theorem le_pos (k J i : ℕ) : i ≤ pos k J i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih => rw [pos_succ]; have := blockLen_pos k J (word k i); omega

theorem exists_block (k J s : ℕ) : ∃ i, pos k J i ≤ s ∧ s < pos k J (i + 1) := by
  have hex : ∃ i, s < pos k J (i + 1) := ⟨s, Nat.lt_of_lt_of_le (Nat.lt_succ_self s) (le_pos _ _ _)⟩
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | i
  · rw [pos_zero]; exact Nat.zero_le _
  · have := Nat.find_min hex (show i < Nat.find hex by omega)
    omega

theorem word_eq_get (k L x : ℕ) (hx : x < L) : (pref k L)[x]? = some (word k x) := by
  simp [pref, hx]

/-- A factor no longer than the next block lies in two consecutive blocks. -/
theorem factor_in_blocks (k J n : ℕ) (hn : ∀ b, n ≤ blockLen k J b) (s : ℕ) :
    ∃ a b : Fin 3, ∃ o < blockLen k J a,
      factor (word k) s n = ((it k J [a, b]).drop o).take n := by
  obtain ⟨i, hi, hs⟩ := exists_block k J s
  refine ⟨word k i, word k (i + 1), s - pos k J i, ?_, ?_⟩
  · rw [pos_succ] at hs; omega
  · have hsplit : it k J (pref k (i + 2)) = it k J (pref k i) ++ it k J [word k i, word k (i + 1)] := by
      rw [show i + 2 = i + 1 + 1 by rfl, pref_succ, pref_succ, List.append_assoc, it_append]
      rfl
    have hend : pos k J (i + 2) = pos k J (i + 1) + blockLen k J (word k (i + 1)) := pos_succ _ _ _
    apply List.ext_getElem?
    intro t
    simp only [factor, List.getElem?_ofFn, List.getElem?_take, List.getElem?_drop]
    by_cases ht : t < n
    · simp only [ht, ↓reduceDIte, ↓reduceIte]
      have hlt : s + t < pos k J (i + 2) := by
        have := hn (word k (i + 1)); omega
      have hp : (it k J (pref k i)).length = pos k J i := rfl
      have hP : pref k (pos k J (i + 2)) =
          it k J (pref k i) ++ it k J [word k i, word k (i + 1)] := by
        unfold pos; rw [pref_it, hsplit]
      rw [← word_eq_get k _ _ hlt, hP, List.getElem?_append_right (by rw [hp]; omega), hp]
      congr 1
      omega
    · simp [ht]

/-! ## The bound -/

/-- **Linear factor complexity.** For `k ≥ 1` and `n ≥ 1`, the fixed word of `σ_k²`
has finitely many factors of length `n`, at most `27 (k² + 2)² n`. -/
theorem factors_finite_and_linear (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    (factors (word k) n).Finite ∧ (factors (word k) n).ncard ≤ 27 * E k ^ 2 * n := by
  classical
  have hex : ∃ j, n ≤ total k j := ⟨n, le_total k n hk⟩
  set j := Nat.find hex
  have hj : n ≤ total k j := Nat.find_spec hex
  have hE : 1 ≤ E k := by unfold E; omega
  -- `S_j ≤ 3 E n`.
  have hS : total k j ≤ 3 * E k * n := by
    rcases h : j with _ | j'
    · rw [total_zero]; nlinarith
    · have hmin : total k j' < n := by
        have := Nat.find_min hex (show j' < j by omega)
        omega
      have := total_succ_le k j' hk
      rw [← h] at this ⊢
      calc total k j ≤ 3 * E k * total k j' := by rw [h]; exact total_succ_le k j' hk
        _ ≤ 3 * E k * n := Nat.mul_le_mul_left _ hmin.le
  set Lb := 3 * E k ^ 2 * n
  have hlen : ∀ a, blockLen k (j + 1) a ≤ Lb := fun a => by
    have := blockLen_le_total k j hk a
    calc blockLen k (j + 1) a ≤ E k * total k j := this
      _ ≤ E k * (3 * E k * n) := Nat.mul_le_mul_left _ hS
      _ = Lb := by ring
  have hlong : ∀ b, n ≤ blockLen k (j + 1) b := fun b => hj.trans (total_le_blockLen k j hk b)
  let g : Fin 3 × Fin 3 × Fin Lb → List (Fin 3) :=
    fun x => ((it k (j + 1) [x.1, x.2.1]).drop x.2.2).take n
  have hsub : factors (word k) n ⊆ ↑(Finset.univ.image g) := by
    rintro u ⟨s, rfl⟩
    obtain ⟨a, b, o, ho, he⟩ := factor_in_blocks k (j + 1) n hlong s
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨(a, b, ⟨o, lt_of_lt_of_le ho (hlen a)⟩), he.symm⟩
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc (factors (word k) n).ncard ≤ (↑(Finset.univ.image g) : Set (List (Fin 3))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.univ.image g).card := Set.ncard_coe_finset _
    _ ≤ (Finset.univ : Finset (Fin 3 × Fin 3 × Fin Lb)).card := Finset.card_image_le
    _ = 27 * E k ^ 2 * n := by simp [Lb]; ring

/-- The same bound for the coded stream `w + 1` over `{0, …, m}`. -/
theorem shifted_factors_linear (k m : ℕ) (hk : 1 ≤ k) (hm : 3 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    (factors (shifted k m hm) n).Finite ∧
      (factors (shifted k m hm) n).ncard ≤ 27 * E k ^ 2 * n := by
  obtain ⟨hfin, hcard⟩ := factors_finite_and_linear k hk n hn
  have himg : factors (shifted k m hm) n = List.map (fun a : Fin 3 =>
      (⟨(a : ℕ) + 1, by have := a.2; omega⟩ : Fin (m + 1))) '' factors (word k) n := by
    ext u
    simp only [factors, Set.mem_range, Set.mem_image, exists_exists_eq_and]
    constructor <;> rintro ⟨s, rfl⟩ <;> exact ⟨s, by simp [factor, shifted, List.map_ofFn]; rfl⟩
  rw [himg]
  exact ⟨hfin.image _, (Set.ncard_image_le hfin).trans hcard⟩

end Psc.BetaFamilyComplexity
