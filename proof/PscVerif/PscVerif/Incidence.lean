/-
# The incidence matrix and the substitution formulas for scattered counts

`docs/c4-concentration-attack-2026-11-06.md` §3;
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, `thm:parikh` (letter
counts) and `lem:conc-subst` (i), (ii) at `r = 2, 3`.

This module is the single home of the incidence matrix of a substitution and of
the word-level formulas that the intertwiner modules (`PscVerif.ParikhIntertwiner`,
`PscVerif.Intertwiner2`, `PscVerif.Intertwiner3`, `PscVerif.PrimitiveExpansion`)
build on.  Words are lists over an alphabet `α` with decidable equality; a
substitution is any map `s : α → List α` (no primitivity, unimodularity, Pisot or
irreducibility hypothesis is used anywhere in this file).

Proved here, in full:

* `subst_cons`: `σ (c :: w) = s c ++ σ w`;
* `n3` (scattered count of `a b c`, `n3 (x :: t) a b c =
  (if x = a then n2 t b c else 0) + n3 t a b c`) and `n3_append`
  (`lem:conc-subst` (i), `r = 3`):
  `n3 (x ++ y) a b c = n3 x a b c + n3 y a b c + |x|_a · n2 y b c + n2 x a b · |y|_c`;
* `inc s a c = |s c|_a` (a `Matrix α α ℕ`) and, over a finite alphabet:
  - `count_subst` (Parikh identity): `|σ w|_a = Σ_c inc s a c · |w|_c`;
  - `count_iterate_subst`: `|σᵏ [c]|_a = (inc s ^ k) a c`;
  - `n2_subst` (`lem:conc-subst` (ii), `r = 2`):
    `n2 (σ w) a b = Σ_c Σ_d inc s a c · inc s b d · n2 w c d + Σ_c |w|_c · n2 (s c) a b`.
-/
import PscVerif.Binomial
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Psc.Incidence

open Psc.Binomial

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem subst_cons (s : α → List α) (c : α) (w : List α) :
    subst s (c :: w) = s c ++ subst s w := by simp [subst]

/-! ### The scattered count of a length-three word -/

/-- Scattered occurrences of the length-three word `a b c` in `w`. -/
def n3 : List α → α → α → α → ℕ
  | [], _, _, _ => 0
  | x :: t, a, b, c => (if x = a then n2 t b c else 0) + n3 t a b c

@[simp] theorem n3_nil (a b c : α) : n3 ([] : List α) a b c = 0 := rfl

theorem n3_cons (x : α) (t : List α) (a b c : α) :
    n3 (x :: t) a b c = (if x = a then n2 t b c else 0) + n3 t a b c := rfl

/-- **`lem:conc-subst` (i) at `r = 3`.** -/
theorem n3_append (x y : List α) (a b c : α) :
    n3 (x ++ y) a b c =
      n3 x a b c + n3 y a b c + x.count a * n2 y b c + n2 x a b * y.count c := by
  induction x with
  | nil => simp [n2]
  | cons d x ih =>
    simp only [List.cons_append, n3, ih, n2_append, n2, List.count_cons]
    by_cases h : d = a
    · subst h; simp only [ite_true, beq_self_eq_true]; ring
    · have h' : (d == a) = false := by simpa using h
      simp [h, h']

/-! ### The incidence matrix -/

/-- The incidence matrix of a substitution: `inc s a c = |s c|_a` (column `c` is
the Parikh vector of the image of `c`). -/
def inc (s : α → List α) : Matrix α α ℕ := Matrix.of fun a c => (s c).count a

@[simp] theorem inc_apply (s : α → List α) (a c : α) : inc s a c = (s c).count a := rfl

section Fintype

variable [Fintype α]

/-- The Parikh identity `|σ w|_a = Σ_c inc s a c · |w|_c`. -/
theorem count_subst (s : α → List α) (w : List α) (a : α) :
    (subst s w).count a = ∑ c, inc s a c * w.count c := by
  induction w with
  | nil => simp [subst]
  | cons c w ih =>
    rw [subst_cons, List.count_append, ih]
    simp only [List.count_cons, mul_add, Finset.sum_add_distrib, inc_apply]
    rw [add_comm]
    congr 1
    simp [beq_iff_eq]

/-- `|σᵏ [c]|_a = (inc s ^ k) a c`. -/
theorem count_iterate_subst (s : α → List α) (k : ℕ) (a c : α) :
    ((subst s)^[k] [c]).count a = (inc s ^ k) a c := by
  induction k generalizing a with
  | zero =>
    by_cases h : a = c
    · subst h; simp
    · simp [h, List.count_cons_of_ne (Ne.symm h)]
  | succ k ih =>
    rw [Function.iterate_succ_apply', count_subst, pow_succ', Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [ih b]

/-- **`lem:conc-subst` (ii) at `r = 2`.** -/
theorem n2_subst (s : α → List α) (w : List α) (a b : α) :
    n2 (subst s w) a b =
      (∑ c, ∑ d, inc s a c * inc s b d * n2 w c d) + ∑ c, w.count c * n2 (s c) a b := by
  induction w with
  | nil => simp [subst, n2]
  | cons c w ih =>
    rw [subst_cons, n2_append, ih, count_subst]
    simp only [n2, List.count_cons, mul_add, add_mul, Finset.sum_add_distrib]
    have e1 : (∑ x : α, ∑ y : α, inc s a x * inc s b y * (if c = x then w.count y else 0)) =
        inc s a c * ∑ y, inc s b y * w.count y := by
      rw [Finset.mul_sum, Finset.sum_eq_single c]
      · refine Finset.sum_congr rfl fun y _ => ?_
        simp; ring
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    have e2 : (∑ x : α, (if (c == x) = true then 1 else 0) * n2 (s x) a b) = n2 (s c) a b := by
      simp [beq_iff_eq]
    rw [e1, e2]
    simp only [inc_apply]
    ring

end Fintype

end Psc.Incidence
