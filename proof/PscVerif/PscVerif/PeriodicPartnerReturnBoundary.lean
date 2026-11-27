/- Signed return-word counts on an original seam cycle. -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Fintype.Basic

public section

namespace Psc.PeriodicPartnerReturnBoundary

open scoped BigOperators

/-- The weighted sum of the central return patches. Missing seams have weight zero. -/
def seamSum {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (w : I → J → ℤ) (patch : I → J → A) : A :=
  ∑ i, ∑ j, w i j • patch i j

private theorem seamSum_congr {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (w : I → J → ℤ) {x y : I → J → A}
    (h : ∀ i j, w i j ≠ 0 → x i j = y i j) : seamSum w x = seamSum w y := by
  unfold seamSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hw : w i j = 0
  · simp [hw]
  · rw [h i j hw]

private theorem seamSum_add {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (w : I → J → ℤ) (x y : I → J → A) :
    seamSum w (fun i j => x i j + y i j) = seamSum w x + seamSum w y := by
  simp only [seamSum, smul_add, Finset.sum_add_distrib]

private theorem map_seamSum {I J A B : Type*} [Fintype I] [Fintype J]
    [AddCommGroup A] [AddCommGroup B] (read : A →+ B) (w : I → J → ℤ) (x : I → J → A) :
    read (seamSum w x) = seamSum w (fun i j => read (x i j)) := by
  simp only [seamSum, map_sum, map_zsmul]

private theorem seamSum_side_terms_zero {I J A : Type*} [Fintype I] [Fintype J]
    [AddCommGroup A] (w : I → J → ℤ)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0)
    (left : I → A) (right : J → A) : seamSum w (fun i j => left i + right j) = 0 := by
  rw [seamSum_add]
  have hleft : seamSum w (fun i _ => left i) = 0 := by
    unfold seamSum
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_smul, hrow i, zero_smul]
  have hright : seamSum w (fun _ j => right j) = 0 := by
    unfold seamSum
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_smul, hcol j, zero_smul]
  rw [hleft, hright, add_zero]

/-- Inflating a seam patch adds a left and a right pad. Their contributions
cancel on a balanced seam cycle, so its signed return count is fixed. -/
theorem seam_sum_fixed_of_side_padding {I J A : Type*} [Fintype I] [Fintype J]
    [AddCommGroup A] (w : I → J → ℤ)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0)
    (x : I → J → A) (step : A →+ A) (left : I → A) (right : J → A)
    (hpad : ∀ i j, w i j ≠ 0 → step (x i j) = left i + x i j + right j) :
    step (seamSum w x) = seamSum w x := by
  have h (i j) (hw : w i j ≠ 0) : step (x i j) = x i j + (left i + right j) := by
    rw [hpad i j hw]
    ac_rfl
  rw [map_seamSum, seamSum_congr w h, seamSum_add, seamSum_side_terms_zero w hrow hcol, add_zero]

/-- Flattening to original letter counts kills the cycle when each flattened
patch is the concatenation of its original left and right ray pieces. -/
theorem seam_sum_map_zero_of_side_terms {I J A B : Type*} [Fintype I] [Fintype J]
    [AddCommGroup A] [AddCommGroup B] (w : I → J → ℤ)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0)
    (x : I → J → A) (read : A →+ B) (left : I → B) (right : J → B)
    (hside : ∀ i j, w i j ≠ 0 → read (x i j) = left i + right j) :
    read (seamSum w x) = 0 := by
  rw [map_seamSum, seamSum_congr w hside, seamSum_side_terms_zero w hrow hcol]

/-- A readout made of side terms and a specified seam contribution
recovers the latter multiplied by that edge's cycle coefficient. -/
theorem seam_sum_readout_eq_marker_mul {I J A : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [AddCommGroup A] (w : I → J → ℤ)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0)
    (x : I → J → A) (read : A →+ ℤ) (left : I → ℤ) (right : J → ℤ)
    (a : I) (b : J) (value : ℤ)
    (hread : ∀ i j, w i j ≠ 0 →
      read (x i j) = (left i + right j) + if i = a ∧ j = b then value else 0) :
    read (seamSum w x) = w a b * value := by
  rw [map_seamSum, seamSum_congr w hread, seamSum_add, seamSum_side_terms_zero w hrow hcol, zero_add]
  simp only [seamSum, Int.zsmul_eq_mul, mul_ite, mul_zero, ite_and]
  simp

private theorem grouped_value_eq_side_terms_add_marker (diagonal offDiagonal : ℤ) (i j : Bool) :
    (if i = j then diagonal else offDiagonal) =
      ((if i = false then -(diagonal - offDiagonal) else 0) +
        (if j = false then offDiagonal else diagonal)) +
        (if i = false ∧ j = false then 2 * (diagonal - offDiagonal) else 0) := by
  cases i <;> cases j <;> simp
  omega

/-- When the zero groups are singletons, the exact joint term of the
quotient count, up to side terms, is twice the winding at their seam. -/
theorem grouped_seam_marked_count {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (w : I → J → ℤ)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0)
    (p : I → Bool) (q : J → Bool) (a : I) (b : J)
    (hp : ∀ i, p i = false ↔ i = a) (hq : ∀ j, q j = false ↔ j = b)
    (diagonal offDiagonal : ℤ) :
    seamSum w (fun i j => if p i = q j then diagonal else offDiagonal) =
      w a b * (2 * (diagonal - offDiagonal)) := by
  let left (i : I) := if i = a then -(diagonal - offDiagonal) else 0
  let right (j : J) := if j = b then offDiagonal else diagonal
  apply seam_sum_readout_eq_marker_mul w hrow hcol _ (AddMonoidHom.id ℤ) left right a b
  intro i j _
  simpa only [AddMonoidHom.id_apply, hp, hq, left, right] using
    grouped_value_eq_side_terms_add_marker diagonal offDiagonal (p i) (q j)

/-- On a unit cycle, odd winding gives the exact residue two modulo four. -/
theorem grouped_seam_marked_count_mod_four {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (w : I → J → ℤ)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0)
    (p : I → Bool) (q : J → Bool) (a : I) (b : J)
    (hp : ∀ i, p i = false ↔ i = a) (hq : ∀ j, q j = false ↔ j = b)
    (diagonal offDiagonal : ℤ) (hunit : w a b = 1) (hodd : (diagonal - offDiagonal) % 2 = 1) :
    seamSum w (fun i j => if p i = q j then diagonal else offDiagonal) % 4 = 2 := by
  rw [grouped_seam_marked_count w hrow hcol p q a b hp hq, hunit, one_mul]
  omega

/-- Count changes of sheet owner starting at the specified vertex. -/
def sheetChanges (start : Bool) : List Bool → ℕ
  | [] => 0
  | b :: bs => (if start = b then 0 else 1) + sheetChanges b bs

private theorem sheetChanges_same_run (b c : Bool) (n : ℕ) :
    sheetChanges b (List.replicate n b ++ [c]) = if b = c then 0 else 1 := by
  induction n with
  | zero => simp [sheetChanges]
  | succ n ih => simp [List.replicate_succ, sheetChanges, ih]

/-- At the two ends of a first-sheet tile, the owner is the first sheet.
Every strictly interior vertex belongs to its twin. The resulting number of
marked tiles is two exactly when there is a twin vertex. -/
theorem marks_crossing_stack_tile (n : ℕ) :
    sheetChanges false (List.replicate n true ++ [false]) = if n = 0 then 0 else 2 := by
  cases n with
  | zero => simp [sheetChanges]
  | succ n => simp [List.replicate_succ, sheetChanges, sheetChanges_same_run]

/-- The four central return words to `0.0` in the Thue–Morse square give
a fixed signed return vector with zero original counts and total count one. -/
theorem thue_morse_marker_return_control :
    let s : Bool → List Bool := fun a => [a, !a, !a, a]
    let blocks : Fin 4 → List Bool := fun i =>
      match i.val with
      | 0 => [false, true, false, true, true, false]
      | 1 => [false, true, true, false, true, false]
      | 2 => [false, true, true, false]
      | _ => [false, true, false, true, true, false, true, false]
    let derived : Fin 4 → List (Fin 4) := fun i =>
      match i.val with
      | 0 => [1, 3, 2, 0]
      | 1 => [1, 2, 3, 0]
      | 2 => [1, 2, 0]
      | _ => [1, 3, 2, 3, 0]
    let positive : List (Fin 4) := [0, 1, 2]
    let negative : List (Fin 4) := [3, 3]
    ((s false).flatMap s).drop 10 = blocks 0 ∧
    ((s false).flatMap s).take 6 = blocks 1 ∧
    (s true).drop 2 ++ (s true).take 2 = blocks 2 ∧
    blocks 0 ++ (s true).take 2 = blocks 3 ∧ (s true).drop 2 ++ blocks 1 = blocks 3 ∧
    (∀ i : Fin 4, (blocks i).flatMap s = (derived i).flatMap blocks ∧
      (blocks i).head? = some false ∧ (blocks i).getLast? = some false ∧
      ((blocks i).zip (blocks i).tail).all (fun pair => pair != (false, false)) = true) ∧
    (∀ i : Fin 4, ((positive.flatMap derived).count i : ℤ) - (negative.flatMap derived).count i =
      (positive.count i : ℤ) - negative.count i) ∧
    (∀ a : Bool, (positive.flatMap blocks).count a = (negative.flatMap blocks).count a) ∧
    (positive.length : ℤ) - negative.length = 1 := by
  decide

end Psc.PeriodicPartnerReturnBoundary
