import PscVerif.Intertwiner2
import PscVerif.Termination
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The finiteness premise cannot be removed from the generic closure route

The binary substitution `0 ↦ 00001`, `1 ↦ 011` has an immediate coincidence
from every noncoincident irreducible balanced block (coincident blocks are
productive at depth zero), but the actual swap-seed closure is infinite.
It is not Pisot: its incidence roots are `3 ± sqrt 2`.
The proof uses the existing degree-two defect, whose expansion factor is
seven, against the literal image-length bound five.
-/

namespace Psc.UniversalClosureReduction

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants Psc.Intertwiner2

abbrev Word := List (Fin 2)
abbrev Pair := Word × Word

def substitution : Fin 2 → Word
  | 0 => [0, 0, 0, 0, 1]
  | 1 => [0, 1, 1]

def seed : Pair := ([0, 1], [1, 0])

def defect (T : Pair) : ℤ := K2 T.1 T.2 0 1

theorem seed_isBlock : IsBlock seed := by
  unfold IsBlock seed
  decide +kernel

theorem seed_defect : defect seed = 1 := by decide +kernel

theorem image_has_initial_zero (a : Fin 2) : ∃ w, substitution a = 0 :: w := by
  fin_cases a <;> simp [substitution]

private theorem subst_has_initial_zero {w : Word} (hne : w ≠ []) :
    ∃ t, subst substitution w = 0 :: t := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨t, ht⟩ := image_has_initial_zero a
  exact ⟨t ++ subst substitution w, by simp [subst, ht]⟩

/-- Each noncoincident block has an immediate actual diagonal child. -/
theorem immediate_coincidence {T : Pair} (hT : IsBlock T) (hne : T.1 ≠ T.2) :
    ChildNC substitution T ([0], [0]) := by
  obtain ⟨u, hu⟩ := subst_has_initial_zero hT.1
  have hbot : T.2 ≠ [] := fun h => hT.1 <|
    List.length_eq_zero_iff.mp (by simpa [h] using hT.2.1.length_eq)
  obtain ⟨v, hv⟩ := subst_has_initial_zero hbot
  have hbal := equiv1_subst substitution hT.2.1
  have htail : Equiv1 u v := by
    apply equiv1_cancel (x := [0]) (y := [0]) (by intro a; rfl)
    simpa [hu, hv] using hbal
  refine ⟨hne, ?_⟩
  change ([0], [0]) ∈ red _ _
  rw [hu, hv]
  change ([0], [0]) ∈ red ([0] ++ u) ([0] ++ v)
  rw [red_append (by intro a; rfl) htail]
  apply List.mem_append_left
  rw [red_of_isBlock (by unfold IsBlock; decide +kernel : IsBlock (([0], [0]) : Pair))]
  exact List.mem_singleton_self _

/-- Productivity holds for every actual block, independently of reachability. -/
theorem all_blocks_productive {T : Pair} (hT : IsBlock T) :
    Psc.StrictSystem.Productive substitution T := by
  by_cases h : T.1 = T.2
  · exact ⟨T, .refl, h⟩
  · exact ⟨([0], [0]), Relation.ReflTransGen.single (immediate_coincidence hT h), rfl⟩

/-- The degree-two defect expands faster than any image length. -/
theorem defect_subst {u v : Word} (h : Equiv1 u v) :
    K2 (subst substitution u) (subst substitution v) 0 1 = 7 * K2 u v 0 1 := by
  rw [k2_subst substitution h]
  simp only [Fin.sum_univ_two]
  have h00 := k2_self h (0 : Fin 2)
  have h11 := k2_self h (1 : Fin 2)
  have h10 := k2_antisymm h (a := (1 : Fin 2)) (b := 0) (by decide)
  norm_num [inc, substitution, h00, h11, h10]
  ring

theorem image_length_le (a : Fin 2) : (substitution a).length ≤ 5 := by
  fin_cases a <;> decide

theorem subst_length_le (w : Word) : (subst substitution w).length ≤ 5 * w.length := by
  induction w with
  | nil => simp [subst]
  | cons a w ih =>
    have ha := image_length_le a
    simpa only [subst, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using Nat.add_le_add ha ih

private theorem defect_reduction {u v : Word} (h : Equiv1 u v) :
    (defect (u, v) : ℝ) = ((red u v).map fun T => (defect T : ℝ)).sum := by
  have hjoin := k2_join (red u v) (fun T hT => (red_isBlock h T hT).2.1) 0 1
  rw [red_top h.length_eq, red_bot h.length_eq] at hjoin
  simp only [defect]
  have hc := congrArg (fun z : ℤ => (z : ℝ)) hjoin
  simpa only [Int.cast_list_sum, List.map_map, Function.comp_def] using hc

private theorem abs_defect_le_of_rows (bs : List Pair) (r : ℝ)
    (h : ∀ U ∈ bs, |(defect U : ℝ)| ≤ r * U.1.length) :
    |(bs.map fun U => (defect U : ℝ)).sum| ≤
      r * ((bs.map Prod.fst).flatten).length := by
  induction bs with
  | nil => simp
  | cons U bs ih =>
    have hu := h U (by simp)
    have ht := ih (fun V hV => h V (by simp [hV]))
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append,
      Nat.cast_add, mul_add]
    exact (abs_add_le _ _).trans (add_le_add hu ht)

/-- No finite carrier can contain the seed and every actual child of each
noncoincident member. Coincidence states remain admitted in the carrier. -/
theorem no_finite_forward_carrier (C : Finset Pair) (hseed : seed ∈ C)
    (hblock : ∀ U ∈ C, IsBlock U)
    (hclosed : ∀ U ∈ C, U.1 ≠ U.2 →
      ∀ V ∈ red (subst substitution U.1) (subst substitution U.2), V ∈ C) : False := by
  let ratio (U : Pair) : ℝ := |(defect U : ℝ)| / U.1.length
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image C ratio ⟨seed, hseed⟩
  let r := ratio T
  have hseedratio : ratio seed = (1 / 2 : ℝ) := by
    dsimp only [ratio]
    rw [seed_defect]
    norm_num [seed]
  have hr : 0 < r := by
    have h := hmax seed hseed
    rw [hseedratio] at h
    change (1 / 2 : ℝ) ≤ r at h
    linarith
  have hlen : 0 < (T.1.length : ℝ) :=
    Nat.cast_pos.mpr (List.length_pos_iff.mpr (hblock T hT).1)
  have hratio : r * (T.1.length : ℝ) = |(defect T : ℝ)| :=
    div_mul_cancel₀ _ (ne_of_gt hlen)
  have hdef : 0 < |(defect T : ℝ)| := by
    rw [← hratio]
    exact mul_pos hr hlen
  have hne : T.1 ≠ T.2 := by
    intro he
    simp [defect, K2, he] at hdef
  have hrow : ∀ U ∈ red (subst substitution T.1) (subst substitution T.2),
      |(defect U : ℝ)| ≤ r * U.1.length := by
    intro U hU
    have hmem := hclosed T hT hne U hU
    have hlenU : 0 < (U.1.length : ℝ) :=
      Nat.cast_pos.mpr (List.length_pos_iff.mpr (hblock U hmem).1)
    exact (div_le_iff₀ hlenU).mp (hmax U hmem)
  have hbal := equiv1_subst substitution (hblock T hT).2.1
  have hsum := abs_defect_le_of_rows
    (red (subst substitution T.1) (subst substitution T.2)) r hrow
  rw [red_top hbal.length_eq] at hsum
  have hscale :
      (defect (subst substitution T.1, subst substitution T.2) : ℝ) =
        7 * (defect T : ℝ) := by
    exact_mod_cast defect_subst (hblock T hT).2.1
  have hlength : ((subst substitution T.1).length : ℝ) ≤ 5 * T.1.length := by
    exact_mod_cast subst_length_le T.1
  have hcontra : 7 * |(defect T : ℝ)| ≤ 5 * |(defect T : ℝ)| := calc
    7 * |(defect T : ℝ)| = |7 * (defect T : ℝ)| := by rw [abs_mul]; norm_num
    _ = |(defect (subst substitution T.1, subst substitution T.2) : ℝ)| := by
      rw [hscale]
    _ = |((red (subst substitution T.1) (subst substitution T.2)).map
        fun U => (defect U : ℝ)).sum| := by rw [defect_reduction hbal]
    _ ≤ r * (subst substitution T.1).length := hsum
    _ ≤ r * (5 * T.1.length) := mul_le_mul_of_nonneg_left hlength hr.le
    _ = 5 * |(defect T : ℝ)| := by rw [← hratio]; ring
  linarith

/-- The actual ordered seed closure is infinite, despite immediate productivity. -/
theorem infinite_seed_reachability :
    {U | Relation.ReflTransGen (ChildNC substitution) seed U}.Infinite := by
  intro hfin
  apply no_finite_forward_carrier hfin.toFinset
  · exact hfin.mem_toFinset.mpr Relation.ReflTransGen.refl
  · intro U hU
    have hpath := hfin.mem_toFinset.mp hU
    clear hU
    induction hpath with
    | refl => exact seed_isBlock
    | tail _ hVU ih => exact red_isBlock (equiv1_subst substitution ih.2.1) _ hVU.2
  · intro U hU hne V hV
    exact hfin.mem_toFinset.mpr ((hfin.mem_toFinset.mp hU).tail ⟨hne, hV⟩)

/-- This is a counterexample to dropping finiteness from the generic
balanced-pair termination contract, not to the Pisot conjecture. -/
theorem productive_but_not_terminating :
    (∀ U : Pair, IsBlock U → Psc.StrictSystem.Productive substitution U) ∧
      ¬ Psc.StrictSystem.TerminatesWithCoincidence substitution seed := by
  exact ⟨fun _ h => all_blocks_productive h,
    fun h => infinite_seed_reachability h.1⟩

/-- The control's incidence matrix is bound to its literal images. -/
theorem incidence_matrix : inc substitution = !![4, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem incidence_charpoly :
    ((inc substitution).map (Nat.cast : ℕ → ℚ)).charpoly =
      Polynomial.X ^ 2 - Polynomial.C 6 * Polynomial.X + Polynomial.C 7 := by
  rw [Matrix.charpoly_fin_two, incidence_matrix]
  norm_num [Matrix.trace, Matrix.det_fin_two, Matrix.map_apply, Fin.sum_univ_two]

/-- Both roots of the displayed characteristic polynomial exceed one.
Thus this control cannot be mistaken for a Pisot counterexample. -/
theorem two_expanding_roots :
    ∃ a b : ℝ, 1 < a ∧ a < b ∧
      a ^ 2 - 6 * a + 7 = 0 ∧ b ^ 2 - 6 * b + 7 = 0 := by
  refine ⟨3 - Real.sqrt 2, 3 + Real.sqrt 2, ?_, ?_, ?_, ?_⟩
  all_goals
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    nlinarith

end Psc.UniversalClosureReduction
