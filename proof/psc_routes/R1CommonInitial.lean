import Mathlib
import Lean.Util.CollectAxioms

namespace PscRoutes.R1CommonInitial

/-- Matching letters at the very beginning have empty (hence equal)
preceding Parikh prefixes. This is stronger than equal letters at an
arbitrary physical index; it witnesses a first one-letter diagonal. -/
def FirstDiagonal {A : Type*} (u v : List A) : Prop :=
  ∃ c : A, ∃ u' v' : List A, u = c :: u' ∧ v = c :: v'

/-- The sound ALL-STATE certificate missing from root productivity:
if every source-letter image begins with the same c, then the images
of every pair of nonempty source words have a first-step diagonal.
No legality, Pisot spectrum, source balance, or finite-state cap is used. -/
theorem common_initial_letter_forces_diagonal
    {A : Type*} (subst : A → List A) (c : A)
    (himages : ∀ a, ∃ rest, subst a = c :: rest)
    (u v : List A) (hu : u ≠ []) (hv : v ≠ []) :
    FirstDiagonal (u.flatMap subst) (v.flatMap subst) := by
  cases u with
  | nil => exact False.elim (hu rfl)
  | cons a us =>
    cases v with
    | nil => exact False.elim (hv rfl)
    | cons b vs =>
      obtain ⟨ar, ha⟩ := himages a
      obtain ⟨br, hb⟩ := himages b
      refine ⟨c, ar ++ us.flatMap subst, br ++ vs.flatMap subst, ?_, ?_⟩
      · simp only [List.flatMap_cons, ha, List.cons_append]
      · simp only [List.flatMap_cons, hb, List.cons_append]

def triImage (a : Fin 3) : List (Fin 3) :=
  if a = 0 then [0,1] else if a = 1 then [0,2] else [0]

theorem tribonacci_images_have_common_initial_letter (a : Fin 3) :
    ∃ rest : List (Fin 3), triImage a = 0 :: rest := by
  fin_cases a
  · exact ⟨[1], rfl⟩
  · exact ⟨[2], rfl⟩
  · exact ⟨[], rfl⟩

/-- Valid classification for ANY nonempty Tribonacci source pair,
including every actual irreducible balanced descendant of a swap
seed. It does not generalize to arbitrary primitive Pisot substitutions. -/
theorem every_nonempty_tribonacci_pair_has_first_diagonal
    (u v : List (Fin 3)) (hu : u ≠ []) (hv : v ≠ []) :
    FirstDiagonal (u.flatMap triImage) (v.flatMap triImage) :=
  common_initial_letter_forces_diagonal triImage 0
    tribonacci_images_have_common_initial_letter u v hu hv

/-- A nonempty source pair for this particular substitution cannot
avoid even its first-step diagonal, hence cannot belong to a strict
child-closed nonproductive component under the repository definition. -/
theorem tribonacci_first_step_avoidance_impossible
    (u v : List (Fin 3)) (hu : u ≠ []) (hv : v ≠ [])
    (havoid : ¬ FirstDiagonal (u.flatMap triImage) (v.flatMap triImage)) :
    False :=
  havoid (every_nonempty_tribonacci_pair_has_first_diagonal u v hu hv)

end PscRoutes.R1CommonInitial

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := #[
    `PscRoutes.R1CommonInitial.common_initial_letter_forces_diagonal,
    `PscRoutes.R1CommonInitial.tribonacci_images_have_common_initial_letter,
    `PscRoutes.R1CommonInitial.every_nonempty_tribonacci_pair_has_first_diagonal,
    `PscRoutes.R1CommonInitial.tribonacci_first_step_avoidance_impossible]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_COMMON_INITIAL_AXIOMS_OK\t{name}"
