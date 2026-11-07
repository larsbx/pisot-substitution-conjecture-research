import Mathlib
import Lean.Util.CollectAxioms

/-!
# Productive parent versus a strict descendant: literal negative control

The substitution is 0 -> 01, 1 -> 10. Its incidence is the positive
rank-one matrix [[1,1],[1,1]], so it does NOT satisfy the standing
irreducible-characteristic PIP hypothesis. All word calculations below
are exact, retain ordered raw orientations, and use ALL balanced cuts.

The result corrects a graph-logic inference, not PSC: one reachable
diagonal from a root does not exclude a different strict descendant.
-/
namespace PscRoutes.R1ProductivityScope

abbrev Word := List (Fin 2)
abbrev Pair := Word × Word

def image (a : Fin 2) : Word := if a = 0 then [0, 1] else [1, 0]
def inflate (w : Word) : Word := w.flatMap image
def mass (w : Word) : List Nat := [w.count 0, w.count 1]

def cuts (p : Pair) : List Nat :=
  (List.range (p.1.length + 1)).filter fun k =>
    decide (mass (p.1.take k) = mass (p.2.take k))

/-- Every adjacent pair of zero-return positions contributes one raw
child, in order; there is no state merging or skipped coincidence. -/
def factors (p : Pair) : List Pair :=
  ((cuts p).zip ((cuts p).drop 1)).map fun ij =>
    ((p.1.drop ij.1).take (ij.2 - ij.1),
     (p.2.drop ij.1).take (ij.2 - ij.1))

def children (p : Pair) : List Pair := factors (inflate p.1, inflate p.2)

def irreducible (p : Pair) : Bool :=
  decide (p.1.length = p.2.length) && !(p.1.isEmpty) &&
    decide (cuts p = [0, p.1.length])

inductive State where
  | root | plus | minus | zero | one
  deriving DecidableEq, BEq, Repr

open State

def pair : State → Pair
  | root => ([0,0,1], [1,0,0])
  | plus => ([0,1], [1,0])
  | minus => ([1,0], [0,1])
  | zero => ([0], [0])
  | one => ([1], [1])

/-- This table is independently bound to literal inflated-word
factorizations for EVERY state by literal_factorization below. -/
def childStates : State → List State
  | root => [plus, zero, one, minus]
  | plus => [plus, minus]
  | minus => [minus, plus]
  | zero => [zero, one]
  | one => [one, zero]

def inStrict : State → Bool
  | plus | minus => true
  | _ => false

def target : State → Bool
  | zero | one => true
  | _ => false

/-- Stronger than merely comparing incidence or pair Parikh vectors. -/
theorem literal_factorization (s : State) :
    (childStates s).map pair = children (pair s) := by
  cases s <;> decide

/-- A purported child cannot evade the finite table: ALL literal
irreducible factors of the inflated pair have a represented child. -/
theorem raw_child_coverage (s : State) (q : Pair)
    (h : q ∈ children (pair s)) :
    ∃ t : State, t ∈ childStates s ∧ pair t = q := by
  rw [← literal_factorization s] at h
  exact List.mem_map.mp h

theorem all_named_pairs_irreducible (s : State) :
    irreducible (pair s) = true := by
  cases s <;> decide

/-- The productive root has exactly these cuts. In particular the
matching letters are at balanced prefixes, not at nonzero residuals. -/
theorem productive_root_complete_cuts :
    inflate (pair root).1 = [0,1,0,1,1,0] ∧
    inflate (pair root).2 = [1,0,0,1,0,1] ∧
    cuts (inflate (pair root).1, inflate (pair root).2) = [0,2,3,4,6] := by
  decide

/-- Both root words are legal factors in one literal finite iterate. -/
theorem root_words_are_legal_factors :
    inflate (inflate (inflate [0])) = [0,1,1,0,1,0,0,1] ∧
    (inflate (inflate (inflate [0]))).drop 5 = (pair root).1 ∧
    ((inflate (inflate (inflate [0]))).drop 4).take 3 = (pair root).2 := by
  decide

/-- The fixture is intentionally OUTSIDE irreducible characteristic
hypotheses. Its nonzero integral kernel vector is explicitly exhibited. -/
def incidence (i j : Fin 2) : Int := ((image j).count i : Int)

theorem incidence_has_nonzero_kernel :
    (∀ i : Fin 2, incidence i 0 * 1 + incidence i 1 * (-1) = 0) ∧
    ((1 : Int), (-1 : Int)) ≠ (0, 0) := by
  constructor
  · intro i; fin_cases i <;> decide
  · decide

theorem strict_class_child_closed (s t : State)
    (hs : inStrict s = true) (hchild : t ∈ childStates s) :
    inStrict t = true := by
  cases s <;> cases t <;> simp_all [inStrict, childStates]

theorem strict_class_has_no_target (s : State)
    (hs : inStrict s = true) : target s = false := by
  cases s <;> simp_all [inStrict, target]

/-- Both raw orientations reach each other, with all children retained. -/
theorem strict_class_recurrent :
    minus ∈ childStates plus ∧ plus ∈ childStates minus ∧
    plus ∈ childStates plus ∧ minus ∈ childStates minus := by
  decide

inductive Reach : State → State → Prop where
  | refl (s : State) : Reach s s
  | step {s t u : State} : t ∈ childStates s → Reach t u → Reach s u

theorem reach_trans {s t : State} (p : Reach s t) :
    ∀ {u : State}, Reach t u → Reach s u := by
  induction p with
  | refl _ => intro u q; exact q
  | step h _ ih =>
      intro u q
      exact Reach.step h (ih q)

/-- Arbitrarily long descendant paths stay in the strict class: this
is induction, not a bounded simulation of a few inflation levels. -/
theorem strict_reachable_closed {s t : State} (p : Reach s t) :
    inStrict s = true → inStrict t = true := by
  induction p with
  | refl _ => intro hs; exact hs
  | step h _ ih =>
      intro hs
      exact ih (strict_class_child_closed _ _ hs h)

def Productive (s : State) : Prop :=
  ∃ t : State, Reach s t ∧ target t = true

theorem strict_class_unproductive (s : State) (hs : inStrict s = true) :
    ¬ Productive s := by
  rintro ⟨t, p, ht⟩
  have hfalse := strict_class_has_no_target t (strict_reachable_closed p hs)
  rw [hfalse] at ht
  cases ht

theorem root_productive : Productive root := by
  exact ⟨zero, Reach.step (by decide) (Reach.refl zero), rfl⟩

/-- The valid transport direction is BACKWARD along reachability. -/
theorem productivity_propagates_to_predecessors {s t : State}
    (p : Reach s t) (h : Productive t) : Productive s := by
  rcases h with ⟨u, q, hu⟩
  exact ⟨u, reach_trans p q, hu⟩

/-- A source-legal, irreducible productive parent has a literal child
in a strict closed, nonproductive class. This refutes the unrestricted
forward-propagation shortcut, NOT any irreducible-Pisot theorem. -/
theorem productive_parent_has_unproductive_child :
    Productive root ∧ plus ∈ childStates root ∧
      inStrict plus = true ∧ ¬ Productive plus := by
  exact ⟨root_productive, by decide, rfl,
    strict_class_unproductive plus rfl⟩

end PscRoutes.R1ProductivityScope

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := #[
    `PscRoutes.R1ProductivityScope.literal_factorization,
    `PscRoutes.R1ProductivityScope.raw_child_coverage,
    `PscRoutes.R1ProductivityScope.all_named_pairs_irreducible,
    `PscRoutes.R1ProductivityScope.productive_root_complete_cuts,
    `PscRoutes.R1ProductivityScope.root_words_are_legal_factors,
    `PscRoutes.R1ProductivityScope.incidence_has_nonzero_kernel,
    `PscRoutes.R1ProductivityScope.strict_class_child_closed,
    `PscRoutes.R1ProductivityScope.strict_class_has_no_target,
    `PscRoutes.R1ProductivityScope.strict_class_recurrent,
    `PscRoutes.R1ProductivityScope.reach_trans,
    `PscRoutes.R1ProductivityScope.strict_reachable_closed,
    `PscRoutes.R1ProductivityScope.strict_class_unproductive,
    `PscRoutes.R1ProductivityScope.root_productive,
    `PscRoutes.R1ProductivityScope.productivity_propagates_to_predecessors,
    `PscRoutes.R1ProductivityScope.productive_parent_has_unproductive_child]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_PRODUCTIVITY_SCOPE_AXIOMS_OK\t{name}"
