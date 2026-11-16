/-
# The quantifier interface on the balanced-pair automaton

`Psc.QuantifierInterface` is graph logic.  This module binds it to the objects
the repository already has, so that the interface is not a parallel vocabulary:

* `bpaGraph s` is the balanced-pair automaton `B_σ` of `def:bpa` as a child
  graph: the child relation is `Psc.Descendants.ChildNC s` (coincidence blocks
  terminal) and the targets are the coincidence blocks.
* `Psc.StrictSystem.Productive` **is** (E) on `bpaGraph s` (`productive_iff`),
  and `Psc.StrictSystem.TerminatesWithCoincidence` **is** "finite reachable set
  and (AE)" (`terminatesWithCoincidence_iff`); both are `Iff.rfl`.
* A strict system is a strict closed set of `bpaGraph s`
  (`strictClosed_of_strictSystem`).
* `terminatesWithCoincidence_iff_finite_and_exclusion` is the typed separation
  of the two inputs of termination with coincidence: finiteness of the reachable
  set (an extraction/termination statement, G1-type) and exclusion of reachable
  finite strict closed strongly connected sets (a component-exclusion
  statement, C4-type).  Neither is proved here for any substitution.

Literal realisations of the abstract countermodels:

* `fib_lasso` — Fibonacci `0 ↦ 01, 1 ↦ 0`, which satisfies the standing
  primitive, irreducible, Pisot hypotheses: from the seed `(01, 10)` the
  algorithm terminates with coincidence, so (AE) holds, and the two seeds form
  a cycle of non-coincident states, so (A) fails.  An interface that asks for
  "every admissible path meets a coincidence" is therefore unsatisfiable inside
  the standing class; density one is (AE), not (A).
* `tm_fork` — Thue–Morse `0 ↦ 01, 1 ↦ 10`, which is **outside** the standing
  class (its incidence matrix is singular): the irreducible balanced pair
  `(001, 100)` is productive and has the child `(01, 10)`, which lies in a
  strict system.  This is the control of
  `proof/psc_routes/R1ProductivityScope.lean`, restated on the definitions of
  `Psc.Descendants`; the first violated standing premise is irreducibility of
  the characteristic polynomial.

Not proved here: any statement that a strict closed set exists or does not
exist for a substitution in the standing class; finiteness of the reachable set
of `bpaGraph s` beyond the two specimens above; any spectral conclusion.
-/
import PscVerif.StrictSystem
import PscVerif.QuantifierInterface

namespace Psc.QuantifierBinding

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.StrictSystem Psc.QuantifierInterface
open Psc.QuantifierInterface.ChildGraph

variable {α : Type*} [DecidableEq α]

/-- The balanced-pair automaton `B_σ` (`def:bpa`) as a child graph: children
through `ChildNC` (coincidence blocks terminal), targets the coincidence
blocks. -/
def bpaGraph (s : α → List α) : ChildGraph (List α × List α) where
  child := ChildNC s
  target U := U.1 = U.2

variable {s : α → List α}

/-- `Psc.StrictSystem.Productive` is (E) on `bpaGraph s`. -/
theorem productive_iff {T : List α × List α} :
    (bpaGraph s).Productive T ↔ Psc.StrictSystem.Productive s T :=
  Iff.rfl

/-- `TerminatesWithCoincidence` is "finite reachable set and (AE)". -/
theorem terminatesWithCoincidence_iff {T₀ : List α × List α} :
    TerminatesWithCoincidence s T₀ ↔
      {U | (bpaGraph s).Reach T₀ U}.Finite ∧ (bpaGraph s).HereditarilyProductive T₀ :=
  Iff.rfl

/-- Coincidence blocks are terminal in `bpaGraph s`, so targets are
child-closed. -/
theorem bpaGraph_targetClosed (s : α → List α) : (bpaGraph s).TargetClosed :=
  fun _ _ hT hTU => absurd hT hTU.1

/-- A strict system is a strict closed set of `bpaGraph s`. -/
theorem strictClosed_of_strictSystem {C : Finset (List α × List α)} (h : StrictSystem s C) :
    (bpaGraph s).StrictClosed (↑C : Set (List α × List α)) where
  nonempty := Finset.coe_nonempty.2 h.nonempty
  closed := fun T U hT hTU => h.closed T hT U hTU.2
  strict := fun T hT => h.noncoincident T hT

/-- **The two inputs of termination with coincidence.**  The balanced pair
algorithm from `T₀` terminates with coincidence iff (1) the set of states
reachable from `T₀` is finite and (2) no finite strict closed strongly connected
set is reachable from `T₀`.  (1) and (2) are independent statements: the
abstract `Psc.QuantifierInterface.ray_exclusion_vacuous` satisfies (2) and has
no productive state. -/
theorem terminatesWithCoincidence_iff_finite_and_exclusion {T₀ : List α × List α} :
    TerminatesWithCoincidence s T₀ ↔
      {U | (bpaGraph s).Reach T₀ U}.Finite ∧
        ¬ ∃ C : Set (List α × List α), C.Finite ∧ (bpaGraph s).StrictClosed C ∧
          (bpaGraph s).StronglyConnected C ∧ ∃ T ∈ C, (bpaGraph s).Reach T₀ T :=
  terminatesWithCoincidence_iff.trans
    (and_congr_right fun hfin => hereditarilyProductive_iff_exclusion_of_finite hfin)

/-- A reachable strict system refutes (AE), whatever else the root reaches. -/
theorem not_hereditarilyProductive_of_strictSystem {C : Finset (List α × List α)}
    (h : StrictSystem s C) {T₀ T : List α × List α} (hT : T ∈ C)
    (hreach : (bpaGraph s).Reach T₀ T) : ¬ (bpaGraph s).HereditarilyProductive T₀ :=
  fun hAE => (strictClosed_of_strictSystem h).not_productive hT (hAE T hreach)

/-! ### Fibonacci: (AE) holds and (A) fails inside the standing class -/

theorem fib_reach_subset :
    {U | (bpaGraph fibSubst).Reach tmPair U} ⊆
      ↑({tmPair, tmPair.swap, ([0], [0])} : Finset (List (Fin 2) × List (Fin 2))) := by
  intro U hU
  rw [← fib_bpaStatesNC]
  exact ⟨tmPair, by rw [tm_seeds]; decide, hU⟩

theorem fib_reach_finite : {U | (bpaGraph fibSubst).Reach tmPair U}.Finite :=
  (Finset.finite_toSet _).subset fib_reach_subset

/-- The two Fibonacci seeds form a cycle of non-coincident states. -/
theorem fib_strict_cycle :
    Relation.TransGen (bpaGraph fibSubst).StrictStep tmPair tmPair :=
  Relation.TransGen.head
    (show (bpaGraph fibSubst).StrictStep tmPair tmPair.swap from
      ⟨show tmPair.1 ≠ tmPair.2 by decide, by decide, show _ ∈ _ by decide⟩)
    (.single (show (bpaGraph fibSubst).StrictStep tmPair.swap tmPair from
      ⟨show tmPair.swap.1 ≠ tmPair.swap.2 by decide, by decide, show _ ∈ _ by decide⟩))

/-- From the seed `(01, 10)` the Fibonacci balanced pair algorithm terminates
with coincidence. -/
theorem fib_terminatesWithCoincidence : TerminatesWithCoincidence fibSubst tmPair := by
  refine ⟨fib_reach_finite, fun U hU => ?_⟩
  have hmem := fib_reach_subset hU
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact ⟨([0], [0]), .single ⟨by decide, show _ ∈ _ by decide⟩, rfl⟩
  · exact ⟨([0], [0]), .single ⟨by decide, show _ ∈ _ by decide⟩, rfl⟩
  · exact ⟨([0], [0]), .refl, rfl⟩

/-- **(AE) without (A) on a Pisot substitution.**  For Fibonacci and the seed
`(01, 10)`: the algorithm terminates with coincidence, every reachable state is
productive, a cycle of non-coincident states passes through the seed, and some
admissible path from the seed never meets a coincidence. -/
theorem fib_lasso :
    TerminatesWithCoincidence fibSubst tmPair ∧
      (bpaGraph fibSubst).HereditarilyProductive tmPair ∧
      Relation.TransGen (bpaGraph fibSubst).StrictStep tmPair tmPair ∧
      ¬ (bpaGraph fibSubst).Inevitable tmPair :=
  ⟨fib_terminatesWithCoincidence, fib_terminatesWithCoincidence.2, fib_strict_cycle,
    fun h => (inevitable_iff_no_strict_cycle_of_finite fib_reach_finite).1 h
      ⟨tmPair, .refl, fib_strict_cycle⟩⟩

/-! ### Thue–Morse: (E) without (AE), outside the standing class -/

/-- The irreducible balanced pair `(001, 100)`. -/
def tmRoot : List (Fin 2) × List (Fin 2) := ([0, 0, 1], [1, 0, 0])

theorem tmRoot_isBlock : IsBlock tmRoot := by decide

/-- The children of `(001, 100)` under Thue–Morse, in order. -/
theorem tmRoot_children :
    red (subst thueMorseSubst tmRoot.1) (subst thueMorseSubst tmRoot.2) =
      [tmPair, ([0], [0]), ([1], [1]), tmPair.swap] := by
  decide

/-- **(E) without (AE) on a substitution.**  Under Thue–Morse the irreducible
balanced pair `(001, 100)` is productive, its child `(01, 10)` is a state of a
strict system and is not productive, and so (AE) fails at `(001, 100)`.
Thue–Morse has a singular incidence matrix: this is a control on the inference
"one coincidence below the root, hence every descendant is productive", and no
statement about the standing class. -/
theorem tm_fork :
    (bpaGraph thueMorseSubst).Productive tmRoot ∧
      (bpaGraph thueMorseSubst).child tmRoot tmPair ∧
      ¬ (bpaGraph thueMorseSubst).Productive tmPair ∧
      ¬ (bpaGraph thueMorseSubst).HereditarilyProductive tmRoot := by
  have hchild : (bpaGraph thueMorseSubst).child tmRoot tmPair :=
    ⟨by decide, show _ ∈ _ by rw [tmRoot_children]; decide⟩
  have hnp : ¬ (bpaGraph thueMorseSubst).Productive tmPair :=
    (strictClosed_of_strictSystem tm_strictSystem).not_productive (by decide)
  refine ⟨⟨([0], [0]), .single ⟨by decide, show _ ∈ _ by rw [tmRoot_children]; decide⟩, rfl⟩,
    hchild, hnp, fun h => hnp (h tmPair (.single hchild))⟩

/-- The first violated standing premise of `tm_fork`: the incidence matrix of
Thue–Morse kills `(1, -1)`. -/
theorem tm_incidence_singular :
    ∀ a : Fin 2, ((thueMorseSubst 0).count a : ℤ) - (thueMorseSubst 1).count a = 0 := by
  decide

end Psc.QuantifierBinding
