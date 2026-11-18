import PscVerif.StrictSystem

/-!
# Finite actual reachability under strict-system exclusion

For every irreducible balanced block, absence of a finite strict system
turns finite `ChildNC` reachability into termination with coincidence.
This does not construct a finite reachable set. Productivity retains its
existing existential-path meaning for every reachable state.

The proof uses actual complete word reduction and preserves the block
hypothesis along reachable paths. No finite alphabet, nonerasure, Pisot,
primitivity, or strong-coincidence hypothesis is needed for this bridge.

Pre-code gate: `docs/c4-finite-productivity-literature-2026-11-12.md`.
-/

namespace Psc.FiniteProductivity

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.StrictSystem

variable {α : Type*} [DecidableEq α]
variable {s : α → List α} {T U : List α × List α}

/-- Actual terminal-child paths preserve the irreducible balanced-block
condition by lifting to the complete child relation. -/
theorem isBlock_of_reachableNC (hT : IsBlock T)
    (hTU : Relation.ReflTransGen (ChildNC s) T U) : IsBlock U := by
  apply reachable_isBlock (s := s) (S := {T})
    (fun V hV => by simpa only [Set.mem_singleton_iff.mp hV] using hT) U
  exact ⟨T, Set.mem_singleton T, hTU.lift id (fun _ _ h => h.2)⟩

/-- Reachability from a reached state stays inside the original reachable
set; no replacement graph or omitted child is involved. -/
theorem reachableNC_subset (hTU : Relation.ReflTransGen (ChildNC s) T U) :
    {V | Relation.ReflTransGen (ChildNC s) U V} ⊆
      {V | Relation.ReflTransGen (ChildNC s) T V} :=
  fun _ hUV => hTU.trans hUV

/-- A nonproductive block with finite actual reachability would give a
finite coincidence-free factor set and hence a strict system. -/
theorem productive_of_finite_reachable
    (noStrict : ∀ C : Finset (List α × List α), ¬ StrictSystem s C)
    (hT : IsBlock T)
    (hfin : {U | Relation.ReflTransGen (ChildNC s) T U}.Finite) :
    Productive s T := by
  by_contra hnp
  have hfactor : (factorSet s T).Finite := hfin.subset (by
    rw [factorSet_eq_reachable hT]
    exact fun U hU => (reachable_of_not_productive hnp hU).1)
  have hnc : ∀ U ∈ factorSet s T, U.1 ≠ U.2 := by
    rw [factorSet_eq_reachable hT]
    exact fun U hU => (reachable_of_not_productive hnp hU).2
  exact noStrict _ (strictSystem_of_factorSet hT.2.1 hT.1 hfactor hnc)

/-- Finite actual reachability is the remaining premise: every reached
block is productive, not merely the initial block. -/
theorem terminates_of_finite_reachable
    (noStrict : ∀ C : Finset (List α × List α), ¬ StrictSystem s C)
    (hT : IsBlock T)
    (hfin : {U | Relation.ReflTransGen (ChildNC s) T U}.Finite) :
    TerminatesWithCoincidence s T := by
  refine ⟨hfin, fun U hTU => ?_⟩
  exact productive_of_finite_reachable noStrict (isBlock_of_reachableNC hT hTU)
    (hfin.subset (reachableNC_subset hTU))

/-- Under strict-system exclusion, termination for an arbitrary actual
block is equivalent to finite reachability. This does not prove G1. -/
theorem terminates_iff_finite_reachable
    (noStrict : ∀ C : Finset (List α × List α), ¬ StrictSystem s C)
    (hT : IsBlock T) :
    TerminatesWithCoincidence s T ↔
      {U | Relation.ReflTransGen (ChildNC s) T U}.Finite :=
  ⟨fun h => h.1, terminates_of_finite_reachable noStrict hT⟩

/-- Nonproductivity under exclusion forces an infinite actual reachable
set; an incomplete finite search cannot supply this premise. -/
theorem infinite_reachable_of_not_productive
    (noStrict : ∀ C : Finset (List α × List α), ¬ StrictSystem s C)
    (hT : IsBlock T) (hnp : ¬ Productive s T) :
    {U | Relation.ReflTransGen (ChildNC s) T U}.Infinite :=
  fun hfin => hnp (productive_of_finite_reachable noStrict hT hfin)

/-- The exact remaining obstruction to termination is infinite actual
reachability. This equivalence asserts neither alternative outright. -/
theorem not_terminates_iff_infinite_reachable
    (noStrict : ∀ C : Finset (List α × List α), ¬ StrictSystem s C)
    (hT : IsBlock T) :
    (¬ TerminatesWithCoincidence s T) ↔
      {U | Relation.ReflTransGen (ChildNC s) T U}.Infinite :=
  not_congr (terminates_iff_finite_reachable noStrict hT)

/-- Genuine Thue–Morse calibration: finite actual reachability alone
does not give productivity or termination with coincidence. -/
theorem thueMorse_finite_nonproductive :
    IsBlock tmPair ∧
      {U | Relation.ReflTransGen (ChildNC thueMorseSubst) tmPair U}.Finite ∧
      ¬ Productive thueMorseSubst tmPair ∧
      ¬ TerminatesWithCoincidence thueMorseSubst tmPair := by
  refine ⟨tm_strictSystem.isBlock tmPair (by decide), ?_,
    tm_strictSystem.not_productive (by decide), tm_not_terminates⟩
  exact tm_finite.subset (fun U hU =>
    ⟨tmPair, by rw [tm_seeds]; decide, hU.lift id (fun _ _ h => h.2)⟩)

/-- Positive control: the existing complete Fibonacci terminal-child
carrier and strict-system exclusion satisfy the new all-block bridge. -/
theorem fibonacci_terminates : TerminatesWithCoincidence fibSubst tmPair := by
  apply terminates_of_finite_reachable fib_no_strictSystem (by decide)
  have hfinite : (bpaStatesNC fibSubst).Finite := by
    rw [fib_bpaStatesNC]
    exact Finset.finite_toSet _
  exact hfinite.subset (fun U hU => ⟨tmPair, by rw [tm_seeds]; decide, hU⟩)

end Psc.FiniteProductivity
