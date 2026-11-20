import PscVerif.Termination

/-!
# Single-seed termination and actual iterated factors

For an irreducible balanced seed over a finite alphabet, the repository's
`TerminatesWithCoincidence` predicate is equivalent to the full-iterate factor
condition used by Barge--Stimac--Williams, section 3 and Corollary 2:
the set of all irreducible factors in all iterates is finite, and each such
factor eventually produces a singleton coincidence in an actual iterate.

The factor set is written literally in the public theorem. It is definitionally
the existing `Psc.StrictSystem.factorSet`, without importing the unrelated
spectral and strict-system developments in that module.

Full `Child` paths may continue after a coincidence. The conversion back to
`ChildNC` therefore stops at the first coincidence; it does not assert that the
same final singleton is reachable when coincidence blocks are terminal.
No Pisot, primitivity, nonerasing, or spectral hypothesis is used here.

Pre-code source decision: `docs/c4-family-pisot-bridge-stop-go-2026-11-14.md`.
-/

namespace Psc.TerminationFactors

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.StrictSystem

variable {α : Type*} [DecidableEq α]

/-- A full child path to a coincidence gives a terminal-child path to some
coincidence, stopping before any subsequent expansion of a diagonal. -/
theorem productive_of_full_child_path {s : α → List α} {T U : List α × List α}
    (hTU : Relation.ReflTransGen (Child s) T U) (hU : U.1 = U.2) :
    Productive s T := by
  induction hTU using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨U, .refl, hU⟩
  | @head T V hTV _ ih =>
    by_cases hT : T.1 = T.2
    · exact ⟨T, .refl, hT⟩
    · obtain ⟨W, hVW, hW⟩ := ih
      exact ⟨W, hVW.head ⟨hT, hTV⟩, hW⟩

/-- Productivity of an actual block means a singleton coincidence occurs in
the ordered reduction of some actual substitution iterate. -/
theorem productive_iff_iterate_coincidence {s : α → List α} {T : List α × List α}
    (hT : IsBlock T) :
    Productive s T ↔ ∃ n a,
      ([a], [a]) ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2) := by
  constructor
  · rintro ⟨U, hTU, hU⟩
    obtain ⟨n, hn⟩ := (reflTransGen_child_iff s hT).1
      (hTU.lift id fun _ _ h => h.2)
    obtain ⟨a, rfl⟩ := eq_coincidence_of_isBlock
      (red_isBlock (equiv1_iterate_subst s n hT.2.1) U hn) hU
    exact ⟨n, a, hn⟩
  · rintro ⟨n, a, ha⟩
    exact productive_of_full_child_path ((reflTransGen_child_iff s hT).2 ⟨n, ha⟩) rfl

/-- Single-seed finiteness correspondence: full iteration can add only the
finite set of singleton diagonal blocks to terminal-child reachability. -/
theorem finite_factors_iff_finite_reachableNC [Finite α] {s : α → List α}
    {T : List α × List α} (hT : IsBlock T) :
    {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite ↔
      {U | Relation.ReflTransGen (ChildNC s) T U}.Finite := by
  constructor
  · intro hfin
    exact hfin.subset fun U hU => (reflTransGen_child_iff s hT).1
      (hU.lift id fun _ _ h => h.2)
  · intro hfin
    apply (hfin.union (Set.finite_range fun a : α => ([a], [a]))).subset
    rintro U ⟨n, hn⟩
    by_cases hU : U.1 = U.2
    · obtain ⟨a, rfl⟩ := eq_coincidence_of_isBlock
        (red_isBlock (equiv1_iterate_subst s n hT.2.1) U hn) hU
      exact Or.inr ⟨a, rfl⟩
    · exact Or.inl (reflTransGen_childNC ((reflTransGen_child_iff s hT).2 ⟨n, hn⟩) hU)

/-- Exact single-seed equivalence with the full-iterate balanced-pair condition.
Both sides concern actual ordered reductions; every factor must be productive.
The existential coincidence depth may depend on the factor. -/
theorem terminates_iff_finite_factors_and_coincidences [Finite α]
    {s : α → List α} {T : List α × List α} (hT : IsBlock T) :
    TerminatesWithCoincidence s T ↔
      {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite ∧
        ∀ U, (∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)) →
          ∃ m a, ([a], [a]) ∈ red ((subst s)^[m] U.1) ((subst s)^[m] U.2) := by
  constructor
  · rintro ⟨hfin, hprod⟩
    refine ⟨(finite_factors_iff_finite_reachableNC hT).2 hfin, ?_⟩
    rintro U ⟨n, hn⟩
    have hB := red_isBlock (equiv1_iterate_subst s n hT.2.1) U hn
    apply (productive_iff_iterate_coincidence hB).1
    by_cases hU : U.1 = U.2
    · exact ⟨U, .refl, hU⟩
    · exact hprod U (reflTransGen_childNC ((reflTransGen_child_iff s hT).2 ⟨n, hn⟩) hU)
  · rintro ⟨hfin, hprod⟩
    refine ⟨(finite_factors_iff_finite_reachableNC hT).1 hfin, ?_⟩
    intro U hU
    have hfactor := (reflTransGen_child_iff s hT).1 (hU.lift id fun _ _ h => h.2)
    obtain ⟨n, hn⟩ := hfactor
    exact (productive_iff_iterate_coincidence
      (red_isBlock (equiv1_iterate_subst s n hT.2.1) U hn)).2 (hprod U ⟨n, hn⟩)

/-! ## Controls: finiteness is insufficient, and full paths really differ. -/

/-- The identity substitution preserves every literal word. -/
private theorem subst_singletons (w : List α) : subst (fun a : α => [a]) w = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [Psc.Incidence.subst_cons, ih, List.singleton_append]

/-- Every iterate of the identity substitution fixes the given word. -/
private theorem iterate_subst_singletons (n : Nat) (w : List α) :
    (subst (fun a : α => [a]))^[n] w = w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', subst_singletons, ih]

/-- Finiteness alone does not yield termination with coincidence: the literal
identity substitution has the noncoincident swap seed as its only factor. -/
theorem identity_finite_without_coincidence :
    {U | ∃ n, U ∈ red ((subst (fun a : Fin 2 => [a]))^[n] [0, 1])
      ((subst (fun a : Fin 2 => [a]))^[n] [1, 0])}.Finite ∧
      ¬ TerminatesWithCoincidence (fun a : Fin 2 => [a]) ([0, 1], [1, 0]) := by
  have hb : IsBlock (([0, 1], [1, 0]) : List (Fin 2) × List (Fin 2)) :=
    seed_isBlock (by decide)
  have hred : ∀ n, red ((subst (fun a : Fin 2 => [a]))^[n] [0, 1])
      ((subst (fun a : Fin 2 => [a]))^[n] [1, 0]) = [([0, 1], [1, 0])] := by
    intro n
    rw [iterate_subst_singletons, iterate_subst_singletons, red_of_isBlock hb]
  constructor
  · exact (Set.finite_singleton _).subset fun U ⟨n, hn⟩ => by
      simpa only [hred n, List.mem_singleton, Set.mem_singleton_iff] using hn
  · intro h
    obtain ⟨n, a, ha⟩ := (productive_iff_iterate_coincidence hb).1 (h.2 _ .refl)
    rw [hred n, List.mem_singleton] at ha
    have := congrArg (fun p : List (Fin 2) × List (Fin 2) => p.1.length) ha
    simp at this

/-- A full iterate may contain a singleton that is not terminal-child reachable:
the existing Fibonacci control forces truncation at an earlier coincidence. -/
theorem full_factor_need_not_be_terminal_reachable :
    (([1], [1]) : List (Fin 2) × List (Fin 2)) ∈
      red ((subst fibSubst)^[2] tmPair.1) ((subst fibSubst)^[2] tmPair.2) ∧
      ¬ Relation.ReflTransGen (ChildNC fibSubst) tmPair ([1], [1]) := by
  constructor
  · have hb : IsBlock tmPair := seed_isBlock (by decide : (0 : Fin 2) ≠ 1)
    rw [← descR_of_isBlock fibSubst 2 hb, fib_descR_two]
    decide
  · intro h
    exact fib_one_not_mem_bpaStatesNC ⟨tmPair, by rw [tm_seeds]; decide, h⟩

end Psc.TerminationFactors
