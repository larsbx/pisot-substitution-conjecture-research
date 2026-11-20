import PscVerif.Descendants

/-!
# Balanced-pair productivity and termination

The existing `Psc.StrictSystem` predicates depend only on actual ordered
`ChildNC` reachability. They live here so a combinatorial termination proof
does not need to import spectral or strict-system exclusion arguments.
-/

namespace Psc.StrictSystem

open Psc.Descendants

variable {α : Type*} [DecidableEq α]

/-- `def:bpa`: a state is **productive** if some directed path of `B_σ`
(coincidence blocks terminal, `ChildNC`) from it reaches a coincidence block. -/
def Productive (s : α → List α) (T : List α × List α) : Prop :=
  ∃ U, Relation.ReflTransGen (ChildNC s) T U ∧ U.1 = U.2

/-- `def:bpa`: the balanced pair algorithm started at `T₀` **terminates with
coincidence** if the set of states reachable from `T₀` in `B_σ` is finite and
every one of them is productive. -/
def TerminatesWithCoincidence (s : α → List α) (T₀ : List α × List α) : Prop :=
  {U | Relation.ReflTransGen (ChildNC s) T₀ U}.Finite ∧
    ∀ U, Relation.ReflTransGen (ChildNC s) T₀ U → Productive s U

end Psc.StrictSystem
