import PscVerif.FiniteProductivity
import PscVerif.NamedStrictExclusion

/-!
# Named finite-reachability consumers

An original validated archive supplies strict-system exclusion only for
its own literal fixture. These consumers still require finite actual
`ChildNC` reachability before concluding termination. The inverse-overlap
archive is not used as a forward balanced-pair carrier.

Pre-code gate: `docs/c4-finite-productivity-literature-2026-11-12.md`.
-/

namespace Psc.ArchivedPayload

open Psc.Reduction Psc.Descendants Psc.StrictSystem Psc.NamedPrefixCompact

/-- Finite actual reachability makes a block productive for the
authenticated fixture. Finiteness is not supplied by the archive. -/
theorem Packet.productive_of_finite_reachable (p : Packet) (h : p.Valid)
    {T : List (Fin 3) × List (Fin 3)} (hT : IsBlock T)
    (hfin : {U | Relation.ReflTransGen (ChildNC (substitution p.fixture)) T U}.Finite) :
    Productive (substitution p.fixture) T :=
  Psc.FiniteProductivity.productive_of_finite_reachable (p.no_strictSystem h) hT hfin

/-- Every state reachable from this block is productive once the actual
reachable set is finite. No seed-membership restriction is imposed. -/
theorem Packet.terminates_of_finite_reachable (p : Packet) (h : p.Valid)
    {T : List (Fin 3) × List (Fin 3)} (hT : IsBlock T)
    (hfin : {U | Relation.ReflTransGen (ChildNC (substitution p.fixture)) T U}.Finite) :
    TerminatesWithCoincidence (substitution p.fixture) T :=
  Psc.FiniteProductivity.terminates_of_finite_reachable (p.no_strictSystem h) hT hfin

/-- For an actual block of the authenticated fixture, finite reachability
is exactly the remaining condition for termination with coincidence. -/
theorem Packet.terminates_iff_finite_reachable (p : Packet) (h : p.Valid)
    {T : List (Fin 3) × List (Fin 3)} (hT : IsBlock T) :
    TerminatesWithCoincidence (substitution p.fixture) T ↔
      {U | Relation.ReflTransGen (ChildNC (substitution p.fixture)) T U}.Finite :=
  Psc.FiniteProductivity.terminates_iff_finite_reachable (p.no_strictSystem h) hT

/-- A nonproductive actual block would require infinitely many reachable
states. This is a conditional obstruction, not an exhibited example. -/
theorem Packet.infinite_reachable_of_not_productive (p : Packet) (h : p.Valid)
    {T : List (Fin 3) × List (Fin 3)} (hT : IsBlock T)
    (hnp : ¬ Productive (substitution p.fixture) T) :
    {U | Relation.ReflTransGen (ChildNC (substitution p.fixture)) T U}.Infinite :=
  Psc.FiniteProductivity.infinite_reachable_of_not_productive (p.no_strictSystem h) hT hnp

/-- Nontermination for an actual named block is equivalent to infinite
reachability; neither side is asserted without its own evidence. -/
theorem Packet.not_terminates_iff_infinite_reachable (p : Packet) (h : p.Valid)
    {T : List (Fin 3) × List (Fin 3)} (hT : IsBlock T) :
    (¬ TerminatesWithCoincidence (substitution p.fixture) T) ↔
      {U | Relation.ReflTransGen (ChildNC (substitution p.fixture)) T U}.Infinite :=
  Psc.FiniteProductivity.not_terminates_iff_infinite_reachable (p.no_strictSystem h) hT

/-- The swap-seed specialization discharges only block validity. The
actual reachability-finiteness premise remains explicit. -/
theorem Packet.seed_terminates_of_finite_reachable (p : Packet) (h : p.Valid)
    {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ (seeds : Finset _))
    (hfin : {U | Relation.ReflTransGen (ChildNC (substitution p.fixture)) T U}.Finite) :
    TerminatesWithCoincidence (substitution p.fixture) T :=
  p.terminates_of_finite_reachable h (seeds_isBlock T hT) hfin

end Psc.ArchivedPayload
