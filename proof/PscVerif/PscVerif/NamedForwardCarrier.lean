import PscVerif.ForwardCarrier
import PscVerif.NamedFiniteProductivity
import PscVerif.NamedForwardCarrierData0
import PscVerif.NamedForwardCarrierData1

/-!
# Forward-carrier consumers for the two literal named substitutions

The fixture-indexed checker recomputes actual children for that exact
substitution. Its successful check supplies forward reachability
finiteness; an independently validated original archive supplies strict-
system exclusion. Neither receipt is inferred from the other.

The generated literal carriers are bound definitionally to the canonical
named substitutions. Their checked finiteness needs no archive premise;
termination for seeds and their actual descendants still requires a valid
original archive. Concrete-data and complete named-chain acceptance are
recorded separately from this source construction.

Pre-code gate: `docs/c4-forward-carrier-literature-2026-11-12.md`.
-/

namespace Psc.NamedForwardCarrier

open Psc.Descendants Psc.NamedPrefixCompact

/-- Binding to the finite fixture index prevents transferring a check
merely because two substitutions have the same incidence matrix. -/
def check (fixture : Fin 2) (states : List (List (Fin 3) × List (Fin 3))) : Bool :=
  Psc.ForwardCarrier.check (substitution fixture) states

/-- Recover the source-bound closure proposition for the exact fixture. -/
theorem valid_of_check (fixture : Fin 2)
    (states : List (List (Fin 3) × List (Fin 3)))
    (h : check fixture states = true) :
    Psc.ForwardCarrier.Valid (substitution fixture) states :=
  (Psc.ForwardCarrier.check_eq_true_iff (substitution fixture) states).1 h

/-- A checked literal carrier gives named seed-generated G1; the checker
equality remains an explicit premise until concrete data are accepted. -/
theorem finite_bpaStatesNC_of_check (fixture : Fin 2)
    (states : List (List (Fin 3) × List (Fin 3)))
    (h : check fixture states = true) :
    (bpaStatesNC (substitution fixture)).Finite :=
  (valid_of_check fixture states h).finite_bpaStatesNC

/-- Every listed starting state has finite actual forward reachability. -/
theorem finite_reachable_of_mem (fixture : Fin 2)
    (states : List (List (Fin 3) × List (Fin 3)))
    (h : check fixture states = true)
    {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ states) :
    {U | Relation.ReflTransGen (ChildNC (substitution fixture)) T U}.Finite :=
  (valid_of_check fixture states h).finite_reachable hT

/-- Exact word-order binding for `1/021/001`. -/
theorem fixture0Substitution_eq :
    Psc.GeneratedForwardCarrier.fixture0Substitution = substitution 0 := rfl

/-- Exact word-order binding for `1/012/001`. -/
theorem fixture1Substitution_eq :
    Psc.GeneratedForwardCarrier.fixture1Substitution = substitution 1 := rfl

/-- Select the literal ordered carrier for the same named fixture. -/
noncomputable def checkedStates (fixture : Fin 2) : List (List (Fin 3) × List (Fin 3)) :=
  ![Psc.GeneratedForwardCarrier.fixture0States,
    Psc.GeneratedForwardCarrier.fixture1States] fixture

-- Use generic selector lemmas instead of comparing expanded state lists.
-- Scope the generated checkers' allowance to remaining conversion here.
set_option maxRecDepth 200000 in
/-- Generated complete checks are transported by literal definitional
identity, without an incidence-only or normalized-state identification. -/
theorem check_checkedStates (fixture : Fin 2) :
    check fixture (checkedStates fixture) = true := by
  fin_cases fixture
  · have hstates : checkedStates 0 = Psc.GeneratedForwardCarrier.fixture0States :=
      Matrix.cons_val_zero Psc.GeneratedForwardCarrier.fixture0States
        ![Psc.GeneratedForwardCarrier.fixture1States]
    exact (congrArg₂ Psc.ForwardCarrier.check fixture0Substitution_eq hstates.symm).symm.trans
      Psc.GeneratedForwardCarrier.fixture0ForwardCheck
  · have hstates : checkedStates 1 = Psc.GeneratedForwardCarrier.fixture1States :=
      (Matrix.cons_val_one Psc.GeneratedForwardCarrier.fixture0States
        ![Psc.GeneratedForwardCarrier.fixture1States]).trans
        (Matrix.cons_val_zero Psc.GeneratedForwardCarrier.fixture1States ![])
    exact (congrArg₂ Psc.ForwardCarrier.check fixture1Substitution_eq hstates.symm).symm.trans
      Psc.GeneratedForwardCarrier.fixture1ForwardCheck

/-- The concrete forward certificate supplies named seed-generated
finiteness independently of any inverse-overlap archive. -/
theorem finite_bpaStatesNC (fixture : Fin 2) :
    (bpaStatesNC (substitution fixture)).Finite := by
  fin_cases fixture
  · change (bpaStatesNC Psc.GeneratedForwardCarrier.fixture0Substitution).Finite
    exact Psc.GeneratedForwardCarrier.fixture0Finite
  · change (bpaStatesNC Psc.GeneratedForwardCarrier.fixture1Substitution).Finite
    exact Psc.GeneratedForwardCarrier.fixture1Finite

end Psc.NamedForwardCarrier

namespace Psc.ArchivedPayload

open Psc.Reduction Psc.Descendants Psc.StrictSystem Psc.NamedPrefixCompact

/-- Combine the two independent inputs: checked actual forward closure
and the original archive's validated strict-system exclusion. -/
theorem Packet.terminates_of_forwardCarrier (p : Packet) (hp : p.Valid)
    (states : List (List (Fin 3) × List (Fin 3)))
    (hcheck : Psc.NamedForwardCarrier.check p.fixture states = true)
    {T : List (Fin 3) × List (Fin 3)} (hT : IsBlock T) (hmem : T ∈ states) :
    TerminatesWithCoincidence (substitution p.fixture) T :=
  p.terminates_of_finite_reachable hp hT
    (Psc.NamedForwardCarrier.finite_reachable_of_mem p.fixture states hcheck hmem)

/-- All actual seed descendants are blocks in the checked carrier.
This does not assert finiteness from an arbitrary unlisted block. -/
theorem Packet.reachable_terminates_of_forwardCarrier (p : Packet) (hp : p.Valid)
    (states : List (List (Fin 3) × List (Fin 3)))
    (hcheck : Psc.NamedForwardCarrier.check p.fixture states = true)
    {T : List (Fin 3) × List (Fin 3)}
    (hT : T ∈ bpaStatesNC (substitution p.fixture)) :
    TerminatesWithCoincidence (substitution p.fixture) T := by
  have hvalid := Psc.NamedForwardCarrier.valid_of_check p.fixture states hcheck
  apply p.terminates_of_forwardCarrier hp states hcheck
  · exact bpaStates_isBlock (substitution p.fixture) T
      (bpaStatesNC_subset_bpaStates (substitution p.fixture) hT)
  · exact hvalid.bpaStatesNC_subset hT

/-- Every ordered swap seed is covered by a successful fixture check. -/
theorem Packet.seed_terminates_of_forwardCarrier (p : Packet) (hp : p.Valid)
    (states : List (List (Fin 3) × List (Fin 3)))
    (hcheck : Psc.NamedForwardCarrier.check p.fixture states = true)
    {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ (seeds : Finset _)) :
    TerminatesWithCoincidence (substitution p.fixture) T :=
  p.reachable_terminates_of_forwardCarrier hp states hcheck ⟨T, hT, .refl⟩

/-- The concrete forward carrier discharges finiteness for every actual
seed descendant; validated archived strict exclusion remains explicit. -/
theorem Packet.reachable_terminates (p : Packet) (hp : p.Valid)
    {T : List (Fin 3) × List (Fin 3)}
    (hT : T ∈ bpaStatesNC (substitution p.fixture)) :
    TerminatesWithCoincidence (substitution p.fixture) T :=
  p.reachable_terminates_of_forwardCarrier hp
    (Psc.NamedForwardCarrier.checkedStates p.fixture)
    (Psc.NamedForwardCarrier.check_checkedStates p.fixture) hT

/-- Each ordered swap seed terminates once the original archive is valid
for its own fixture. No unlisted starting block is covered. -/
theorem Packet.seed_terminates (p : Packet) (hp : p.Valid)
    {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ (seeds : Finset _)) :
    TerminatesWithCoincidence (substitution p.fixture) T :=
  p.seed_terminates_of_forwardCarrier hp
    (Psc.NamedForwardCarrier.checkedStates p.fixture)
    (Psc.NamedForwardCarrier.check_checkedStates p.fixture) hT

end Psc.ArchivedPayload
