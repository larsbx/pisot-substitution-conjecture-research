import PscVerif.Descendants

/-!
# Finite carriers checked against actual terminal balanced-pair children

The payload is a literal list of ordered word pairs. The checker recomputes
every actual `red` child, verifies all ordered swap seeds, and treats
coincidences as terminal. It trusts neither exported adjacency nor a
normalization quotient. A finite closed superset is sufficient; accepted
lists need not be minimal, duplicate-free, or wholly reachable.

These theorems certify finiteness, not productivity. Concrete named checks
and the separate strict-system exclusion are additional inputs.

Pre-code gate: `docs/c4-forward-carrier-literature-2026-11-12.md`.
-/

namespace Psc.ForwardCarrier

open Psc.Binomial Psc.Reduction Psc.Descendants

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The literal list contains every ordered seed and all actual children
of each listed noncoincident state. Diagonal states are terminal. -/
def Valid (s : α → List α) (states : List (List α × List α)) : Prop :=
  (∀ T ∈ (seeds : Finset (List α × List α)), T ∈ states) ∧
    ∀ T ∈ states, T.1 ≠ T.2 →
      ∀ U ∈ red (subst s T.1) (subst s T.2), U ∈ states

/-- All quantifiers range over the actual finite seed or word lists. -/
instance validDecidable (s : α → List α) (states : List (List α × List α)) :
    Decidable (Valid s states) := by
  unfold Valid
  infer_instance

/-- Recompute source children rather than accept proposed child rows. -/
def check (s : α → List α) (states : List (List α × List α)) : Bool :=
  decide (Valid s states)

theorem check_eq_true_iff (s : α → List α) (states : List (List α × List α)) :
    check s states = true ↔ Valid s states := by
  simp [check]

variable {s : α → List α} {states : List (List α × List α)}
variable {T U : List α × List α}

/-- Every actual terminal-child edge stays inside an accepted carrier. -/
theorem Valid.child_mem (h : Valid s states) (hT : T ∈ states)
    (hTU : ChildNC s T U) : U ∈ states :=
  h.2 T hT hTU.1 U hTU.2

/-- Membership is preserved along arbitrary finite actual paths, without
assuming that the initial listed state is itself seed-reachable. -/
theorem Valid.reachable_mem (h : Valid s states) (hT : T ∈ states)
    (hTU : Relation.ReflTransGen (ChildNC s) T U) : U ∈ states := by
  induction hTU with
  | refl => exact hT
  | tail _ hVU ih => exact h.child_mem ih hVU

/-- Every listed state has finite actual terminal-child reachability. -/
theorem Valid.finite_reachable (h : Valid s states) (hT : T ∈ states) :
    {U | Relation.ReflTransGen (ChildNC s) T U}.Finite :=
  (List.finite_toSet states).subset fun _ hTU => h.reachable_mem hT hTU

/-- The existing least-closed-set theorem supplies seed reachability. -/
theorem Valid.bpaStatesNC_subset (h : Valid s states) :
    bpaStatesNC s ⊆ {T | T ∈ states} := by
  apply Psc.Descendants.bpaStatesNC_subset s
  · exact h.1
  · exact h.2

/-- A finite closed superset discharges the actual terminal BPA
finiteness premise. Exact discovery and minimality are not needed. -/
theorem Valid.finite_bpaStatesNC (h : Valid s states) :
    (bpaStatesNC s).Finite :=
  (List.finite_toSet states).subset h.bpaStatesNC_subset

/-- Over the finite alphabet, the existing diagonal-state bridge also
gives finiteness of the full child graph. It does not identify its states
with the checked terminal-child carrier. -/
theorem Valid.finite_bpaStates (h : Valid s states) :
    (bpaStates s).Finite :=
  (Psc.Descendants.finite_bpaStates_iff s).2 h.finite_bpaStatesNC

/-- Boolean checker soundness for the actual seed-generated automaton. -/
theorem finite_bpaStatesNC_of_check (h : check s states = true) :
    (bpaStatesNC s).Finite :=
  ((check_eq_true_iff s states).1 h).finite_bpaStatesNC

/-- Boolean checker soundness for arbitrary listed starting states. -/
theorem finite_reachable_of_check (h : check s states = true) (hT : T ∈ states) :
    {U | Relation.ReflTransGen (ChildNC s) T U}.Finite :=
  ((check_eq_true_iff s states).1 h).finite_reachable hT

/-! ## Literal finite controls -/

/-- The terminal Fibonacci carrier omits the full-child descendant
`([1],[1])`, which occurs only after expanding a coincidence. -/
def fibonacciCarrier : List (List (Fin 2) × List (Fin 2)) :=
  [tmPair, tmPair.swap, ([0], [0])]

theorem fibonacci_carrier_accepted : check fibSubst fibonacciCarrier = true := by
  decide

/-- With no seeds, closure would be vacuous. Seed coverage rejects this. -/
theorem empty_carrier_rejected : check fibSubst [] = false := by
  decide

/-- Both ordered seeds are present, but their actual diagonal exit is
missing. Checking only supplied vertices or edges cannot certify closure. -/
theorem missing_actual_child_rejected :
    check fibSubst [tmPair, tmPair.swap] = false := by
  decide

/-- Normalized representatives are not the ordered Lean carrier. -/
theorem normalized_carrier_rejected :
    check fibSubst [tmPair, ([0], [0])] = false := by
  decide

/-- Extra terminal states and duplicates preserve the upper-bound claim;
acceptance does not assert exact or minimal reachability. -/
theorem finite_superset_accepted :
    check fibSubst [tmPair, tmPair.swap, ([0], [0]), ([1], [1]), tmPair] = true := by
  decide

/-- The genuine Thue–Morse carrier is finite. Its existing strict-system
control separately proves nonproductivity, so finiteness is not a
termination-with-coincidence certificate. -/
theorem thueMorse_carrier_accepted :
    check thueMorseSubst [tmPair, tmPair.swap] = true := by
  decide

end Psc.ForwardCarrier
