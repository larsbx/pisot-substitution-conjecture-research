import Mathlib
import Lean.Util.CollectAxioms

/-!
R2C: finite signed occurrence-edge potential certificate.
The certificate covers exactly the supplied edge list. Full source
extraction, multiplicities, and complete ordered-child closure remain
separate obligations; these lemmas do not assert PSC/C4.
-/

namespace PscRoutes.R2C

/-- An ordered directed occurrence *candidate* with a rational signed
edge weight. Finite source/target indices are explicit; occurrence
provenance must be bound by a separate checked packet importer. -/
structure WeightedEdge (n : ℕ) where
  source : Fin n
  target : Fin n
  weight : ℚ
  deriving DecidableEq

/-- The statement certified by a complete finite edge list. -/
def SatisfiesEdges {n : ℕ}
    (edges : List (WeightedEdge n)) (potential : Fin n → ℚ) : Prop :=
  ∀ e ∈ edges, e.weight = potential e.target - potential e.source

/-- Executable Boolean checker using decidable exact rational equality. -/
def checkPotential {n : ℕ}
    (edges : List (WeightedEdge n)) (potential : Fin n → ℚ) : Bool :=
  edges.all fun e => decide (e.weight = potential e.target - potential e.source)

/-- Soundness is with respect to the *provided* edge list; it does not
establish that every child occurrence has been included. -/
theorem checkPotential_sound {n : ℕ}
    (edges : List (WeightedEdge n)) (potential : Fin n → ℚ)
    (hchecked : checkPotential edges potential = true) :
    SatisfiesEdges edges potential := by
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp hchecked e he)

/-- Any one-cycle graph with total nonzero rational edge score
cannot be the gradient of a vertex potential. -/
theorem positive_two_edge_cycle_forbids_potential
    (potential : Fin 2 → ℚ)
    (hforward : (1 : ℚ) = potential 1 - potential 0)
    (hbackward : (0 : ℚ) = potential 0 - potential 1) :
    False := by
  linarith

/-- Executable counter-calibration: every rational candidate potential
is refused on the specified positive-sum two-edge cycle. -/
theorem positive_cycle_checker_refuses
    (potential : Fin 2 → ℚ) :
    checkPotential
      [⟨0, 1, 1⟩, ⟨1, 0, 0⟩] potential = false := by
  by_contra h
  have hcheck : checkPotential
      [⟨0, 1, 1⟩, ⟨1, 0, 0⟩] potential = true := by
    cases hbool : checkPotential
        [⟨0, 1, 1⟩, ⟨1, 0, 0⟩] potential <;> simp_all
  have hvalid := checkPotential_sound
    [⟨0, 1, 1⟩, ⟨1, 0, 0⟩] potential hcheck
  have hf : (1 : ℚ) = potential 1 - potential 0 :=
    hvalid ⟨0, 1, 1⟩ (by simp)
  have hb : (0 : ℚ) = potential 0 - potential 1 :=
    hvalid ⟨1, 0, 0⟩ (by simp)
  exact positive_two_edge_cycle_forbids_potential potential hf hb


/-- Explicit omission adversary: a rational potential correctly passes a
truncated one-edge packet but fails the complete two-edge packet.
Therefore a successful per-edge checker is NOT a completeness proof. -/
def omittedEdgePotential : Fin 2 → ℚ :=
  fun i => if i = 0 then 0 else 1

theorem omitted_edge_false_acceptance :
    checkPotential [⟨0, 1, 1⟩] omittedEdgePotential = true ∧
    checkPotential [⟨0, 1, 1⟩, ⟨1, 0, 0⟩] omittedEdgePotential = false := by
  constructor
  · norm_num [checkPotential, omittedEdgePotential]
  · exact positive_cycle_checker_refuses omittedEdgePotential


/-- Real literal non-Pisot strict-control substitution (0-based letters):
0↦1, 1↦012, 2↦1. These are source images, not synthetic graph edges. -/
def strictControlImage (a : Fin 3) : List (Fin 3) :=
  if a = 0 then [1] else if a = 1 then [0, 1, 2] else [1]

def strictControlWord (w : List (Fin 3)) : List (Fin 3) :=
  w.flatMap strictControlImage

/-- Complete *ordered* child factorization for the two-state
non-Pisot control A=(01,10), B=(12,21).
A maps to swapped A then direct B; B maps to direct A then swapped B.
This is literal equality, without normalizing away the orientation bit. -/
theorem nonPisotLiteralOrderedFactorization :
    strictControlWord [0, 1] = ([1, 0] ++ [1, 2]) ∧
    strictControlWord [1, 0] = ([0, 1] ++ [2, 1]) ∧
    strictControlWord [1, 2] = ([0, 1] ++ [2, 1]) ∧
    strictControlWord [2, 1] = ([1, 0] ++ [1, 2]) := by
  decide

/-- The two named children really are Parikh-balanced but
noncoincident. Their only proper cut (after the first letter) is not
balanced because the first letters differ. -/
theorem nonPisotControlChildBalanceAndNoncoincidence :
    (∀ a : Fin 3,
       (List.count a ([0, 1] : List (Fin 3))) =
         (List.count a ([1, 0] : List (Fin 3))) ∧
       (List.count a ([1, 2] : List (Fin 3))) =
         (List.count a ([2, 1] : List (Fin 3)))) ∧
    ([0, 1] : List (Fin 3)) ≠ [1, 0] ∧
    ([1, 2] : List (Fin 3)) ≠ [2, 1] := by
  decide

end PscRoutes.R2C

#print axioms PscRoutes.R2C.checkPotential_sound
#print axioms PscRoutes.R2C.positive_two_edge_cycle_forbids_potential
#print axioms PscRoutes.R2C.positive_cycle_checker_refuses
#print axioms PscRoutes.R2C.omitted_edge_false_acceptance
#print axioms PscRoutes.R2C.nonPisotLiteralOrderedFactorization
#print axioms PscRoutes.R2C.nonPisotControlChildBalanceAndNoncoincidence

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R2C.checkPotential_sound,
      `PscRoutes.R2C.positive_two_edge_cycle_forbids_potential,
      `PscRoutes.R2C.positive_cycle_checker_refuses,
      `PscRoutes.R2C.omitted_edge_false_acceptance,
      `PscRoutes.R2C.nonPisotLiteralOrderedFactorization,
      `PscRoutes.R2C.nonPisotControlChildBalanceAndNoncoincidence] do
    let axs ← collectAxioms name
    for ax in axs do
      if !allowed.contains ax then
        throwError "Nonstandard axiom {ax} in {name}"
    liftIO <| IO.println s!"PSC_R2C_AXIOMS_OK\t{name}"
