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

/-- The statement certified by a complete finite edge list. -/
def SatisfiesEdges {n : ℕ}
    (edges : List (WeightedEdge n)) (potential : Fin n → ℚ) : Prop :=
  ∀ e ∈ edges, e.weight = potential e.target - potential e.source

/-- Executable Boolean checker using decidable exact rational equality. -/
def checkPotential {n : ℕ}
    (edges : List (WeightedEdge n)) (potential : Fin n → ℚ) : Bool :=
  decide (SatisfiesEdges edges potential)

/-- Soundness is with respect to the *provided* edge list; it does not
establish that every child occurrence has been included. -/
theorem checkPotential_sound {n : ℕ}
    (edges : List (WeightedEdge n)) (potential : Fin n → ℚ)
    (hchecked : checkPotential edges potential = true) :
    SatisfiesEdges edges potential := by
  exact of_decide_true hchecked

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

end PscRoutes.R2C

#print axioms PscRoutes.R2C.checkPotential_sound
#print axioms PscRoutes.R2C.positive_two_edge_cycle_forbids_potential
#print axioms PscRoutes.R2C.positive_cycle_checker_refuses

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R2C.checkPotential_sound,
      `PscRoutes.R2C.positive_two_edge_cycle_forbids_potential,
      `PscRoutes.R2C.positive_cycle_checker_refuses] do
    let axs ← collectAxioms name
    for ax in axs do
      if !allowed.contains ax then
        throwError "Nonstandard axiom {ax} in {name}"
    liftIO <| IO.println s!"PSC_R2C_AXIOMS_OK\t{name}"
