import Mathlib
import Lean.Util.CollectAxioms

/-!
R1F modular ancestry certificate. No real embeddings or floating-point
arithmetic. A finite-field left-null witness certifies *unsatisfiability*
of one reduced affine-cycle equation. Matrix reduction and the literal
correction-word/occurrence binding remain independent hypotheses.
-/

namespace PscRoutes.R1Modular

variable (p : ℕ) [Fact p.Prime]

/-- A nonzero finite-field pairing on the right-hand side contradicts
the existence of a solution when the functional annihilates the
matrix's image. Valid for arbitrary finite dimension. -/
theorem no_mod_solution_from_left_null
    {d : ℕ}
    (A : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))
    (left : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (b : Fin d → ZMod p)
    (hnull : left.comp A = 0)
    (hpair : left b ≠ 0) :
    ¬ ∃ x : Fin d → ZMod p, A x = b := by
  rintro ⟨x, hx⟩
  apply hpair
  calc
    left b = left (A x) := by rw [hx]
    _ = (left.comp A) x := rfl
    _ = 0 := by rw [hnull]; rfl

/-- Canonical integral address reduction, coordinatewise, to ZMod p.
This is a *definition* of the bridge, not a proof that an arbitrary
claimed mod-p matrix was reduced from its exact integer parent. -/
def modVec {d : ℕ} (v : Fin d → ℤ) : Fin d → ZMod p :=
  fun i => (v i : ZMod p)

/-- A typed refinement obligation: if an independently supplied
finite-field matrix A_p actually commutes with reduction of a
supplied integer affine-cycle operator, the left-null certificate
rejects every integral solution of that cycle equation. -/
theorem no_integral_solution_from_modular_witness
    {d : ℕ}
    (Aint : (Fin d → ℤ) → (Fin d → ℤ))
    (Amod : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))
    (b : Fin d → ℤ)
    (left : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (hreduction : ∀ x, Amod (modVec p x) = modVec p (Aint x))
    (hnull : left.comp Amod = 0)
    (hpair : left (modVec p b) ≠ 0) :
    ¬ ∃ x : Fin d → ℤ, Aint x = b := by
  rintro ⟨x, hx⟩
  have hmod : Amod (modVec p x) = modVec p b := by
    rw [hreduction x, hx]
  exact (no_mod_solution_from_left_null p Amod left
    (modVec p b) hnull hpair) ⟨modVec p x, hmod⟩

/-- A tiny deterministic finite-field negative control, not a
substitution-cycle instance. -/
theorem no_mod_two_solution_to_zero_times_x_eq_one :
    ¬ ∃ x : ZMod 2, (0 : ZMod 2) * x = 1 := by
  rintro ⟨x, hx⟩
  norm_num at hx

end PscRoutes.R1Modular

#print axioms PscRoutes.R1Modular.no_mod_solution_from_left_null
#print axioms PscRoutes.R1Modular.no_integral_solution_from_modular_witness
#print axioms PscRoutes.R1Modular.no_mod_two_solution_to_zero_times_x_eq_one

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R1Modular.no_mod_solution_from_left_null,
      `PscRoutes.R1Modular.no_integral_solution_from_modular_witness,
      `PscRoutes.R1Modular.no_mod_two_solution_to_zero_times_x_eq_one] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_R1F_AXIOMS_OK\t{name}"
