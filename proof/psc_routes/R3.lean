import Mathlib
import Lean.Util.CollectAxioms

/-!
# Route R3: literal prefix shifts and block-discrepancy bounds

The lemmas are exact and computable. Uniform existence of the block cuts
for all substitution depths, and eventual coincidence/productivity,
remain open. No implication from balance alone is claimed.
-/
namespace PscRoutes.R3

/-- A two-track difference of coordinate prefix counts, each no
larger than the common block length, is bounded by that length. -/
theorem bounded_block_coordinate
    (blockLength topCount bottomCount : ℕ)
    (htop : topCount ≤ blockLength)
    (hbottom : bottomCount ≤ blockLength) :
    -(blockLength : ℤ) ≤ (topCount : ℤ) - bottomCount ∧
    (topCount : ℤ) - bottomCount ≤ (blockLength : ℤ) := by
  constructor <;> omega

/-- The B-prime shift/factor identity is algebraic, independent of
frequencies, primitivity, or assumptions about balanced cuts. -/
theorem shift_factor_identity (P : ℕ → ℤ) (t k : ℕ) :
    P k - (P (t + k) - P t) =
      P t - (P (k + t) - P k) := by
  rw [Nat.add_comm t k]
  ring

end PscRoutes.R3

#print axioms PscRoutes.R3.bounded_block_coordinate
#print axioms PscRoutes.R3.shift_factor_identity

/- Fail-closed exact-declaration axiom audit for this standalone branch.
   All declared helper theorems must use only the standard Lean axioms.
   This does not establish a full substitution-to-Lemma refinement. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R3.bounded_block_coordinate, `PscRoutes.R3.shift_factor_identity] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_ROUTE_AXIOMS_OK\t{name}"
