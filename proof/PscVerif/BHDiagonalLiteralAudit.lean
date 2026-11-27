import PscVerif.BHDiagonalLiteral
import Lean.Util.CollectAxioms

open Psc.OccurrenceTransport Psc.BHNearDiagonalLiteral

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β)
    (x y z t : ℤ) (hs : Central r r β (runPacket x y z))
    (ht : |(t : ℝ) + ((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β) :
    InteriorStep (sigma r r) (lengths r β) (runPacket x y z)
      (runPacket (y+(r : ℤ)*z) t y) ∧ Central r r β (runPacket (y+(r : ℤ)*z) t y) :=
  Psc.BHDiagonalLiteral.literal_rounding_step h x y z t hs ht

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket (-1) 1 (-1)) Psc.BHDiagonalLiteral.zero00 :=
  Psc.BHDiagonalLiteral.unit_injection_hits_labelled_zero h

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β) (x : ℤ)
    (hs : Central r r β (runPacket x 0 0)) :
    InteriorStep (sigma r r) (lengths r β) (runPacket x 0 0) (runPacket 0 0 0) :=
  Psc.BHDiagonalLiteral.central_zero_pair_step h x hs

example (r : ℕ) (β : ℝ) : ¬ Central r r β (runPacket r 0 0) :=
  Psc.BHDiagonalLiteral.saturation_not_central r β

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β) :
    (runPacket r 0 0).delta ≠ 0 := Psc.BHDiagonalLiteral.saturation_not_zero h

example : Psc.BHDiagonalLiteral.zero12.top ≠ Psc.BHDiagonalLiteral.zero12.bottom :=
  Psc.BHDiagonalLiteral.zero12_not_labelled

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β) :
    ¬ Psc.BHNearDiagonalDescent.Window (β-r) (r/β) (((r : ℝ)-1)/β) :=
  Psc.BHDiagonalLiteral.not_near_diagonal_window h

#print axioms literal_rounding_step_of_runFamily
#print axioms Psc.BHDiagonalLiteral.literal_rounding_step
#print axioms Psc.BHDiagonalLiteral.unit_injection_hits_labelled_zero
#print axioms Psc.BHDiagonalLiteral.central_zero_pair_step

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    for mod in #[`PscVerif.BHNearDiagonalLiteral, `PscVerif.BHDiagonalLiteral] do
      let some index := env.getModuleIdx? mod | throwError "Missing module {mod}"
      let mut declarations := 0
      let mut theorems := 0
      for info in env.header.moduleData[index.toNat]!.constants do
        unless env.getModuleIdxFor? info.name == some index do continue
        if info.isAxiom then throwError "Local axiom {info.name}"
        for ax in ← collectAxioms info.name do
          unless allowed.contains ax do
            throwError "Unexpected axiom in {info.name}: {ax}"
        declarations := declarations + 1
        if info.isTheorem then theorems := theorems + 1
      if theorems == 0 then throwError "Empty compiled module {mod}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_BH_DIAGONAL_LITERAL_AUDIT\t{mod}\t{declarations}\t{theorems}"
