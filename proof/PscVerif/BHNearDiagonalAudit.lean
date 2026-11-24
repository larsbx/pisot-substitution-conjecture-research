import PscVerif.BHNearDiagonalLiteral
import Lean.Util.CollectAxioms

open Psc.BHNearDiagonalDescent Psc.BHNearDiagonalLiteral
open Psc.OccurrenceTransport

example {r k : ℕ} {β : ℝ} (h : Family r k β) (p : Packet)
    (ht : p.top = 1) (hb : p.bottom = 1)
    (hw : |offset (lengths r β) p.delta| ≤ (k : ℝ) - 1) :
    Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β)) p (runPacket 0 0 0) :=
  central_hits_zero h ⟨ht, hb, hw⟩

#print axioms choose_rounding
#print axioms literal_rounding_step
#print axioms central_hits_zero

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    for mod in #[`PscVerif.BHNearDiagonalDescent, `PscVerif.BHNearDiagonalLiteral] do
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
      Lean.Core.liftIOCore <| IO.println s!"PSC_BH_NEAR_DIAGONAL_AUDIT\t{mod}\t{declarations}\t{theorems}"
