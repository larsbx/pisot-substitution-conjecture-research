/- Replay directly after rebuilding both modules; do not accept a cached audit.
Every compiled declaration owned by either module is scanned, including helpers.
Endpoint specifications below are independent types, not copied inferred types.
-/
import PscVerif.C4FiniteTileAutomaton
import PscVerif.C4FamilyTileAutomatonWords
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace Psc.C4FiniteTileAutomatonAudit

open Psc.C4FiniteTileAutomaton
open Psc.C4FamilyTileAutomatonWords

def ReplayType : Prop := ∀ (v : Fin 3 → ℤ) (b : Fin 3),
  replay 1 (certificate v b) = some (b, v)

def ExistenceType : Prop := ∀ (v : Fin 3 → ℤ) (b : Fin 3),
  ∃ w : List (Fin 10), replay 1 w = some (b, v)

def ReplaySemanticsType : Prop := ∀ (a b : Fin 3) (w : List (Fin 10)) (v : Fin 3 → ℤ),
  replay a w = some (b, v) ↔ Walk a w b v

def ControlTableType : Prop := controlTable = [
  3, 3, 0, 2, 3, 3, 1, 0, 3, 3,
  1, 0, 3, 3, 3, 1, 3, 3, 3, 2,
  3, 3, 3, 3, 1, 3, 3, 3, 0, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

def OutputTableType : Prop := outputTable = [
  1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1,
  -1, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, -1]

def ReducedGraphType : Prop :=
  ¬ ∃ w : List (Fin 10), Walk 1 w 1 (basis 0) ∧ (∀ e ∈ w, ReducedEdge e)

def DisconnectedType : Prop := replay 1 [0] = none

def WrongSignType : Prop := replay 1 [7] ≠ some (1, basis 1)

def ForwardOccurrenceType : Prop := ∀ (k : ℕ), 2 ≤ k → ∀ i : Fin 5,
  ∃ n ≤ 2, OccursInIterate k n
    (source ⟨i.val, by omega⟩) (target ⟨i.val, by omega⟩)

def SignedOccurrenceType : Prop := ∀ (k : ℕ), 2 ≤ k → ∀ e : Fin 10,
  ∃ n ≤ 2, OccursInIterate k n (source e) (target e) ∨
    OccursInIterate k n (target e) (source e)

theorem wrongTypeControl : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let modules := #[`PscVerif.C4FiniteTileAutomaton, `PscVerif.C4FamilyTileAutomatonWords]
    let endpoints : Array (Name × Name × Name) := #[
      (``certificate_replay, ``ReplayType, `PscVerif.C4FiniteTileAutomaton),
      (``exists_signed_walk, ``ExistenceType, `PscVerif.C4FiniteTileAutomaton),
      (``replay_iff_walk, ``ReplaySemanticsType, `PscVerif.C4FiniteTileAutomaton),
      (``control_table_exact, ``ControlTableType, `PscVerif.C4FiniteTileAutomaton),
      (``output_table_exact, ``OutputTableType, `PscVerif.C4FiniteTileAutomaton),
      (``reduced_basis0_impossible, ``ReducedGraphType, `PscVerif.C4FiniteTileAutomaton),
      (``disconnected_rejected, ``DisconnectedType, `PscVerif.C4FiniteTileAutomaton),
      (``reversed_sign_rejected, ``WrongSignType, `PscVerif.C4FiniteTileAutomaton),
      (``all_forward_edges_have_literal_witness, ``ForwardOccurrenceType,
        `PscVerif.C4FamilyTileAutomatonWords),
      (``all_signed_edges_have_literal_witness, ``SignedOccurrenceType,
        `PscVerif.C4FamilyTileAutomatonWords)]
    let matchesType (name expected : Name) : Term.TermElabM Bool := do
      let some info := env.find? name | return false
      if !info.isTheorem then return false
      let some expectedInfo := env.find? expected | return false
      if info.levelParams.length != expectedInfo.levelParams.length then return false
      withNewMCtxDepth do
        let declaration ← mkConstWithFreshMVarLevels name
        let declarationType ← inferType declaration
        let expectedType := mkConst expected (expectedInfo.levelParams.map Level.param)
        withTransparency .all <| isDefEq declarationType expectedType
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let mut declarations := 0
    let mut proofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled finite-tile module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local finite-tile axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard finite-tile axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 || ownedProofs == 0 then throwError "Empty finite-tile module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_FINITE_TILE_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed finite-tile endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Finite-tile endpoint has no compiled owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong finite-tile endpoint owner: {name}"
      let axioms ← collectAxioms name
      let names := String.intercalate "," (axioms.toList.map toString)
      Lean.Core.liftIOCore <| IO.println s!"PSC_FINITE_TILE_ENDPOINT\t{name}\t{names}"
    let missing := `Psc.C4FiniteTileAutomatonAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (_, expected, _) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Finite-tile matcher accepted a wrong-typed theorem"
      if ← matchesType missing expected then
        throwError "Finite-tile matcher accepted a missing declaration"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_FINITE_TILE_REFUSAL_CONTROLS\t{2 * endpoints.size}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_FINITE_TILE_AUDIT_COMPLETE\t{declarations}\t{proofs}"

end Psc.C4FiniteTileAutomatonAudit
