/- Replay with `lake env lean C4ParameterFamilyAudit.lean` after compiling the
family modules. This is an endpoint acceptance fixture, not a cached library
target. The unchanged full proof-bank audit separately inspects every imported
project constant. -/
import PscVerif.C4ParameterFamilyCarrier
import PscVerif.C4ParameterFamilyControls
import Lean.Util.CollectAxioms

namespace Psc.ParameterFamilyAudit

/-- Independent literal binding: 0 ↦ 1, 1 ↦ 0 1^k 2, 2 ↦ 001. -/
def literalSubstitution (k : Nat) (a : Fin 3) : List (Fin 3) :=
  if a = 0 then [1]
  else if a = 1 then [0] ++ List.replicate k 1 ++ [2]
  else [0, 0, 1]

def FiniteAndProductiveType : Prop :=
  ∀ k : Nat, 2 ≤ k →
    {T | Relation.ReflTransGen (Psc.Descendants.ChildNC (literalSubstitution k))
      ([0, 1], [1, 0]) T}.Finite ∧
    ∀ T, Relation.ReflTransGen (Psc.Descendants.ChildNC (literalSubstitution k))
      ([0, 1], [1, 0]) T →
      ∃ U, Relation.ReflTransGen (Psc.Descendants.ChildNC (literalSubstitution k))
        T U ∧ U.1 = U.2

def CoincidenceChildType : Prop :=
  ∀ k : Nat, 3 ≤ k → ∀ {T : List (Fin 3) × List (Fin 3)},
    Relation.ReflTransGen (Psc.Descendants.ChildNC (literalSubstitution k))
      ([0, 1], [1, 0]) T → T.1 ≠ T.2 →
      ∃ U, Psc.Descendants.ChildNC (literalSubstitution k) T U ∧ U.1 = U.2

def TerminationType : Prop :=
  ∀ k : Nat, 2 ≤ k →
    Psc.StrictSystem.TerminatesWithCoincidence (literalSubstitution k)
      ([0, 1], [1, 0])

-- These are whole declaration assignments, so an extra premise, another seed,
-- a different substitution or a weaker parameter range cannot be supplied.
example : FiniteAndProductiveType := Psc.ParameterFamily.finite_and_productive
example : CoincidenceChildType := Psc.ParameterFamily.coincidence_child
example : TerminationType := Psc.ParameterFamily.terminates_with_coincidence

/-- A theorem of the right declaration kind but the wrong semantic type. -/
theorem wrongTypeControl : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name) := #[
      (``Psc.ParameterFamily.finite_and_productive, ``FiniteAndProductiveType),
      (``Psc.ParameterFamily.coincidence_child, ``CoincidenceChildType),
      (``Psc.ParameterFamily.terminates_with_coincidence, ``TerminationType)]
    let env ← getEnv
    let matchesType (name expected : Name) : Term.TermElabM Bool := do
      let some info := env.find? name | return false
      if !info.isTheorem then return false
      withTransparency .all <| isDefEq info.type (mkConst expected)
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let modules := #[`PscVerif.Termination, `PscVerif.C4ParameterFamilyWords,
      `PscVerif.C4ParameterFamilyCarrier, `PscVerif.C4ParameterFamilyControls]
    let mut declarations := 0
    let mut proofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled family module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local family axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard family axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 then throwError "Empty compiled family module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println s!"PSC_PARAMETER_FAMILY_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_PARAMETER_FAMILY_DECLARATIONS\t4\t{declarations}\t{proofs}"
    for (name, expected) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed family endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Family endpoint has no imported owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == `PscVerif.C4ParameterFamilyCarrier do
        throwError "Wrong family endpoint owner: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard family endpoint axiom in {name}: {ax}"
      let names := String.intercalate "," (axioms.toList.map toString)
      Lean.Core.liftIOCore <| IO.println s!"PSC_PARAMETER_FAMILY_ENDPOINT\t{name}\t{names}"
    -- Exercise the same recognizer independently of the successful endpoints.
    -- Missing declarations and harmless True proofs both must be refused.
    if (env.find? `Psc.ParameterFamilyAudit.absentEndpoint).isSome then
      throwError "Missing-declaration control name collision"
    for (_, expected) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Family endpoint audit accepted a wrong-type theorem"
      if ← matchesType `Psc.ParameterFamilyAudit.absentEndpoint expected then
        throwError "Family endpoint audit accepted a missing declaration"
    Lean.Core.liftIOCore <| IO.println "PSC_PARAMETER_FAMILY_AUDIT_COMPLETE\t3\t6"

end Psc.ParameterFamilyAudit
