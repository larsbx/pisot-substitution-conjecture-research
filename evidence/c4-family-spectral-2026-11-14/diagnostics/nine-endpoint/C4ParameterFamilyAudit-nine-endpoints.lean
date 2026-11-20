/- Replay with `lake env lean C4ParameterFamilyAudit.lean` after compiling the
family modules. This is an endpoint acceptance fixture, not a cached library
target. The unchanged full proof-bank audit separately inspects every imported
project constant. -/
import PscVerif.C4ParameterFamilyBridge
import PscVerif.C4ParameterFamilyControls
import Lean.Util.CollectAxioms

namespace Psc.ParameterFamilyAudit

open Psc.Binomial (subst)
open Psc.Reduction (red IsBlock)
open Psc.Incidence (inc)

universe u

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

def PrimitiveType : Prop :=
  ∀ k : Nat, 1 ≤ k → ∃ n ≥ 1,
    ∀ a c, 0 < (inc (literalSubstitution k) ^ n) a c

def IrreducibleType : Prop :=
  ∀ k : Nat, 1 ≤ k →
    Irreducible ((inc (literalSubstitution k)).map (Nat.cast : Nat → Rat)).charpoly

def PisotType : Prop :=
  ∀ k : Nat, 1 ≤ k → ∃ b : Real, 2 < b ∧
    Polynomial.aeval (b : Complex)
      ((inc (literalSubstitution k)).map (Nat.cast : Nat → Rat)).charpoly = 0 ∧
    ∀ z : Complex,
      Polynomial.aeval z
        ((inc (literalSubstitution k)).map (Nat.cast : Nat → Rat)).charpoly = 0 →
      z ≠ b → ‖z‖ < 1

/-- The complete generic theorem, including its alphabet, block and finiteness
hypotheses, is checked at an arbitrary universe. -/
def FactorsEquivalenceType : Prop :=
  ∀ {α : Type u} [DecidableEq α] [Finite α] {s : α → List α}
    {T : List α × List α}, IsBlock T →
    (Psc.StrictSystem.TerminatesWithCoincidence s T ↔
      {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite ∧
        ∀ U, (∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)) →
          ∃ m a, ([a], [a]) ∈ red ((subst s)^[m] U.1) ((subst s)^[m] U.2))

def FullFactorTerminationType : Prop :=
  ∀ k : Nat, 2 ≤ k →
    {U | ∃ n, U ∈ red ((subst (literalSubstitution k))^[n] [0, 1])
      ((subst (literalSubstitution k))^[n] [1, 0])}.Finite ∧
      ∀ U, (∃ n, U ∈ red ((subst (literalSubstitution k))^[n] [0, 1])
        ((subst (literalSubstitution k))^[n] [1, 0])) →
        ∃ m a, ([a], [a]) ∈ red ((subst (literalSubstitution k))^[m] U.1)
          ((subst (literalSubstitution k))^[m] U.2)

def SpectralCriterionInputsType : Prop :=
  ∀ k : Nat, 2 ≤ k →
    (∃ n ≥ 1, ∀ a c, 0 < (inc (literalSubstitution k) ^ n) a c) ∧
    Irreducible ((inc (literalSubstitution k)).map (Nat.cast : Nat → Rat)).charpoly ∧
    (∃ b : Real, 2 < b ∧ Irrational b ∧
      Polynomial.aeval (b : Complex)
        ((inc (literalSubstitution k)).map (Nat.cast : Nat → Rat)).charpoly = 0 ∧
      (∀ z : Complex,
        Polynomial.aeval z
          ((inc (literalSubstitution k)).map (Nat.cast : Nat → Rat)).charpoly = 0 →
        z ≠ b → ‖z‖ < 1) ∧
      ∃ w : Fin 3 → Real, (∀ a, 0 < w a) ∧
        Matrix.vecMul w ((inc (literalSubstitution k)).map (Nat.cast : Nat → Real)) =
          b • w) ∧
    {U | ∃ n, U ∈ red ((subst (literalSubstitution k))^[n] [0, 1])
      ((subst (literalSubstitution k))^[n] [1, 0])}.Finite ∧
      ∀ U, (∃ n, U ∈ red ((subst (literalSubstitution k))^[n] [0, 1])
        ((subst (literalSubstitution k))^[n] [1, 0])) →
        ∃ m a, ([a], [a]) ∈ red ((subst (literalSubstitution k))^[m] U.1)
          ((subst (literalSubstitution k))^[m] U.2)

-- These are whole declaration assignments, so an extra premise, another seed,
-- a different substitution or a weaker parameter range cannot be supplied.
example : FiniteAndProductiveType := Psc.ParameterFamily.finite_and_productive
example : CoincidenceChildType := Psc.ParameterFamily.coincidence_child
example : TerminationType := Psc.ParameterFamily.terminates_with_coincidence
example : PrimitiveType := Psc.ParameterFamilyPisot.primitive
example : IrreducibleType := Psc.ParameterFamilyPisot.irreducible
example : PisotType := Psc.ParameterFamilyPisot.pisot
example : FactorsEquivalenceType.{u} :=
  Psc.TerminationFactors.terminates_iff_finite_factors_and_coincidences
example : FullFactorTerminationType := Psc.ParameterFamilyBridge.full_factor_termination
example : SpectralCriterionInputsType := Psc.ParameterFamilyBridge.spectral_criterion_inputs

/-- A theorem of the right declaration kind but the wrong semantic type. -/
theorem wrongTypeControl : True := True.intro

/-- Match the universe and binder shape so the generic negative control also
exercises semantic type rejection, not merely a universe-arity mismatch. -/
theorem wrongPolymorphicTypeControl :
    ∀ {α : Type u} [DecidableEq α] [Finite α] {s : α → List α}
      {T : List α × List α}, IsBlock T → True := by
  intros
  trivial

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``Psc.ParameterFamily.finite_and_productive, ``FiniteAndProductiveType,
        `PscVerif.C4ParameterFamilyCarrier),
      (``Psc.ParameterFamily.coincidence_child, ``CoincidenceChildType,
        `PscVerif.C4ParameterFamilyCarrier),
      (``Psc.ParameterFamily.terminates_with_coincidence, ``TerminationType,
        `PscVerif.C4ParameterFamilyCarrier),
      (``Psc.ParameterFamilyPisot.primitive, ``PrimitiveType,
        `PscVerif.C4ParameterFamilyPisot),
      (``Psc.ParameterFamilyPisot.irreducible, ``IrreducibleType,
        `PscVerif.C4ParameterFamilyPisot),
      (``Psc.ParameterFamilyPisot.pisot, ``PisotType,
        `PscVerif.C4ParameterFamilyPisot),
      (``Psc.TerminationFactors.terminates_iff_finite_factors_and_coincidences,
        ``FactorsEquivalenceType, `PscVerif.TerminationFactors),
      (``Psc.ParameterFamilyBridge.full_factor_termination, ``FullFactorTerminationType,
        `PscVerif.C4ParameterFamilyBridge),
      (``Psc.ParameterFamilyBridge.spectral_criterion_inputs, ``SpectralCriterionInputsType,
        `PscVerif.C4ParameterFamilyBridge)]
    let env ← getEnv
    let matchesType (name expected : Name) : Term.TermElabM Bool := do
      let some info := env.find? name | return false
      if !info.isTheorem then return false
      let some expectedInfo := env.find? expected | return false
      if info.levelParams.length != expectedInfo.levelParams.length then return false
      withNewMCtxDepth do
        let declaration ← mkConstWithFreshMVarLevels name
        let declarationType ← inferType declaration
        -- Expected universe parameters remain rigid: a Type-0 specialization
        -- cannot be substituted for the universe-polymorphic generic endpoint.
        let expectedType := mkConst expected (expectedInfo.levelParams.map Level.param)
        withTransparency .all <| isDefEq declarationType expectedType
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let modules := #[`PscVerif.Termination, `PscVerif.C4ParameterFamilyWords,
      `PscVerif.C4ParameterFamilyCarrier, `PscVerif.C4ParameterFamilyControls,
      `PscVerif.C4ParameterFamilyPisot, `PscVerif.TerminationFactors,
      `PscVerif.C4ParameterFamilyBridge]
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
    Lean.Core.liftIOCore <| IO.println s!"PSC_PARAMETER_FAMILY_DECLARATIONS\t7\t{declarations}\t{proofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed family endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Family endpoint has no imported owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
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
    for (_, expected, _) in endpoints do
      let expectedInfo ← getConstInfo expected
      let wrong := if expectedInfo.levelParams.isEmpty then ``wrongTypeControl
        else ``wrongPolymorphicTypeControl
      if ← matchesType wrong expected then
        throwError "Family endpoint audit accepted a wrong-type theorem"
      if ← matchesType `Psc.ParameterFamilyAudit.absentEndpoint expected then
        throwError "Family endpoint audit accepted a missing declaration"
    Lean.Core.liftIOCore <| IO.println "PSC_PARAMETER_FAMILY_AUDIT_COMPLETE\t9\t18"

end Psc.ParameterFamilyAudit
