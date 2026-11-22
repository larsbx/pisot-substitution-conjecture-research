/- Independent acceptance types for unique ergodicity of the literal family.
The audit refuses the uniqueness statements with the invariance premise
removed, and the spectral statement with the scope premise `2 ≤ k` removed. -/
import PscVerif.C4FamilyUniqueErgodicity
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace Psc.C4FamilyUniqueErgodicityAudit

open MeasureTheory Function
open scoped Psc.PeriodicPartnerSolenoidHaar Psc.C4FamilyMeasuredRealization
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (pisotData)
open Psc.PeriodicPartnerRealization (Solenoid flow)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate)
open Psc.PeriodicPartnerSolenoidHaar (haar)
open Psc.C4FamilyMeasuredRealization (hullMeasure)
open Psc.C4FamilyMeasuredSpectrum (translationPhase)

def SolenoidUniqueType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (ν : Measure (Solenoid (geometry k hk))) [IsProbabilityMeasure ν],
    (∀ t, MeasurePreserving (flow (pisotData k hk) t) ν ν) → ν = haar (geometry k hk)

def HullUniqueType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) (μ : Measure (LocalHull (geometry k hk)))
    [IsProbabilityMeasure μ],
    (∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ) → μ = hullMeasure k hk hk₂

def PureDiscreteType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ (μ : Measure (LocalHull (geometry k hk)))
    [IsProbabilityMeasure μ]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ),
    (Submodule.span ℂ {v : Lp ℂ 2 μ | v ≠ 0 ∧ ∃ ξ : ℝ, ∀ t : ℝ,
      Lp.compMeasurePreservingₗᵢ ℂ (translate (geometry k hk) t) (hμ t) v =
        translationPhase t ξ • v}).topologicalClosure = ⊤

/-- Altered contract: every probability on the solenoid is Haar. -/
def SolenoidNoInvarianceType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (ν : Measure (Solenoid (geometry k hk))) [IsProbabilityMeasure ν],
    ν = haar (geometry k hk)

/-- Altered contract: every probability on the hull is the lifted Haar measure. -/
def HullNoInvarianceType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) (μ : Measure (LocalHull (geometry k hk)))
    [IsProbabilityMeasure μ], μ = hullMeasure k hk hk₂

/-- Altered contract: the spectral conclusion at `k ≥ 1`, without `2 ≤ k`. -/
def PureDiscreteNoScopeType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (μ : Measure (LocalHull (geometry k hk)))
    [IsProbabilityMeasure μ]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ),
    (Submodule.span ℂ {v : Lp ℂ 2 μ | v ≠ 0 ∧ ∃ ξ : ℝ, ∀ t : ℝ,
      Lp.compMeasurePreservingₗᵢ ℂ (translate (geometry k hk) t) (hμ t) v =
        translationPhase t ξ • v}).topologicalClosure = ⊤

theorem wrongTypeControl : True := trivial

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let mod := `PscVerif.C4FamilyUniqueErgodicity
    let endpoints : Array (Name × Name) := #[
      (`Psc.C4FamilyUniqueErgodicity.flowInvariant_eq_haar, ``SolenoidUniqueType),
      (`Psc.C4FamilyUniqueErgodicity.translationInvariant_eq_hullMeasure, ``HullUniqueType),
      (`Psc.C4FamilyUniqueErgodicity.pureDiscrete_of_invariant, ``PureDiscreteType)]
    let semanticRefusals : Array (Name × Name) := #[
      (`Psc.C4FamilyUniqueErgodicity.flowInvariant_eq_haar, ``SolenoidNoInvarianceType),
      (`Psc.C4FamilyUniqueErgodicity.translationInvariant_eq_hullMeasure, ``HullNoInvarianceType),
      (`Psc.C4FamilyUniqueErgodicity.pureDiscrete_of_invariant, ``PureDiscreteNoScopeType)]
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
    let some index := env.getModuleIdx? mod | throwError "Missing compiled unique-ergodicity module"
    let data := env.header.moduleData[index.toNat]!
    let mut declarations := 0
    let mut proofs := 0
    for info in data.constants do
      let some owner := env.getModuleIdxFor? info.name | continue
      if owner != index then continue
      if info.isAxiom then throwError "Local unique-ergodicity axiom: {info.name}"
      for ax in ← collectAxioms info.name do
        unless allowed.contains ax do
          throwError "Nonstandard unique-ergodicity axiom in {info.name}: {ax}"
      declarations := declarations + 1
      if info.isTheorem then proofs := proofs + 1
    if declarations == 0 || proofs == 0 then throwError "Empty unique-ergodicity module"
    for (name, expected) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed unique-ergodicity endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Unique-ergodicity endpoint has no compiled owner: {name}"
      unless owner == index do throwError "Wrong unique-ergodicity endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_UNIQUE_ERGODICITY_ENDPOINT\t{name}"
    let missing := `Psc.C4FamilyUniqueErgodicityAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (_, expected) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Unique-ergodicity matcher accepted a wrong-typed theorem"
      if ← matchesType missing expected then
        throwError "Unique-ergodicity matcher accepted a missing declaration"
    for (name, wrong) in semanticRefusals do
      if ← matchesType name wrong then
        throwError "Unique-ergodicity matcher accepted altered contract {wrong} for {name}"
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_UNIQUE_ERGODICITY_CONTRACT_REFUSED\t{name}\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_UNIQUE_ERGODICITY_REFUSAL_CONTROLS\t{2 * endpoints.size + semanticRefusals.size}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_UNIQUE_ERGODICITY_AUDIT_COMPLETE\t{declarations}\t{proofs}"

end Psc.C4FamilyUniqueErgodicityAudit
