/- Replay after freshly compiling both character modules.
Expected endpoint types independently retain finite support, every history
level, the exact frequency denominator, the actual family factor map, and the
explicit nonunit witness. All owned declarations are recursively axiom-audited.
The changed-contract refusals test type matching only, except that the actual
nonunit-history theorems separately disprove zeroth-coordinate injectivity and
prove the displayed minus sign.
-/
import PscVerif.PeriodicPartnerSolenoidCharacters
import PscVerif.C4FamilySolenoidCharacters
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace Psc.C4SolenoidCharactersAudit

open Function Set Matrix
open Psc.PeriodicPartnerHull (LengthSubst)
open Psc.PeriodicPartnerRealization (Torus Solenoid PisotData flow mat)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate)
open Psc.PeriodicPartnerSolenoidCharacters
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize)
open Psc.C4FamilySolenoidCharacters
open scoped Topology

universe u

def TorusCoordinateType : Prop :=
  ∀ {α : Type u} (a : α) (v : α → ℝ),
    torusCoordinate a (v : Torus α) = (v a : UnitAddCircle)

def TorusExtType : Prop :=
  ∀ {α : Type u} {z w : Torus α},
    (∀ a, torusCoordinate a z = torusCoordinate a w) → z = w

def PhaseAddType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c d : (ℕ × α) →₀ ℤ) (z : Solenoid S),
    phase S (c + d) z = phase S c z + phase S d z

def PhaseNegType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c : (ℕ × α) →₀ ℤ) (z : Solenoid S),
    phase S (-c) z = -phase S c z

def PhaseSingleType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (ni : ℕ × α) (e : ℤ) (z : Solenoid S),
    phase S (Finsupp.single ni e) z = e • torusCoordinate ni.2 (z.1 ni.1)

def PhaseContinuousType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c : (ℕ × α) →₀ ℤ), Continuous (phase S c)

def CharacterAddType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c d : (ℕ × α) →₀ ℤ),
    character S (c + d) = character S c * character S d

def CharacterNegType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c : (ℕ × α) →₀ ℤ), character S (-c) = star (character S c)

def CharacterNormType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c : (ℕ × α) →₀ ℤ) (z : Solenoid S), ‖character S c z‖ = 1

def CharacterGroupType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c : (ℕ × α) →₀ ℤ) (z w : Solenoid S),
    character S c (z + w) = character S c z * character S c w

def FrequencyAddType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (P : PisotData S) (c d : (ℕ × α) →₀ ℤ),
    frequency S P (c + d) = frequency S P c + frequency S P d

def FrequencySingleType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (P : PisotData S) (ni : ℕ × α) (e : ℤ),
    frequency S P (Finsupp.single ni e) = (e : ℝ) * P.u ni.2 / S.β ^ ni.1

def PhaseFlowType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) [Nonempty α] (P : PisotData S) (c : (ℕ × α) →₀ ℤ) (t : ℝ),
    phase S c (flow P t 0) = ((t * c.sum (fun ni e => (e : ℝ) * P.u ni.2 / S.β ^ ni.1) : ℝ) : UnitAddCircle)

def FlowCharacterType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) [Nonempty α] (P : PisotData S) (c : (ℕ × α) →₀ ℤ)
    (t : ℝ) (z : Solenoid S), character S c (flow P t z) =
      Complex.exp (((2 * Real.pi * (t * c.sum (fun ni e => (e : ℝ) * P.u ni.2 / S.β ^ ni.1)) : ℝ) : ℂ) * Complex.I) * character S c z

def CharacterExtType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) {z w : Solenoid S},
    (∀ c : (ℕ × α) →₀ ℤ, character S c z = character S c w) → z = w

def SingleSeparatesType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) {z w : Solenoid S}, z ≠ w →
    ∃ n a, character S (Finsupp.single (n, a) 1) z ≠ character S (Finsupp.single (n, a) 1) w

def AlgebraSpanType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α),
    (characterAlgebra S).toSubalgebra.toSubmodule = Submodule.span ℂ (range (character S))

def CharacterDenseType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α),
    (Submodule.span ℂ (range (character S))).topologicalClosure = ⊤

def FamilyNormType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : (ℕ × Fin 3) →₀ ℤ) (T : LocalHull (geometry k hk)),
    ‖eigenfunction k hk c T‖ = 1

def FamilyTranslationType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : (ℕ × Fin 3) →₀ ℤ) (t : ℝ) (T : LocalHull (geometry k hk)),
    eigenfunction k hk c (translate (geometry k hk) t T) =
      Complex.exp (((2 * Real.pi * (t * c.sum (fun ni e => (e : ℝ) * (pisotData k hk).u ni.2 / (geometry k hk).β ^ ni.1)) : ℝ) : ℂ) * Complex.I) *
        eigenfunction k hk c T

def FamilyImageType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (T U : LocalHull (geometry k hk)),
    (∀ c : (ℕ × Fin 3) →₀ ℤ, eigenfunction k hk c T = eigenfunction k hk c U) ↔
      solenoidRealize k hk T = solenoidRealize k hk U

def FamilyDenseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    (Submodule.span ℂ (range (character (geometry k hk)))).topologicalClosure = ⊤

def MatrixInverseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (v : Fin 3 → ℝ),
    mat (geometry k hk) *ᵥ ![v 1 - (k : ℝ) * v 2 - (v 0 - v 2) / 2,
      v 2, (v 0 - v 2) / 2] = v

def ControlZeroType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), (nonunitHistory k hk).1 0 = 0

def ControlFirstType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    torusCoordinate (2 : Fin 3) ((nonunitHistory k hk).1 1) = ((1 / 2 : ℝ) : UnitAddCircle)

def ControlSignType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    character (geometry k hk) (Finsupp.single (1, (2 : Fin 3)) 1) (nonunitHistory k hk) = -1

def ControlNonzeroType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), nonunitHistory k hk ≠ 0

def ControlProjectionType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), ¬ Injective (fun z : Solenoid (geometry k hk) => z.1 0)

/- Changed contract: a type-refusal control, not a new counterexample proof. -/
def WrongProductType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c d : (ℕ × α) →₀ ℤ),
    character S (c + d) = character S c + character S d

/- Changed contract: a type-refusal control, not a new counterexample proof. -/
def MissingConjugationType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) (c : (ℕ × α) →₀ ℤ), character S (-c) = character S c

/- Changed contract: a type-refusal control, not a new counterexample proof. -/
def MissingPhaseType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) [Nonempty α] (P : PisotData S) (c : (ℕ × α) →₀ ℤ)
    (t : ℝ) (z : Solenoid S), character S c (flow P t z) = character S c z

/- Changed contract: a type-refusal control, not a new counterexample proof. -/
def MissingDenominatorType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) [Nonempty α] (P : PisotData S) (c : (ℕ × α) →₀ ℤ)
    (t : ℝ) (z : Solenoid S), character S c (flow P t z) =
      Complex.exp (((2 * Real.pi *
        (t * c.sum (fun ni e => (e : ℝ) * P.u ni.2)) : ℝ) : ℂ) * Complex.I) * character S c z

/- Changed contract: a type-refusal control, not a new counterexample proof. -/
def ZerothSeparatesType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α) {z w : Solenoid S}, z.1 0 = w.1 0 → z = w

/- Changed contract: a type-refusal control, not a new counterexample proof. -/
def WrongControlSignType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    character (geometry k hk) (Finsupp.single (1, (2 : Fin 3)) 1) (nonunitHistory k hk) = 1

/- Changed contract: a type-refusal control, not a new counterexample proof. -/
def ZeroProjectionInjectiveType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), Injective (fun z : Solenoid (geometry k hk) => z.1 0)

/- Changed contract: a type-refusal control, not a new counterexample proof. -/
def UnprovedHullDenseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    (Submodule.span ℂ (range (eigenfunction k hk))).topologicalClosure = ⊤

theorem wrongTypeControl : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let generic := `PscVerif.PeriodicPartnerSolenoidCharacters
    let family := `PscVerif.C4FamilySolenoidCharacters
    let modules := #[generic, family]
    let endpoints : Array (Name × Name × Name) := #[
      (`Psc.PeriodicPartnerSolenoidCharacters.torusCoordinate_mk, ``TorusCoordinateType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.torusCoordinate_ext, ``TorusExtType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.phase_add, ``PhaseAddType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.phase_neg, ``PhaseNegType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.phase_single, ``PhaseSingleType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.continuous_phase, ``PhaseContinuousType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_add, ``CharacterAddType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_neg, ``CharacterNegType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_norm, ``CharacterNormType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_map_add, ``CharacterGroupType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.frequency_add, ``FrequencyAddType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.frequency_single, ``FrequencySingleType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.phase_flow_zero, ``PhaseFlowType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_flow, ``FlowCharacterType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_ext, ``CharacterExtType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.exists_single_character_ne, ``SingleSeparatesType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.characterAlgebra_toSubmodule, ``AlgebraSpanType, generic),
      (`Psc.PeriodicPartnerSolenoidCharacters.span_character_closure_eq_top, ``CharacterDenseType, generic),
      (`Psc.C4FamilySolenoidCharacters.eigenfunction_norm, ``FamilyNormType, family),
      (`Psc.C4FamilySolenoidCharacters.eigenfunction_translate, ``FamilyTranslationType, family),
      (`Psc.C4FamilySolenoidCharacters.eigenfunctions_eq_iff, ``FamilyImageType, family),
      (`Psc.C4FamilySolenoidCharacters.solenoid_character_span_dense, ``FamilyDenseType, family),
      (`Psc.C4FamilySolenoidCharacters.mat_predecessor, ``MatrixInverseType, family),
      (`Psc.C4FamilySolenoidCharacters.nonunitHistory_coord_zero, ``ControlZeroType, family),
      (`Psc.C4FamilySolenoidCharacters.nonunitHistory_coord_one_two, ``ControlFirstType, family),
      (`Psc.C4FamilySolenoidCharacters.nonunitHistory_character, ``ControlSignType, family),
      (`Psc.C4FamilySolenoidCharacters.nonunitHistory_ne_zero, ``ControlNonzeroType, family),
      (`Psc.C4FamilySolenoidCharacters.coord_zero_not_injective, ``ControlProjectionType, family)]
    let semanticRefusals : Array (Name × Name) := #[
      (`Psc.PeriodicPartnerSolenoidCharacters.character_add, ``WrongProductType),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_neg, ``MissingConjugationType),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_flow, ``MissingPhaseType),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_flow, ``MissingDenominatorType),
      (`Psc.PeriodicPartnerSolenoidCharacters.character_ext, ``ZerothSeparatesType),
      (`Psc.C4FamilySolenoidCharacters.nonunitHistory_character, ``WrongControlSignType),
      (`Psc.C4FamilySolenoidCharacters.coord_zero_not_injective, ``ZeroProjectionInjectiveType),
      (`Psc.C4FamilySolenoidCharacters.solenoid_character_span_dense, ``UnprovedHullDenseType)]
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
        | throwError "Missing compiled solenoid-character module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local solenoid-character axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard solenoid-character axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 || ownedProofs == 0 then throwError "Empty solenoid-character module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_SOLENOID_CHARACTER_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed solenoid-character endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Finite-hull endpoint has no compiled owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong solenoid-character endpoint owner: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard solenoid-character endpoint axiom in {name}: {ax}"
      let names := String.intercalate "," (axioms.toList.map toString)
      Lean.Core.liftIOCore <| IO.println s!"PSC_SOLENOID_CHARACTER_ENDPOINT\t{name}\t{names}"
    let missing := `Psc.C4SolenoidCharactersAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (_, expected, _) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Finite-hull matcher accepted a wrong-typed theorem"
      if ← matchesType missing expected then
        throwError "Finite-hull matcher accepted a missing declaration"
    for (name, wrong) in semanticRefusals do
      if ← matchesType name wrong then
        throwError "Finite-hull matcher accepted altered contract {wrong} for {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_SOLENOID_CHARACTER_CONTRACT_REFUSED\t{name}\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_SOLENOID_CHARACTER_REFUSAL_CONTROLS\t{2 * endpoints.size + semanticRefusals.size}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_SOLENOID_CHARACTER_AUDIT_COMPLETE\t{declarations}\t{proofs}"


end Psc.C4SolenoidCharactersAudit
