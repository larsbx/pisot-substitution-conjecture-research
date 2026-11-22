/- Independent acceptance types for actual finite character orbit samples.
The nontriviality premise concerns the represented character, not its
integer certificate. The literal compatibility certificate supplies a
proved counterexample to that proposed weakening. -/
import PscVerif.C4FamilyCharacterOrbits
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace Psc.C4CharacterOrbitsAudit

open Function Set
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (pisotData)
open Psc.PeriodicPartnerRealization (Solenoid flow shiftS)
open Psc.PeriodicPartnerSolenoidCharacters (Certificate character frequency)
open Psc.C4FamilyCharacterOrbits (orbitCharacter)

def ShiftFlowType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (z : Solenoid (geometry k hk)),
    shiftS (geometry k hk) (flow (pisotData k hk) t z) =
      flow (pisotData k hk) ((geometry k hk).β * t) (shiftS (geometry k hk) z)

def IterateFlowType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (t : ℝ) (z : Solenoid (geometry k hk)),
    (shiftS (geometry k hk))^[n] (flow (pisotData k hk) t z) =
      flow (pisotData k hk) ((geometry k hk).β ^ n * t)
        ((shiftS (geometry k hk))^[n] z)

def IterateZeroType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (n : ℕ), (shiftS (geometry k hk))^[n] 0 = 0

def OrbitApplyType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)) (n : ℕ)
    (z : Solenoid (geometry k hk)),
    orbitCharacter k hk c n z = character (geometry k hk) c
      ((shiftS (geometry k hk))^[n] z)

def OrbitZeroType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)),
    orbitCharacter k hk c 0 = character (geometry k hk) c

def OrbitNormType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)) (n : ℕ)
    (z : Solenoid (geometry k hk)), ‖orbitCharacter k hk c n z‖ = 1

def OrbitAddType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)) (n : ℕ)
    (z w : Solenoid (geometry k hk)),
    orbitCharacter k hk c n (z + w) =
      orbitCharacter k hk c n z * orbitCharacter k hk c n w

def OrbitFlowType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)) (n : ℕ) (t : ℝ),
    orbitCharacter k hk c n (flow (pisotData k hk) t 0) =
      (AddCircle.toCircle (((t * ((geometry k hk).β ^ n *
        frequency (geometry k hk) (pisotData k hk) c) : ℝ) : UnitAddCircle)) : ℂ)

def EqualFrequencyType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)) {m n : ℕ},
    orbitCharacter k hk c m = orbitCharacter k hk c n →
    (geometry k hk).β ^ m * frequency (geometry k hk) (pisotData k hk) c =
      (geometry k hk).β ^ n * frequency (geometry k hk) (pisotData k hk) c

def ZeroFrequencyType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)),
    frequency (geometry k hk) (pisotData k hk) c = 0 → character (geometry k hk) c = 1

def InjectiveOrbitType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)),
    character (geometry k hk) c ≠ 1 → Injective (orbitCharacter k hk c)

def PeriodicCharacterType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)) {p : ℕ}, 0 < p →
    (∀ z : Solenoid (geometry k hk),
      character (geometry k hk) c ((shiftS (geometry k hk))^[p] z) =
        character (geometry k hk) c z) → character (geometry k hk) c = 1

def FiniteOrbitType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)),
    character (geometry k hk) c ≠ 1 → ∀ N : ℕ,
    Injective (fun i : Fin N => orbitCharacter k hk c i.1)

noncomputable def ControlCertificate : Certificate (Fin 3) :=
  Finsupp.single (0, (2 : Fin 3)) 1 + -Finsupp.single (1, (1 : Fin 3)) 1

def NonzeroCertificateType : Prop := ControlCertificate ≠ 0

def ControlFrequencyType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    frequency (geometry k hk) (pisotData k hk) ControlCertificate = 0

def ControlCharacterType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), character (geometry k hk) ControlCertificate = 1

def NonzeroCertificateOrbitType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)),
    c ≠ 0 → Injective (orbitCharacter k hk c)

def MissingPositivePeriodType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)) {p : ℕ},
    (∀ z : Solenoid (geometry k hk),
      character (geometry k hk) c ((shiftS (geometry k hk))^[p] z) =
        character (geometry k hk) c z) → character (geometry k hk) c = 1

def SinglePointFrequencyType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)) {m n : ℕ},
    orbitCharacter k hk c m 0 = orbitCharacter k hk c n 0 →
    (geometry k hk).β ^ m * frequency (geometry k hk) (pisotData k hk) c =
      (geometry k hk).β ^ n * frequency (geometry k hk) (pisotData k hk) c

def InverseScalingType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (t : ℝ) (z : Solenoid (geometry k hk)),
    (shiftS (geometry k hk))^[n] (flow (pisotData k hk) t z) =
      flow (pisotData k hk) (t / (geometry k hk).β ^ n)
        ((shiftS (geometry k hk))^[n] z)

theorem wrongTypeControl : True := trivial

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let mod := `PscVerif.C4FamilyCharacterOrbits
    let endpoints : Array (Name × Name) := #[
      (`Psc.C4FamilyCharacterOrbits.shiftS_flow, ``ShiftFlowType),
      (`Psc.C4FamilyCharacterOrbits.shiftS_iterate_flow, ``IterateFlowType),
      (`Psc.C4FamilyCharacterOrbits.shiftS_iterate_zero, ``IterateZeroType),
      (`Psc.C4FamilyCharacterOrbits.orbitCharacter_apply, ``OrbitApplyType),
      (`Psc.C4FamilyCharacterOrbits.orbitCharacter_zero, ``OrbitZeroType),
      (`Psc.C4FamilyCharacterOrbits.orbitCharacter_norm, ``OrbitNormType),
      (`Psc.C4FamilyCharacterOrbits.orbitCharacter_map_add, ``OrbitAddType),
      (`Psc.C4FamilyCharacterOrbits.orbitCharacter_flow_zero, ``OrbitFlowType),
      (`Psc.C4FamilyCharacterOrbits.scaled_frequency_eq_of_orbitCharacter_eq, ``EqualFrequencyType),
      (`Psc.C4FamilyCharacterOrbits.character_eq_one_of_frequency_eq_zero, ``ZeroFrequencyType),
      (`Psc.C4FamilyCharacterOrbits.orbitCharacter_injective, ``InjectiveOrbitType),
      (`Psc.C4FamilyCharacterOrbits.character_eq_one_of_inflation_period, ``PeriodicCharacterType),
      (`Psc.C4FamilyCharacterOrbits.finite_orbit_injective, ``FiniteOrbitType),
      (`Psc.C4FamilyCharacterOrbits.compatibilityCertificate_ne_zero, ``NonzeroCertificateType),
      (`Psc.C4FamilyCharacterOrbits.compatibilityCertificate_frequency, ``ControlFrequencyType),
      (`Psc.C4FamilyCharacterOrbits.compatibilityCertificate_character, ``ControlCharacterType)]
    let semanticRefusals : Array (Name × Name) := #[
      (`Psc.C4FamilyCharacterOrbits.orbitCharacter_injective, ``NonzeroCertificateOrbitType),
      (`Psc.C4FamilyCharacterOrbits.character_eq_one_of_inflation_period, ``MissingPositivePeriodType),
      (`Psc.C4FamilyCharacterOrbits.scaled_frequency_eq_of_orbitCharacter_eq, ``SinglePointFrequencyType),
      (`Psc.C4FamilyCharacterOrbits.shiftS_iterate_flow, ``InverseScalingType)]
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
    let some index := env.getModuleIdx? mod | throwError "Missing compiled character-orbit module"
    let data := env.header.moduleData[index.toNat]!
    let mut declarations := 0
    let mut proofs := 0
    for info in data.constants do
      let some owner := env.getModuleIdxFor? info.name | continue
      if owner != index then continue
      if info.isAxiom then throwError "Local character-orbit axiom: {info.name}"
      for ax in ← collectAxioms info.name do
        unless allowed.contains ax do
          throwError "Nonstandard character-orbit axiom in {info.name}: {ax}"
      declarations := declarations + 1
      if info.isTheorem then proofs := proofs + 1
    if declarations == 0 || proofs == 0 then throwError "Empty character-orbit module"
    for (name, expected) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed character-orbit endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Character-orbit endpoint has no compiled owner: {name}"
      unless owner == index do throwError "Wrong character-orbit endpoint owner: {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Nonstandard character-orbit endpoint axiom in {name}: {ax}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_CHARACTER_ORBIT_ENDPOINT\t{name}"
    let missing := `Psc.C4CharacterOrbitsAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (_, expected) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Character-orbit matcher accepted a wrong-typed theorem"
      if ← matchesType missing expected then
        throwError "Character-orbit matcher accepted a missing declaration"
    for (name, wrong) in semanticRefusals do
      if ← matchesType name wrong then
        throwError "Character-orbit matcher accepted altered contract {wrong} for {name}"
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_CHARACTER_ORBIT_CONTRACT_REFUSED\t{name}\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CHARACTER_ORBIT_REFUSAL_CONTROLS\t{2 * endpoints.size + semanticRefusals.size}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CHARACTER_ORBIT_AUDIT_COMPLETE\t{declarations}\t{proofs}"

end Psc.C4CharacterOrbitsAudit
