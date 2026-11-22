/- Independent acceptance types for the measured pure-discrete interface.
The family endpoint is conditional on a measurable almost everywhere inverse
of the realization; the audit refuses the statement with that premise removed. -/
import PscVerif.C4FamilyMeasuredSpectrum
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace Psc.C4MeasuredSpectrumAudit

open MeasureTheory Function
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize)
open Psc.PeriodicPartnerRealization (Solenoid flow)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate)
open Psc.MeasuredPureDiscrete
open Psc.PeriodicPartnerSolenoidPureDiscrete (solenoidFlow)
open Psc.C4FamilyMeasuredSpectrum (hullFlow image_flow_invariant)

universe u v

def TransferType : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (F : MeasuredFlow μ) (G : MeasuredFlow ν) {g : X → Y}
    (_ : MeasurePreserving g μ ν), (∀ t, g ∘ F.φ t =ᵐ[μ] G.φ t ∘ g) →
    ∀ {h : Y → X}, Measurable h → h ∘ g =ᵐ[μ] id → PureDiscrete G → PureDiscrete F

def StationaryControlType : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} {f : Lp ℂ 2 μ},
    (∀ t, koopman (stationary μ) t f = phase 1 t • f) → f = 0

def ImageInvariantType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k)
    [MeasurableSpace (LocalHull (geometry k hk))] [BorelSpace (LocalHull (geometry k hk))]
    [MeasurableSpace (Solenoid (geometry k hk))] [BorelSpace (Solenoid (geometry k hk))]
    (μ : Measure (LocalHull (geometry k hk))),
    (∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ) → ∀ t : ℝ,
    MeasurePreserving (flow (pisotData k hk) t)
      (μ.map (solenoidRealize k hk)) (μ.map (solenoidRealize k hk))

def ImagePureDiscreteType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k)
    [MeasurableSpace (LocalHull (geometry k hk))] [BorelSpace (LocalHull (geometry k hk))]
    [MeasurableSpace (Solenoid (geometry k hk))] [BorelSpace (Solenoid (geometry k hk))]
    (μ : Measure (LocalHull (geometry k hk))) [IsFiniteMeasure μ]
    [(μ.map (solenoidRealize k hk)).WeaklyRegular]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ),
    PureDiscrete (solenoidFlow (geometry k hk) (pisotData k hk)
      (μ.map (solenoidRealize k hk)) (image_flow_invariant k hk μ hμ))

def HullConditionalType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k)
    [MeasurableSpace (LocalHull (geometry k hk))] [BorelSpace (LocalHull (geometry k hk))]
    [MeasurableSpace (Solenoid (geometry k hk))] [BorelSpace (Solenoid (geometry k hk))]
    (μ : Measure (LocalHull (geometry k hk))) [IsFiniteMeasure μ]
    [(μ.map (solenoidRealize k hk)).WeaklyRegular]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ)
    {h : Solenoid (geometry k hk) → LocalHull (geometry k hk)}, Measurable h →
    h ∘ solenoidRealize k hk =ᵐ[μ] id → PureDiscrete (hullFlow k hk μ hμ)

/-- The altered contract: the same conclusion with no almost everywhere inverse. -/
def HullUnconditionalType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k)
    [MeasurableSpace (LocalHull (geometry k hk))] [BorelSpace (LocalHull (geometry k hk))]
    [MeasurableSpace (Solenoid (geometry k hk))] [BorelSpace (Solenoid (geometry k hk))]
    (μ : Measure (LocalHull (geometry k hk))) [IsFiniteMeasure μ]
    [(μ.map (solenoidRealize k hk)).WeaklyRegular]
    (hμ : ∀ t, MeasurePreserving (translate (geometry k hk) t) μ μ),
    PureDiscrete (hullFlow k hk μ hμ)

/-- The altered contract: transfer with no inverse and no density premise. -/
def TransferNoInverseType : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (F : MeasuredFlow μ) (G : MeasuredFlow ν) {g : X → Y}
    (_ : MeasurePreserving g μ ν), (∀ t, g ∘ F.φ t =ᵐ[μ] G.φ t ∘ g) →
    PureDiscrete G → PureDiscrete F

theorem wrongTypeControl : True := trivial

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let mods := #[`PscVerif.MeasuredPureDiscrete,
      `PscVerif.PeriodicPartnerSolenoidPureDiscrete, `PscVerif.C4FamilyMeasuredSpectrum]
    let endpoints : Array (Name × Name) := #[
      (`Psc.MeasuredPureDiscrete.pureDiscrete_of_ae_inverse, ``TransferType),
      (`Psc.MeasuredPureDiscrete.eq_zero_of_stationary_frequency_one, ``StationaryControlType),
      (`Psc.C4FamilyMeasuredSpectrum.image_flow_invariant, ``ImageInvariantType),
      (`Psc.C4FamilyMeasuredSpectrum.image_pureDiscrete, ``ImagePureDiscreteType),
      (`Psc.C4FamilyMeasuredSpectrum.hull_pureDiscrete_of_ae_inverse, ``HullConditionalType)]
    let semanticRefusals : Array (Name × Name) := #[
      (`Psc.C4FamilyMeasuredSpectrum.hull_pureDiscrete_of_ae_inverse, ``HullUnconditionalType),
      (`Psc.MeasuredPureDiscrete.pureDiscrete_of_ae_inverse, ``TransferNoInverseType)]
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
    for mod in mods do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled measured-spectrum module {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut localProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local measured-spectrum axiom: {info.name}"
        for ax in ← collectAxioms info.name do
          unless allowed.contains ax do
            throwError "Nonstandard measured-spectrum axiom in {info.name}: {ax}"
        declarations := declarations + 1
        if info.isTheorem then
          proofs := proofs + 1
          localProofs := localProofs + 1
      if localProofs == 0 then throwError "Empty measured-spectrum module {mod}"
    for (name, expected) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed measured-spectrum endpoint: {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Nonstandard measured-spectrum endpoint axiom in {name}: {ax}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_MEASURED_SPECTRUM_ENDPOINT\t{name}"
    let missing := `Psc.C4MeasuredSpectrumAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (_, expected) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Measured-spectrum matcher accepted a wrong-typed theorem"
      if ← matchesType missing expected then
        throwError "Measured-spectrum matcher accepted a missing declaration"
    for (name, wrong) in semanticRefusals do
      if ← matchesType name wrong then
        throwError "Measured-spectrum matcher accepted altered contract {wrong} for {name}"
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_MEASURED_SPECTRUM_CONTRACT_REFUSED\t{name}\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_MEASURED_SPECTRUM_REFUSAL_CONTROLS\t{2 * endpoints.size + semanticRefusals.size}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_MEASURED_SPECTRUM_AUDIT_COMPLETE\t{declarations}\t{proofs}"

end Psc.C4MeasuredSpectrumAudit
