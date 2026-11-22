/- Independent types, axioms and controls for the actual measured translation spectrum. -/
import PscVerif.C4FamilyMeasuredSpectrum
import PscVerif.C4ParameterFamilyZeroFibreControls
import Mathlib.MeasureTheory.Measure.Count
import Lean.Util.CollectAxioms

namespace Psc.C4FamilyMeasuredSpectrumAudit

open Function Set MeasureTheory
open scoped Psc.PeriodicPartnerSolenoidHaar Psc.C4FamilyMeasuredRealization
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (solenoidRealize pisotData)
open Psc.PeriodicPartnerRealization (Solenoid)
open Psc.PeriodicPartnerLocalTopology (LocalHull inflate translate)
open Psc.PeriodicPartnerSolenoidHaar (haar)
open Psc.PeriodicPartnerSolenoidCharacters (Certificate frequency)
open Psc.C4FamilyMeasuredRealization (hullMeasure measurableInverse measurePreserving_translate)
open Psc.C4FamilyMeasuredSpectrum (pullback eigenfunctionLp translationKoopman)
open Psc.C4FamilySolenoidCharacters (eigenfunction)

section
variable (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)
local notation "μₛ" => haar (geometry k hk)
local notation "νₕ" => hullMeasure k hk hk₂
local notation "π" => solenoidRealize k hk
local notation "s" => measurableInverse k hk hk₂
local notation "phase" => fun (t ξ : ℝ) => Complex.exp (((2 * Real.pi * (t * ξ) : ℝ) : ℂ) * Complex.I)

def RightInverseType : Prop := (π ∘ s) =ᵐ[μₛ] id

def LeftInverseType : Prop := (s ∘ π) =ᵐ[νₕ] id

def FactorPreservingType : Prop := MeasurePreserving π νₕ μₛ

def InversePreservingType : Prop := MeasurePreserving s μₛ νₕ

def TranslationInvariantType : Prop :=
  ∀ t : ℝ, MeasurePreserving (translate (geometry k hk) t) νₕ νₕ

def InflationInvariantType : Prop := MeasurePreserving (inflate (geometry k hk)) νₕ νₕ

def PullbackSurjectiveType : Prop := Surjective (pullback k hk hk₂)

def TranslationSurjectiveType : Prop := ∀ t : ℝ, Surjective (translationKoopman k hk hk₂ t)

def RepresentativeType : Prop := ∀ c : Certificate (Fin 3),
  (eigenfunctionLp k hk hk₂ c : LocalHull (geometry k hk) → ℂ) =ᵐ[νₕ] eigenfunction k hk c

def FrequencyType : Prop := ∀ (c : Certificate (Fin 3)) (t : ℝ),
  Lp.compMeasurePreserving (translate (geometry k hk) t) (measurePreserving_translate k hk hk₂ t)
    (eigenfunctionLp k hk hk₂ c) =
    (phase) t (frequency (geometry k hk) (pisotData k hk) c) • eigenfunctionLp k hk hk₂ c

def OppositeFrequencyType : Prop := ∀ (c : Certificate (Fin 3)) (t : ℝ),
  Lp.compMeasurePreserving (translate (geometry k hk) t) (measurePreserving_translate k hk hk₂ t)
    (eigenfunctionLp k hk hk₂ c) =
    (phase) (-t) (frequency (geometry k hk) (pisotData k hk) c) • eigenfunctionLp k hk hk₂ c

def MeasuredSpanType : Prop :=
  (Submodule.span ℂ (range (eigenfunctionLp k hk hk₂))).topologicalClosure = ⊤

def PureDiscreteType : Prop :=
  (Submodule.span ℂ {v : Lp ℂ 2 νₕ | v ≠ 0 ∧ ∃ ξ : ℝ, ∀ t : ℝ,
    Lp.compMeasurePreserving (translate (geometry k hk) t) (measurePreserving_translate k hk hk₂ t)
      v = (phase) t ξ • v}).topologicalClosure = ⊤

def EverywhereInverseType : Prop := LeftInverse s π

example : IsProbabilityMeasure νₕ := inferInstance

end

/-- The actual zero-fibre seam pair obstructs every global left inverse. -/
theorem no_global_leftInverse (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ s : Solenoid (geometry k hk) → LocalHull (geometry k hk),
      LeftInverse s (solenoidRealize k hk) := by
  rintro ⟨s, hs⟩
  exact Psc.ParameterFamilyZeroFibreControls.solenoidRealize_not_injective k hk hs.injective

/-- A measure-preserving collapse of two positive atoms has a proper L² pullback range. -/
theorem two_atom_pullback_control :
    ∃ (f : Bool → Bool) (ν : Measure Bool) (h : MeasurePreserving f Measure.count ν),
      ¬ Surjective (Lp.compMeasurePreservingₗᵢ ℂ f h : Lp ℂ 2 ν → Lp ℂ 2 Measure.count) := by
  let f : Bool → Bool := fun _ => false
  let ν := Measure.map f Measure.count
  have hf : MeasurePreserving f Measure.count ν := ⟨measurable_const, rfl⟩
  refine ⟨f, ν, hf, fun h => ?_⟩
  have hs : MeasurableSet ({false} : Set Bool) := measurableSet_singleton _
  have hfin : (Measure.count : Measure Bool) {false} ≠ ⊤ := measure_ne_top _ _
  let u : Lp ℂ 2 (Measure.count : Measure Bool) := indicatorConstLp 2 hs hfin (1 : ℂ)
  obtain ⟨v, hv⟩ := h u
  have hcomp := Lp.coeFn_compMeasurePreserving v hf
  change ((Lp.compMeasurePreservingₗᵢ ℂ f hf) v : Bool → ℂ) =ᵐ[Measure.count] v ∘ f at hcomp
  rw [hv] at hcomp
  have hu : (u : Bool → ℂ) =ᵐ[Measure.count] ({false} : Set Bool).indicator (fun _ => 1) :=
    indicatorConstLp_coeFn
  have he := Measure.ae_count_iff.mp (hu.symm.trans hcomp)
  have hfalse : (1 : ℂ) = v false := by simpa [f] using he false
  have htrue : (0 : ℂ) = v false := by simpa [f] using he true
  exact one_ne_zero (hfalse.trans htrue.symm)

theorem wrongTypeControl : True := trivial

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let realization := `PscVerif.C4FamilyMeasuredRealization
    let spectrum := `PscVerif.C4FamilyMeasuredSpectrum
    let endpoints : Array (Name × Name × Name) := #[
      (`Psc.C4FamilyMeasuredRealization.factor_inverse_ae, ``RightInverseType, realization),
      (`Psc.C4FamilyMeasuredRealization.inverse_factor_ae, ``LeftInverseType, realization),
      (`Psc.C4FamilyMeasuredRealization.measurePreserving_factor, ``FactorPreservingType, realization),
      (`Psc.C4FamilyMeasuredRealization.measurePreserving_inverse, ``InversePreservingType, realization),
      (`Psc.C4FamilyMeasuredRealization.measurePreserving_translate, ``TranslationInvariantType, realization),
      (`Psc.C4FamilyMeasuredRealization.measurePreserving_inflate, ``InflationInvariantType, realization),
      (`Psc.C4FamilyMeasuredSpectrum.pullback_surjective, ``PullbackSurjectiveType, spectrum),
      (`Psc.C4FamilyMeasuredSpectrum.translationKoopman_surjective, ``TranslationSurjectiveType, spectrum),
      (`Psc.C4FamilyMeasuredSpectrum.eigenfunctionLp_ae, ``RepresentativeType, spectrum),
      (`Psc.C4FamilyMeasuredSpectrum.eigenfunctionLp_translate, ``FrequencyType, spectrum),
      (`Psc.C4FamilyMeasuredSpectrum.span_eigenfunctionLp_closure_eq_top, ``MeasuredSpanType, spectrum),
      (`Psc.C4FamilyMeasuredSpectrum.pureDiscrete_translation, ``PureDiscreteType, spectrum)]
    let refusals : Array (Name × Name) := #[
      (`Psc.C4FamilyMeasuredRealization.inverse_factor_ae, ``EverywhereInverseType),
      (`Psc.C4FamilyMeasuredSpectrum.eigenfunctionLp_translate, ``OppositeFrequencyType)]
    let matchesType (name expected : Name) : Term.TermElabM Bool := do
      let some decl := env.find? name | return false
      let some target := env.find? expected | return false
      if !decl.isTheorem || decl.levelParams.length != target.levelParams.length then return false
      withNewMCtxDepth do
        let actual ← inferType (← mkConstWithFreshMVarLevels name)
        let targetConst := mkConst expected (target.levelParams.map Level.param)
        let expectedType ← forallTelescope target.type fun args _ =>
          mkForallFVars args (mkAppN targetConst args)
        withTransparency .all <| isDefEq actual expectedType
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let checkAxioms (name : Name) : Term.TermElabM Unit := do
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom in {name}: {ax}"
    let mut declarations := 0
    let mut proofs := 0
    for mod in #[realization, spectrum] do
      let some index := env.getModuleIdx? mod | throwError "Missing compiled module {mod}"
      let mut owned := 0
      for info in env.header.moduleData[index.toNat]!.constants do
        if env.getModuleIdxFor? info.name == some index then
          if info.isAxiom then throwError "Local axiom: {info.name}"
          checkAxioms info.name
          owned := owned + 1
          declarations := declarations + 1
          if info.isTheorem then proofs := proofs + 1
      if owned == 0 then throwError "Empty compiled module {mod}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_MEASURED_MODULE\t{mod}\t{owned}"
    let missing := `Psc.C4FamilyMeasuredSpectrumAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (name, expected, mod) in endpoints do
      unless (← matchesType name expected) && env.getModuleIdxFor? name == env.getModuleIdx? mod do
        throwError "Missing, wrong-typed or wrong-owner endpoint: {name}"
      if (← matchesType missing expected) || (← matchesType ``wrongTypeControl expected) then
        throwError "Matcher accepted a missing or wrong-typed declaration"
      Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_MEASURED_ENDPOINT\t{name}"
    for (name, wrong) in refusals do
      if ← matchesType name wrong then throwError "Matcher accepted altered contract {wrong}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_MEASURED_CONTRACT_REFUSED\t{name}\t{wrong}"
    checkAxioms ``no_global_leftInverse
    checkAxioms ``two_atom_pullback_control
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_MEASURED_REFUSAL_CONTROLS\t{2 * endpoints.size + refusals.size}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_MEASURED_AUDIT_COMPLETE\t{declarations}\t{proofs}"

end Psc.C4FamilyMeasuredSpectrumAudit
