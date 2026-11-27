/- Independent measure-identification contracts and recursive axiom audit. -/
import PscVerif.C4FamilyCanonicalSpectrum
import Lean.Util.CollectAxioms

namespace Psc.C4FamilyCanonicalMeasureAudit

open MeasureTheory
open scoped Psc.C4FamilySymbolicSpectrum Psc.C4FamilyMeasuredRealization
  Psc.PeriodicPartnerSolenoidHaar
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize)
open Psc.PeriodicPartnerRealization (flow)
open Psc.C4FamilyMeasuredRealization (hullMeasure)
open Psc.C4FamilySymbolicSection (Transversal next roof roof_pos)
open Psc.C4FamilySymbolicLanguage (SymbolicHull shift continuous_shift
  itineraryHomeomorph itineraryHomeomorph_next)
open Psc.C4FamilySymbolicSpectrum (wordMeasure symbolicMeasure symbolicFactor)
open Psc.C4FamilySymbolicMeasureUniqueness (suspensionMeasure)

def BaseMarginalType (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∀ (μ : Measure (Transversal k hk)) [IsProbabilityMeasure μ],
    (suspensionMeasure k hk μ).map (symbolicFactor k hk) = μ

def SuspensionEqualityType (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) : Prop :=
  ∀ (μ : Measure (Transversal k hk)) [IsProbabilityMeasure μ],
    MeasurePreserving (next (k := k) (hk := hk)) μ μ →
      suspensionMeasure k hk μ = hullMeasure k hk hk₂

def FlowMarginalInvariantType (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∀ (μ : Measure (Transversal k hk)) [IsProbabilityMeasure μ],
    MeasurePreserving (next (k := k) (hk := hk)) μ μ →
      ∀ t : ℝ, MeasurePreserving (flow (pisotData k hk) t)
        ((suspensionMeasure k hk μ).map (solenoidRealize k hk))
        ((suspensionMeasure k hk μ).map (solenoidRealize k hk))

def ReturnUniquenessType (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) : Prop :=
  ∀ (μ : Measure (Transversal k hk)) [IsProbabilityMeasure μ],
    MeasurePreserving (next (k := k) (hk := hk)) μ μ →
      μ = symbolicMeasure k hk hk₂

def UniquenessType (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) : Prop :=
  ∀ (μ : Measure (SymbolicHull k hk)) [IsProbabilityMeasure μ],
    MeasurePreserving (shift (k := k) (hk := hk)) μ μ →
      μ = wordMeasure k hk hk₂

def EqualityTransportType (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) : Prop :=
  ∀ (μ : Measure (SymbolicHull k hk))
    (hμ : MeasurePreserving (shift (k := k) (hk := hk)) μ μ),
    μ = wordMeasure k hk hk₂ →
      (Submodule.span ℂ {v : Lp ℂ 2 μ |
        v ≠ 0 ∧ ∃ z : ℂ,
          Lp.compMeasurePreserving (shift (k := k) (hk := hk)) hμ v = z • v}
      ).topologicalClosure = ⊤

def InvariantSpectrumType (k : ℕ) (hk : 1 ≤ k) (_hk₂ : 2 ≤ k) : Prop :=
  ∀ (μ : Measure (SymbolicHull k hk)) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift (k := k) (hk := hk)) μ μ),
    (Submodule.span ℂ {v : Lp ℂ 2 μ |
      v ≠ 0 ∧ ∃ z : ℂ,
        Lp.compMeasurePreserving (shift (k := k) (hk := hk)) hμ v = z • v}
    ).topologicalClosure = ⊤

def UniqueExistenceType (k : ℕ) (hk : 1 ≤ k) (_hk₂ : 2 ≤ k) : Prop :=
  ∃! μ : Measure (SymbolicHull k hk),
    IsProbabilityMeasure μ ∧ MeasurePreserving (shift (k := k) (hk := hk)) μ μ

def InvarianceWithoutProbabilityType (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) : Prop :=
  ∀ (μ : Measure (SymbolicHull k hk)),
    MeasurePreserving (shift (k := k) (hk := hk)) μ μ →
      μ = wordMeasure k hk hk₂

def ProbabilityWithoutInvarianceType (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) : Prop :=
  ∀ (μ : Measure (SymbolicHull k hk)) [IsProbabilityMeasure μ],
    μ = wordMeasure k hk hk₂

/-- A deliberately stronger parameter contract. Its refusal checks that the
accepted theorem retains `k ≥ 2`; it does not assert failure at `k = 1`. -/
def UniqueExistenceWithoutKTwoType (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃! μ : Measure (SymbolicHull k hk),
    IsProbabilityMeasure μ ∧ MeasurePreserving (shift (k := k) (hk := hk)) μ μ

/-- An actual invariant measure that fails the normalization hypothesis. -/
theorem zero_invariant_not_probability (k : ℕ) (hk : 1 ≤ k) :
    MeasurePreserving (shift (k := k) (hk := hk))
      (0 : Measure (SymbolicHull k hk)) 0 ∧
      ¬ IsProbabilityMeasure (0 : Measure (SymbolicHull k hk)) := by
  refine ⟨⟨continuous_shift.measurable, Measure.map_zero _⟩, ?_⟩
  intro h
  have hmass := h.measure_univ
  change (0 : ENNReal) = 1 at hmass
  exact zero_ne_one hmass

/-- Invariance alone demonstrably does not identify the induced probability. -/
theorem invariance_alone_does_not_identify (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k) :
    ∃ μ : Measure (SymbolicHull k hk),
      MeasurePreserving (shift (k := k) (hk := hk)) μ μ ∧
        μ ≠ wordMeasure k hk hk₂ := by
  refine ⟨0, (zero_invariant_not_probability k hk).1, ?_⟩
  exact (IsProbabilityMeasure.ne_zero (wordMeasure k hk hk₂)).symm

/-- A point mass is a probability but fails shift invariance on this actual
aperiodic legal shift. Thus normalization does not supply invariance. -/
theorem dirac_probability_not_invariant (k : ℕ) (hk : 1 ≤ k)
    (x : SymbolicHull k hk) :
    IsProbabilityMeasure (Measure.dirac x) ∧
      ¬ MeasurePreserving (shift (k := k) (hk := hk))
        (Measure.dirac x) (Measure.dirac x) := by
  refine ⟨inferInstance, ?_⟩
  intro h
  have he := h.map_eq
  rw [Measure.map_dirac' continuous_shift.measurable] at he
  have hx : shift x = x := injective_dirac he
  let e := itineraryHomeomorph (k := k) (hk := hk)
  let B := e.symm x
  have hB : next B = B := e.injective (by
    change itineraryHomeomorph (next B) = itineraryHomeomorph B
    rw [itineraryHomeomorph_next]
    simpa only [B, e, Homeomorph.apply_symm_apply] using hx)
  have hp := Psc.ParameterFamilyTiling.aperiodic k hk B.1 (roof B)
    (congrArg Subtype.val hB)
  exact (ne_of_gt (roof_pos B)) hp

theorem wrongTypeControl : True := trivial

open Lean Meta Elab Command in
elab "#audit_canonical_measure" : command => liftTermElabM do
  let env ← getEnv
  let invariantMod := `PscVerif.C4FamilyInvariantMeasureUniqueness
  let symbolicMod := `PscVerif.C4FamilySymbolicMeasureUniqueness
  let spectrumMod := `PscVerif.C4FamilyCanonicalSpectrum
  let endpoints : Array (Name × Name × Name) := #[
    (`Psc.C4FamilySymbolicMeasureUniqueness.map_symbolicFactor_suspensionMeasure,
      ``BaseMarginalType, symbolicMod),
    (`Psc.C4FamilySymbolicMeasureUniqueness.measurePreserving_flow_suspensionFactor,
      ``FlowMarginalInvariantType, symbolicMod),
    (`Psc.C4FamilySymbolicMeasureUniqueness.suspensionMeasure_eq_hullMeasure,
      ``SuspensionEqualityType, symbolicMod),
    (`Psc.C4FamilySymbolicMeasureUniqueness.invariant_probability_eq_symbolicMeasure,
      ``ReturnUniquenessType, symbolicMod),
    (`Psc.C4FamilySymbolicMeasureUniqueness.invariant_probability_eq_wordMeasure,
      ``UniquenessType, symbolicMod),
    (`Psc.C4FamilyCanonicalSpectrum.pureDiscrete_shift_of_measure_eq,
      ``EqualityTransportType, spectrumMod),
    (`Psc.C4FamilyCanonicalSpectrum.pureDiscrete_shift_of_invariant_probability,
      ``InvariantSpectrumType, spectrumMod),
    (`Psc.C4FamilyCanonicalSpectrum.existsUnique_invariant_probability,
      ``UniqueExistenceType, spectrumMod)]
  let refusals : Array (Name × Name) := #[
    (`Psc.C4FamilySymbolicMeasureUniqueness.invariant_probability_eq_wordMeasure,
      ``InvarianceWithoutProbabilityType),
    (`Psc.C4FamilySymbolicMeasureUniqueness.invariant_probability_eq_wordMeasure,
      ``ProbabilityWithoutInvarianceType),
    (`Psc.C4FamilyCanonicalSpectrum.existsUnique_invariant_probability,
      ``UniqueExistenceWithoutKTwoType)]
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
  let mut theorems := 0
  for mod in #[invariantMod, symbolicMod, spectrumMod] do
    let some index := env.getModuleIdx? mod | throwError "Missing compiled module {mod}"
    let mut owned := 0
    for info in env.header.moduleData[index.toNat]!.constants do
      if env.getModuleIdxFor? info.name == some index then
        if info.isAxiom then throwError "Local axiom: {info.name}"
        checkAxioms info.name
        declarations := declarations + 1
        owned := owned + 1
        if info.isTheorem then theorems := theorems + 1
    if owned == 0 then throwError "Empty compiled module {mod}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_CANONICAL_MODULE\t{mod}\t{owned}"
  let missing := `Psc.C4FamilyCanonicalMeasureAudit.absentEndpoint
  if (env.find? missing).isSome then throwError "Missing-declaration control collision"
  for (name, expected, mod) in endpoints do
    unless (← matchesType name expected) && env.getModuleIdxFor? name == env.getModuleIdx? mod do
      throwError "Missing, wrong-typed or wrong-owner endpoint: {name}"
    if (← matchesType missing expected) || (← matchesType ``wrongTypeControl expected) then
      throwError "Matcher accepted a missing or wrong-typed declaration"
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_CANONICAL_ENDPOINT\t{name}"
  for (name, wrong) in refusals do
    if ← matchesType name wrong then throwError "Matcher accepted altered contract {wrong}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_CANONICAL_CONTRACT_REFUSED\t{name}\t{wrong}"
  checkAxioms ``zero_invariant_not_probability
  checkAxioms ``invariance_alone_does_not_identify
  checkAxioms ``dirac_probability_not_invariant
  Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_CANONICAL_CONTROLS\t{2 * endpoints.size + refusals.size + 3}"
  Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_CANONICAL_AUDIT_COMPLETE\t{declarations}\t{theorems}"

#audit_canonical_measure
#print axioms Psc.C4FamilySymbolicMeasureUniqueness.invariant_probability_eq_wordMeasure
#print axioms Psc.C4FamilyCanonicalSpectrum.pureDiscrete_shift_of_invariant_probability

end Psc.C4FamilyCanonicalMeasureAudit
