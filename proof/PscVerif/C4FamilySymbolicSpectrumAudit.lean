/- Independent contracts and axiom audit for the literal symbolic shift. -/
import PscVerif.C4FamilySymbolicSpectrum
import Lean.Util.CollectAxioms

namespace Psc.C4FamilySymbolicSpectrumAudit

open Function MeasureTheory Set
open scoped Psc.C4FamilyMeasuredRealization Psc.C4FamilySymbolicSpectrum
open Psc.ParameterFamilyTiling (geometry expansion two_lt_expansion)
open Psc.PeriodicPartnerHull (LengthSubst)
open Psc.PeriodicPartnerRealization (origin)
open Psc.PeriodicPartnerLocalTopology (LocalHull translate)
open Psc.C4FamilySymbolicSection
open Psc.C4FamilySymbolicLanguage (SymbolicHull itinerary itineraryHomeomorph shift)
open Psc.C4FamilySymbolicSpectrum

section
variable (k : ℕ) (hk : 1 ≤ k) (hk₂ : 2 ≤ k)

def RoofType : Prop := ∀ B : Transversal k hk,
  roof B = meanRoof k hk + correction (next B) - correction B

def OppositeRoofType : Prop := ∀ B : Transversal k hk,
  roof B = meanRoof k hk - correction (next B) + correction B

def FirstReturnType : Prop := ∀ (B : Transversal k hk) ⦃s : ℝ⦄,
  0 < s → s < roof B → (origin (LengthSubst.translate s B.1)).2 ≠ 0

def LiteralCarrierType : Prop := ∀ x : SymbolicHull k hk,
  ∃ B : Transversal k hk, itinerary B = x.1

def ItineraryShiftType : Prop := ∀ B : Transversal k hk,
  itineraryHomeomorph (next B) = shift (itineraryHomeomorph B)

def TimeCType : Prop := ∀ T : LocalHull (geometry k hk),
  symbolicFactor k hk (translate (geometry k hk) (meanRoof k hk) T) =
    next (symbolicFactor k hk T)

def WordInvariantType : Prop :=
  MeasurePreserving (shift (k := k) (hk := hk)) (wordMeasure k hk hk₂) (wordMeasure k hk hk₂)

def PureDiscreteWordType : Prop :=
  (Submodule.span ℂ {v : Lp ℂ 2 (wordMeasure k hk hk₂) |
    v ≠ 0 ∧ ∃ z : ℂ, Lp.compMeasurePreserving (shift (k := k) (hk := hk))
      (measurePreserving_wordShift k hk hk₂) v = z • v}).topologicalClosure = ⊤

/-- Time one in the historical PF scale lies strictly inside the first tile. -/
theorem time_one_misses_transversal (B : Transversal k hk) :
    (origin (LengthSubst.translate 1 B.1)).2 ≠ 0 := by
  have hb := two_lt_expansion k hk
  have hℓ (a : Fin 3) : 1 < (geometry k hk).ℓ a := by
    fin_cases a
    · change 1 < expansion k hk
      linarith
    · change 1 < expansion k hk ^ 2
      nlinarith
    · change 1 < expansion k hk + 2
      linarith
  exact no_boundary_before_roof B (by norm_num) (hℓ _)

end

open Lean Meta Elab Command in
elab "#audit_symbolic_spectrum" : command => liftTermElabM do
  let env ← getEnv
  let sectionMod := `PscVerif.C4FamilySymbolicSection
  let languageMod := `PscVerif.C4FamilySymbolicLanguage
  let spectrumMod := `PscVerif.C4FamilySymbolicSpectrum
  let endpoints : Array (Name × Name × Name) := #[
    (`Psc.C4FamilySymbolicSection.roof_eq_mean_add_coboundary, ``RoofType, sectionMod),
    (`Psc.C4FamilySymbolicSection.no_boundary_before_roof, ``FirstReturnType, sectionMod),
    (`Psc.C4FamilySymbolicLanguage.exists_itinerary, ``LiteralCarrierType, languageMod),
    (`Psc.C4FamilySymbolicLanguage.itineraryHomeomorph_next, ``ItineraryShiftType, languageMod),
    (`Psc.C4FamilySymbolicSpectrum.symbolicFactor_translate, ``TimeCType, spectrumMod),
    (`Psc.C4FamilySymbolicSpectrum.measurePreserving_wordShift, ``WordInvariantType, spectrumMod),
    (`Psc.C4FamilySymbolicSpectrum.pureDiscrete_shift, ``PureDiscreteWordType, spectrumMod)]
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
  for mod in #[sectionMod, languageMod, spectrumMod] do
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
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_SYMBOLIC_MODULE\t{mod}\t{owned}"
  for (name, expected, mod) in endpoints do
    unless (← matchesType name expected) && env.getModuleIdxFor? name == env.getModuleIdx? mod do
      throwError "Missing, wrong-typed or wrong-owner endpoint: {name}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_SYMBOLIC_ENDPOINT\t{name}"
  if ← matchesType `Psc.C4FamilySymbolicSection.roof_eq_mean_add_coboundary ``OppositeRoofType then
    throwError "Accepted the opposite roof coboundary"
  if ← matchesType `Psc.C4FamilyMeasuredSpectrum.pureDiscrete_translation ``PureDiscreteWordType then
    throwError "Accepted the real-translation theorem as the word theorem"
  checkAxioms ``time_one_misses_transversal
  Lean.Core.liftIOCore <| IO.println "PSC_FAMILY_SYMBOLIC_CONTROLS\t3"
  Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_SYMBOLIC_AUDIT_COMPLETE\t{declarations}\t{theorems}"

#audit_symbolic_spectrum
#print axioms Psc.C4FamilySymbolicSpectrum.pureDiscrete_shift

end Psc.C4FamilySymbolicSpectrumAudit
