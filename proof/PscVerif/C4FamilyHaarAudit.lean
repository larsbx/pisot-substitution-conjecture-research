/- Independent endpoint types and concrete negative controls for the Haar argument. -/
import PscVerif.C4FamilyHaarSingletonFibres
import PscVerif.C4ParameterFamilyZeroFibreControls
import Lean.Util.CollectAxioms

namespace Psc.C4FamilyHaarAudit

open Function MeasureTheory Set
open scoped InnerProductSpace Psc.PeriodicPartnerSolenoidHaar
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (solenoidRealize)
open Psc.PeriodicPartnerHull (LengthSubst)
open Psc.PeriodicPartnerLocalTopology (LocalHull)
open Psc.PeriodicPartnerRealization (Solenoid shiftS)
open Psc.PeriodicPartnerSolenoidHaar (haar measurePreserving_shiftS)
open Psc.PeriodicPartnerSolenoidCharacters (Certificate character)
open Psc.C4FamilySolenoidCharacters (nonunitHistory_ne_zero)
open Psc.C4FamilyCharacterOrbits (orbitCharacter compatibilityCertificate
  compatibilityCertificate_character compatibilityCertificate_ne_zero)
open Psc.C4FamilyHaarErgodicity (characterLp)

universe u

def ShiftPreservingType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] (S : LengthSubst α),
    MeasurePreserving (shiftS S) (haar S) (haar S)

def SpanDenseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    (Submodule.span ℂ (range (characterLp k hk))).topologicalClosure = ⊤

def OrthogonalityType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {f g : C(Solenoid (geometry k hk), ℂ)}, f ≠ g →
    (∀ x y, f (x + y) = f x * f y) → (∀ x y, g (x + y) = g x * g y) →
    (∀ x, ‖f x‖ = 1) →
    ⟪ContinuousMap.toLp 2 (haar (geometry k hk)) ℂ f,
      ContinuousMap.toLp 2 (haar (geometry k hk)) ℂ g⟫_ℂ = 0

def OrthonormalType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)),
    character (geometry k hk) c ≠ 1 → ∀ N : ℕ,
    Orthonormal ℂ (fun i : Fin N => ContinuousMap.toLp 2 (haar (geometry k hk)) ℂ
      (orbitCharacter k hk c i.1))

def BesselType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (f : Lp ℂ 2 (haar (geometry k hk))),
    Lp.compMeasurePreserving (shiftS (geometry k hk)) (measurePreserving_shiftS _) f = f →
    ∀ c : Certificate (Fin 3), character (geometry k hk) c ≠ 1 → ∀ N : ℕ,
    (N : ℝ) * ‖⟪characterLp k hk c, f⟫_ℂ‖ ^ 2 ≤ ‖f‖ ^ 2

def ErgodicType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), Ergodic (shiftS (geometry k hk)) (haar (geometry k hk))

def FixedConstantType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (f : Lp ℂ 2 (haar (geometry k hk))),
    Lp.compMeasurePreserving (shiftS (geometry k hk)) (measurePreserving_shiftS _) f = f →
    f = ⟪characterLp k hk 0, f⟫_ℂ • characterLp k hk 0

def ConullType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∃ A : Set (Solenoid (geometry k hk)),
    IsGδ A ∧ (∀ᵐ z ∂haar (geometry k hk), z ∈ A) ∧
    ∀ z ∈ A, ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z

def SingletonType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ᵐ z ∂haar (geometry k hk), ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z

def NonzeroCertificateType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Certificate (Fin 3)), c ≠ 0 → ∀ N : ℕ,
    Orthonormal ℂ (fun i : Fin N => ContinuousMap.toLp 2 (haar (geometry k hk)) ℂ
      (orbitCharacter k hk c i.1))

def MissingGeometryType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    ∀ᵐ z ∂haar (geometry k hk), ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z

def EveryFibreType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ z : Solenoid (geometry k hk), ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z

example (k : ℕ) (hk : 1 ≤ k) :
    (haar (geometry k hk)).IsAddHaarMeasure ∧ haar (geometry k hk) univ = 1 :=
  ⟨inferInstance, measure_univ⟩

/-- A nonzero redundant label gives two identical vectors in its first orbit sample. -/
theorem redundant_certificate_control (k : ℕ) (hk : 1 ≤ k) :
    compatibilityCertificate ≠ 0 ∧
    ¬ Orthonormal ℂ (fun i : Fin 2 => ContinuousMap.toLp 2 (haar (geometry k hk)) ℂ
      (orbitCharacter k hk compatibilityCertificate i.1)) := by
  refine ⟨compatibilityCertificate_ne_zero, fun h => ?_⟩
  have heq : orbitCharacter k hk compatibilityCertificate 0 =
      orbitCharacter k hk compatibilityCertificate 1 := by
    ext z
    simp [compatibilityCertificate_character]
  have hd := (orthonormal_iff_ite.mp h) 0 0
  have ho := (orthonormal_iff_ite.mp h) 0 1
  rw [ite_eq_right (by decide : (0 : Fin 2) ≠ 1)] at ho
  change ⟪ContinuousMap.toLp 2 (haar (geometry k hk)) ℂ
    (orbitCharacter k hk compatibilityCertificate 0), ContinuousMap.toLp 2 (haar (geometry k hk)) ℂ
    (orbitCharacter k hk compatibilityCertificate 1)⟫_ℂ = 0 at ho
  rw [← heq] at ho
  exact one_ne_zero (hd.symm.trans ho)

/-- The original seam obstruction still refutes an everywhere-singleton conclusion. -/
theorem not_every_fibre_singleton (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∀ z : Solenoid (geometry k hk), ∃! T : LocalHull (geometry k hk),
      solenoidRealize k hk T = z := by
  intro h
  apply Psc.ParameterFamilyZeroFibreControls.solenoidRealize_not_injective k hk
  intro T U heq
  obtain ⟨V, _, hV⟩ := h (solenoidRealize k hk U)
  exact (hV T heq).trans (hV U rfl).symm

/-- On the same solenoid the identity preserves Haar and has a proper open invariant set
whose measure and complement measure are both positive. -/
theorem identity_not_ergodic (k : ℕ) (hk : 1 ≤ k) :
    ¬ Ergodic id (haar (geometry k hk)) := by
  intro hid
  obtain ⟨U, V, hU, hV, hzU, h0V, hdis⟩ := t2_separation (nonunitHistory_ne_zero k hk)
  have hposU := hU.measure_pos (haar (geometry k hk)) ⟨_, hzU⟩
  have hposV := hV.measure_pos (haar (geometry k hk)) ⟨_, h0V⟩
  have hsub : V ⊆ Uᶜ := fun _ hv hu => (Set.disjoint_left.mp hdis) hu hv
  have hposCompl := hposV.trans_le (measure_mono hsub :
    haar (geometry k hk) V ≤ haar (geometry k hk) Uᶜ)
  exact (hid.toPreErgodic.measure_self_or_compl_eq_zero hU.measurableSet rfl).elim
    hposU.ne' hposCompl.ne'

theorem wrongTypeControl : True := trivial

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let haarModule := `PscVerif.PeriodicPartnerSolenoidHaar
    let ergodicModule := `PscVerif.C4FamilyHaarErgodicity
    let fibreModule := `PscVerif.C4FamilyHaarSingletonFibres
    let endpoints : Array (Name × Name × Name) := #[
      (`Psc.PeriodicPartnerSolenoidHaar.measurePreserving_shiftS, ``ShiftPreservingType, haarModule),
      (`Psc.C4FamilyHaarErgodicity.span_characterLp_closure_eq_top, ``SpanDenseType, ergodicModule),
      (`Psc.C4FamilyHaarErgodicity.haar_inner_eq_zero, ``OrthogonalityType, ergodicModule),
      (`Psc.C4FamilyHaarErgodicity.orthonormal_finite_orbit, ``OrthonormalType, ergodicModule),
      (`Psc.C4FamilyHaarErgodicity.finite_bessel_bound, ``BesselType, ergodicModule),
      (`Psc.C4FamilyHaarErgodicity.fixed_eq_smul_one, ``FixedConstantType, ergodicModule),
      (`Psc.C4FamilyHaarErgodicity.ergodic_shiftS, ``ErgodicType, ergodicModule),
      (`Psc.C4FamilyHaarSingletonFibres.exists_conull_singleton_fibres, ``ConullType, fibreModule),
      (`Psc.C4FamilyHaarSingletonFibres.ae_singleton_fibre, ``SingletonType, fibreModule)]
    let refusals : Array (Name × Name) := #[
      (`Psc.C4FamilyHaarErgodicity.orthonormal_finite_orbit, ``NonzeroCertificateType),
      (`Psc.C4FamilyHaarSingletonFibres.ae_singleton_fibre, ``MissingGeometryType),
      (`Psc.C4FamilyHaarSingletonFibres.ae_singleton_fibre, ``EveryFibreType)]
    let matchesType (name expected : Name) : Term.TermElabM Bool := do
      let some decl := env.find? name | return false
      let some target := env.find? expected | return false
      if !decl.isTheorem || decl.levelParams.length != target.levelParams.length then return false
      withNewMCtxDepth do
        let actual ← inferType (← mkConstWithFreshMVarLevels name)
        withTransparency .all <| isDefEq actual (mkConst expected (target.levelParams.map Level.param))
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let checkAxioms (name : Name) : Term.TermElabM Unit := do
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom in {name}: {ax}"
    let mut declarations := 0
    let mut proofs := 0
    for mod in #[haarModule, ergodicModule, fibreModule] do
      let some index := env.getModuleIdx? mod | throwError "Missing compiled module {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      for info in data.constants do
        if env.getModuleIdxFor? info.name == some index then
          if info.isAxiom then throwError "Local axiom: {info.name}"
          checkAxioms info.name
          owned := owned + 1
          declarations := declarations + 1
          if info.isTheorem then proofs := proofs + 1
      if owned == 0 then throwError "Empty compiled module {mod}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_HAAR_MODULE\t{mod}\t{owned}"
    let missing := `Psc.C4FamilyHaarAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (name, expected, mod) in endpoints do
      unless (← matchesType name expected) && env.getModuleIdxFor? name == env.getModuleIdx? mod do
        throwError "Missing, wrong-typed or wrong-owner endpoint: {name}"
      if (← matchesType missing expected) || (← matchesType ``wrongTypeControl expected) then
        throwError "Matcher accepted a missing or wrong-typed declaration"
      Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_HAAR_ENDPOINT\t{name}"
    for (name, wrong) in refusals do
      if ← matchesType name wrong then throwError "Matcher accepted altered contract {wrong}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_HAAR_CONTRACT_REFUSED\t{name}\t{wrong}"
    checkAxioms ``redundant_certificate_control
    checkAxioms ``not_every_fibre_singleton
    checkAxioms ``identity_not_ergodic
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_HAAR_REFUSAL_CONTROLS\t{2 * endpoints.size + refusals.size}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_FAMILY_HAAR_AUDIT_COMPLETE\t{declarations}\t{proofs}"

end Psc.C4FamilyHaarAudit
