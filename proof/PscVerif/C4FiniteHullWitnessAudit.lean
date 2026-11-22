/- Replay after freshly compiling both automaton/hull modules.
The expected endpoint types below independently spell out the integer
displacements, actual hull memberships and witness quantifiers. Every compiled
declaration owned by either new module is scanned recursively for axioms.
The additional type-refusal controls guard the contract; they do not assert
that every altered proposition is mathematically false.
-/
import PscVerif.C4FamilyTileAutomatonHull
import PscVerif.C4FamilyFiniteZeroFibre
import PscVerif.C4ParameterFamilyZeroFibreControls
import PscVerif.C4ParameterFamilyInteriorZero
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace Psc.C4FiniteHullWitnessAudit

open Function Set Matrix
open Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (inflateH Agree translate shift)
open Psc.PeriodicPartnerEventualCoincidence (eventual)
open Psc.PeriodicPartnerLegalCoincidence (originPatch)
open Psc.PeriodicPartnerRealization (realize torusRealize origin)
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilyRecognizability (inflateH_bijective)
open Psc.ParameterFamilySolenoid (pisotData)
open Psc.C4FiniteTileAutomaton (source target edgeOutput replay Walk)

universe u

def LengthSum (S : LengthSubst (Fin 3)) (v : Fin 3 → ℤ) : ℝ :=
  ∑ i : Fin 3, S.ℓ i * (v i : ℝ)

def ExactShifts (S : LengthSubst (Fin 3)) (T U : S.Hull) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ t : ℝ, Agree R (translate t T) (translate t U)

def ThreeWindows (S : LengthSubst (Fin 3)) (R : ℝ) (T U : S.Hull) : Prop :=
  ∃ T' U' : S.Hull, ∃ t : ℝ,
    Agree R T T' ∧ Agree R U U' ∧ Agree R (translate t T') (translate t U')

def ThreeOrigins (S : LengthSubst (Fin 3)) (T U : S.Hull) : Prop :=
  ∃ T' U' : S.Hull, ∃ t : ℝ,
    originPatch S T.1 = originPatch S T'.1 ∧
    originPatch S U.1 = originPatch S U'.1 ∧
    originPatch S (shift t T'.1) = originPatch S (shift t U'.1)

def SupertileHullType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) (n : ℕ),
    ∃ H : (geometry k hk).Hull, (geometry k hk).supertile c n ⊆ H.1

def OccurrenceBridgeType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {n : ℕ} {a b : Fin 3},
    Psc.C4FamilyTileAutomatonWords.OccursInIterate k n a b → ∀ x : ℝ,
    ∃ H : (geometry k hk).Hull,
      (a, x) ∈ H.1 ∧ (b, x + (geometry k hk).ℓ a) ∈ H.1

def ForwardEdgeType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ (e : Fin 10), e.val < 5 → ∀ x : ℝ,
    ∃ H : (geometry k hk).Hull,
      (source e, x) ∈ H.1 ∧
      (target e, x + LengthSum (geometry k hk) (edgeOutput e)) ∈ H.1

def SignedEdgeType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ (e : Fin 10) (x : ℝ),
    ∃ H : (geometry k hk).Hull,
      (source e, x) ∈ H.1 ∧
      (target e, x + LengthSum (geometry k hk) (edgeOutput e)) ∈ H.1

def DenseTransType : Prop :=
  ∀ {α : Type u} [Nonempty α] (S : LengthSubst α)
    {P Q R : Set (α × ℝ)}, S.IsTiling Q →
    Dense (eventual S P Q) → Dense (eventual S Q R) → Dense (eventual S P R)

def WalkTransferType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ {a b : Fin 3} {w : List (Fin 10)} {v : Fin 3 → ℤ}, Walk a w b v →
    ∀ {T U : (geometry k hk).Hull} (x : ℝ),
      (a, x) ∈ T.1 → (b, x + LengthSum (geometry k hk) v) ∈ U.1 →
      Dense (eventual (geometry k hk) T.1 U.1)

def ReplayTransferType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ {a b : Fin 3} {w : List (Fin 10)} {v : Fin 3 → ℤ},
      replay a w = some (b, v) →
    ∀ {T U : (geometry k hk).Hull} (x : ℝ),
      (a, x) ∈ T.1 → (b, x + LengthSum (geometry k hk) v) ∈ U.1 →
      Dense (eventual (geometry k hk) T.1 U.1)

def IntegerDisplacementType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ {a b : Fin 3} (v : Fin 3 → ℤ) {T U : (geometry k hk).Hull} (x : ℝ),
      (a, x) ∈ T.1 → (b, x + LengthSum (geometry k hk) v) ∈ U.1 →
      Dense (eventual (geometry k hk) T.1 U.1)

def IntegerOriginType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {T : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    ∃ z : Fin 3 → ℤ, (origin T).2 = -LengthSum (geometry k hk) z

def IntegerOriginsTransferType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    (∃ z : Fin 3 → ℤ, (origin T).2 = -LengthSum (geometry k hk) z) →
    (∃ z : Fin 3 → ℤ, (origin U).2 = -LengthSum (geometry k hk) z) →
    Dense (eventual (geometry k hk) T.1 U.1)

def EqualTorusDenseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    torusRealize (pisotData k hk) (inflateH_bijective k hk) T =
      torusRealize (pisotData k hk) (inflateH_bijective k hk) U →
    Dense (eventual (geometry k hk) T.1 U.1)

def SameFibreDenseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T =
      realize (pisotData k hk) (inflateH_bijective k hk) U →
    Dense (eventual (geometry k hk) T.1 U.1)

def ZeroDenseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    Dense (eventual (geometry k hk) T.1 U.1)

def ZeroCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    (T.1 ∩ U.1).Nonempty

def ZeroExactShiftsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    ExactShifts (geometry k hk) T U

def ZeroWindowsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    ∀ {R : ℝ}, 0 < R → ThreeWindows (geometry k hk) R T U

def ZeroOriginsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    ThreeOrigins (geometry k hk) T U

def ZeroRegionalType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    ∀ R : ℝ, 0 < R → ThreeWindows (geometry k hk) R T U

/-- Recheck an actual retained control, not merely a proposed wrong type. -/
def LiteralSeamControlType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), ∃ T U : (geometry k hk).Hull,
    inflateH T = U ∧ inflateH^[2] T = T ∧
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ∧
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 ∧
    (1, 0) ∈ T.1 ∧ (0, 0) ∈ U.1 ∧ T ≠ U ∧
    originPatch (geometry k hk) T.1 ≠ originPatch (geometry k hk) U.1 ∧ ¬ Agree 1 T U

def LiteralInteriorControlType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ¬ ∀ T : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
      ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1

/- These are deliberately changed contracts. Refusing them checks the
matcher and preserves explicit guards; only the retained literal controls
above claim mathematical counterexamples. -/
def WrongSignedEdgeType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ (e : Fin 10) (x : ℝ),
    ∃ H : (geometry k hk).Hull,
      (source e, x) ∈ H.1 ∧
      (target e, x - LengthSum (geometry k hk) (edgeOutput e)) ∈ H.1

def MissingFamilyGuardType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    (T.1 ∩ U.1).Nonempty

def WeakerFamilyGuardType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 1 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    (T.1 ∩ U.1).Nonempty

def MissingZeroPremiseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    (T.1 ∩ U.1).Nonempty

def MissingIntegerOriginsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    Dense (eventual (geometry k hk) T.1 U.1)

def DirectOriginAgreementType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    originPatch (geometry k hk) T.1 = originPatch (geometry k hk) U.1

def DirectWindowAgreementType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    ∀ {R : ℝ}, 0 < R → Agree R T U

def SameFibreCommonTileWithoutPeriodsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T =
      realize (pisotData k hk) (inflateH_bijective k hk) U →
    (T.1 ∩ U.1).Nonempty

theorem wrongTypeControl : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let modules := #[`PscVerif.C4FamilyTileAutomatonHull, `PscVerif.C4FamilyFiniteZeroFibre]
    let hull := `PscVerif.C4FamilyTileAutomatonHull
    let zero := `PscVerif.C4FamilyFiniteZeroFibre
    let endpoints : Array (Name × Name × Name) := #[
      (`Psc.C4FamilyTileAutomatonHull.supertile_hull, ``SupertileHullType, hull),
      (`Psc.C4FamilyTileAutomatonHull.occurrence_hull_bridge, ``OccurrenceBridgeType, hull),
      (`Psc.C4FamilyTileAutomatonHull.forward_edge_hull_bridge, ``ForwardEdgeType, hull),
      (`Psc.C4FamilyTileAutomatonHull.signed_edge_hull_bridge, ``SignedEdgeType, hull),
      (`Psc.PeriodicPartnerEventualCoincidence.dense_eventual_trans, ``DenseTransType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.dense_eventual_of_walk, ``WalkTransferType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.dense_eventual_of_replay, ``ReplayTransferType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.dense_eventual_of_integer_displacement, ``IntegerDisplacementType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.integer_origin_of_zero, ``IntegerOriginType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.dense_eventual_of_integer_origins, ``IntegerOriginsTransferType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.dense_eventual_of_torusRealize_eq, ``EqualTorusDenseType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.same_fibre_dense_eventual, ``SameFibreDenseType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_dense_eventual, ``ZeroDenseType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_common_tile, ``ZeroCommonTileType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_exactProximal, ``ZeroExactShiftsType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_windowWitnesses, ``ZeroWindowsType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_closedOriginWitnesses, ``ZeroOriginsType, zero),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_stronglyRegionallyProximal, ``ZeroRegionalType, zero),
      (`Psc.ParameterFamilyZeroFibreControls.zero_fibre_seam_control, ``LiteralSeamControlType,
        `PscVerif.C4ParameterFamilyZeroFibreControls),
      (`Psc.ParameterFamilyInteriorZero.zero_fibre_not_all_vertices, ``LiteralInteriorControlType,
        `PscVerif.C4ParameterFamilyInteriorZero)]
    let semanticRefusals : Array (Name × Name) := #[
      (`Psc.C4FamilyTileAutomatonHull.signed_edge_hull_bridge, ``WrongSignedEdgeType),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_common_tile, ``MissingFamilyGuardType),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_common_tile, ``WeakerFamilyGuardType),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_common_tile, ``MissingZeroPremiseType),
      (`Psc.C4FamilyFiniteZeroFibre.dense_eventual_of_integer_origins, ``MissingIntegerOriginsType),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_closedOriginWitnesses, ``DirectOriginAgreementType),
      (`Psc.C4FamilyFiniteZeroFibre.zero_fibre_windowWitnesses, ``DirectWindowAgreementType),
      (`Psc.C4FamilyFiniteZeroFibre.same_fibre_dense_eventual,
        ``SameFibreCommonTileWithoutPeriodsType)]
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
        | throwError "Missing compiled finite-hull module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local finite-hull axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard finite-hull axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 || ownedProofs == 0 then throwError "Empty finite-hull module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_FINITE_HULL_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed finite-hull endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Finite-hull endpoint has no compiled owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong finite-hull endpoint owner: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard finite-hull endpoint axiom in {name}: {ax}"
      let names := String.intercalate "," (axioms.toList.map toString)
      Lean.Core.liftIOCore <| IO.println s!"PSC_FINITE_HULL_ENDPOINT\t{name}\t{names}"
    let missing := `Psc.C4FiniteHullWitnessAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (_, expected, _) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Finite-hull matcher accepted a wrong-typed theorem"
      if ← matchesType missing expected then
        throwError "Finite-hull matcher accepted a missing declaration"
    for (name, wrong) in semanticRefusals do
      if ← matchesType name wrong then
        throwError "Finite-hull matcher accepted altered contract {wrong} for {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_FINITE_HULL_CONTRACT_REFUSED\t{name}\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_FINITE_HULL_REFUSAL_CONTROLS\t{2 * endpoints.size + semanticRefusals.size}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_FINITE_HULL_AUDIT_COMPLETE\t{declarations}\t{proofs}"

end Psc.C4FiniteHullWitnessAudit
