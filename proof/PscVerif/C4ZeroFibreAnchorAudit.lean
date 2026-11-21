/- Replay after building the return-module and zero-fibre anchor modules.
Expected endpoint types are stated independently below, with the coincidence
shift group spelled out as dense eventual coincidence; no theorem's inferred
type is used as its acceptance specification. Every owned declaration is
scanned recursively for axiom dependencies. Missing and wrong-typed endpoints
must be refused. -/
import PscVerif.PeriodicPartnerReturnModule
import PscVerif.C4ParameterFamilyZeroFibreAnchor
import Lean.Util.CollectAxioms

namespace Psc.ZeroFibreAnchorAudit

open Function Set Matrix
open Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (inflateH Agree translate shift)
open Psc.PeriodicPartnerLegalCoincidence (originPatch)
open Psc.PeriodicPartnerEventualCoincidence (eventual)
open Psc.PeriodicPartnerRealization (realize lattice origin)
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilyRecognizability (inflateH_bijective)
open Psc.ParameterFamilySolenoid (pisotData)

universe u

def CommonTileDense {α : Type u} (S : LengthSubst α) : Prop :=
  ∀ {T U : S.Hull}, (T.1 ∩ U.1).Nonempty → Dense (eventual S T.1 U.1)

def SelfDense {α : Type u} (S : LengthSubst α) (T : S.Hull) (w : ℝ) : Prop :=
  Dense (eventual S T.1 (shift w T.1))

def ExactShifts {α : Type u} (S : LengthSubst α) (T U : S.Hull) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ t : ℝ, Agree R (translate t T) (translate t U)

def ThreeWindows {α : Type u} (S : LengthSubst α) (R : ℝ) (T U : S.Hull) : Prop :=
  ∃ T' U' : S.Hull, ∃ t : ℝ,
    Agree R T T' ∧ Agree R U U' ∧ Agree R (translate t T') (translate t U')

def ThreeOrigins {α : Type u} (S : LengthSubst α) (T U : S.Hull) : Prop :=
  ∃ T' U' : S.Hull, ∃ t : ℝ,
    originPatch S T.1 = originPatch S T'.1 ∧
    originPatch S U.1 = originPatch S U'.1 ∧
    originPatch S (shift t T'.1) = originPatch S (shift t U'.1)

def Zero (k : ℕ) (hk : 1 ≤ k) (T : (geometry k hk).Hull) : Prop :=
  realize (pisotData k hk) (inflateH_bijective k hk) T = 0

def SameImage (k : ℕ) (hk : 1 ≤ k) (T U : (geometry k hk).Hull) : Prop :=
  realize (pisotData k hk) (inflateH_bijective k hk) T =
    realize (pisotData k hk) (inflateH_bijective k hk) U

def LatticeOffset (k : ℕ) (hk : 1 ≤ k) (T U : (geometry k hk).Hull) (v : Fin 3 → ℝ) : Prop :=
  (origin T).2 - (origin U).2 = (geometry k hk).ℓ ⬝ᵥ v

/-! Generic return-module endpoints -/

def DenseTransType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) [Nonempty α] {P Q R : Set (α × ℝ)}, S.IsTiling Q →
    Dense (eventual S P Q) → Dense (eventual S Q R) → Dense (eventual S P R)

def StartDifferenceType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) (T : S.Hull) {p q : α × ℝ}, p ∈ T.1 → q ∈ T.1 →
    q.2 - p.2 ∈ AddSubgroup.closure (range S.ℓ)

def LatticeCombinationType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) [Fintype α] {v : α → ℝ}, v ∈ lattice α →
    S.ℓ ⬝ᵥ v ∈ AddSubgroup.closure (range S.ℓ)

def ReturnVectorType : Prop :=
  ∀ {α : Type u} {S : LengthSubst α} (_ : CommonTileDense S) [Nonempty α] {T : S.Hull}
    {a : α} {x y : ℝ}, (a, x) ∈ T.1 → (a, y) ∈ T.1 → SelfDense S T (y - x)

def InflateShiftType : Prop :=
  ∀ {α : Type u} {S : LengthSubst α} (_ : CommonTileDense S) [Nonempty α] {T : S.Hull}
    {w : ℝ}, SelfDense S T w → SelfDense S (inflateH T) (S.β * w)

def LengthGroupCoincidenceType : Prop :=
  ∀ {α : Type u} {S : LengthSubst α} (_ : CommonTileDense S) [Nonempty α] {T U : S.Hull},
    (∀ a, SelfDense S T (S.ℓ a)) → ∀ {a : α} {x y : ℝ}, (a, x) ∈ T.1 → (a, y) ∈ U.1 →
      x - y ∈ AddSubgroup.closure (range S.ℓ) → Dense (eventual S T.1 U.1)

/-! Family endpoints -/

def ImagePatchType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (T : (geometry k hk).Hull) (c : Fin 3),
    ∃ s, shift s ((geometry k hk).supertile c 1) ⊆ T.1

def ZeroPairType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k),
    ((0 : Fin 3), (0 : ℝ)) ∈ (geometry k hk).supertile 2 1 ∧
      ((0 : Fin 3), (geometry k hk).ℓ 0) ∈ (geometry k hk).supertile 2 1

def OnePairType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ((1 : Fin 3), (geometry k hk).ℓ 0) ∈ (geometry k hk).supertile 1 1 ∧
      ((1 : Fin 3), (geometry k hk).ℓ 0 + (geometry k hk).ℓ 1) ∈ (geometry k hk).supertile 1 1

def LengthTwoType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), (geometry k hk).ℓ 2 =
    (geometry k hk).β * (geometry k hk).ℓ 1 - (geometry k hk).ℓ 0 - k • (geometry k hk).ℓ 1

def BoundaryControlType : Prop :=
  ((1 : Fin 3), (geometry 1 le_rfl).ℓ 0 + (geometry 1 le_rfl).ℓ 1) ∉
    (geometry 1 le_rfl).supertile 1 1

def SameImageOffsetType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {T U : (geometry k hk).Hull}, SameImage k hk T U →
    ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧ LatticeOffset k hk T U v

def FamilyLengthShiftType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ (T : (geometry k hk).Hull) (a : Fin 3),
    SelfDense (geometry k hk) T ((geometry k hk).ℓ a)

def LatticeOffsetDenseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull} {v : Fin 3 → ℝ},
    v ∈ lattice (Fin 3) → LatticeOffset k hk T U v →
    Dense (eventual (geometry k hk) T.1 U.1)

def FibreDenseType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull}, SameImage k hk T U →
    Dense (eventual (geometry k hk) T.1 U.1)

def PeriodicLatticeCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull} {m n : ℕ},
    0 < m → 0 < n → inflateH^[m] T = T → inflateH^[n] U = U →
    ∀ {v : Fin 3 → ℝ}, v ∈ lattice (Fin 3) → LatticeOffset k hk T U v →
    (T.1 ∩ U.1).Nonempty

def PeriodicFibreCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull} {m n : ℕ},
    0 < m → 0 < n → inflateH^[m] T = T → inflateH^[n] U = U →
    SameImage k hk T U → (T.1 ∩ U.1).Nonempty

def ZeroCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    Zero k hk T → Zero k hk U → (T.1 ∩ U.1).Nonempty

def AnchorType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {V : (geometry k hk).Hull}, Zero k hk V →
    ∀ U : (geometry k hk).Hull,
      (∃ n > 0, inflateH^[n] U = U ∧ ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧
        (origin U).2 = -((geometry k hk).ℓ ⬝ᵥ v)) →
      (V.1 ∩ U.1).Nonempty

def ZeroExactShiftsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    Zero k hk T → Zero k hk U → ExactShifts (geometry k hk) T U

def ZeroAllWindowsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    Zero k hk T → Zero k hk U → ∀ R : ℝ, 0 < R → ThreeWindows (geometry k hk) R T U

def ZeroUnitWindowsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ T U : (geometry k hk).Hull,
    Zero k hk T → Zero k hk U → ThreeWindows (geometry k hk) 1 T U

def ZeroOriginsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    Zero k hk T → Zero k hk U → ThreeOrigins (geometry k hk) T U

def DistinctControlType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∃ T U : (geometry k hk).Hull,
    SameImage k hk T U ∧ T ≠ U ∧ ¬ Agree 1 T U ∧
    Dense (eventual (geometry k hk) T.1 U.1) ∧ (T.1 ∩ U.1).Nonempty

theorem wrongTypeControl : True := True.intro
theorem wrongPolymorphicTypeControl {α : Type u} (_ : α) : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``Psc.PeriodicPartnerReturnModule.dense_eventual_trans, ``DenseTransType,
        `PscVerif.PeriodicPartnerReturnModule),
      (``Psc.PeriodicPartnerReturnModule.start_sub_mem_lengthGroup, ``StartDifferenceType,
        `PscVerif.PeriodicPartnerReturnModule),
      (``Psc.PeriodicPartnerReturnModule.dot_mem_lengthGroup, ``LatticeCombinationType,
        `PscVerif.PeriodicPartnerReturnModule),
      (``Psc.PeriodicPartnerReturnModule.return_mem, ``ReturnVectorType,
        `PscVerif.PeriodicPartnerReturnModule),
      (``Psc.PeriodicPartnerReturnModule.inflate_mem, ``InflateShiftType,
        `PscVerif.PeriodicPartnerReturnModule),
      (``Psc.PeriodicPartnerReturnModule.dense_eventual_of_lengthGroup,
        ``LengthGroupCoincidenceType, `PscVerif.PeriodicPartnerReturnModule),
      (``Psc.ParameterFamilyZeroFibreAnchor.contains_image_patch, ``ImagePatchType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.zero_pair_in_image, ``ZeroPairType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.one_pair_in_image, ``OnePairType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.length_two_eq, ``LengthTwoType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.one_pair_absent_at_one, ``BoundaryControlType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.lattice_offset_of_realize_eq, ``SameImageOffsetType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.length_mem_coincidenceShifts, ``FamilyLengthShiftType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.dense_eventual_of_lattice_offset,
        ``LatticeOffsetDenseType, `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.fibre_dense_eventual, ``FibreDenseType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.periodic_common_tile_of_lattice_offset,
        ``PeriodicLatticeCommonTileType, `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.periodic_fibre_common_tile,
        ``PeriodicFibreCommonTileType, `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.zero_fibre_common_tile, ``ZeroCommonTileType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.periodic_lattice_anchor, ``AnchorType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.zero_fibre_exactProximal, ``ZeroExactShiftsType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.zero_fibre_stronglyRegionallyProximal,
        ``ZeroAllWindowsType, `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.zero_fibre_window_witnesses, ``ZeroUnitWindowsType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.zero_fibre_closedOriginWitnesses, ``ZeroOriginsType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor),
      (``Psc.ParameterFamilyZeroFibreAnchor.same_fibre_distinct_control, ``DistinctControlType,
        `PscVerif.C4ParameterFamilyZeroFibreAnchor)]
    let env ← getEnv
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
    let modules := #[`PscVerif.PeriodicPartnerReturnModule,
      `PscVerif.C4ParameterFamilyZeroFibreAnchor]
    let mut declarations := 0
    let mut proofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled zero-fibre anchor module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local zero-fibre anchor axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard zero-fibre anchor axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 then throwError "Empty zero-fibre anchor module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println s!"PSC_ZERO_FIBRE_ANCHOR_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    Lean.Core.liftIOCore <|
      IO.println s!"PSC_ZERO_FIBRE_ANCHOR_DECLARATIONS\t{modules.size}\t{declarations}\t{proofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed zero-fibre anchor endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Zero-fibre anchor endpoint has no imported owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong zero-fibre anchor endpoint owner: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard zero-fibre anchor endpoint axiom in {name}: {ax}"
      let names := String.intercalate "," (axioms.toList.map toString)
      Lean.Core.liftIOCore <| IO.println s!"PSC_ZERO_FIBRE_ANCHOR_ENDPOINT\t{name}\t{names}"
    if (env.find? `Psc.ZeroFibreAnchorAudit.absentEndpoint).isSome then
      throwError "Missing-declaration control name collision"
    for (_, expected, _) in endpoints do
      let expectedInfo ← getConstInfo expected
      let wrong := if expectedInfo.levelParams.isEmpty then ``wrongTypeControl
        else ``wrongPolymorphicTypeControl
      if ← matchesType wrong expected then
        throwError "Zero-fibre anchor matcher accepted a wrong-type theorem"
      if ← matchesType `Psc.ZeroFibreAnchorAudit.absentEndpoint expected then
        throwError "Zero-fibre anchor matcher accepted a missing declaration"
    Lean.Core.liftIOCore <|
      IO.println s!"PSC_ZERO_FIBRE_ANCHOR_AUDIT_COMPLETE\t{endpoints.size}\t{2 * endpoints.size}"

end Psc.ZeroFibreAnchorAudit
