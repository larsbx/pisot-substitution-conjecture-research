/- Independent type, owner and axiom audit of the finite all-at-once
coincidence and origin-separation contracts. Altered-contract refusals
guard the checker; they do not claim each altered proposition is false. -/
import PscVerif.C4FamilyFiniteFibreSynchronization
import PscVerif.C4FamilyOpenSynchronization
import PscVerif.PeriodicPartnerOriginSeparation
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace Psc.C4FiniteSynchronizationAudit

open Function Set Matrix
open Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (inflateH Agree translate)
open Psc.PeriodicPartnerEventualCoincidence (eventual)
open Psc.PeriodicPartnerRealization (PisotData torusRealize origin lattice Solenoid flow shiftS)
open Psc.PeriodicPartnerLocalTopology (LocalHull patch)
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilySolenoid (solenoidRealize pisotData)

universe u v

def FinitePointType : Prop :=
  ∀ {α : Type u} {ι : Type v} [Nonempty α] [Fintype ι] (S : LengthSubst α)
    (T : ι → S.Hull) (i₀ : ι) {x : ℝ},
    (∀ i, x ∈ eventual S (T i₀).1 (T i).1) →
    ∃ n : ℕ, ∃ q : α × ℝ,
      (∀ i, q ∈ (inflateH^[n] (T i)).1) ∧ S.β ^ n * x ∈ S.supp q

def FiniteTileType : Prop :=
  ∀ {α : Type u} {ι : Type v} [Nonempty α] [Fintype ι] (S : LengthSubst α)
    (T : ι → S.Hull) (i₀ : ι),
    (∀ i, Dense (eventual S (T i₀).1 (T i).1)) →
    ∃ n : ℕ, ∃ q : α × ℝ, ∀ i, q ∈ (inflateH^[n] (T i)).1

def FiniteWindowType : Prop :=
  ∀ {α : Type u} {ι : Type v} [Nonempty α] [Fintype ι] (S : LengthSubst α),
    1 < S.β → ∀ (T : ι → S.Hull) (i₀ : ι),
    (∀ i, Dense (eventual S (T i₀).1 (T i).1)) → ∀ {R : ℝ}, 0 < R →
    ∃ n : ℕ, ∃ t : ℝ, ∀ i j,
      Agree R (translate t (inflateH^[n] (T i)))
        (translate t (inflateH^[n] (T j)))

def FibreTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ z : Solenoid (geometry k hk),
    ∃ n : ℕ, ∃ q : Fin 3 × ℝ, ∀ T : LocalHull (geometry k hk),
      solenoidRealize k hk T = z → q ∈ (inflateH^[n] T.toHull).1

def FibreWindowType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ z : Solenoid (geometry k hk),
    ∀ {R : ℝ}, 0 < R → ∃ n : ℕ, ∃ t : ℝ,
      ∀ T U : LocalHull (geometry k hk),
      solenoidRealize k hk T = z → solenoidRealize k hk U = z →
      Agree R (translate t (inflateH^[n] T.toHull))
        (translate t (inflateH^[n] U.toHull))

def FiniteOriginsType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S))),
    ∃ D : Set ℝ, D.Finite ∧ ∀ T U : S.Hull,
      torusRealize P hR T = torusRealize P hR U →
      (origin T).2 - (origin U).2 ∈ D

def ShiftedFibreWindowType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ z : Solenoid (geometry k hk),
    ∀ {R : ℝ}, 0 < R → ∃ n : ℕ, ∃ t : ℝ,
      ∀ T U : LocalHull (geometry k hk),
      solenoidRealize k hk T = flow (pisotData k hk) t ((shiftS (geometry k hk))^[n] z) →
      solenoidRealize k hk U = flow (pisotData k hk) t ((shiftS (geometry k hk))^[n] z) →
      Agree R T.toHull U.toHull

def SomeFibreWindowType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {R : ℝ}, 0 < R →
    ∃ z : Solenoid (geometry k hk),
      (∃ T : LocalHull (geometry k hk), solenoidRealize k hk T = z) ∧
      ∀ T U : LocalHull (geometry k hk),
        solenoidRealize k hk T = z → solenoidRealize k hk U = z →
        Agree R T.toHull U.toHull

def FiniteGapType : Prop :=
  ∀ {D : Set ℝ}, D.Finite →
    ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ D, d ≠ 0 → ε ≤ |d|

def OriginSeparationType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S))),
    ∃ ε : ℝ, 0 < ε ∧ ∀ T U : S.Hull,
      torusRealize P hR T = torusRealize P hR U →
      |(origin T).2 - (origin U).2| < ε → (origin T).2 = (origin U).2

def CenteredFibreType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∃ z : Solenoid (geometry k hk), ∃ a : Fin 3,
      ∀ T : LocalHull (geometry k hk), solenoidRealize k hk T = z →
        (a, -((geometry k hk).ℓ a / 2)) ∈ T.toHull.1

def CenteredPatchType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (a : Fin 3) {δ : ℝ},
    δ ≤ (geometry k hk).ℓ a / 4 → ∀ {T U : LocalHull (geometry k hk)},
    (a, -((geometry k hk).ℓ a / 2)) ∈ T.toHull.1 →
    U ∈ patch (geometry k hk) T δ 1 →
    ∃ s : ℝ, |s| < δ ∧
      origin U.toHull = (a, -((geometry k hk).ℓ a / 2) - s)

def OpenWindowFromSeedType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (z : Solenoid (geometry k hk)) (a : Fin 3),
    (∀ T : LocalHull (geometry k hk), solenoidRealize k hk T = z →
      (a, -((geometry k hk).ℓ a / 2)) ∈ T.toHull.1) →
    ∃ W : Set (Solenoid (geometry k hk)), IsOpen W ∧ z ∈ W ∧
      ∀ w ∈ W, ∀ T U : LocalHull (geometry k hk),
        solenoidRealize k hk T = w → solenoidRealize k hk U = w →
        Agree ((geometry k hk).ℓ a / 4) T.toHull U.toHull

def OpenWindowType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∃ r : ℝ, 0 < r ∧ ∃ W : Set (Solenoid (geometry k hk)),
      IsOpen W ∧ W.Nonempty ∧
      ∀ w ∈ W, ∀ T U : LocalHull (geometry k hk),
        solenoidRealize k hk T = w → solenoidRealize k hk U = w →
        Agree r T.toHull U.toHull

def MissingFamilyGuardType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (z : Solenoid (geometry k hk)),
    ∃ n : ℕ, ∃ q : Fin 3 × ℝ, ∀ T : LocalHull (geometry k hk),
      solenoidRealize k hk T = z → q ∈ (inflateH^[n] T.toHull).1

def UninflatedFibreTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ z : Solenoid (geometry k hk),
    ∃ q : Fin 3 × ℝ, ∀ T : LocalHull (geometry k hk),
      solenoidRealize k hk T = z → q ∈ T.toHull.1

def UniformAllRadiiType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ z : Solenoid (geometry k hk),
    ∃ n : ℕ, ∃ t : ℝ, ∀ R : ℝ, 0 < R →
      ∀ T U : LocalHull (geometry k hk),
      solenoidRealize k hk T = z → solenoidRealize k hk U = z →
      Agree R (translate t (inflateH^[n] T.toHull))
        (translate t (inflateH^[n] U.toHull))

def MissingEqualTorusType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (_P : PisotData S) (_hR : Bijective (inflateH (S := S))),
    ∃ ε : ℝ, 0 < ε ∧ ∀ T U : S.Hull,
      |(origin T).2 - (origin U).2| < ε → (origin T).2 = (origin U).2

def MissingFiniteSetType : Prop :=
  ∀ {D : Set ℝ}, ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ D, d ≠ 0 → ε ≤ |d|

def OpenAgreementWithoutFibreType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∃ r : ℝ, 0 < r ∧ ∃ W : Set (Solenoid (geometry k hk)),
      IsOpen W ∧ W.Nonempty ∧
      ∀ (_w : Solenoid (geometry k hk)), _w ∈ W →
      ∀ T U : LocalHull (geometry k hk), Agree r T.toHull U.toHull

theorem wrongTypeControl : True := trivial

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let generic := `PscVerif.PeriodicPartnerFiniteCoincidence
    let family := `PscVerif.C4FamilyFiniteFibreSynchronization
    let origin := `PscVerif.PeriodicPartnerOriginSeparation
    let openSync := `PscVerif.C4FamilyOpenSynchronization
    let modules := #[generic, family, origin, openSync]
    let endpoints : Array (Name × Name × Name) := #[
      (`Psc.PeriodicPartnerFiniteCoincidence.common_tile_of_finite_eventual,
        ``FinitePointType, generic),
      (`Psc.PeriodicPartnerFiniteCoincidence.common_tile_of_finite_dense_eventual,
        ``FiniteTileType, generic),
      (`Psc.PeriodicPartnerFiniteCoincidence.common_window_of_finite_dense_eventual,
        ``FiniteWindowType, generic),
      (`Psc.C4FamilyFiniteFibreSynchronization.fibre_common_tile_after_inflation,
        ``FibreTileType, family),
      (`Psc.C4FamilyFiniteFibreSynchronization.fibre_common_window_after_inflation,
        ``FibreWindowType, family),
      (`Psc.C4FamilyFiniteFibreSynchronization.fibre_common_window_at_shifted_base,
        ``ShiftedFibreWindowType, family),
      (`Psc.C4FamilyFiniteFibreSynchronization.exists_fibre_common_window,
        ``SomeFibreWindowType, family),
      (`Psc.PeriodicPartnerOriginSeparation.exists_finite_origin_displacements,
        ``FiniteOriginsType, origin),
      (`Psc.PeriodicPartnerOriginSeparation.finite_nonzero_gap,
        ``FiniteGapType, origin),
      (`Psc.PeriodicPartnerOriginSeparation.exists_origin_separation,
        ``OriginSeparationType, origin),
      (`Psc.C4FamilyOpenSynchronization.exists_centered_tile_fibre,
        ``CenteredFibreType, openSync),
      (`Psc.C4FamilyOpenSynchronization.origin_of_centered_patch,
        ``CenteredPatchType, openSync),
      (`Psc.C4FamilyOpenSynchronization.open_common_window_of_centered_tile_fibre,
        ``OpenWindowFromSeedType, openSync),
      (`Psc.C4FamilyOpenSynchronization.exists_open_common_window,
        ``OpenWindowType, openSync)]
    let semanticRefusals : Array (Name × Name) := #[
      (`Psc.C4FamilyFiniteFibreSynchronization.fibre_common_tile_after_inflation,
        ``MissingFamilyGuardType),
      (`Psc.C4FamilyFiniteFibreSynchronization.fibre_common_tile_after_inflation,
        ``UninflatedFibreTileType),
      (`Psc.C4FamilyFiniteFibreSynchronization.fibre_common_window_after_inflation,
        ``UniformAllRadiiType),
      (`Psc.PeriodicPartnerOriginSeparation.exists_origin_separation,
        ``MissingEqualTorusType),
      (`Psc.PeriodicPartnerOriginSeparation.finite_nonzero_gap,
        ``MissingFiniteSetType),
      (`Psc.C4FamilyOpenSynchronization.exists_open_common_window,
        ``OpenAgreementWithoutFibreType)]
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
        | throwError "Missing compiled synchronization module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local synchronization axiom: {info.name}"
        for ax in ← collectAxioms info.name do
          unless allowed.contains ax do
            throwError "Nonstandard synchronization axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 || ownedProofs == 0 then throwError "Empty synchronization module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_FINITE_SYNC_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed synchronization endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Synchronization endpoint has no compiled owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong synchronization endpoint owner: {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Nonstandard synchronization endpoint axiom in {name}: {ax}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_FINITE_SYNC_ENDPOINT\t{name}"
    let missing := `Psc.C4FiniteSynchronizationAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing-declaration control collision"
    for (_, expected, _) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Synchronization matcher accepted a wrong-typed theorem"
      if ← matchesType missing expected then
        throwError "Synchronization matcher accepted a missing declaration"
    for (name, wrong) in semanticRefusals do
      if ← matchesType name wrong then
        throwError "Synchronization matcher accepted altered contract {wrong} for {name}"
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_FINITE_SYNC_CONTRACT_REFUSED\t{name}\t{wrong}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_FINITE_SYNC_REFUSAL_CONTROLS\t{2 * endpoints.size + semanticRefusals.size}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_FINITE_SYNC_AUDIT_COMPLETE\t{declarations}\t{proofs}"

end Psc.C4FiniteSynchronizationAudit
