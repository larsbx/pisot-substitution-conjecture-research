/- Replay after building the new zero-fibre modules. Expected witness predicates
are stated independently below; no theorem's inferred type is used as its
acceptance specification. Every owned declaration is scanned recursively for
axiom dependencies. Missing and wrong-typed endpoints must be refused. -/
import PscVerif.PeriodicPartnerProximal
import PscVerif.PeriodicPartnerPeriodicZero
import PscVerif.C4ParameterFamilyZeroFibreWitnesses
import PscVerif.C4ParameterFamilyZeroFibreControls
import PscVerif.C4ParameterFamilyInteriorSeed
import PscVerif.C4ParameterFamilyInteriorProximal
import PscVerif.C4ParameterFamilyInteriorZero
import Lean.Util.CollectAxioms

namespace Psc.ZeroFibreWitnessAudit

open Function Set Matrix
open Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (inflateH Agree translate shift)
open Psc.PeriodicPartnerLegalCoincidence (originPatch)
open Psc.PeriodicPartnerRealization (PisotData realize torusRealize lattice origin)
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilyRecognizability (inflateH_bijective)
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize)

universe u

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

def AllThreeWindows {α : Type u} (S : LengthSubst α) (T U : S.Hull) : Prop :=
  ∀ R : ℝ, 0 < R → ThreeWindows S R T U

def OriginFromAgreementType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) {R : ℝ}, 0 < R →
    ∀ {T U : S.Hull}, Agree R T U → originPatch S T.1 = originPatch S U.1

def MidpointAgreementType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) {T U : S.Hull} {q : α × ℝ},
    q ∈ T.1 → q ∈ U.1 →
    Agree (S.ℓ q.1 / 2) (translate (q.2 + S.ℓ q.1 / 2) T)
      (translate (q.2 + S.ℓ q.1 / 2) U)

def InflationTranslationType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) [Nonempty α] (T : S.Hull) (t : ℝ) (n : ℕ),
    inflateH^[n] (translate t T) = translate (S.β ^ n * t) (inflateH^[n] T)

def InflationPreservesShiftsType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) [Nonempty α] {T U : S.Hull},
    ExactShifts S T U → ∀ d : ℕ, ExactShifts S (inflateH^[d] T) (inflateH^[d] U)

def PeriodicCommonTileToShiftsType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) [Nonempty α], 1 < S.β →
    ∀ {T U : S.Hull} {m n : ℕ}, 0 < m → 0 < n →
    inflateH^[m] T = T → inflateH^[n] U = U →
    (T.1 ∩ U.1).Nonempty → ExactShifts S T U

def ShiftsToCommonTileType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) {T U : S.Hull},
    ExactShifts S T U → (T.1 ∩ U.1).Nonempty

def PeriodicCommonTileIffShiftsType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) [Nonempty α], 1 < S.β →
    ∀ {T U : S.Hull} {m n : ℕ}, 0 < m → 0 < n →
    inflateH^[m] T = T → inflateH^[n] U = U →
    (ExactShifts S T U ↔ (T.1 ∩ U.1).Nonempty)

def OriginWitnessFromWindowsType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) {R : ℝ}, 0 < R →
    ∀ {T U : S.Hull}, ThreeWindows S R T U → ThreeOrigins S T U

def RegionalFromShiftsType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) {T U : S.Hull},
    ExactShifts S T U → AllThreeWindows S T U

def PeriodicTorusToHistoryType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))
    {T : S.Hull} {p : ℕ}, 0 < p → inflateH^[p] T = T →
    torusRealize P hR T = 0 → realize P hR T = 0

def PeriodicLatticeToTorusType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))
    {T : S.Hull} {p : ℕ}, 0 < p → inflateH^[p] T = T →
    ∀ {v : α → ℝ}, v ∈ lattice α → (origin T).2 = -(S.ℓ ⬝ᵥ v) →
    torusRealize P hR T = 0

def PeriodicLatticeToHistoryType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))
    {T : S.Hull} {p : ℕ}, 0 < p → inflateH^[p] T = T →
    ∀ {v : α → ℝ}, v ∈ lattice α → (origin T).2 = -(S.ℓ ⬝ᵥ v) →
    realize P hR T = 0

def HistoryToLatticeType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))
    {T : S.Hull}, realize P hR T = 0 →
    ∃ v : α → ℝ, v ∈ lattice α ∧ (origin T).2 = -(S.ℓ ⬝ᵥ v)

def PeriodicZeroCharacterizationType : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))
    {T : S.Hull} {p : ℕ}, 0 < p → inflateH^[p] T = T →
    (realize P hR T = 0 ↔
      ∃ v : α → ℝ, v ∈ lattice α ∧ (origin T).2 = -(S.ℓ ⬝ᵥ v))

def FamilyOriginToCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    ThreeOrigins (geometry k hk) T U → (T.1 ∩ U.1).Nonempty

def FamilyZeroCharacterizationType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {T : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ↔
      ∃ n > 0, inflateH^[n] T = T ∧
        ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧
          (origin T).2 = -((geometry k hk).ℓ ⬝ᵥ v)

def FamilyShiftsIffCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    (ExactShifts (geometry k hk) T U ↔ (T.1 ∩ U.1).Nonempty)

def FamilyWindowsIffCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {R : ℝ}, 0 < R →
    ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    (ThreeWindows (geometry k hk) R T U ↔ (T.1 ∩ U.1).Nonempty)

def FamilyOriginsIffCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    (ThreeOrigins (geometry k hk) T U ↔ (T.1 ∩ U.1).Nonempty)

def FamilyRegionalIffCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    (AllThreeWindows (geometry k hk) T U ↔ (T.1 ∩ U.1).Nonempty)

def FamilyCommonTileTransType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T V U : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
    (T.1 ∩ V.1).Nonempty → (V.1 ∩ U.1).Nonempty → (T.1 ∩ U.1).Nonempty

def FamilyAnchorReductionType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    ((∀ T U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
      ThreeWindows (geometry k hk) 1 T U) ↔
    (∀ U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
      ThreeWindows (geometry k hk) 1 V U))

def FamilyPeriodicLatticeAnchorType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    ((∀ T U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
      ThreeWindows (geometry k hk) 1 T U) ↔
    (∀ U : (geometry k hk).Hull,
      (∃ n > 0, inflateH^[n] U = U ∧
        ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧
          (origin U).2 = -((geometry k hk).ℓ ⬝ᵥ v)) →
      (V.1 ∩ U.1).Nonempty))

def LiteralSeamNegativeType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), ∃ T U : (geometry k hk).Hull,
    inflateH T = U ∧ inflateH^[2] T = T ∧
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ∧
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 ∧
    (1, 0) ∈ T.1 ∧ (0, 0) ∈ U.1 ∧ T ≠ U ∧
    originPatch (geometry k hk) T.1 ≠ originPatch (geometry k hk) U.1 ∧ ¬ Agree 1 T U

def LiteralNoninjectiveType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), ¬ Injective (solenoidRealize k hk)

def LiteralSeamCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T : (geometry k hk).Hull},
    (1, 0) ∈ T.1 → inflateH^[2] T = T →
    (1, (geometry k hk).ℓ 0 + (geometry k hk).ℓ 1) ∈ T.1 ∩ (inflateH T).1

def LiteralSeamPositiveType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∃ T U : (geometry k hk).Hull,
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ∧
    realize (pisotData k hk) (inflateH_bijective k hk) U = 0 ∧
    originPatch (geometry k hk) T.1 ≠ originPatch (geometry k hk) U.1 ∧
    ExactShifts (geometry k hk) T U

def InteriorSeedType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∃ T : (geometry k hk).Hull,
    (1, -(geometry k hk).ℓ 0) ∈ T.1 ∧ inflateH^[3] T = T

def InteriorChildrenType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ x : ℝ,
    let S := geometry k hk
    (1, S.β * x + S.ℓ 0) ∈ S.place (S.σ 1) (S.β * x) ∧
    (1, S.β * x + S.ℓ 0 + ((k - 1 : ℕ) : ℝ) * S.ℓ 1) ∈
      S.place (S.σ 1) (S.β * x) ∧
    (1, S.β * x + S.ℓ 0 + S.ℓ 1) ∈ S.place (S.σ 1) (S.β * x)

def InteriorCycleTilesType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {P : Set (Fin 3 × ℝ)},
    (1, -(geometry k hk).ℓ 0) ∈ P →
    let S := geometry k hk
    (1, S.ℓ 0 - S.ℓ 1) ∈ S.inflate P ∧
    (1, -S.ℓ 2) ∈ S.inflate^[2] P ∧ (1, -S.ℓ 0) ∈ S.inflate^[3] P

def InteriorCycleOriginsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∃ T : (geometry k hk).Hull,
    inflateH^[3] T = T ∧
    origin T = (1, -(geometry k hk).ℓ 0) ∧
    origin (inflateH T) = (1, (geometry k hk).ℓ 0 - (geometry k hk).ℓ 1) ∧
    origin (inflateH^[2] T) = (1, -(geometry k hk).ℓ 2)

def InteriorNoVertexType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {T : (geometry k hk).Hull},
    origin T = (1, -(geometry k hk).ℓ 0) → ¬ ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1

def SeamInteriorCommonTileType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    (1, 0) ∈ T.1 → inflateH^[2] T = T →
    (1, -(geometry k hk).ℓ 0) ∈ U.1 → inflateH^[3] U = U →
    (0, (geometry k hk).ℓ 1 + (geometry k hk).β * (geometry k hk).ℓ 1) ∈ T.1 ∩ U.1

def SeamInteriorShiftsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    (1, 0) ∈ T.1 → inflateH^[2] T = T →
    (1, -(geometry k hk).ℓ 0) ∈ U.1 → inflateH^[3] U = U →
    ExactShifts (geometry k hk) T U

def SeamInteriorOrbitShiftsType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : (geometry k hk).Hull},
    (1, 0) ∈ T.1 → inflateH^[2] T = T →
    (1, -(geometry k hk).ℓ 0) ∈ U.1 → inflateH^[3] U = U →
    ∀ i : ℕ, ExactShifts (geometry k hk) T (inflateH^[i] U)

def InteriorZeroCycleType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∃ T : (geometry k hk).Hull,
    inflateH^[3] T = T ∧
    origin T = (1, -(geometry k hk).ℓ 0) ∧
    origin (inflateH T) = (1, (geometry k hk).ℓ 0 - (geometry k hk).ℓ 1) ∧
    origin (inflateH^[2] T) = (1, -(geometry k hk).ℓ 2) ∧
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ∧
    realize (pisotData k hk) (inflateH_bijective k hk) (inflateH T) = 0 ∧
    realize (pisotData k hk) (inflateH_bijective k hk) (inflateH^[2] T) = 0 ∧
    ¬ ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1

def ZeroNotAllVerticesType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ¬ ∀ T : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
      ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1

def SeamAndInteriorZeroWitnessesType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∃ V T : (geometry k hk).Hull,
    (1, 0) ∈ V.1 ∧ inflateH^[2] V = V ∧ inflateH^[3] T = T ∧
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 ∧
    origin T = (1, -(geometry k hk).ℓ 0) ∧
    (¬ ∃ a : Fin 3, (a, (0 : ℝ)) ∈ T.1) ∧
    ∀ i : ℕ,
      realize (pisotData k hk) (inflateH_bijective k hk) (inflateH^[i] T) = 0 ∧
      ExactShifts (geometry k hk) V (inflateH^[i] T)

theorem wrongTypeControl : True := True.intro
theorem wrongPolymorphicTypeControl {α : Type u} (_ : α) : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``Psc.PeriodicPartnerProximal.originPatch_eq_of_agree, ``OriginFromAgreementType,
        `PscVerif.PeriodicPartnerProximal),
      (``Psc.PeriodicPartnerProximal.agree_at_common_tile, ``MidpointAgreementType,
        `PscVerif.PeriodicPartnerProximal),
      (``Psc.PeriodicPartnerProximal.inflateH_iterate_translate, ``InflationTranslationType,
        `PscVerif.PeriodicPartnerProximal),
      (``Psc.PeriodicPartnerProximal.ExactProximal.inflate_iterate,
        ``InflationPreservesShiftsType, `PscVerif.PeriodicPartnerProximal),
      (``Psc.PeriodicPartnerProximal.exactProximal_of_periodic_common_tile,
        ``PeriodicCommonTileToShiftsType, `PscVerif.PeriodicPartnerProximal),
      (``Psc.PeriodicPartnerProximal.common_tile_of_exactProximal, ``ShiftsToCommonTileType,
        `PscVerif.PeriodicPartnerProximal),
      (``Psc.PeriodicPartnerProximal.exactProximal_iff_common_tile_of_periodic,
        ``PeriodicCommonTileIffShiftsType, `PscVerif.PeriodicPartnerProximal),
      (``Psc.PeriodicPartnerProximal.closedOriginWitnesses_of_windowWitnesses,
        ``OriginWitnessFromWindowsType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.PeriodicPartnerProximal.stronglyRegionallyProximal_of_exactProximal,
        ``RegionalFromShiftsType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.PeriodicPartnerPeriodicZero.realize_zero_of_periodic_torus_zero,
        ``PeriodicTorusToHistoryType, `PscVerif.PeriodicPartnerPeriodicZero),
      (``Psc.PeriodicPartnerPeriodicZero.torusRealize_zero_of_periodic_lattice_origin,
        ``PeriodicLatticeToTorusType, `PscVerif.PeriodicPartnerPeriodicZero),
      (``Psc.PeriodicPartnerPeriodicZero.realize_zero_of_periodic_lattice_origin,
        ``PeriodicLatticeToHistoryType, `PscVerif.PeriodicPartnerPeriodicZero),
      (``Psc.PeriodicPartnerPeriodicZero.lattice_origin_of_realize_zero,
        ``HistoryToLatticeType, `PscVerif.PeriodicPartnerPeriodicZero),
      (``Psc.PeriodicPartnerPeriodicZero.realize_zero_iff_lattice_origin_of_periodic,
        ``PeriodicZeroCharacterizationType, `PscVerif.PeriodicPartnerPeriodicZero),
      (``Psc.ParameterFamilyZeroFibreWitnesses.realize_zero_iff_periodic_lattice_origin,
        ``FamilyZeroCharacterizationType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreWitnesses.common_tile_of_closedOriginWitnesses,
        ``FamilyOriginToCommonTileType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreWitnesses.exactProximal_iff_common_tile,
        ``FamilyShiftsIffCommonTileType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreWitnesses.windowWitnesses_iff_common_tile,
        ``FamilyWindowsIffCommonTileType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreWitnesses.closedOriginWitnesses_iff_common_tile,
        ``FamilyOriginsIffCommonTileType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreWitnesses.stronglyRegionallyProximal_iff_common_tile,
        ``FamilyRegionalIffCommonTileType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreWitnesses.common_tile_trans,
        ``FamilyCommonTileTransType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreWitnesses.all_pair_witnesses_iff_anchor,
        ``FamilyAnchorReductionType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreWitnesses.all_pair_witnesses_iff_periodic_lattice_anchor,
        ``FamilyPeriodicLatticeAnchorType, `PscVerif.C4ParameterFamilyZeroFibreWitnesses),
      (``Psc.ParameterFamilyZeroFibreControls.zero_fibre_seam_control,
        ``LiteralSeamNegativeType, `PscVerif.C4ParameterFamilyZeroFibreControls),
      (``Psc.ParameterFamilyZeroFibreControls.solenoidRealize_not_injective,
        ``LiteralNoninjectiveType, `PscVerif.C4ParameterFamilyZeroFibreControls),
      (``Psc.ParameterFamilyZeroFibreControls.seam_pair_common_tile,
        ``LiteralSeamCommonTileType, `PscVerif.C4ParameterFamilyZeroFibreControls),
      (``Psc.ParameterFamilyZeroFibreControls.zero_fibre_pair_with_exact_shifts,
        ``LiteralSeamPositiveType, `PscVerif.C4ParameterFamilyZeroFibreControls),
      (``Psc.ParameterFamilyInteriorSeed.interior_periodic_tiling,
        ``InteriorSeedType, `PscVerif.C4ParameterFamilyInteriorSeed),
      (``Psc.ParameterFamilyInteriorSeed.interior_child_positions,
        ``InteriorChildrenType, `PscVerif.C4ParameterFamilyInteriorSeed),
      (``Psc.ParameterFamilyInteriorSeed.interior_cycle_tiles,
        ``InteriorCycleTilesType, `PscVerif.C4ParameterFamilyInteriorSeed),
      (``Psc.ParameterFamilyInteriorSeed.interior_periodic_origins,
        ``InteriorCycleOriginsType, `PscVerif.C4ParameterFamilyInteriorSeed),
      (``Psc.ParameterFamilyInteriorSeed.no_origin_vertex,
        ``InteriorNoVertexType, `PscVerif.C4ParameterFamilyInteriorSeed),
      (``Psc.ParameterFamilyInteriorProximal.seam_interior_common_tile,
        ``SeamInteriorCommonTileType, `PscVerif.C4ParameterFamilyInteriorProximal),
      (``Psc.ParameterFamilyInteriorProximal.seam_interior_exactProximal,
        ``SeamInteriorShiftsType, `PscVerif.C4ParameterFamilyInteriorProximal),
      (``Psc.ParameterFamilyInteriorProximal.seam_interior_orbit_exactProximal,
        ``SeamInteriorOrbitShiftsType, `PscVerif.C4ParameterFamilyInteriorProximal),
      (``Psc.ParameterFamilyInteriorZero.interior_zero_cycle,
        ``InteriorZeroCycleType, `PscVerif.C4ParameterFamilyInteriorZero),
      (``Psc.ParameterFamilyInteriorZero.zero_fibre_not_all_vertices,
        ``ZeroNotAllVerticesType, `PscVerif.C4ParameterFamilyInteriorZero),
      (``Psc.ParameterFamilyInteriorZero.seam_and_interior_zero_witnesses,
        ``SeamAndInteriorZeroWitnessesType, `PscVerif.C4ParameterFamilyInteriorZero)]
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
    let modules := #[`PscVerif.PeriodicPartnerProximal,
      `PscVerif.PeriodicPartnerPeriodicZero, `PscVerif.C4ParameterFamilyZeroFibreWitnesses,
      `PscVerif.C4ParameterFamilyZeroFibreControls, `PscVerif.C4ParameterFamilyInteriorSeed,
      `PscVerif.C4ParameterFamilyInteriorProximal, `PscVerif.C4ParameterFamilyInteriorZero]
    let mut declarations := 0
    let mut proofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled zero-fibre module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local zero-fibre axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard zero-fibre axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 then throwError "Empty zero-fibre module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println s!"PSC_ZERO_FIBRE_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_ZERO_FIBRE_DECLARATIONS\t{modules.size}\t{declarations}\t{proofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed zero-fibre endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Zero-fibre endpoint has no imported owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong zero-fibre endpoint owner: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard zero-fibre endpoint axiom in {name}: {ax}"
      let names := String.intercalate "," (axioms.toList.map toString)
      Lean.Core.liftIOCore <| IO.println s!"PSC_ZERO_FIBRE_ENDPOINT\t{name}\t{names}"
    if (env.find? `Psc.ZeroFibreWitnessAudit.absentEndpoint).isSome then
      throwError "Missing-declaration control name collision"
    for (_, expected, _) in endpoints do
      let expectedInfo ← getConstInfo expected
      let wrong := if expectedInfo.levelParams.isEmpty then ``wrongTypeControl
        else ``wrongPolymorphicTypeControl
      if ← matchesType wrong expected then
        throwError "Zero-fibre matcher accepted a wrong-type theorem"
      if ← matchesType `Psc.ZeroFibreWitnessAudit.absentEndpoint expected then
        throwError "Zero-fibre matcher accepted a missing declaration"
    Lean.Core.liftIOCore <| IO.println s!"PSC_ZERO_FIBRE_AUDIT_COMPLETE\t{endpoints.size}\t{2 * endpoints.size}"

end Psc.ZeroFibreWitnessAudit
