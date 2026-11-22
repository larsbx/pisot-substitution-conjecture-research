/- Independent acceptance specification for the finite-automaton proximal route.
The retained expected types are adapted from the accepted closure audit at
4b02c2d4c55fb62bf37f25aa0bbc4e44bec0b6a7. The predicates below are independently
expanded, not aliases of the implementation definitions. Every owned declaration
is scanned recursively for axioms; endpoint types, owners, and missing/wrong-type
refusal controls are checked. The old tile-chain route is excluded from imports.

NonproximalRank counts finite pairwise nonproximal subsets of a fibre, not its
cardinality. The actual zero_not_fibreDistal endpoint remains a concrete control
against universal singleton fibres. Almost-everywhere inputs remain explicit
in the independently stated expected types. The ordinary-hull compactness
boundary is reused unchanged, as recorded in the source decision
`docs/c4-finite-fibre-obligations-2026-11-21.md`. -/
import PscVerif.PeriodicPartnerOrdinaryProximal
import PscVerif.C4ParameterFamilyOrdinaryProximal
import PscVerif.C4FamilyFiniteProximal
import PscVerif.PeriodicPartnerRotationFactor
import PscVerif.C4ParameterFamilyRotationFactor
import PscVerif.PeriodicPartnerEquicontinuousFactor
import PscVerif.C4ParameterFamilyEquicontinuousFactor
import PscVerif.PeriodicPartnerFibreDistal
import PscVerif.C4ParameterFamilyFibreDistal
import Lean.Util.CollectAxioms

namespace Psc.FiniteProximalAudit

open Function Set MeasureTheory
open Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst (Agree translate)
open Psc.PeriodicPartnerLocalTopology (LocalHull ofExact patch)
open Psc.PeriodicPartnerRealization (realize Solenoid flow)
open Psc.ParameterFamilyTiling (geometry)
open Psc.ParameterFamilyRecognizability (inflateH_bijective)
open Psc.ParameterFamilySolenoid (pisotData solenoidRealize)

universe u v w

def ExactShifts {α : Type u} (S : LengthSubst α) (T U : S.Hull) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ t : ℝ, Agree R (translate t T) (translate t U)

def ThreeWindows {α : Type u} (S : LengthSubst α) (R : ℝ) (T U : S.Hull) : Prop :=
  ∃ T' U' : S.Hull, ∃ t : ℝ,
    Agree R T T' ∧ Agree R U U' ∧ Agree R (translate t T') (translate t U')

def OrdinaryProximal {X : Type u} [TopologicalSpace X]
    (act : ℝ → X → X) (x y : X) : Prop :=
  ∃ z : X, (z, z) ∈ closure (range (fun t : ℝ => (act t x, act t y)))

def FibreDistal {X : Type u} {Y : Type v} [TopologicalSpace X]
    (act : ℝ → X → X) (g : X → Y) (z : Y) : Prop :=
  ∀ x : X, g x = z → ∀ y : X, OrdinaryProximal act x y → y = x

noncomputable def NonproximalRank {X : Type u} {Y : Type v} [TopologicalSpace X]
    (act : ℝ → X → X) (g : X → Y) (z : Y) : ℕ∞ :=
  ⨆ (F : Finset X) (_ : ∀ x ∈ F, g x = z)
    (_ : (F : Set X).Pairwise (fun x y => ¬ OrdinaryProximal act x y)), (F.card : ℕ∞)

def PairOrbitInvarianceType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (act : ℝ → X → X),
    (∀ t, Continuous (act t)) →
    (∀ s t x, act s (act t x) = act (s + t) x) → ∀ {x y : X} {p : X × X},
    p ∈ closure (range (fun t : ℝ => (act t x, act t y))) → ∀ s : ℝ,
    (act s p.1, act s p.2) ∈ closure (range (fun t : ℝ => (act t x, act t y)))

def CompactAnchorTransportType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (act : ℝ → X → X),
    (∀ t, Continuous (act t)) →
    (∀ s t x, act s (act t x) = act (s + t) x) →
    (∀ x, DenseRange (fun t : ℝ => act t x)) →
    ∀ (g : X → Y), Continuous g →
    (∀ t x y, g x = g y → g (act t x) = g (act t y)) →
    ∀ v : X, (∀ w, g w = g v → OrdinaryProximal act v w) →
    ∀ {x y : X}, g x = g y → OrdinaryProximal act x y

def PatchTransferType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) {V T U : LocalHull S} {ε R : ℝ} {n : ℕ},
    ε ≤ 1 → T ∈ patch S V ε n → (n : ℝ) + 1 ≤ R →
    Agree R T.toHull U.toHull → U ∈ patch S V ε n

def ExactToOrdinaryType : Prop :=
  ∀ {α : Type u} (S : LengthSubst α) [Fintype α] [DecidableEq α] [Nonempty α]
    {T U : S.Hull}, ExactShifts S T U →
    OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate S)
      (ofExact S T) (ofExact S U)

def FamilyExactAnchorTransportType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    (∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      ExactShifts (geometry k hk) V W) →
    ∀ {T U : LocalHull (geometry k hk)},
    solenoidRealize k hk T = solenoidRealize k hk U →
    OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U

def FamilyCommonTileAnchorTransportType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    (∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty) →
    ∀ {T U : LocalHull (geometry k hk)},
    solenoidRealize k hk T = solenoidRealize k hk U →
    OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U

def FamilyWindowAnchorTransportType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    (∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      ThreeWindows (geometry k hk) 1 V W) →
    ∀ {T U : LocalHull (geometry k hk)},
    solenoidRealize k hk T = solenoidRealize k hk U →
    OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U

def FamilyAllWindowsTransportType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    (∀ A B : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) A = 0 →
      realize (pisotData k hk) (inflateH_bijective k hk) B = 0 →
      ThreeWindows (geometry k hk) 1 A B) →
    ∀ {T U : LocalHull (geometry k hk)},
    solenoidRealize k hk T = solenoidRealize k hk U →
    OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U

def SameFibreOrdinaryType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ {T U : LocalHull (geometry k hk)},
    solenoidRealize k hk T = solenoidRealize k hk U →
    OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U

def ContinuousImageProximalType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (act : ℝ → X → X) (act' : ℝ → Y → Y) (f : X → Y), Continuous f →
    (∀ t x, f (act t x) = act' t (f x)) → ∀ {x y : X},
    OrdinaryProximal act x y → OrdinaryProximal act' (f x) (f y)

def RotationDistalityType : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [T2Space G]
    (ρ : ℝ → G) {x y : G}, OrdinaryProximal (fun t z => ρ t * z) x y → x = y

def AddRotationDistalityType : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [T2Space G]
    (ρ : ℝ → G) {x y : G}, OrdinaryProximal (fun t z => ρ t + z) x y → x = y

def ContinuousEquivariantDescentType : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace X] [T2Space Y]
    (act : ℝ → X → X) (actY : ℝ → Y → Y) (actZ : ℝ → Z → Z)
    (g : X → Y), Continuous g → Surjective g →
    (∀ t x, g (act t x) = actY t (g x)) →
    (∀ x y, g x = g y → OrdinaryProximal act x y) →
    (∀ z w, OrdinaryProximal actZ z w → z = w) →
    ∀ f : X → Z, Continuous f →
    (∀ t x, f (act t x) = actZ t (f x)) →
    ∃! d : Y → Z, Continuous d ∧ (∀ x, d (g x) = f x) ∧
      ∀ t y, d (actY t y) = actZ t (d y)

def RotationDescentType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    {G : Type w} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [T2Space G]
    (act : ℝ → X → X) (actY : ℝ → Y → Y) (g : X → Y),
    Continuous g → Surjective g →
    (∀ t x, g (act t x) = actY t (g x)) →
    (∀ x y, g x = g y → OrdinaryProximal act x y) →
    ∀ (ρ : ℝ → G) (f : X → G), Continuous f →
    (∀ t x, f (act t x) = ρ t * f x) →
    ∃! d : Y → G, Continuous d ∧ (∀ x, d (g x) = f x) ∧
      ∀ t y, d (actY t y) = ρ t * d y

def AddRotationDescentType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    {G : Type w} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [T2Space G]
    (act : ℝ → X → X) (actY : ℝ → Y → Y) (g : X → Y),
    Continuous g → Surjective g →
    (∀ t x, g (act t x) = actY t (g x)) →
    (∀ x y, g x = g y → OrdinaryProximal act x y) →
    ∀ (ρ : ℝ → G) (f : X → G), Continuous f →
    (∀ t x, f (act t x) = ρ t + f x) →
    ∃! d : Y → G, Continuous d ∧ (∀ x, d (g x) = f x) ∧
      ∀ t y, d (actY t y) = ρ t + d y

def FibreRankOneType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X]
    (act : ℝ → X → X) (g : X → Y) (z : Y), (∃ x, g x = z) →
    (∀ x y, g x = z → g y = z → OrdinaryProximal act x y) →
    NonproximalRank act g z = 1

def AllFibreRankOneType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X]
    (act : ℝ → X → X) (g : X → Y), Surjective g →
    (∀ x y, g x = g y → OrdinaryProximal act x y) →
    ∀ z : Y, NonproximalRank act g z = 1

def FamilyFlowRotationType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (z : Solenoid (geometry k hk)),
    flow (pisotData k hk) t z = flow (pisotData k hk) t 0 + z

def FamilyProximalImagesType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {T U : LocalHull (geometry k hk)},
    OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U →
    solenoidRealize k hk T = solenoidRealize k hk U

def FamilyFibreIffProximalType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    (∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty) →
    ∀ T U : LocalHull (geometry k hk),
    solenoidRealize k hk T = solenoidRealize k hk U ↔
      OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U

def FamilyConditionalRankType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    (∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty) →
    ∀ z : Solenoid (geometry k hk),
    NonproximalRank (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk))
      (solenoidRealize k hk) z = 1

def FamilyConditionalDescentType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    (∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty) →
    ∀ {G : Type u} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
      [T2Space G] (ρ : ℝ → G) (f : LocalHull (geometry k hk) → G), Continuous f →
    (∀ t T, f (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk) t T) =
      ρ t + f T) →
    ∃! d : Solenoid (geometry k hk) → G,
      Continuous d ∧ (∀ T, d (solenoidRealize k hk T) = f T) ∧
        ∀ t z, d (flow (pisotData k hk) t z) = ρ t + d z

def FamilyUnconditionalFibreIffType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ T U : LocalHull (geometry k hk),
    solenoidRealize k hk T = solenoidRealize k hk U ↔
      OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) T U

def FamilyProximalClosedType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    IsClosed {p : LocalHull (geometry k hk) × LocalHull (geometry k hk) |
      OrdinaryProximal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk)) p.1 p.2}

def FamilyUnconditionalRankType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ z : Solenoid (geometry k hk),
    NonproximalRank (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk))
      (solenoidRealize k hk) z = 1

def FamilyUnconditionalDescentType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ {G : Type u} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
      [T2Space G] (ρ : ℝ → G) (f : LocalHull (geometry k hk) → G), Continuous f →
    (∀ t T, f (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk) t T) =
      ρ t + f T) →
    ∃! d : Solenoid (geometry k hk) → G,
      Continuous d ∧ (∀ T, d (solenoidRealize k hk T) = f T) ∧
        ∀ t z, d (flow (pisotData k hk) t z) = ρ t + d z

def EquicontinuousDistalityType : Prop :=
  ∀ {Z : Type u} [UniformSpace Z] [T2Space Z] (act : ℝ → Z → Z),
    (∀ z, act 0 z = z) → (∀ s t z, act s (act t z) = act (s + t) z) →
    Equicontinuous act → ∀ {x y : Z}, OrdinaryProximal act x y → x = y

def EquicontinuousDescentType : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y]
    [UniformSpace Z] [T2Space Z]
    (act : ℝ → X → X) (actY : ℝ → Y → Y) (actZ : ℝ → Z → Z)
    (g : X → Y), Continuous g → Surjective g →
    (∀ t x, g (act t x) = actY t (g x)) →
    (∀ x y, g x = g y → OrdinaryProximal act x y) →
    (∀ z, actZ 0 z = z) →
    (∀ s t z, actZ s (actZ t z) = actZ (s + t) z) →
    Equicontinuous actZ → ∀ f : X → Z, Continuous f →
    (∀ t x, f (act t x) = actZ t (f x)) →
    ∃! d : Y → Z, Continuous d ∧ (∀ x, d (g x) = f x) ∧
      ∀ t y, d (actY t y) = actZ t (d y)

def UniformRotationsType : Prop :=
  ∀ {ι : Type u} {G : Type v} [UniformSpace G] [Group G] [IsRightUniformGroup G]
    (ρ : ι → G), UniformEquicontinuous (fun i z => z * ρ i)

def UniformAddRotationsType : Prop :=
  ∀ {ι : Type u} {G : Type v} [UniformSpace G] [AddGroup G] [IsRightUniformAddGroup G]
    (ρ : ι → G), UniformEquicontinuous (fun i z => z + ρ i)

def FamilyUniformEquicontinuityType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), UniformEquicontinuous (flow (pisotData k hk))

def FamilyEquicontinuityType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), Equicontinuous (flow (pisotData k hk))

def FamilyFlowZeroType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (z : Solenoid (geometry k hk)),
    flow (pisotData k hk) 0 z = z

def FamilyFlowAddType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (s t : ℝ) (z : Solenoid (geometry k hk)),
    flow (pisotData k hk) s (flow (pisotData k hk) t z) =
      flow (pisotData k hk) (s + t) z

def FamilyConditionalEquicontinuousDescentType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {V : (geometry k hk).Hull},
    realize (pisotData k hk) (inflateH_bijective k hk) V = 0 →
    (∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty) →
    ∀ {Z : Type u} [UniformSpace Z] [T2Space Z] (act : ℝ → Z → Z),
    (∀ z, act 0 z = z) → (∀ s t z, act s (act t z) = act (s + t) z) →
    Equicontinuous act → ∀ f : LocalHull (geometry k hk) → Z, Continuous f →
    (∀ t T, f (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk) t T) =
      act t (f T)) →
    ∃! d : Solenoid (geometry k hk) → Z,
      Continuous d ∧ (∀ T, d (solenoidRealize k hk T) = f T) ∧
        ∀ t z, d (flow (pisotData k hk) t z) = act t (d z)

def FamilyUnconditionalEquicontinuousDescentType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ {Z : Type u} [UniformSpace Z] [T2Space Z] (act : ℝ → Z → Z),
    (∀ z, act 0 z = z) → (∀ s t z, act s (act t z) = act (s + t) z) →
    Equicontinuous act → ∀ f : LocalHull (geometry k hk) → Z, Continuous f →
    (∀ t T, f (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk) t T) =
      act t (f T)) →
    ∃! d : Solenoid (geometry k hk) → Z,
      Continuous d ∧ (∀ T, d (solenoidRealize k hk T) = f T) ∧
        ∀ t z, d (flow (pisotData k hk) t z) = act t (d z)

def FibreDistalSubsingletonType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X]
    (act : ℝ → X → X) (g : X → Y),
    (∀ x y, g x = g y ↔ OrdinaryProximal act x y) → ∀ z : Y,
    FibreDistal act g z ↔ ({x : X | g x = z} : Set X).Subsingleton

def FibreDistalUniqueType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X]
    (act : ℝ → X → X) (g : X → Y),
    (∀ x y, g x = g y ↔ OrdinaryProximal act x y) →
    ∀ z : Y, (∃ x, g x = z) → (FibreDistal act g z ↔ ∃! x : X, g x = z)

def FibreNonDistalityType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X]
    (act : ℝ → X → X) (g : X → Y) {z : Y} {x y : X},
    g x = z → OrdinaryProximal act x y → x ≠ y → ¬ FibreDistal act g z

def AlmostEverywhereFibreDistalType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X]
    (act : ℝ → X → X) (g : X → Y) [MeasurableSpace Y], Surjective g →
    (∀ x y, g x = g y ↔ OrdinaryProximal act x y) → ∀ ν : Measure Y,
    (∀ᵐ z ∂ν, FibreDistal act g z) ↔ (∀ᵐ z ∂ν, ∃! x : X, g x = z)

def FamilyFibreDistalUniqueType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k → ∀ z : Solenoid (geometry k hk),
    FibreDistal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk))
      (solenoidRealize k hk) z ↔
      ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z

def FamilyAlmostEverywhereFibreDistalIffType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ [MeasurableSpace (Solenoid (geometry k hk))] (ν : Measure (Solenoid (geometry k hk))),
    (∀ᵐ z ∂ν, FibreDistal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk))
      (solenoidRealize k hk) z) ↔
      (∀ᵐ z ∂ν, ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z)

def FamilyAlmostEverywhereUniqueType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ∀ [MeasurableSpace (Solenoid (geometry k hk))] (ν : Measure (Solenoid (geometry k hk))),
    (∀ᵐ z ∂ν, FibreDistal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk))
      (solenoidRealize k hk) z) →
      (∀ᵐ z ∂ν, ∃! T : LocalHull (geometry k hk), solenoidRealize k hk T = z)

def FamilyZeroNotDistalType : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), 2 ≤ k →
    ¬ FibreDistal (Psc.PeriodicPartnerLocalTopology.translate (geometry k hk))
      (solenoidRealize k hk) 0

theorem wrongTypeControl : True := True.intro
theorem wrongOneUniverseControl {α : Type u} (_ : α) : True := True.intro
theorem wrongTwoUniverseControl {α : Type u} {β : Type v} (_ : α) (_ : β) : True := True.intro
theorem wrongThreeUniverseControl {α : Type u} {β : Type v} {γ : Type w}
    (_ : α) (_ : β) (_ : γ) : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``Psc.PeriodicPartnerOrdinaryProximal.pair_orbit_closure_invariant, ``PairOrbitInvarianceType,
        `PscVerif.PeriodicPartnerOrdinaryProximal),
      (``Psc.PeriodicPartnerOrdinaryProximal.topologicallyProximal_of_anchor, ``CompactAnchorTransportType,
        `PscVerif.PeriodicPartnerOrdinaryProximal),
      (``Psc.PeriodicPartnerOrdinaryProximal.mem_patch_of_agree, ``PatchTransferType,
        `PscVerif.PeriodicPartnerOrdinaryProximal),
      (``Psc.PeriodicPartnerOrdinaryProximal.topologicallyProximal_of_exactProximal, ``ExactToOrdinaryType,
        `PscVerif.PeriodicPartnerOrdinaryProximal),
      (``Psc.ParameterFamilyOrdinaryProximal.same_fibre_proximal_of_zero_anchor, ``FamilyExactAnchorTransportType,
        `PscVerif.C4ParameterFamilyOrdinaryProximal),
      (``Psc.ParameterFamilyOrdinaryProximal.same_fibre_proximal_of_zero_anchor_common_tile, ``FamilyCommonTileAnchorTransportType,
        `PscVerif.C4ParameterFamilyOrdinaryProximal),
      (``Psc.ParameterFamilyOrdinaryProximal.same_fibre_proximal_of_zero_anchor_witnesses, ``FamilyWindowAnchorTransportType,
        `PscVerif.C4ParameterFamilyOrdinaryProximal),
      (``Psc.ParameterFamilyOrdinaryProximal.same_fibre_proximal_of_zero_fibre_witnesses, ``FamilyAllWindowsTransportType,
        `PscVerif.C4ParameterFamilyOrdinaryProximal),
      (``Psc.C4FamilyFiniteProximal.same_fibre_topologicallyProximal, ``SameFibreOrdinaryType,
        `PscVerif.C4FamilyFiniteProximal),
      (``Psc.C4FamilyFiniteProximal.same_fibre_iff_topologicallyProximal,
        ``FamilyUnconditionalFibreIffType, `PscVerif.C4FamilyFiniteProximal),
      (``Psc.C4FamilyFiniteProximal.isClosed_topologicallyProximal,
        ``FamilyProximalClosedType, `PscVerif.C4FamilyFiniteProximal),
      (``Psc.C4FamilyFiniteProximal.concreteFibreRank_eq_one,
        ``FamilyUnconditionalRankType, `PscVerif.C4FamilyFiniteProximal),
      (``Psc.C4FamilyFiniteProximal.rotation_factor_descent,
        ``FamilyUnconditionalDescentType, `PscVerif.C4FamilyFiniteProximal),
      (``Psc.C4FamilyFiniteProximal.equicontinuous_factor_descent,
        ``FamilyUnconditionalEquicontinuousDescentType, `PscVerif.C4FamilyFiniteProximal),
      (``Psc.PeriodicPartnerRotationFactor.topologicallyProximal_map, ``ContinuousImageProximalType,
        `PscVerif.PeriodicPartnerRotationFactor),
      (``Psc.PeriodicPartnerRotationFactor.eq_of_topologicallyProximal_rotation, ``RotationDistalityType,
        `PscVerif.PeriodicPartnerRotationFactor),
      (``Psc.PeriodicPartnerRotationFactor.eq_of_topologicallyProximal_add_rotation, ``AddRotationDistalityType,
        `PscVerif.PeriodicPartnerRotationFactor),
      (``Psc.PeriodicPartnerRotationFactor.existsUnique_continuous_equivariant_descent, ``ContinuousEquivariantDescentType,
        `PscVerif.PeriodicPartnerRotationFactor),
      (``Psc.PeriodicPartnerRotationFactor.existsUnique_rotation_descent, ``RotationDescentType,
        `PscVerif.PeriodicPartnerRotationFactor),
      (``Psc.PeriodicPartnerRotationFactor.existsUnique_add_rotation_descent, ``AddRotationDescentType,
        `PscVerif.PeriodicPartnerRotationFactor),
      (``Psc.PeriodicPartnerRotationFactor.fibreNonproximalRank_eq_one, ``FibreRankOneType,
        `PscVerif.PeriodicPartnerRotationFactor),
      (``Psc.PeriodicPartnerRotationFactor.fibreNonproximalRank_eq_one_of_surjective, ``AllFibreRankOneType,
        `PscVerif.PeriodicPartnerRotationFactor),
      (``Psc.ParameterFamilyRotationFactor.solenoid_flow_eq_add, ``FamilyFlowRotationType,
        `PscVerif.C4ParameterFamilyRotationFactor),
      (``Psc.ParameterFamilyRotationFactor.solenoidRealize_eq_of_topologicallyProximal, ``FamilyProximalImagesType,
        `PscVerif.C4ParameterFamilyRotationFactor),
      (``Psc.ParameterFamilyRotationFactor.same_fibre_iff_proximal_of_zero_anchor_common_tile, ``FamilyFibreIffProximalType,
        `PscVerif.C4ParameterFamilyRotationFactor),
      (``Psc.ParameterFamilyRotationFactor.concreteFibreRank_eq_one_of_zero_anchor_common_tile, ``FamilyConditionalRankType,
        `PscVerif.C4ParameterFamilyRotationFactor),
      (``Psc.ParameterFamilyRotationFactor.rotation_descent_of_zero_anchor_common_tile, ``FamilyConditionalDescentType,
        `PscVerif.C4ParameterFamilyRotationFactor),
      (``Psc.PeriodicPartnerEquicontinuousFactor.eq_of_topologicallyProximal_of_equicontinuous, ``EquicontinuousDistalityType,
        `PscVerif.PeriodicPartnerEquicontinuousFactor),
      (``Psc.PeriodicPartnerEquicontinuousFactor.existsUnique_equicontinuous_descent, ``EquicontinuousDescentType,
        `PscVerif.PeriodicPartnerEquicontinuousFactor),
      (``Psc.PeriodicPartnerEquicontinuousFactor.uniformEquicontinuous_right_rotations, ``UniformRotationsType,
        `PscVerif.PeriodicPartnerEquicontinuousFactor),
      (``Psc.PeriodicPartnerEquicontinuousFactor.uniformEquicontinuous_add_right_rotations, ``UniformAddRotationsType,
        `PscVerif.PeriodicPartnerEquicontinuousFactor),
      (``Psc.ParameterFamilyEquicontinuousFactor.uniformEquicontinuous_solenoid_flow, ``FamilyUniformEquicontinuityType,
        `PscVerif.C4ParameterFamilyEquicontinuousFactor),
      (``Psc.ParameterFamilyEquicontinuousFactor.equicontinuous_solenoid_flow, ``FamilyEquicontinuityType,
        `PscVerif.C4ParameterFamilyEquicontinuousFactor),
      (``Psc.ParameterFamilyEquicontinuousFactor.solenoid_flow_zero, ``FamilyFlowZeroType,
        `PscVerif.C4ParameterFamilyEquicontinuousFactor),
      (``Psc.ParameterFamilyEquicontinuousFactor.solenoid_flow_add, ``FamilyFlowAddType,
        `PscVerif.C4ParameterFamilyEquicontinuousFactor),
      (``Psc.ParameterFamilyEquicontinuousFactor.equicontinuous_factor_descent_of_zero_anchor_common_tile, ``FamilyConditionalEquicontinuousDescentType,
        `PscVerif.C4ParameterFamilyEquicontinuousFactor),
      (``Psc.PeriodicPartnerFibreDistal.fibreDistal_iff_subsingleton, ``FibreDistalSubsingletonType,
        `PscVerif.PeriodicPartnerFibreDistal),
      (``Psc.PeriodicPartnerFibreDistal.fibreDistal_iff_existsUnique, ``FibreDistalUniqueType,
        `PscVerif.PeriodicPartnerFibreDistal),
      (``Psc.PeriodicPartnerFibreDistal.not_fibreDistal_of_distinct_proximal, ``FibreNonDistalityType,
        `PscVerif.PeriodicPartnerFibreDistal),
      (``Psc.PeriodicPartnerFibreDistal.ae_fibreDistal_iff_ae_existsUnique, ``AlmostEverywhereFibreDistalType,
        `PscVerif.PeriodicPartnerFibreDistal),
      (``Psc.ParameterFamilyFibreDistal.fibreDistal_iff_unique_preimage, ``FamilyFibreDistalUniqueType,
        `PscVerif.C4ParameterFamilyFibreDistal),
      (``Psc.ParameterFamilyFibreDistal.ae_fibreDistal_iff_ae_unique_preimage, ``FamilyAlmostEverywhereFibreDistalIffType,
        `PscVerif.C4ParameterFamilyFibreDistal),
      (``Psc.ParameterFamilyFibreDistal.ae_unique_preimage_of_ae_fibreDistal, ``FamilyAlmostEverywhereUniqueType,
        `PscVerif.C4ParameterFamilyFibreDistal),
      (``Psc.ParameterFamilyFibreDistal.zero_not_fibreDistal, ``FamilyZeroNotDistalType,
        `PscVerif.C4ParameterFamilyFibreDistal)]
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
    let modules := #[`PscVerif.PeriodicPartnerOrdinaryProximal,
      `PscVerif.C4ParameterFamilyOrdinaryProximal,
      `PscVerif.PeriodicPartnerRotationFactor,
      `PscVerif.C4ParameterFamilyRotationFactor,
      `PscVerif.PeriodicPartnerEquicontinuousFactor,
      `PscVerif.C4ParameterFamilyEquicontinuousFactor,
      `PscVerif.PeriodicPartnerFibreDistal,
      `PscVerif.C4FamilyFiniteProximal,
      `PscVerif.C4ParameterFamilyFibreDistal]
    for forbidden in #[`PscVerif.PeriodicPartnerCoincidenceChains,
        `PscVerif.C4ParameterFamilyTileChains,
        `PscVerif.C4ParameterFamilyZeroFibreClosure] do
      if (env.getModuleIdx? forbidden).isSome then
        throwError "Unexpected geometric dependency: {forbidden}"
    let mut declarations : Nat := 0
    let mut proofs : Nat := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled finite-proximal module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned : Nat := 0
      let mut ownedProofs : Nat := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local finite-proximal axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard finite-proximal axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 then throwError "Empty finite-proximal module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println s!"PSC_FINITE_PROXIMAL_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    unless modules.size == 9 && declarations == 50 && proofs == 45 do
      throwError "Unexpected finite-proximal inventory: {modules.size} modules, {declarations} declarations, {proofs} theorem constants"
    unless endpoints.size == 44 do
      throwError "Unexpected finite-proximal endpoint count: {endpoints.size}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_FINITE_PROXIMAL_DECLARATIONS\t{modules.size}\t{declarations}\t{proofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed finite-proximal endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Zero-fibre closure endpoint has no imported owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong finite-proximal endpoint owner: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard finite-proximal endpoint axiom in {name}: {ax}"
      let names := String.intercalate "," (axioms.toList.map toString)
      Lean.Core.liftIOCore <| IO.println s!"PSC_FINITE_PROXIMAL_ENDPOINT\t{name}\t{names}"
    if (env.find? `Psc.FiniteProximalAudit.absentEndpoint).isSome then
      throwError "Missing-declaration control name collision"
    for (_, expected, _) in endpoints do
      let expectedInfo ← getConstInfo expected
      let wrong ← match expectedInfo.levelParams.length with
        | 0 => pure ``wrongTypeControl
        | 1 => pure ``wrongOneUniverseControl
        | 2 => pure ``wrongTwoUniverseControl
        | 3 => pure ``wrongThreeUniverseControl
        | _ => throwError "No wrong-type control for this universe count"
      if ← matchesType wrong expected then
        throwError "Zero-fibre closure matcher accepted a wrong-type theorem"
      if ← matchesType `Psc.FiniteProximalAudit.absentEndpoint expected then
        throwError "Zero-fibre closure matcher accepted a missing declaration"
    Lean.Core.liftIOCore <| IO.println s!"PSC_FINITE_PROXIMAL_AUDIT_COMPLETE\t{endpoints.size}\t{2 * endpoints.size}"

end Psc.FiniteProximalAudit
