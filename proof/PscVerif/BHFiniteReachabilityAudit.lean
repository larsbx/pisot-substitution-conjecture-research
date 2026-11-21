/- Exact-type acceptance for the literal half-coincidence finiteness bridge.
Replay after compiling PscVerif.BHFiniteReachability. The expected types below
spell out actual occurrence coverage and prefix cuts independently, so adding
a finite-word or factor-bound premise cannot satisfy this fixture. -/
import PscVerif.BHFiniteCarrier
import Lean.Util.CollectAxioms

namespace Psc.BHFiniteReachabilityAudit

open Psc.Binomial Psc.Reduction Psc.Descendants
open Psc.OccurrenceNewborn Psc.OccurrenceTransport

/-- Independent literal spelling of a prefix cut and its original tile bounds. -/
def LiteralTileCut (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (m : MarkedPair) (n : ℕ) : Prop :=
  ∃ u v ru rv : Word,
    (subst s)^[n] m.words.1 = u ++ ru ∧
    (subst s)^[n] m.words.2 = v ++ rv ∧ Equiv1 u v ∧
    β ^ n * physicalLength ℓ m.top.before ≤ physicalLength ℓ u ∧
    physicalLength ℓ u ≤ β ^ n * (physicalLength ℓ m.top.before + ℓ m.top.letter)

/-- Independent seed-word coverage for the finite closed-carrier interface. -/
def LiteralWordCoverage (ℓ : Fin 3 → ℝ) (T : WordPair) (C : Set Packet) : Prop :=
  ∀ (top : Mark T.1) (bottom : Mark T.2),
    (MarkedPair.mk T top bottom).Overlaps ℓ → (MarkedPair.mk T top bottom).packet ∈ C

/-- Independent all-generation literal mark coverage, not a factor carrier. -/
def LiteralCoverage (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (T : WordPair) (C : Finset Packet) : Prop :=
  ∀ n (top : Mark ((subst s)^[n] T.1)) (bottom : Mark ((subst s)^[n] T.2)),
    (MarkedPair.mk (((subst s)^[n] T.1), ((subst s)^[n] T.2)) top bottom).Overlaps ℓ →
    (MarkedPair.mk (((subst s)^[n] T.1), ((subst s)^[n] T.2)) top bottom).packet ∈ C

def PathCutType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ {p q : Packet}, Relation.ReflTransGen (InteriorStep s ℓ) p q → q.delta = 0 →
      ∃ n, ∀ m : MarkedPair, m.packet = p → LiteralTileCut s ℓ β m n

def PaddingType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    0 < β → (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ {m : MarkedPair} {n D : ℕ}, LiteralTileCut s ℓ β m n → n ≤ D →
      LiteralTileCut s ℓ β m D

def UniformDepthType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ C : Finset Packet,
      (∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) →
      ∃ D, ∀ m : MarkedPair, m.packet ∈ C → LiteralTileCut s ℓ β m D

def FactorBoundType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ M : ℝ, (∀ a, ℓ a ≤ M) → ∀ D : ℕ, ∀ {u v : Word}, Equiv1 u v →
      (∀ (top : Mark u) (bottom : Mark v),
        (MarkedPair.mk (u, v) top bottom).Overlaps ℓ →
        LiteralTileCut s ℓ β (MarkedPair.mk (u, v) top bottom) D) →
      ∀ {U : WordPair}, U ∈ red ((subst s)^[D] u) ((subst s)^[D] v) →
        physicalLength ℓ U.1 ≤ 2 * β ^ D * M

def BoundedPairsType : Prop :=
  ∀ ℓ : Fin 3 → ℝ, (∀ a, 0 < ℓ a) → ∀ B : ℝ,
    {U : WordPair | Equiv1 U.1 U.2 ∧ physicalLength ℓ U.1 ≤ B}.Finite

def LateBoundType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ T : WordPair, Equiv1 T.1 T.2 → ∀ C : Finset Packet,
      LiteralCoverage s ℓ T C →
      (∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) →
      ∃ D : ℕ, ∃ B : ℝ, ∀ n U,
        U ∈ red ((subst s)^[D + n] T.1) ((subst s)^[D + n] T.2) →
        physicalLength ℓ U.1 ≤ B

def FullFactorsType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ T : WordPair, Equiv1 T.1 T.2 → ∀ C : Finset Packet,
      LiteralCoverage s ℓ T C →
      (∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) →
      {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite

def ReachabilityType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ T : WordPair, IsBlock T → ∀ C : Finset Packet,
      LiteralCoverage s ℓ T C →
      (∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) →
      {U | Relation.ReflTransGen (ChildNC s) T U}.Finite

def AncestryCoverageType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ (T : WordPair) (C : Set Packet), LiteralWordCoverage ℓ T C →
      (∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) →
      ∀ n, LiteralWordCoverage ℓ (((subst s)^[n] T.1), ((subst s)^[n] T.2)) C

def ClosedCarrierReachabilityType : Prop :=
  ∀ (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (s a) = β * ℓ a) →
    ∀ T : WordPair, IsBlock T → ∀ C : Finset Packet,
      LiteralWordCoverage ℓ T (↑C : Set Packet) →
      (∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) →
      (∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) →
      {U | Relation.ReflTransGen (ChildNC s) T U}.Finite

/-- Independent literal occurrence for the rational-independence boundary. -/
def physicalZeroMark : MarkedPair :=
  ⟨([0, 2, 1], [1, 2, 0]), ⟨[0], 2, [1], rfl⟩, ⟨[1], 2, [0], rfl⟩⟩

def PhysicalZeroControlType : Prop :=
  IsBlock physicalZeroMark.words ∧
    physicalZeroMark.Overlaps (fun _ => 1) ∧
    offset (fun _ => 1) physicalZeroMark.packet.delta = 0 ∧
    physicalZeroMark.packet.delta ≠ 0 ∧
    ¬ LiteralTileCut (fun a => [a]) (fun _ => 1) 1 physicalZeroMark 0

example : PathCutType := Psc.BHFiniteReachability.packet_path_tileCut
example : PaddingType := Psc.BHFiniteReachability.TileCut.pad
example : UniformDepthType := Psc.BHFiniteReachability.uniform_tileCut_depth
example : FactorBoundType := Psc.BHFiniteReachability.factor_bound_of_tileCuts
example : BoundedPairsType := Psc.BHFiniteReachability.finite_balanced_pairs_of_physical_bound
example : LateBoundType := Psc.BHFiniteReachability.bounded_late_factors_of_finite_packet_hits
example : FullFactorsType := Psc.BHFiniteReachability.finite_factors_of_finite_packet_hits
example : ReachabilityType := Psc.BHFiniteReachability.finite_reachable_of_finite_packet_hits
example : PhysicalZeroControlType := Psc.BHFiniteReachability.physical_zero_does_not_supply_tileCut

example : AncestryCoverageType := Psc.OccurrenceAncestry.covers_iterates_of_closed
example : ClosedCarrierReachabilityType :=
  Psc.BHFiniteCarrier.finite_reachable_of_closed_packet_cover

/-- Harmless theorem with the right declaration kind and wrong semantic type. -/
theorem wrongTypeControl : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``Psc.BHFiniteReachability.packet_path_tileCut, ``PathCutType, `PscVerif.BHFiniteReachability),
      (``Psc.BHFiniteReachability.TileCut.pad, ``PaddingType, `PscVerif.BHFiniteReachability),
      (``Psc.BHFiniteReachability.uniform_tileCut_depth, ``UniformDepthType, `PscVerif.BHFiniteReachability),
      (``Psc.BHFiniteReachability.factor_bound_of_tileCuts, ``FactorBoundType, `PscVerif.BHFiniteReachability),
      (``Psc.BHFiniteReachability.finite_balanced_pairs_of_physical_bound, ``BoundedPairsType, `PscVerif.BHFiniteReachability),
      (``Psc.BHFiniteReachability.bounded_late_factors_of_finite_packet_hits, ``LateBoundType, `PscVerif.BHFiniteReachability),
      (``Psc.BHFiniteReachability.finite_factors_of_finite_packet_hits, ``FullFactorsType, `PscVerif.BHFiniteReachability),
      (``Psc.BHFiniteReachability.finite_reachable_of_finite_packet_hits, ``ReachabilityType, `PscVerif.BHFiniteReachability),
      (``Psc.BHFiniteReachability.physical_zero_does_not_supply_tileCut, ``PhysicalZeroControlType,
        `PscVerif.BHFiniteReachability),
      (``Psc.OccurrenceAncestry.covers_iterates_of_closed, ``AncestryCoverageType,
        `PscVerif.OccurrenceAncestry),
      (``Psc.BHFiniteCarrier.finite_reachable_of_closed_packet_cover,
        ``ClosedCarrierReachabilityType, `PscVerif.BHFiniteCarrier)]
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
    let modules := #[`PscVerif.OccurrenceAncestry, `PscVerif.BHFiniteReachability,
      `PscVerif.BHFiniteCarrier]
    let mut declarations := 0
    let mut proofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled BH finiteness module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local BH finiteness axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard BH finiteness axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 then throwError "Empty compiled BH finiteness module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_BH_FINITE_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_BH_FINITE_DECLARATIONS\t3\t{declarations}\t{proofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed BH finiteness endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "BH finiteness endpoint has no imported owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong BH finiteness endpoint owner: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard BH endpoint axiom in {name}: {ax}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_BH_FINITE_ENDPOINT\t{name}"
    if (env.find? `Psc.BHFiniteReachabilityAudit.absentEndpoint).isSome then
      throwError "Missing-declaration control name collision"
    for (_, expected, _) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "BH finiteness audit accepted a wrong-type theorem"
      if ← matchesType `Psc.BHFiniteReachabilityAudit.absentEndpoint expected then
        throwError "BH finiteness audit accepted a missing declaration"
    Lean.Core.liftIOCore <| IO.println "PSC_BH_FINITE_AUDIT_COMPLETE\t11\t22"

end Psc.BHFiniteReachabilityAudit
