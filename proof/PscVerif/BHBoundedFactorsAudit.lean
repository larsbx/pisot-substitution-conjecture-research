import PscVerif.BHBoundedFactors

open Psc.Binomial Psc.Reduction Psc.Descendants
open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceAncestry
open Psc.BHBoundedFactors

-- Check the public binders and axioms from a separately elaborated file.
example (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 1 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (m : MarkedPair) (hbal : Equiv1 m.words.1 m.words.2) (hover : m.Overlaps ℓ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n U, U ∈ red ((subst s)^[n] m.words.1)
      ((subst s)^[n] m.words.2) → physicalLength ℓ U.1 ≤ B) :
    ∃ m', Relation.ReflTransGen (WholeStep s ℓ) m m' ∧ m'.packet.delta = 0 :=
  whole_zero_hit_of_bound s ℓ β hpos hβ hscale m hbal hover B hB hbound

example (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 1 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (T : WordPair) (hT : IsBlock T) :
    {U | Relation.ReflTransGen (ChildNC s) T U}.Finite ↔
      ∃ C : Finset Packet, CoversWords ℓ T (↑C : Set Packet) ∧
        (∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) ∧
        (∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) :=
  finite_reachable_iff_closed_packet_cover s ℓ β hpos hβ hscale T hT

example (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (T : WordPair) (hT : IsBlock T)
    (C : Finset Packet) (hseed : CoversWords ℓ T (↑C : Set Packet))
    (hclosed : ∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C)
    (hhit : ∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.Diagonal) :
    Psc.StrictSystem.TerminatesWithCoincidence s T :=
  terminates_of_closed_diagonal_cover s ℓ β hpos hβ hscale T hT C hseed hclosed hhit

#print axioms inflate_interval_bounds
#print axioms WholeStep.packet
#print axioms whole_zero_hit_of_bound
#print axioms seedPackets_closed
#print axioms seedPackets_finite_of_finite_factors
#print axioms seedPackets_zero_hits_of_bound
#print axioms finite_reachable_iff_closed_packet_cover
#print axioms terminates_of_closed_diagonal_cover
#print axioms expanding_zero_cover_without_coincidence

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let mod := `PscVerif.BHBoundedFactors
    let some index := env.getModuleIdx? mod | throwError "Missing compiled module {mod}"
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let mut declarations := 0
    let mut theorems := 0
    for info in env.header.moduleData[index.toNat]!.constants do
      unless env.getModuleIdxFor? info.name == some index do continue
      if info.isAxiom then throwError "Local axiom {info.name}"
      for ax in ← collectAxioms info.name do
        unless allowed.contains ax do
          throwError "Unexpected axiom in {info.name}: {ax}"
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
    if theorems == 0 then throwError "Empty compiled theorem inventory"
    Lean.Core.liftIOCore <| IO.println s!"PSC_BH_BOUNDED_FACTORS_AUDIT\t{declarations}\t{theorems}"
