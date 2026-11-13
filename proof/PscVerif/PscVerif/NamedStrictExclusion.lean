import PscVerif.NamedPositiveOverlap
import PscVerif.ArchivedPayloadConsumer
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Strict-system exclusion from the original named root certificates

The actual cut-pair overlap is covered by the three original zero-offset
roots: strictness excludes equal letters, and reversing unequal letters
does not change a zero-offset intersection.  The positive-measure theorem
and the checked root-nullity theorem therefore concern the same set and
the same product measure.  No coverage of all `strictPackets` is used.

The probability additive Haar measure is constructed on the already
proved compact original matrix-adic carrier.  The final packet consumer
has no caller-supplied measure premise.  Its substitution remains the
literal fixture authenticated by `Packet.Valid`; there are only two
named fixtures, and no universal C4 or PSC conclusion is asserted.

Pre-code gate: `docs/c4-named-strict-exclusion-literature-2026-11-12.md`.
-/

open Set MeasureTheory

namespace Psc.NamedStrictExclusion

open Psc.OccurrenceTransport Psc.OccurrencePiece Psc.OccurrenceResidue
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedCutNeighborhood
open Psc.NamedFundamentalCell Psc.ArchivedGraphRefinement

/-- All six ordered distinct-letter intersections are represented by the
three original zero-offset roots.  The reversed cases use commutativity
of intersection, not a claim about arbitrary displaced overlaps. -/
theorem intersection_eq_archivedRoot {G : Type*} [AddCommGroup G]
    (star : (Fin 3 → ℤ) →+ G) (K : Fin 3 → Set G)
    (a b : Fin 3) (hab : a ≠ b) :
    ∃ k : Fin 3, K a ∩ K b = overlap star K (archivedRoot k) := by
  fin_cases a <;> fin_cases b
  · exact (hab rfl).elim
  · exact ⟨0, by ext x; simp [overlap, archivedRoot]⟩
  · exact ⟨1, by ext x; simp [overlap, archivedRoot]⟩
  · exact ⟨0, by ext x; simp [overlap, archivedRoot, and_comm]⟩
  · exact (hab rfl).elim
  · exact ⟨2, by ext x; simp [overlap, archivedRoot]⟩
  · exact ⟨1, by ext x; simp [overlap, archivedRoot, and_comm]⟩
  · exact ⟨2, by ext x; simp [overlap, archivedRoot, and_comm]⟩
  · exact (hab rfl).elim

/-- The overlap carrying the strict-cut lower bound is covered by the
three roots whose nullity is supplied by the original checked archive. -/
theorem carrierOverlap_subset_archivedRoots (f : Fin 2)
    {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution f) C) :
    carrierOverlap f C ⊆ ⋃ k : Fin 3,
      overlap (ambientStar (substitution f) piZ) (tiles f) (archivedRoot k) := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨a, hx⟩
  rcases mem_iUnion.mp hx with ⟨b, hx⟩
  rcases mem_iUnion.mp hx with ⟨hpair, hx⟩
  obtain ⟨k, hk⟩ := intersection_eq_archivedRoot
    (ambientStar (substitution f) piZ) (tiles f) a b (strict.cutPair_ne hpair)
  exact mem_iUnion.mpr ⟨k, hk ▸ hx⟩

/-- The existing positive-overlap and null-root conclusions contradict
each other with exactly one shared normalized product-Haar measure. -/
theorem no_strictSystem_of_roots_null (f : Fin 2)
    (ν : Measure (Psc.NamedFundamentalCell.H f))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (null : ∀ k : Fin 3, (volume.prod ν)
      (overlap (ambientStar (substitution f) piZ) (tiles f) (archivedRoot k)) = 0)
    (C : Finset WordPair) :
    ¬ Psc.StrictSystem.StrictSystem (substitution f) C := by
  intro strict
  exact PscVerif.OverlapContraction.no_positive_subset_of_null
    (internalMeasure f ν)
    (fun k => overlap (ambientStar (substitution f) piZ) (tiles f) (archivedRoot k))
    (carrierOverlap f C) null
    (carrierOverlap_subset_archivedRoots f strict)
    (Psc.NamedPositiveOverlap.carrierOverlap_measure_pos f ν strict)

/-- Compactness of the original carrier supplies a probability additive
Haar measure, normalized on its whole positive compact set. -/
theorem exists_probabilityHaar (f : Fin 2) :
    ∃ ν : Measure (Psc.NamedFundamentalCell.H f),
      ν.IsAddHaarMeasure ∧ IsProbabilityMeasure ν := by
  letI : CompactSpace (Psc.NamedFundamentalCell.H f) :=
    Psc.MadicResidue.carrier_compactSpace (Psc.NamedFundamentalCell.M f)
      (Psc.NamedProductHaar.integral_injective (substitution f) (incidence_eq f))
  let K : TopologicalSpace.PositiveCompacts (Psc.NamedFundamentalCell.H f) := ⊤
  let ν : Measure (Psc.NamedFundamentalCell.H f) := Measure.addHaarMeasure K
  have hν : ν Set.univ = 1 := by
    change Measure.addHaarMeasure K (K : Set _) = 1
    exact Measure.addHaarMeasure_self
  exact ⟨ν, inferInstance, ⟨hν⟩⟩

end Psc.NamedStrictExclusion

namespace Psc.ArchivedPayload

open Psc.OccurrenceTransport Psc.NamedStableChart Psc.NamedPrefixCompact

/-- A valid original payload excludes every finite strict system for its
own literal fixture, for any supplied normalized additive Haar measure. -/
theorem Packet.no_strictSystem_of_measure (p : Packet) (h : p.Valid)
    (ν : Measure (Psc.NamedFundamentalCell.H p.fixture))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (C : Finset WordPair) :
    ¬ Psc.StrictSystem.StrictSystem (substitution p.fixture) C :=
  Psc.NamedStrictExclusion.no_strictSystem_of_roots_null p.fixture ν
    (p.roots_null h ν) C

/-- The original checked certificate excludes every finite strict system
for its authenticated fixture.  Haar existence is discharged internally. -/
theorem Packet.no_strictSystem (p : Packet) (h : p.Valid)
    (C : Finset WordPair) :
    ¬ Psc.StrictSystem.StrictSystem (substitution p.fixture) C := by
  obtain ⟨ν, hHaar, hProbability⟩ :=
    Psc.NamedStrictExclusion.exists_probabilityHaar p.fixture
  letI : ν.IsAddHaarMeasure := hHaar
  letI : IsProbabilityMeasure ν := hProbability
  exact p.no_strictSystem_of_measure h ν C

/-- Strong connectivity adds no premise to the exclusion: every strict
component is already a strict system. -/
theorem Packet.no_strictComponent (p : Packet) (h : p.Valid)
    (C : Finset WordPair) :
    ¬ Psc.StrictSystem.StrictComponent (substitution p.fixture) C := by
  intro strict
  exact p.no_strictSystem h C strict.toStrictSystem

/-- The manuscript's BPA strict-component representation also projects
to the same actual strict system.  This does not prove global extraction. -/
theorem Packet.no_bpaStrictComponent (p : Packet) (h : p.Valid)
    (C : Finset WordPair) :
    ¬ Psc.StrictSystem.BpaStrictComponent (substitution p.fixture) C := by
  intro strict
  exact p.no_strictSystem h C strict.toStrictComponent.toStrictSystem

end Psc.ArchivedPayload
