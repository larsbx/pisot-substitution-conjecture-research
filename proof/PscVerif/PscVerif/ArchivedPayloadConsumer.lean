import PscVerif.ArchivedPayload

/-!
# Geometric consumers of checked original archived payloads

An accepted payload supplies every finite table, closure, root, discovery
and potential premise of `NamedArchivedGraph`.  The remaining measure is
the existing probability additive Haar measure on the original matrix-adic
factor.  The conclusion concerns original rooted inverse ancestry; no
identification with all strict packets or strict-root positivity is made.

Pre-code gate: `docs/c4-archived-payload-import-literature-2026-11-12.md`.
-/

namespace Psc.ArchivedPayload

open Set MeasureTheory
open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceGraphBinding
open Psc.OccurrencePiece Psc.OccurrenceResidue Psc.OccurrenceAdmissibility
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedProductHaar
open Psc.ArchivedGraphRefinement

theorem Packet.denominator_eq (p : Packet) (h : p.Valid) :
    (p.toCertificate h).denominator = 20 := rfl

/-- The actual nonempty geometric domain is exactly the nonempty part of
the complete original rooted inverse ancestry, at every finite depth. -/
theorem Packet.rooted_nonempty_domain_iff (p : Packet) (h : p.Valid)
    (u : OccurrenceTransport.Packet) :
    (u ∈ orderedLift p.states ∧
      (overlap (ambientStar (substitution p.fixture) piZ) (tiles p.fixture) u).Nonempty) ↔
    (Ancestry (iterateImages (substitution p.fixture) 2) ArchivedRoot u ∧
      (overlap (ambientStar (substitution p.fixture) piZ) (tiles p.fixture) u).Nonempty) :=
  NamedArchivedGraph.rooted_nonempty_domain_iff p.fixture p.states (p.toCertificate h)
    (p.tableBinding h) (p.candidatesClosed h) (p.rootID h) (p.rootBound h)
    (p.tableDiscovery h) u

/-- The kernel-checked integer inequalities act on the very same rows as
the source-bound geometric cover. -/
theorem Packet.states_null (p : Packet) (h : p.Valid)
    (ν : Measure (H (substitution p.fixture)))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :
    ∀ i, (volume.prod ν)
      (overlap (ambientStar (substitution p.fixture) piZ) (tiles p.fixture) (p.states i)) = 0 :=
  NamedArchivedGraph.null_of_source_bound_table p.fixture ν p.states (p.toCertificate h)
    (p.tableBinding h) (p.candidatesClosed h) (p.toCertificate_check h)
    (p.numerator_eq h) (p.denominator_eq h) (p.rootID h)

/-- All three original zero-offset roots have zero product-Haar measure. -/
theorem Packet.roots_null (p : Packet) (h : p.Valid)
    (ν : Measure (H (substitution p.fixture)))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :
    ∀ k, (volume.prod ν)
      (overlap (ambientStar (substitution p.fixture) piZ) (tiles p.fixture) (archivedRoot k)) = 0 :=
  NamedArchivedGraph.original_roots_null_of_table p.fixture ν p.states (p.toCertificate h)
    (p.tableBinding h) (p.candidatesClosed h) (p.toCertificate_check h)
    (p.numerator_eq h) (p.denominator_eq h) (p.rootID h) (p.rootBound h)

/-- Nullity includes every original literal inverse ancestor, even an
empty ancestor legitimately omitted by the finite geometric exclusions. -/
theorem Packet.ancestors_null (p : Packet) (h : p.Valid)
    (ν : Measure (H (substitution p.fixture)))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (u : OccurrenceTransport.Packet)
    (hu : Ancestry (iterateImages (substitution p.fixture) 2) ArchivedRoot u) :
    (volume.prod ν)
      (overlap (ambientStar (substitution p.fixture) piZ) (tiles p.fixture) u) = 0 :=
  NamedArchivedGraph.all_original_ancestors_null_of_table p.fixture ν p.states (p.toCertificate h)
    (p.tableBinding h) (p.candidatesClosed h) (p.toCertificate_check h)
    (p.numerator_eq h) (p.denominator_eq h) (p.rootID h) (p.rootBound h)
    (p.tableDiscovery h) u hu

end Psc.ArchivedPayload
