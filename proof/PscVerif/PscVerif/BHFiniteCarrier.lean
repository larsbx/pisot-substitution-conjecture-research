/-
# Finite closed overlap carriers bound actual balanced-pair reachability

The public hypotheses refer only to the finite packet carrier, actual seed
occurrences, complete literal edge closure, and integral zero hits. The
all-generation occurrence coverage and finite balanced-word carrier are
derived rather than supplied.

Stop/go: docs/bh-finite-reachability-stop-go-2026-11-14.md.
-/
import PscVerif.OccurrenceAncestry
import PscVerif.BHFiniteReachability

namespace Psc.BHFiniteCarrier

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants
open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceAncestry
open Psc.BHFiniteReachability

/-- Complete literal closure propagates the actual seed cover to every
generation required by the bounded-gap theorem. -/
theorem covers_seed_iterates_of_closed
    (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (T : WordPair) (C : Finset Packet)
    (hseed : CoversWords ℓ T (↑C : Set Packet))
    (hclosed : ∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) :
    CoversSeedIterates s ℓ T (↑C : Set Packet) :=
  covers_iterates_of_closed s ℓ β hpos hβ hscale T (↑C : Set Packet) hseed hclosed

/-- The finite packet cover and its zero-hit property imply finiteness of
the complete irreducible-factor set of the actual seed iterates. -/
theorem finite_factors_of_closed_packet_cover
    (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (T : WordPair) (hT : Equiv1 T.1 T.2) (C : Finset Packet)
    (hseed : CoversWords ℓ T (↑C : Set Packet))
    (hclosed : ∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C)
    (hhit : ∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) :
    {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}.Finite :=
  finite_factors_of_finite_packet_hits s ℓ β hpos hβ hscale T hT C
    (covers_seed_iterates_of_closed s ℓ β hpos hβ hscale T C hseed hclosed) hhit

/-- Finiteness of actual terminal-child reachability, with seed coverage and
complete overlap-edge closure in place of an infinite coverage premise. -/
theorem finite_reachable_of_closed_packet_cover
    (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (T : WordPair) (hT : IsBlock T) (C : Finset Packet)
    (hseed : CoversWords ℓ T (↑C : Set Packet))
    (hclosed : ∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C)
    (hhit : ∀ p ∈ C, ∃ q, Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.delta = 0) :
    {U | Relation.ReflTransGen (ChildNC s) T U}.Finite :=
  finite_reachable_of_finite_packet_hits s ℓ β hpos hβ hscale T hT C
    (covers_seed_iterates_of_closed s ℓ β hpos hβ hscale T C hseed hclosed) hhit

end Psc.BHFiniteCarrier
