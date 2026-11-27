import PscVerif.BHDiagonalLiteral

/-!
# Finite residual certificates lift to full literal paths

The finite graph stores only the two rotating coordinates. Its edges are
sound for *every* first integral coordinate in the run window. The proof
reconstructs that coordinate and both actual word occurrences at every edge.

This is a certificate soundness theorem, not an assertion that a certificate
exists for every parameter. The target is the small box; its separate exit
argument is not silently included in this endpoint.
-/

namespace Psc.BHDiagonalCertificate

open Psc.OccurrenceTransport Psc.BHNearDiagonalLiteral

abbrev Pair := ℤ × ℤ

/-- The order is `(z,y)`, so an edge sends it to `(y,t)`. -/
def Small (r : ℕ) (u : Pair) : Prop :=
  u.1.natAbs ≤ (r-2)/3 ∧ u.2.natAbs ≤ (r-2)/3

def Admissible (r : ℕ) (β : ℝ) (u : Pair) (t : ℤ) : Prop :=
  |(t : ℝ) + ((β-r)*u.2+(r/β)*u.1)| ≤ ((r : ℝ)-1)/β

/-- A checkable finite ranking. Membership, a valid chosen edge and strict
rank decrease are explicit premises. No claim of graph completeness is
needed for this existential-path endpoint. -/
structure RankedRegion (r : ℕ) (β : ℝ) where
  carrier : Finset Pair
  rank : Pair → ℕ
  zero_small : ∀ u ∈ carrier, rank u = 0 → Small r u
  decrease : ∀ u ∈ carrier, rank u ≠ 0 →
    ∃ t : ℤ, Admissible r β u t ∧ (u.2, t) ∈ carrier ∧
      rank (u.2, t) < rank u

/-- Every accepted rank certificate produces an actual strict word-occurrence
path to its small-box target, uniformly over the omitted first coordinate. -/
theorem ranked_region_reaches_small {r : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family r β) (cert : RankedRegion r β)
    (x y z : ℤ) (hmem : (z,y) ∈ cert.carrier)
    (hc : Central r r β (runPacket x y z)) :
    ∃ q : Packet,
      Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
        (runPacket x y z) q ∧
      Central r r β q ∧ Small r (q.delta 2, q.delta 1) := by
  have aux : ∀ n : ℕ, ∀ u : Pair, u ∈ cert.carrier → cert.rank u = n →
      ∀ a : ℤ, Central r r β (runPacket a u.2 u.1) →
      ∃ q : Packet,
        Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
          (runPacket a u.2 u.1) q ∧
        Central r r β q ∧ Small r (q.delta 2, q.delta 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hu hn a ha
      by_cases hz : cert.rank u = 0
      · exact ⟨runPacket a u.2 u.1, .refl, ha, cert.zero_small u hu hz⟩
      · obtain ⟨t, ht, hm, hd⟩ := cert.decrease u hu hz
        obtain ⟨hs, hc'⟩ := BHDiagonalLiteral.literal_rounding_step h a u.2 u.1 t ha ht
        obtain ⟨q, hp, hq, hsmall⟩ :=
          ih (cert.rank (u.2,t)) (by simpa only [← hn] using hd)
            (u.2,t) hm rfl (u.2+(r : ℤ)*u.1) hc'
        exact ⟨q, (Relation.ReflTransGen.single hs).trans hp, hq, hsmall⟩
  exact aux (cert.rank (z,y)) (z,y) hmem rfl x hc

/-- A coincident pair of projected coordinates does not erase the first
coordinate of a packet. Certificate consumers must still reconstruct it. -/
theorem projected_zero_is_not_full_zero :
    (runPacket 1 0 0).delta 2 = 0 ∧ (runPacket 1 0 0).delta 1 = 0 ∧
      (runPacket 1 0 0).delta ≠ 0 := by
  refine ⟨rfl, rfl, ?_⟩
  intro heq
  have hfirst := congrFun heq 0
  norm_num [runPacket] at hfirst

end Psc.BHDiagonalCertificate
