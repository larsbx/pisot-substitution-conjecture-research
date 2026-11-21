/-
# Twins and injective endpoint maps

The finite core of the endpoint step in `docs/c4-nonunit-twin-endpoint-2026-11-21.md`.
Let `ι` be an injective map commuting with inflation that carries right-asymptotic pairs
to right-asymptotic pairs, and never sends a tiling with a vertex at the origin to one with
a vertex there (twins share no vertex).  If the ternary endpoint map is injective, a
periodic vertex tiling has no distinct periodic right-asymptotic companion: their twins
would branch at the origin, giving the twin a vertex there.

The left side is the mirror (`PeriodicPartnerReflection`).  The tiling-space inputs (the
twin involution, its continuity, the vertex-disjointness of twins) are hypotheses here and
written mathematics in the note.
-/
import PscVerif.PeriodicPartnerSelection
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Psc.PeriodicPartnerTwinEndpoint

open Function Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerSelection

variable {X : Type*} {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → Fin 3 → Prop}

/-- A periodic pair of distinct right-asymptotic tilings with an injective endpoint map
branches at the origin, so both have a vertex there. -/
theorem vertex_of_injective (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    (hβ : 1 < β) (hBranch : BranchExistence AgreeRight EndsAt) (hg : Injective g)
    {S U : X} (hSU : S ≠ U) (hp : PairPeriodic f S U)
    (hasym : RightAsymptotic AgreeRight S U) :
    VertexAtOrigin EndsAt S ∧ VertexAtOrigin EndsAt U := by
  obtain ⟨y, b, c, hb⟩ := hBranch hSU hasym
  have hy : y = 0 := branch_eq_zero_of_persistent laws hβ hp hb
    (Psc.PeriodicPartner.endpoint_persistent_of_injective g hg hb.2.2.2)
  subst hy
  exact ⟨⟨b, hb.2.1⟩, ⟨c, hb.2.2.1⟩⟩

/-- **Endpoint step.**  Under vertex-disjoint twins and an injective endpoint map, a
periodic tiling with a vertex at the origin has no distinct periodic right-asymptotic
companion. -/
theorem no_asymptotic_companion (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    (hβ : 1 < β) (hBranch : BranchExistence AgreeRight EndsAt) (hg : Injective g)
    (ι : X → X) (hιinj : Injective ι) (hιf : Function.Commute ι f)
    (hιasym : ∀ {S U}, RightAsymptotic AgreeRight S U →
      RightAsymptotic AgreeRight (ι S) (ι U))
    (hdisjoint : ∀ T, VertexAtOrigin EndsAt T → ¬ VertexAtOrigin EndsAt (ι T))
    {S U : X} (hSU : S ≠ U) (hp : PairPeriodic f S U)
    (hasym : RightAsymptotic AgreeRight S U) (hS : VertexAtOrigin EndsAt S) : False := by
  obtain ⟨n, hn, hSn, hUn⟩ := hp
  have hcomm : ∀ x, f^[n] (ι x) = ι (f^[n] x) := fun x => ((hιf.iterate_right n).eq x).symm
  have hp' : PairPeriodic f (ι S) (ι U) := ⟨n, hn, by rw [hcomm, hSn], by rw [hcomm, hUn]⟩
  exact hdisjoint S hS
    (vertex_of_injective laws hβ hBranch hg (hιinj.ne hSU) hp' (hιasym hasym)).1

/-- The graph step: a connected bipartite graph with at least two right vertices has a left
vertex of degree at least two.  Connectivity enters only through `|E| ≥ |L| + |R| − 1`. -/
theorem exists_left_vertex_of_degree_two {L R : Type*} [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) (hR : 2 ≤ (E.image Prod.snd).card)
    (hconn : (E.image Prod.fst).card + (E.image Prod.snd).card ≤ E.card + 1) :
    ∃ b, 2 ≤ (E.filter fun e => e.1 = b).card := by
  by_contra h
  push Not at h
  have hsum : E.card = ∑ b ∈ E.image Prod.fst, (E.filter fun e => e.1 = b).card :=
    Finset.card_eq_sum_card_image Prod.fst E
  have hle : ∑ b ∈ E.image Prod.fst, (E.filter fun e => e.1 = b).card ≤
      ∑ _b ∈ E.image Prod.fst, 1 :=
    Finset.sum_le_sum fun b _ => Nat.le_of_lt_succ (h b)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hle
  omega

end Psc.PeriodicPartnerTwinEndpoint
