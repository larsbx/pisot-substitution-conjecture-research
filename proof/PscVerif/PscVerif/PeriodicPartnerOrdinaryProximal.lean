import PscVerif.PeriodicPartnerProximal
import PscVerif.PeriodicPartnerRealizationOnto
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Ordinary proximality and compact transport from a fibre anchor

Ordinary topological proximality means that the closure of a pair's common
translation orbit meets the diagonal. Exact agreement on arbitrarily large
windows implies this property in the existing ordinary local-hull topology.

The general compactness lemma retains an explicit anchor-fibre proximality
premise. It neither constructs the missing literal-family witnesses nor
asserts maximality, coincidence rank one, or an invariant-measure conclusion.

Source decision: `docs/c4-ordinary-proximal-transport-stop-go-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerOrdinaryProximal

open Function Filter Set Topology
open Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerLocalTopology Psc.PeriodicPartnerProximal
open scoped Topology

/-- Ordinary topological proximality: some common-translation limit lies on
the diagonal. The topology is the supplied ordinary topology, not an exact
agreement metric. -/
def TopologicallyProximal {X : Type*} [TopologicalSpace X]
    (act : ℝ → X → X) (x y : X) : Prop :=
  ∃ z : X, (z, z) ∈ closure (range (fun t : ℝ => (act t x, act t y)))

section CompactTransport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed common orbit is invariant under the action. -/
theorem pair_orbit_closure_invariant (act : ℝ → X → X)
    (hcont : ∀ t, Continuous (act t))
    (hadd : ∀ s t x, act s (act t x) = act (s + t) x)
    {x y : X} {p : X × X}
    (hp : p ∈ closure (range (fun t : ℝ => (act t x, act t y)))) (s : ℝ) :
    (act s p.1, act s p.2) ∈
      closure (range (fun t : ℝ => (act t x, act t y))) := by
  let C := closure (range (fun t : ℝ => (act t x, act t y)))
  have hc : IsClosed C := isClosed_closure
  have hpre : IsClosed {q : X × X | (act s q.1, act s q.2) ∈ C} :=
    hc.preimage ((hcont s).prodMap (hcont s))
  apply hpre.closure_subset_iff.mpr ?_ hp
  rintro _ ⟨t, rfl⟩
  change (act s (act t x), act s (act t y)) ∈ C
  rw [hadd, hadd]
  exact subset_closure (mem_range_self (s + t))

/-- Compact minimal transport from one fibre anchor. The universal proximality
premise on the anchor fibre is explicit and is not supplied by finite fibres.
Only preservation of the factor's fibre relation is needed from equivariance. -/
theorem topologicallyProximal_of_anchor [CompactSpace X] [T2Space Y]
    (act : ℝ → X → X)
    (hcont : ∀ t, Continuous (act t))
    (hadd : ∀ s t x, act s (act t x) = act (s + t) x)
    (hdense : ∀ x, DenseRange (fun t : ℝ => act t x))
    (g : X → Y) (hg : Continuous g)
    (hfibre : ∀ t x y, g x = g y → g (act t x) = g (act t y))
    (v : X) (hanchor : ∀ w, g w = g v → TopologicallyProximal act v w)
    {x y : X} (hxy : g x = g y) : TopologicallyProximal act x y := by
  let C := closure (range (fun t : ℝ => (act t x, act t y)))
  have hc : IsClosed C := isClosed_closure
  have hproj : IsClosed (Prod.fst '' C) :=
    isClosedMap_fst_of_compactSpace C hc
  have hv : v ∈ Prod.fst '' C := by
    apply hproj.closure_subset_iff.mpr ?_ (hdense x v)
    rintro _ ⟨t, rfl⟩
    exact ⟨(act t x, act t y), subset_closure (mem_range_self t), rfl⟩
  obtain ⟨p, hp, hpv⟩ := hv
  have heq : g p.1 = g p.2 := by
    apply (isClosed_eq (hg.comp continuous_fst)
      (hg.comp continuous_snd)).closure_subset_iff.mpr ?_ hp
    rintro _ ⟨t, rfl⟩
    exact hfibre t x y hxy
  have hpa : (v, p.2) ∈ C := by
    have hp' : (p.1, p.2) ∈ C := hp
    simpa only [hpv] using hp'
  obtain ⟨z, hz⟩ := hanchor p.2 (by simpa only [hpv] using heq.symm)
  refine ⟨z, hc.closure_subset_iff.mpr ?_ hz⟩
  rintro _ ⟨t, rfl⟩
  exact pair_orbit_closure_invariant act hcont hadd hpa t

end CompactTransport

section LocalHull

variable {α : Type*} (S : LengthSubst α)

/-- Exact agreement on a slightly larger window transfers membership in a
small-translation neighbourhood. This is the geometric step for moving centres. -/
theorem mem_patch_of_agree {V T U : LocalHull S} {ε R : ℝ} {n : ℕ}
    (hε : ε ≤ 1) (hT : T ∈ patch S V ε n)
    (hR : (n : ℝ) + 1 ≤ R) (hTU : Agree R T.toHull U.toHull) :
    U ∈ patch S V ε n := by
  obtain ⟨t, ht, hVT⟩ := hT
  refine ⟨t, ht, hVT.trans ?_⟩
  apply agree_translate_of_agree (-t)
  apply agree_mono hTU
  rw [abs_neg]
  linarith

/-- Arbitrarily large exact common windows imply ordinary topological
proximality. Compactness gives a cluster point; the existing ordinary patch
basis transfers the second coordinate to the same point. -/
theorem topologicallyProximal_of_exactProximal
    [Fintype α] [DecidableEq α] [Nonempty α] {T U : S.Hull}
    (h : ExactProximal S T U) :
    TopologicallyProximal (translate S) (ofExact S T) (ofExact S U) := by
  classical
  let : CompactSpace (LocalHull S) :=
    Psc.PeriodicPartnerRealizationOnto.localHull_compactSpace
  choose t ht using fun n : ℕ => h ((n : ℝ) + 1) (by positivity)
  let A : ℕ → LocalHull S := fun n => translate S (t n) (ofExact S T)
  let B : ℕ → LocalHull S := fun n => translate S (t n) (ofExact S U)
  obtain ⟨V, hV⟩ := exists_clusterPt_of_compactSpace (Filter.map A atTop)
  refine ⟨V, ?_⟩
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨W₁, hW₁, W₂, hW₂, hWW⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨ε, hε, n, hn⟩ :=
    (Psc.PeriodicPartnerLocalTopology.mem_nhds_iff S V (W₁ ∩ W₂)).mp
      (inter_mem hW₁ hW₂)
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have hpatch : patch S V δ n ∈ 𝓝 V :=
    (nhds_patch_basis S V).mem_of_mem (i := (δ, n)) hδ
  have hfreq : ∃ᶠ m : ℕ in atTop, A m ∈ patch S V δ n :=
    (show MapClusterPt V atTop A from hV).frequently hpatch
  obtain ⟨m, hnm, hm⟩ := frequently_atTop.mp hfreq n
  have hab : Agree ((m : ℝ) + 1) (A m).toHull (B m).toHull := ht m
  have hbm : B m ∈ patch S V δ n := mem_patch_of_agree S (min_le_right _ _)
    hm (by exact_mod_cast Nat.add_le_add_right hnm 1) hab
  have hsub : patch S V δ n ⊆ patch S V ε n := by
    rintro Q ⟨s, hs, ha⟩
    exact ⟨s, hs.trans_le (min_le_left _ _), ha⟩
  exact ⟨(A m, B m), hWW ⟨(hn (hsub hm)).1, (hn (hsub hbm)).2⟩,
    ⟨t m, rfl⟩⟩

end LocalHull

end Psc.PeriodicPartnerOrdinaryProximal
