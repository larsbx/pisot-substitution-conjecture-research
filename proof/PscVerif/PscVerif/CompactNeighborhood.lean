import PscVerif.MadicResidue
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact intersection neighborhoods in the original matrix-adic product

The existing compatible-sequence carrier has a neighborhood basis given by
one quotient kernel at a time. Paired with a norm ball, this gives the actual
product topology. Compactness then turns simultaneous approximation to two
sets into membership in any prescribed open neighborhood of their
intersection. No finiteness, injectivity, local compactness or new uniform
structure is assumed for the original endomorphism or carrier.

This is standard compact-set neighborhood theory specialized to the existing
carrier. It does not imply membership in the intersection itself or positive
measure. Empty intersections and the empty open neighborhood are permitted.

Pre-code gate: `docs/c4-compact-neighborhood-literature-2026-11-12.md`.
-/

namespace Psc.CompactNeighborhood

open Set Filter
open scoped Topology

section CompactTranslation

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- A neighborhood of a compact set admits one translation neighborhood
that works simultaneously at every point of the compact set. -/
theorem eventually_translate_mem {K W : Set G} (hK : IsCompact K)
    (hW : W ∈ 𝓝ˢ K) :
    ∀ᶠ d in 𝓝 (0 : G), ∀ y ∈ K, y + d ∈ W := by
  apply hK.eventually_forall_of_forall_eventually
  intro y hy
  have hWy : W ∈ 𝓝 y := mem_nhdsSet_iff_forall.mp hW y hy
  have hc : Continuous (fun p : G × G => p.2 + p.1) :=
    continuous_snd.add continuous_fst
  exact hc.continuousAt.preimage_mem_nhds (by simpa only [add_zero] using hWy)

/-- Two compact sets have a common difference neighborhood whose simultaneous
translates lie in the prescribed open neighborhood of their intersection. -/
theorem exists_difference_nhds_inter_subset [T2Space G] {K L U : Set G}
    (hK : IsCompact K) (hL : IsCompact L) (hU : IsOpen U) (hKL : K ∩ L ⊆ U) :
    ∃ W ∈ 𝓝 (0 : G), ∀ x : G,
      (∃ y ∈ K, x - y ∈ W) → (∃ z ∈ L, x - z ∈ W) → x ∈ U := by
  have hUn : U ∈ 𝓝ˢ K ⊓ 𝓝ˢ L := by
    rw [← hK.nhdsSet_inter_eq hL]
    exact hU.mem_nhdsSet.mpr hKL
  obtain ⟨WK, hWK, WL, hWL, hWU⟩ := mem_inf_iff_superset.mp hUn
  refine ⟨{d | (∀ y ∈ K, y + d ∈ WK) ∧ (∀ z ∈ L, z + d ∈ WL)},
    (eventually_translate_mem hK hWK).and (eventually_translate_mem hL hWL), ?_⟩
  intro x hy hz
  obtain ⟨y, hyK, hyW⟩ := hy
  obtain ⟨z, hzL, hzW⟩ := hz
  apply hWU
  constructor
  · simpa only [add_sub_cancel] using hyW.1 y hyK
  · simpa only [add_sub_cancel] using hzW.2 z hzL

end CompactTranslation

section ResidueBasis

variable {V : Type*} [AddCommGroup V]

/-- Each finite-level zero condition is a neighborhood in the existing
induced topology. The entire inverse limit is not declared discrete. -/
theorem kernel_mem_nhds (M : V →ₗ[ℤ] V) (q : ℕ) :
    {x : MadicResidue.Carrier M | MadicResidue.eval M q x = 0} ∈ 𝓝 0 := by
  have hopen : IsOpen {x : MadicResidue.Carrier M | MadicResidue.eval M q x = 0} :=
    (isOpen_discrete ({0} : Set (MadicResidue.Residue M q))).preimage
      (MadicResidue.continuous_eval M q)
  exact hopen.mem_nhds (map_zero (MadicResidue.eval M q))

/-- Compatibility compresses every finite list of quotient-coordinate
restrictions to its greatest depth, including the empty list. -/
theorem exists_kernel_subset (M : V →ₗ[ℤ] V) {W : Set (MadicResidue.Carrier M)}
    (hW : W ∈ 𝓝 0) :
    ∃ q : ℕ, {x : MadicResidue.Carrier M | MadicResidue.eval M q x = 0} ⊆ W := by
  rw [nhds_subtype] at hW
  obtain ⟨P, hP, hPW⟩ := mem_comap.mp hW
  rw [nhds_pi] at hP
  obtain ⟨I, S, hS, hSP⟩ := mem_pi'.mp hP
  refine ⟨I.sup id, ?_⟩
  intro x hx
  apply hPW
  apply hSP
  intro i hi
  have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
  have hzero : MadicResidue.eval M i x = 0 := by
    calc
      MadicResidue.eval M i x =
          MadicResidue.reduction M hle (MadicResidue.eval M (I.sup id) x) :=
        (MadicResidue.reduction_eval M hle x).symm
      _ = 0 := by rw [hx, map_zero]
  change x.val i = 0 at hzero
  change x.val i ∈ S i
  rw [hzero]
  exact mem_of_mem_nhds (hS i)

end ResidueBasis

section ProductBasis

variable {V E : Type*} [AddCommGroup V] [NormedAddCommGroup E]

/-- The concrete stable-ball and one-depth zero-residue neighborhoods. -/
def zeroSlice (M : V →ₗ[ℤ] V) (ε : ℝ) (q : ℕ) : Set (E × MadicResidue.Carrier M) :=
  {d | ‖d.1‖ < ε ∧ MadicResidue.eval M q d.2 = 0}

/-- Proximity uses the original matrix-adic carrier and a single finite
residue depth, together with the actual stable norm. -/
def Close (M : V →ₗ[ℤ] V) (ε : ℝ) (q : ℕ)
    (x y : E × MadicResidue.Carrier M) : Prop :=
  ‖x.1 - y.1‖ < ε ∧ MadicResidue.eval M q x.2 = MadicResidue.eval M q y.2

theorem zeroSlice_mem_nhds (M : V →ₗ[ℤ] V) (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    zeroSlice (E := E) M ε q ∈ 𝓝 0 := by
  change zeroSlice M ε q ∈ 𝓝 ((0 : E), (0 : MadicResidue.Carrier M))
  rw [nhds_prod_eq]
  apply mem_of_superset
    (prod_mem_prod (Metric.ball_mem_nhds (0 : E) hε) (kernel_mem_nhds M q))
  intro d hd
  exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hd.1, hd.2⟩

/-- Every neighborhood of zero contains one of these actual product slices.
Neither a new carrier nor a new topology is introduced. -/
theorem exists_zeroSlice_subset (M : V →ₗ[ℤ] V)
    {W : Set (E × MadicResidue.Carrier M)} (hW : W ∈ 𝓝 0) :
    ∃ ε > 0, ∃ q : ℕ, zeroSlice M ε q ⊆ W := by
  change W ∈ 𝓝 ((0 : E), (0 : MadicResidue.Carrier M)) at hW
  rw [nhds_prod_eq] at hW
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.mp hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨q, hker⟩ := exists_kernel_subset M hB
  refine ⟨ε, hε, q, ?_⟩
  intro d hd
  apply hAB
  exact ⟨hball (by simpa only [Metric.mem_ball, dist_zero_right] using hd.1), hker hd.2⟩

/-- The error vector has the same residue precisely when its quotient
coordinate vanishes. This preserves the source-minus-reference direction. -/
theorem close_iff_sub_mem (M : V →ₗ[ℤ] V) (ε : ℝ) (q : ℕ)
    (x y : E × MadicResidue.Carrier M) :
    Close M ε q x y ↔ x - y ∈ zeroSlice M ε q := by
  change (‖x.1 - y.1‖ < ε ∧ MadicResidue.eval M q x.2 = MadicResidue.eval M q y.2) ↔
    (‖x.1 - y.1‖ < ε ∧ MadicResidue.eval M q (x.2 - y.2) = 0)
  rw [map_sub, sub_eq_zero]

/-- Simultaneous approximation to two compact sets eventually lies in any
open neighborhood of their intersection. The two witnesses may differ;
the approximated point is the same, and no nonemptiness premise is used. -/
theorem exists_close_inter_subset (M : V →ₗ[ℤ] V)
    {K L U : Set (E × MadicResidue.Carrier M)}
    (hK : IsCompact K) (hL : IsCompact L) (hU : IsOpen U) (hKL : K ∩ L ⊆ U) :
    ∃ ε > 0, ∃ q : ℕ, ∀ x : E × MadicResidue.Carrier M,
      (∃ y ∈ K, Close M ε q x y) → (∃ z ∈ L, Close M ε q x z) → x ∈ U := by
  obtain ⟨W, hW, hWU⟩ := exists_difference_nhds_inter_subset hK hL hU hKL
  obtain ⟨ε, hε, q, hslice⟩ := exists_zeroSlice_subset M hW
  refine ⟨ε, hε, q, ?_⟩
  intro x hy hz
  obtain ⟨y, hyK, hxy⟩ := hy
  obtain ⟨z, hzL, hxz⟩ := hz
  exact hWU x ⟨y, hyK, hslice ((close_iff_sub_mem M ε q x y).mp hxy)⟩
    ⟨z, hzL, hslice ((close_iff_sub_mem M ε q x z).mp hxz)⟩

end ProductBasis

end Psc.CompactNeighborhood
