import PscVerif.PeriodicPartnerRealizationContinuity

/-!
# Compactness and surjectivity for the concrete solenoid map

Compact anchored hulls cover the ordinary hull after bounded translations.
In the solenoid, bounded lifts of deep coordinates approximate any history
by the unstable real flow, since the error at each fixed depth is stable.
-/

namespace Psc.PeriodicPartnerRealizationOnto

open Function Filter Matrix Set
open Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerLocalTopology
open Psc.PeriodicPartnerLocalRealization Psc.PeriodicPartnerRealizationContinuity
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α} (P : PisotData S)

/-- The ordinary local hull is compact by bounded translation from exact
origin fibres with a tile starting at zero. -/
theorem localHull_compactSpace : CompactSpace (LocalHull S) := by
  let K : Set S.Hull := ⋃ a : α, {T | origin T = (a, 0)}
  let L := ∑ a, S.ℓ a
  have hK : IsCompact K := isCompact_iUnion fun a =>
    Psc.PeriodicPartnerHullCompact.isCompact_origin_fibre (a, 0)
  have hcover : chart S '' (Icc 0 L ×ˢ K) = univ := by
    apply eq_univ_of_forall
    intro T
    let p := origin T.toHull
    let U := LengthSubst.translate p.2 T.toHull
    have hp := tileAt_spec T.toHull 0
    change p ∈ T.toHull.1 ∧ p.2 ≤ 0 ∧ 0 < p.2 + S.ℓ p.1 at hp
    have hU : U ∈ K := by
      apply mem_iUnion.mpr
      refine ⟨p.1, tileAt_eq (show (p.1, 0) ∈ U.1 by simpa [U, LengthSubst.translate, shift]
        using hp.1) ⟨le_rfl, by simpa using S.ℓ_pos p.1⟩⟩
    have hL : S.ℓ p.1 ≤ L := Finset.single_le_sum (f := S.ℓ)
      (fun a _ => (S.ℓ_pos a).le) (Finset.mem_univ p.1)
    refine ⟨(-p.2, U), ⟨⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩, hU⟩, ?_⟩
    apply LocalHull.ext
    change LengthSubst.translate (-p.2) (LengthSubst.translate p.2 T.toHull) = T.toHull
    rw [LengthSubst.translate_translate, neg_add_cancel, LengthSubst.translate_zero]
  apply isCompact_univ_iff.mp
  rw [← hcover]
  exact (isCompact_Icc.prod hK).image (continuous_chart S)

omit [Nonempty α] in
private theorem torusMap_iterate_lift (n : ℕ) (v : α → ℝ) :
    (torusMap S)^[n] (v : Torus α) = (((mat S ^ n) *ᵥ v : α → ℝ) : Torus α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, torusMap_mk, pow_succ', mulVec_mulVec]

/-- The translation orbit of zero is dense in the full nonunit-compatible
history space. At each coordinate the error is an iterated stable projection. -/
theorem denseRange_flow_zero : DenseRange (fun t : ℝ => flow P t 0) := by
  classical
  intro z
  choose v hv hq using fun n => exists_torus_lift (z.1 n)
  let q := QuotientAddGroup.mk' (lattice α)
  let t (n : ℕ) := S.β ^ n * (S.ℓ ⬝ᵥ v n)
  have hc : Continuous (fun w : α → ℝ => ‖P.proj w‖) := by
    unfold PisotData.proj dotProduct
    fun_prop
  have hCube : IsCompact (Set.pi univ (fun _ : α => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨K, hK⟩ := hCube.bddAbove_image hc.continuousOn
  have hbound (n : ℕ) : ‖P.proj (v n)‖ ≤ K := hK ⟨v n, hv n, rfl⟩
  have hcoord (j n : ℕ) (hjn : j ≤ n) :
      (flow P (t n) 0).1 j = z.1 j - q ((mat S ^ (n - j)) *ᵥ P.proj (v n)) := by
    have hz : z.1 j = q ((mat S ^ (n - j)) *ᵥ v n) := by
      rw [← iterate_coord S z (n - j) j, Nat.add_sub_of_le hjn, ← hq n,
        torusMap_iterate_lift]
      rfl
    change 0 + q ((t n / S.β ^ j) • P.u) = _
    rw [zero_add, hz, ← map_sub, P.pow_mulVec_proj, sub_sub_cancel]
    congr 2
    dsimp [t]
    rw [← pow_sub_mul_pow S.β hjn, mul_assoc, mul_comm (S.β ^ j), ← mul_assoc,
      mul_div_cancel_right₀ _ (pow_ne_zero j S.β_pos.ne')]
  have hlim : Tendsto (fun n => flow P (t n) 0) atTop (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro j
    have hj : Tendsto (fun n : ℕ => n - j) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b + j, fun n hn => by omega⟩
    have hb := (tendsto_pow_atTop_nhds_zero_of_lt_one P.ρ_nonneg P.ρ_lt_one).const_mul (P.C * K)
    rw [mul_zero] at hb
    have he : Tendsto (fun n => (mat S ^ (n - j)) *ᵥ P.proj (v n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (hb.comp hj)
      calc
        ‖(mat S ^ (n - j)) *ᵥ P.proj (v n)‖ ≤ P.C * P.ρ ^ (n - j) * ‖P.proj (v n)‖ :=
          P.norm_pow_proj_le _ _
        _ ≤ P.C * P.ρ ^ (n - j) * K :=
          mul_le_mul_of_nonneg_left (hbound n)
            (mul_nonneg P.C_nonneg (pow_nonneg P.ρ_nonneg _))
        _ = (P.C * K) * P.ρ ^ (n - j) := by ring
    have hqcont : Continuous q := QuotientAddGroup.continuous_mk
    have heq := (hqcont.continuousAt (x := 0)).tendsto.comp he
    change Tendsto (fun n => q ((mat S ^ (n - j)) *ᵥ P.proj (v n))) atTop (𝓝 (q 0)) at heq
    rw [map_zero] at heq
    have hdiff := (tendsto_const_nhds (x := z.1 j)).sub heq
    rw [sub_zero] at hdiff
    exact hdiff.congr' (eventually_atTop.mpr ⟨j, fun n hn => (hcoord j n hn).symm⟩)
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun n => mem_range_self (t n))

/-- Translation of both arguments preserves their difference in the solenoid. -/
theorem flow_sub (t : ℝ) (z w : Solenoid S) :
    flow P t z - flow P t w = z - w := by
  unfold flow
  abel

/-- A zero preimage and continuity give an onto map to the full solenoid. -/
theorem realizeLocal_surjective (hβ : 1 < S.β) (hR : Bijective (inflateH (S := S)))
    (hzero : ∃ T, realizeLocal P hR T = 0) : Surjective (realizeLocal P hR) := by
  let : CompactSpace (LocalHull S) := localHull_compactSpace
  let : T2Space (Solenoid S) := solenoid_t2Space S
  have hclosed : IsClosed (range (realizeLocal P hR)) :=
    (isCompact_range (continuous_realizeLocal P hR hβ)).isClosed
  obtain ⟨T, hT⟩ := hzero
  have hsubset : range (fun t : ℝ => flow P t 0) ⊆ range (realizeLocal P hR) := by
    rintro _ ⟨t, rfl⟩
    refine ⟨PeriodicPartnerLocalTopology.translate S t T, ?_⟩
    rw [realizeLocal_translate P hR hβ, hT]
  intro z
  exact hclosed.closure_subset_iff.mpr hsubset (denseRange_flow_zero P z)

end Psc.PeriodicPartnerRealizationOnto
