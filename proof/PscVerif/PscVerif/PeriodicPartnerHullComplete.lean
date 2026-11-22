/-
# Completeness of exact agreement on the legal tiling hull

A Cauchy sequence stabilizes on every bounded window. Eventual tile membership
therefore defines a legal tiling, and the same stabilized windows prove convergence.
No finite-alphabet, recognizability or compactness premise is used.
-/
import PscVerif.PeriodicPartnerHullContinuity
import Mathlib.Topology.MetricSpace.Cauchy

namespace Psc.PeriodicPartnerHull.LengthSubst

open Function Filter Set
open scoped Topology

variable {α : Type*} {S : LengthSubst α}

/-- An exact Cauchy sequence eventually agrees on any prescribed real window. -/
theorem cauchySeq_eventually_agree {u : ℕ → S.Hull} (hu : CauchySeq u) (R : ℝ) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N, Agree R (u m) (u n) := by
  obtain ⟨k, hk⟩ := exists_nat_gt R
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ((1 / 2 : ℝ) ^ k) (by positivity)
  exact ⟨N, fun m hm n hn => agree_mono (agree_of_dist_lt (hN m hm n hn)) hk.le⟩

/-- Stabilized windows of an exact Cauchy sequence have a legal tiling limit. -/
theorem exists_tendsto_of_cauchySeq {u : ℕ → S.Hull} (hu : CauchySeq u) :
    ∃ T : S.Hull, Tendsto u atTop (𝓝 T) := by
  let L : Set (α × ℝ) := {p | ∃ N : ℕ, ∀ n ≥ N, p ∈ (u n).1}
  have hpatch : ∀ R : ℝ, ∃ N, ∀ n ≥ N, S.AgreeOn (Ioo (-R) R) L (u n).1 := by
    intro R
    obtain ⟨N, hN⟩ := cauchySeq_eventually_agree hu R
    refine ⟨N, fun n hn p hp => ?_⟩
    constructor
    · rintro ⟨M, hM⟩
      exact (hN n hn (max N M) (le_max_left _ _) p hp).mpr
        (hM _ (le_max_right _ _))
    · intro hpn
      exact ⟨N, fun m hm => (hN n hn m hm p hp).mp hpn⟩
  have htiling : S.IsTiling L := by
    intro z
    obtain ⟨N, hN⟩ := hpatch (|z| + 1)
    have hz : z ∈ Ioo (-(|z| + 1)) (|z| + 1) := by
      constructor <;> linarith [neg_abs_le z, le_abs_self z]
    obtain ⟨p, ⟨hp, hzp⟩, huniq⟩ := (u N).2.1 z
    refine ⟨p, ⟨(hN N le_rfl p ⟨z, hzp, hz⟩).mpr hp, hzp⟩, ?_⟩
    rintro q ⟨hq, hzq⟩
    exact huniq q ⟨(hN N le_rfl q ⟨z, hzq, hz⟩).mp hq, hzq⟩
  have hlegal : S.Legal L := by
    intro R
    obtain ⟨N, hN⟩ := hpatch R
    obtain ⟨a, n, t, hL⟩ := (u N).2.2 R
    exact ⟨a, n, t, fun p hp hW => hL p ((hN N le_rfl p hW).mp hp) hW⟩
  let T : S.Hull := ⟨L, htiling, hlegal⟩
  refine ⟨T, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨N, hN⟩ := hpatch (k : ℝ)
  refine ⟨N, fun n hn => ?_⟩
  have hA : Agree (k : ℝ) T (u n) := hN n hn
  exact (dist_le_of_agree hA.symm).trans_lt hk

/-- The finer exact-agreement hull is complete, although it need not be compact. -/
noncomputable instance : CompleteSpace S.Hull :=
  Metric.complete_of_cauchySeq_tendsto fun _ hu => exists_tendsto_of_cauchySeq hu

end Psc.PeriodicPartnerHull.LengthSubst
