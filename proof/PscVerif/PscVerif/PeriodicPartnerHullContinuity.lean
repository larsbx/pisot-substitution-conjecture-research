/-
# Continuity and neighbourhoods for the exact-agreement hull

The existing exact-agreement metric is retained. Its agreement cylinders form
an open neighbourhood basis, fixed translations are homeomorphisms, and literal
inflation is continuous. These statements supply the transverse ingredients for
the ordinary local topology; they do not make the real-parameter translation
action jointly continuous in this finer metric.

No recognizability, primitivity, Pisot, compactness or finite-fibre assumption is
used. The source decision is
`docs/c4-ordinary-hull-topology-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerHull
import Mathlib.Topology.Homeomorph.Defs

namespace Psc.PeriodicPartnerHull.LengthSubst

open Function Filter Set
open scoped Topology

variable {α : Type*} {S : LengthSubst α}

/-- Exact agreement is reflexive. -/
theorem Agree.refl (R : ℝ) (T : S.Hull) : Agree R T T :=
  fun _ _ => Iff.rfl

/-- Exact agreement is symmetric. -/
theorem Agree.symm {R : ℝ} {T U : S.Hull} (h : Agree R T U) : Agree R U T :=
  fun p hp => (h p hp).symm

/-- Exact agreement on the same window is transitive. -/
theorem Agree.trans {R : ℝ} {T U V : S.Hull}
    (hTU : Agree R T U) (hUV : Agree R U V) : Agree R T V :=
  fun p hp => (hTU p hp).trans (hUV p hp)

@[simp] theorem translate_zero (T : S.Hull) : translate 0 T = T :=
  Subtype.ext (shift_zero T.1)

/-- A fixed translation costs at most its absolute displacement in window radius. -/
theorem agree_translate_of_agree {R : ℝ} {T U : S.Hull} (t : ℝ)
    (h : Agree (R + |t|) T U) : Agree R (translate t T) (translate t U) := by
  apply AgreeOn.shift h
  rintro z ⟨hz₁, hz₂⟩
  constructor <;> linarith [neg_abs_le t, le_abs_self t]

/-- Inflation carries exact agreement to the window with its scaled radius. -/
theorem Agree.inflate [Nonempty α] {R : ℝ} {T U : S.Hull} (h : Agree R T U) :
    Agree (S.β * R) (inflateH T) (inflateH U) := by
  apply AgreeOn.inflate h
  rintro z ⟨hz₁, hz₂⟩
  have hβ := S.β_pos
  constructor
  · rw [lt_div_iff₀ hβ]
    nlinarith
  · rw [div_lt_iff₀ hβ]
    nlinarith

/-- Each fixed translation is uniformly continuous for exact agreement. -/
theorem uniformContinuous_translate (t : ℝ) :
    UniformContinuous (translate (S := S) t) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ) + |t|)
  refine ⟨(1 / 2) ^ m, by positivity, ?_⟩
  intro T U hTU
  have ha := agree_mono (agree_of_dist_lt hTU) hm.le
  exact (dist_le_of_agree (agree_translate_of_agree t ha)).trans_lt hn

/-- Fixed translations are continuous even though the full real action is not
jointly continuous for this finer metric. -/
theorem continuous_translate (t : ℝ) : Continuous (translate (S := S) t) :=
  (uniformContinuous_translate t).continuous

/-- Translation by the opposite displacement is the continuous inverse. -/
def translateHomeomorph (t : ℝ) : S.Hull ≃ₜ S.Hull where
  toFun := translate t
  invFun := translate (-t)
  left_inv T := by rw [translate_translate, neg_add_cancel, translate_zero]
  right_inv T := by rw [translate_translate, add_neg_cancel, translate_zero]
  continuous_toFun := continuous_translate t
  continuous_invFun := continuous_translate (-t)

/-- Literal inflation is uniformly continuous in the exact-agreement metric. -/
theorem uniformContinuous_inflateH [Nonempty α] :
    UniformContinuous (inflateH (S := S)) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ) / S.β)
  refine ⟨(1 / 2) ^ m, by positivity, ?_⟩
  intro T U hTU
  have hnm : (n : ℝ) ≤ S.β * m := by
    have := (div_lt_iff₀ S.β_pos).mp hm
    nlinarith
  exact (dist_le_of_agree (agree_mono (Agree.inflate (agree_of_dist_lt hTU)) hnm)).trans_lt hn

/-- Inflation continuity does not assert a continuous inverse or recognizability. -/
theorem continuous_inflateH [Nonempty α] : Continuous (inflateH (S := S)) :=
  uniformContinuous_inflateH.continuous

/-- Each exact-agreement cylinder is open in the existing metric topology. -/
theorem isOpen_agreement (T : S.Hull) (n : ℕ) :
    IsOpen {U : S.Hull | Agree (n : ℝ) T U} := by
  rw [Metric.isOpen_iff]
  intro U hU
  refine ⟨(1 / 2) ^ n, by positivity, ?_⟩
  intro V hV
  exact hU.trans (agree_of_dist_lt (by simpa only [Metric.mem_ball, dist_comm] using hV))

/-- Agreement cylinders are neighbourhoods of their central tiling. -/
theorem agreement_mem_nhds (T : S.Hull) (n : ℕ) :
    {U : S.Hull | Agree (n : ℝ) T U} ∈ 𝓝 T :=
  (isOpen_agreement T n).mem_nhds (Agree.refl _ _)

/-- Every neighbourhood contains a cylinder, and every cylinder is a neighbourhood. -/
theorem mem_nhds_iff_exists_agreement_subset (T : S.Hull) (V : Set S.Hull) :
    V ∈ 𝓝 T ↔ ∃ n : ℕ, {U : S.Hull | Agree (n : ℝ) T U} ⊆ V := by
  constructor
  · intro hV
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, fun U hU => hball ?_⟩
    exact (dist_le_of_agree hU.symm).trans_lt hn
  · rintro ⟨n, hn⟩
    exact Filter.mem_of_superset (agreement_mem_nhds T n) hn

/-- The natural-radius agreement cylinders form a neighbourhood basis. -/
theorem nhds_agreement_basis (T : S.Hull) :
    (𝓝 T).HasBasis (fun _ : ℕ => True) (fun n => {U : S.Hull | Agree (n : ℝ) T U}) := by
  rw [Filter.hasBasis_iff]
  intro V
  simpa only [true_and] using mem_nhds_iff_exists_agreement_subset T V

/-- A set is open exactly when it contains a cylinder at every one of its points. -/
theorem isOpen_iff_agreement (V : Set S.Hull) :
    IsOpen V ↔ ∀ T ∈ V, ∃ n : ℕ, {U : S.Hull | Agree (n : ℝ) T U} ⊆ V := by
  rw [isOpen_iff_mem_nhds]
  simp only [mem_nhds_iff_exists_agreement_subset]

end Psc.PeriodicPartnerHull.LengthSubst
