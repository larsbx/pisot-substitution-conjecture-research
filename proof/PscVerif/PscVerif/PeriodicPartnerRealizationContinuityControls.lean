/-
# The origin coordinate must remain on the exact presentation

The scalar start of the tile containing zero jumps at a tile seam in the
ordinary topology. This control prevents replacing the exact-source series
argument by an unjustified continuity assertion for its origin coordinates.
-/
import PscVerif.PeriodicPartnerLocalTopology
import PscVerif.PeriodicPartnerRealization

namespace Psc.PeriodicPartnerRealizationContinuityControls

open Function Filter Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
  Psc.PeriodicPartnerRealization
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α}

/-- At an origin seam, the ordinary-hull origin start has a jump from the left. -/
theorem not_continuousAt_local_originStart_of_zero (T : S.Hull)
    (hx : (origin T).2 = 0) :
    ¬ ContinuousAt (fun U : Psc.PeriodicPartnerLocalTopology.LocalHull S =>
      (origin U.toHull).2) (Psc.PeriodicPartnerLocalTopology.ofExact S T) := by
  intro hc
  let f : ℝ → ℝ := fun t => (origin (translate t T)).2
  have horbit : Continuous (fun t : ℝ => Psc.PeriodicPartnerLocalTopology.translate S t
      (Psc.PeriodicPartnerLocalTopology.ofExact S T)) :=
    (Psc.PeriodicPartnerLocalTopology.continuous_translate S).comp
      (continuous_id.prodMk continuous_const)
  have hfc : ContinuousAt f 0 := by
    have hc' : ContinuousAt (fun U : Psc.PeriodicPartnerLocalTopology.LocalHull S =>
        (origin U.toHull).2) (Psc.PeriodicPartnerLocalTopology.translate S 0
          (Psc.PeriodicPartnerLocalTopology.ofExact S T)) := by
      simpa only [Psc.PeriodicPartnerLocalTopology.translate_zero] using hc
    have h := hc'.comp (f := fun t : ℝ => Psc.PeriodicPartnerLocalTopology.translate S t
      (Psc.PeriodicPartnerLocalTopology.ofExact S T)) (x := 0) horbit.continuousAt
    simpa [f, Function.comp_def, Psc.PeriodicPartnerLocalTopology.translate,
      Psc.PeriodicPartnerLocalTopology.ofExact, translate_zero] using h
  obtain ⟨b, hb⟩ := exists_prev (tileAt_spec T 0).1
  have hb' : (b, -S.ℓ b) ∈ T.1 := by
    change (b, (origin T).2 - S.ℓ b) ∈ T.1 at hb
    simpa only [hx, zero_sub] using hb
  have hlen := S.ℓ_pos b
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hfc (S.ℓ b / 2) (by positivity)
  let r : ℝ := min δ (S.ℓ b / 2) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_left δ (S.ℓ b / 2)]
  have hrl : r < S.ℓ b / 2 := by dsimp [r]; linarith [min_le_right δ (S.ℓ b / 2)]
  have htile : tileAt T (-r) = (b, -S.ℓ b) :=
    tileAt_eq hb' ⟨by linarith, by change -r < -S.ℓ b + S.ℓ b; linarith⟩
  have hzero : f 0 = 0 := by simp [f, translate_zero, hx]
  have hnear : dist (-r) (0 : ℝ) < δ := by
    simpa [Real.dist_eq, abs_neg, abs_of_pos hr] using hrδ
  have hdist := hclose hnear
  rw [hzero] at hdist
  dsimp [f] at hdist
  rw [origin_translate, htile] at hdist
  simp only [Real.dist_eq, sub_zero] at hdist
  have hleft := (abs_lt.mp hdist).1
  linarith

/-- On an inhabited ordinary hull the scalar origin start is not globally continuous. -/
theorem not_continuous_local_originStart (T : S.Hull) :
    ¬ Continuous (fun U : Psc.PeriodicPartnerLocalTopology.LocalHull S =>
      (origin U.toHull).2) := by
  intro hc
  let U : S.Hull := translate (origin T).2 T
  have ht : tileAt T (origin T).2 = origin T :=
    tileAt_eq (tileAt_spec T 0).1 ⟨le_rfl, by
      change (origin T).2 < (origin T).2 + S.ℓ (origin T).1
      linarith [S.ℓ_pos (origin T).1]⟩
  have hU : (origin U).2 = 0 := by simp [U, origin_translate, ht]
  exact not_continuousAt_local_originStart_of_zero U hU hc.continuousAt

end Psc.PeriodicPartnerRealizationContinuityControls
