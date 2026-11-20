import PscVerif.PeriodicPartnerDirectional
import PscVerif.PeriodicPartnerWinding

namespace Psc.PeriodicPartnerWinding

open Filter
open scoped BigOperators Topology

/-- A nonzero grouped seam cycle selects a row and a column crossing.
The resulting two phase paths use opposite lifts of the same base orbit. -/
theorem odd_winding_of_grouped_seams {I J A : Type*} [Fintype I] [Fintype J] [AddCommGroup A]
    (p : I → Bool) (q : J → Bool) (w : I → J → A)
    (hrow : ∀ i, ∑ j, w i j = 0) (hcol : ∀ j, ∑ i, w i j = 0)
    (hentry : (∑ i, ∑ j, if p i = false ∧ q j = false then w i j else 0) ≠ 0)
    (z : Bool → Bool → C(ℝ, UnitAddCircle))
    (hleftTail : ∀ i j k, w i j ≠ 0 → w i k ≠ 0 →
      Tendsto (fun t => z (p i) (q j) t - z (p i) (q k) t) atBot (𝓝 0))
    (hrightTail : ∀ i k j, w i j ≠ 0 → w k j ≠ 0 →
      Tendsto (fun t => z (p i) (q j) t - z (p k) (q j) t) atTop (𝓝 0))
    (hdouble : ∀ t, z false true t + z false true t = z true false t + z true false t)
    (hswitch : z true false 0 - z false true 0 = ((1 / 2 : ℝ) : UnitAddCircle)) :
    ∃ f : HomoclinicPhase,
      (∀ t, f.toContinuousMap t = 2 • (z false false t - z false true t)) ∧ Odd f.winding := by
  have htranspose : (∑ j, ∑ i, if q j = false ∧ p i = false then w i j else 0) ≠ 0 := by
    rw [Finset.sum_comm]
    simpa only [and_comm] using hentry
  let left : ℝ → UnitAddCircle := fun t => z false false t - z false true t
  let right : ℝ → UnitAddCircle := fun t => z false false t - z true false t
  have hl : Continuous left := (z false false).continuous.sub (z false true).continuous
  have hr : Continuous right := (z false false).continuous.sub (z true false).continuous
  have hlEnd : Tendsto left atBot (𝓝 0) := by
    obtain ⟨i, j, k, hi, hj, hk, hwj, hwk⟩ := PeriodicPartner.grouped_row_crosses p q w hrow hentry
    simpa only [hi, hj, hk] using hleftTail i j k hwj hwk
  have hrEnd : Tendsto right atTop (𝓝 0) := by
    obtain ⟨j, i, k, hj, hi, hk, hwi, hwk⟩ := PeriodicPartner.grouped_row_crosses q p
      (fun j i => w i j) hcol htranspose
    simpa only [hi, hj, hk] using hrightTail i k j hwi hwk
  have heq (t : ℝ) : left t + left t = right t + right t := by
    dsimp [left, right]
    rw [sub_add_sub_comm, sub_add_sub_comm, hdouble t]
  have hoffset : left 0 - right 0 = ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [← hswitch]
    dsimp [left, right]
    abel
  let f : HomoclinicPhase :=
    ⟨⟨(fun t => left t + left t), hl.add hl⟩,
      by simpa only [add_zero] using hlEnd.add hlEnd,
      by simpa only [add_zero] using (hrEnd.add hrEnd).congr (fun t => (heq t).symm)⟩
  refine ⟨f, fun t => ?_, f.odd_winding_of_deck_switch hl hr hlEnd hrEnd (fun _ => rfl)
    (fun t => (heq t).symm) hoffset⟩
  exact (two_nsmul (left t)).symm

end Psc.PeriodicPartnerWinding
