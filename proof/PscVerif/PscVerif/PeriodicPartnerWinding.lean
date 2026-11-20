/- The local winding calculation for the two-sheet stack factor. The
normalized lifts are constructed using the period-one circle covering. -/
module

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.AddCircle.Real

public section

namespace Psc.PeriodicPartnerWinding

open Filter Function Set
open scoped Topology

/-- A continuous real lift whose value tends to zero on the chosen tail. -/
structure IsTailLift (tail : Filter ℝ) (phase : ℝ → UnitAddCircle) (lift : ℝ → ℝ) : Prop where
  continuous : Continuous lift
  projects : ∀ t, (lift t : UnitAddCircle) = phase t
  tendsToZero : Tendsto lift tail (𝓝 0)

private theorem circleCover : IsCoveringMap ((↑) : ℝ → UnitAddCircle) :=
  AddCircle.isCoveringMap_coe (1 : ℝ)

/-- A lift fixed in the chart around zero stays in that chart on the whole
connected tail where the phase remains in its target. -/
theorem exists_tailLift_atTop {phase : ℝ → UnitAddCircle} (h : Continuous phase)
    (hlim : Tendsto phase atTop (𝓝 0)) : ∃ lift, IsTailLift atTop phase lift := by
  let chart := AddCircle.openPartialHomeomorphCoe (1 : ℝ) (-(1 / 2))
  have hsource : (0 : ℝ) ∈ chart.source := by
    change (0 : ℝ) ∈ Ioo (-(1 / 2)) (-(1 / 2) + 1)
    norm_num [mem_Ioo]
  have htarget : (0 : UnitAddCircle) ∈ chart.target := by
    change chart (0 : ℝ) ∈ chart.target
    exact chart.map_source hsource
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hlim.eventually (chart.open_target.mem_nhds htarget))
  obtain ⟨lift, ⟨hstart, hprojects⟩, _⟩ := circleCover.existsUnique_continuousMap_lifts
    ⟨phase, h⟩ a (chart.symm (phase a)) (chart.right_inv (ha a le_rfl))
  have hagree : (Ici a).EqOn lift (chart.symm ∘ phase) := by
    apply circleCover.eqOn_of_comp_eqOn isPreconnected_Ici lift.continuous.continuousOn
      (chart.continuousOn_symm.comp h.continuousOn (by
        intro t ht
        exact ha t ht)) _ self_mem_Ici hstart
    intro t ht
    exact (congrFun hprojects t).trans (chart.right_inv (ha t ht)).symm
  have hlocal : Tendsto (chart.symm ∘ phase) atTop (𝓝 0) :=
    (chart.tendsto_symm hsource).comp hlim
  exact ⟨lift, lift.continuous, congrFun hprojects,
    hlocal.congr' (eventually_atTop.mpr ⟨a, fun t ht => (hagree ht).symm⟩)⟩

/-- Reflection gives the same construction on the negative tail. -/
theorem exists_tailLift_atBot {phase : ℝ → UnitAddCircle} (h : Continuous phase)
    (hlim : Tendsto phase atBot (𝓝 0)) : ∃ lift, IsTailLift atBot phase lift := by
  obtain ⟨lift, hlift⟩ := exists_tailLift_atTop (h.comp continuous_neg)
    (hlim.comp tendsto_neg_atTop_atBot)
  exact ⟨lift ∘ Neg.neg, hlift.continuous.comp continuous_neg,
    fun t => by simpa using hlift.projects (-t), hlift.tendsToZero.comp tendsto_neg_atBot_atTop⟩

/-- Two normalized lifts agree once both real values lie in one period
interval at a common tail point. Global uniqueness follows by lifting. -/
theorem IsTailLift.unique {tail : Filter ℝ} [NeBot tail] {phase : ℝ → UnitAddCircle}
    {f g : ℝ → ℝ} (hf : IsTailLift tail phase f) (hg : IsTailLift tail phase g) : f = g := by
  have hnear : Ioo (-(1 / 2 : ℝ)) (-(1 / 2) + 1) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨t, hft, hgt⟩ := ((hf.tendsToZero.eventually hnear).and
    (hg.tendsToZero.eventually hnear)).exists
  apply circleCover.eq_of_comp_eq hf.continuous hg.continuous
    (funext fun s => (hf.projects s).trans (hg.projects s).symm) t
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hft)
    (Ioo_subset_Ico_self hgt)).mp ((hf.projects t).trans (hg.projects t).symm)

private theorem IsTailLift.add {tail : Filter ℝ} {f g : ℝ → UnitAddCircle}
    {l r : ℝ → ℝ} (hl : IsTailLift tail f l) (hr : IsTailLift tail g r) :
    IsTailLift tail (fun t => f t + g t) (fun t => l t + r t) :=
  ⟨hl.continuous.add hr.continuous, fun t => by rw [AddCircle.coe_add, hl.projects, hr.projects],
    by simpa only [add_zero] using hl.tendsToZero.add hr.tendsToZero⟩

/-- The difference of the phases of two homoclinic orbits approaches zero
at both ends of the translation line. -/
structure HomoclinicPhase extends C(ℝ, UnitAddCircle) where
  atBot_zero : Tendsto toContinuousMap atBot (𝓝 0)
  atTop_zero : Tendsto toContinuousMap atTop (𝓝 0)

namespace HomoclinicPhase

private noncomputable def leftLift (f : HomoclinicPhase) : ℝ → ℝ :=
  (exists_tailLift_atBot f.continuous f.atBot_zero).choose

private noncomputable def rightLift (f : HomoclinicPhase) : ℝ → ℝ :=
  (exists_tailLift_atTop f.continuous f.atTop_zero).choose

private theorem leftLift_spec (f : HomoclinicPhase) :
    IsTailLift atBot f.toContinuousMap f.leftLift :=
  (exists_tailLift_atBot f.continuous f.atBot_zero).choose_spec

private theorem rightLift_spec (f : HomoclinicPhase) :
    IsTailLift atTop f.toContinuousMap f.rightLift :=
  (exists_tailLift_atTop f.continuous f.atTop_zero).choose_spec

/-- The left lift minus the right lift at time zero, expressed as an integer. -/
noncomputable def winding (f : HomoclinicPhase) : ℤ :=
  ⌊f.leftLift 0 - f.rightLift 0⌋

private theorem int_of_phase_zero {x : ℝ} (h : (x : UnitAddCircle) = 0) :
    ∃ n : ℤ, (n : ℝ) = x := by
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  exact ⟨n, by simpa only [zsmul_one] using hn⟩

theorem winding_eq_of_lifts (f : HomoclinicPhase) {l r : ℝ → ℝ}
    (hl : IsTailLift atBot f.toContinuousMap l) (hr : IsTailLift atTop f.toContinuousMap r) :
    (f.winding : ℝ) = l 0 - r 0 := by
  have hzero : (↑(l 0 - r 0) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, hl.projects, hr.projects, sub_self]
  obtain ⟨n, hn⟩ := int_of_phase_zero hzero
  rw [winding, f.leftLift_spec.unique hl, f.rightLift_spec.unique hr, ← hn, Int.floor_intCast]

/-- Winding is additive on pointwise sums of homoclinic phases. -/
theorem winding_add (f g h : HomoclinicPhase)
    (hsum : ∀ t, h.toContinuousMap t = f.toContinuousMap t + g.toContinuousMap t) :
    h.winding = f.winding + g.winding := by
  have heq : (fun t => f.toContinuousMap t + g.toContinuousMap t) = h.toContinuousMap :=
    (funext hsum).symm
  have hleft := heq ▸ (f.leftLift_spec.add g.leftLift_spec)
  have hright := heq ▸ (f.rightLift_spec.add g.rightLift_spec)
  have hcast : (h.winding : ℝ) = (f.winding : ℝ) + (g.winding : ℝ) := by
    linarith [h.winding_eq_of_lifts hleft hright, f.winding_eq_of_lifts f.leftLift_spec
      f.rightLift_spec, g.winding_eq_of_lifts g.leftLift_spec g.rightLift_spec]
  exact_mod_cast hcast

/-- A real logarithm with zero difference at both ends contributes no winding. -/
theorem winding_eq_zero_of_lift (f : HomoclinicPhase) {lift : ℝ → ℝ}
    (hl : IsTailLift atBot f.toContinuousMap lift) (hr : IsTailLift atTop f.toContinuousMap lift) :
    f.winding = 0 := by
  have h := f.winding_eq_of_lifts hl hr
  rw [sub_self] at h
  exact_mod_cast h

private theorem winding_of_double (f : HomoclinicPhase) {l r : ℝ → UnitAddCircle}
    (hl : Continuous l) (hr : Continuous r) (hlEnd : Tendsto l atBot (𝓝 0))
    (hrEnd : Tendsto r atTop (𝓝 0)) (hLeft : ∀ t, l t + l t = f.toContinuousMap t)
    (hRight : ∀ t, r t + r t = f.toContinuousMap t) :
    ∃ a b : ℝ, (a : UnitAddCircle) = l 0 ∧ (b : UnitAddCircle) = r 0 ∧
      (f.winding : ℝ) = 2 * (a - b) := by
  obtain ⟨left, hleft⟩ := exists_tailLift_atBot hl hlEnd
  obtain ⟨right, hright⟩ := exists_tailLift_atTop hr hrEnd
  have hl' := funext hLeft ▸ (hleft.add hleft)
  have hr' := funext hRight ▸ (hright.add hright)
  refine ⟨left 0, right 0, hleft.projects 0, hright.projects 0, ?_⟩
  linarith [f.winding_eq_of_lifts hl' hr']

/-- If the two normalized half-phase paths differ by a half-turn at the
origin, their common doubled path winds an odd number of times. -/
theorem odd_winding_of_deck_switch (f : HomoclinicPhase) {l r : ℝ → UnitAddCircle}
    (hl : Continuous l) (hr : Continuous r) (hlEnd : Tendsto l atBot (𝓝 0))
    (hrEnd : Tendsto r atTop (𝓝 0)) (hLeft : ∀ t, l t + l t = f.toContinuousMap t)
    (hRight : ∀ t, r t + r t = f.toContinuousMap t)
    (hswitch : l 0 - r 0 = ((1 / 2 : ℝ) : UnitAddCircle)) : Odd f.winding := by
  obtain ⟨a, b, ha, hb, hw⟩ := f.winding_of_double hl hr hlEnd hrEnd hLeft hRight
  have hzero : (↑(a - b - 1 / 2) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_sub, ha, hb, hswitch, sub_self]
  obtain ⟨n, hn⟩ := int_of_phase_zero hzero
  refine ⟨n, ?_⟩
  have hcast : (f.winding : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hcast

/-- Doubling an ordinary homoclinic phase always gives even winding. -/
theorem even_winding_of_double (f g : HomoclinicPhase)
    (hdouble : ∀ t, g.toContinuousMap t + g.toContinuousMap t = f.toContinuousMap t) :
    Even f.winding := ⟨g.winding, g.winding_add g f fun t => (hdouble t).symm⟩

/-- An odd winding prevents the two tail-normalized sheets from being one
homoclinic half-phase. -/
theorem no_homoclinic_half_of_odd (f : HomoclinicPhase) (hodd : Odd f.winding) :
    ¬ ∃ g : HomoclinicPhase, ∀ t, g.toContinuousMap t + g.toContinuousMap t = f.toContinuousMap t := by
  rintro ⟨g, hg⟩
  exact (Int.not_even_iff_odd.mpr hodd) (f.even_winding_of_double g hg)

end HomoclinicPhase

/-- A continuous circle path can vanish at both tails and wind once. The
right lift is one below the left lift, even for a compactly supported phase. -/
theorem winding_one_control : ∃ f : HomoclinicPhase, f.winding = 1 := by
  let ramp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hcont : Continuous ramp := continuous_const.max (continuous_const.min continuous_id)
  have hleft : Tendsto ramp atBot (𝓝 0) := by
    refine tendsto_const_nhds.congr' (eventually_atBot.mpr ⟨0, fun t ht => ?_⟩)
    have hmin : min 1 t ≤ (0 : ℝ) := (min_le_right 1 t).trans ht
    exact (max_eq_left hmin).symm
  have hright : Tendsto (fun t => ramp t - 1) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
    simp [ramp, min_eq_left ht]
  have hphase (t : ℝ) : (↑(ramp t - 1) : UnitAddCircle) = (ramp t : UnitAddCircle) := by
    rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
  have hcoe : Continuous ((↑) : ℝ → UnitAddCircle) := AddCircle.continuous_mk' 1
  let f : HomoclinicPhase :=
    ⟨⟨(fun t => (ramp t : UnitAddCircle)), hcoe.comp hcont⟩,
      (hcoe.tendsto 0).comp hleft,
      ((hcoe.tendsto 0).comp hright).congr hphase⟩
  refine ⟨f, ?_⟩
  have h := f.winding_eq_of_lifts (l := ramp) (r := fun t => ramp t - 1)
    ⟨hcont, fun _ => rfl, hleft⟩
    ⟨hcont.sub continuous_const, hphase, hright⟩
  have hcast : (f.winding : ℝ) = (1 : ℝ) := by linarith
  exact_mod_cast hcast

end Psc.PeriodicPartnerWinding
