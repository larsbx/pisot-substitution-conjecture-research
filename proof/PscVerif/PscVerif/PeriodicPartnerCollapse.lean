/-
# Collapse from expanding local agreement

This module formalizes the analytic deduction in Lemma M of the periodic-partner note.
It does not construct a substitution tiling space or assume the desired convergence.
The geometric inputs are restriction of exact agreement, one-step inflation of its
radius, compatibility with the chosen metric, and a positive initial agreement radius.

The endpoint interface is partial: `EndsAtZero x a` describes a labelled tile ending at
the origin, and need not hold for tilings with the origin in a tile interior.  A common
right ray and a common endpoint label supply a positive-radius patch.  Reflecting the
line gives the corresponding left-ray application.

See `docs/c4-periodic-partner-formalization-stop-go-2026-11-19.md` for the pre-code
source decision.  No compactness, rank condition, or vertex-asymptote hypothesis is used.
-/
import PscVerif.PeriodicPartner
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace Psc.PeriodicPartnerCollapse

open Function Filter
open scoped Topology

/-- Local agreement compatible with a metric and with one step of inflation.
The data do not assert expansion or convergence; `1 < β` is a separate theorem premise.
Restriction to a smaller radius is essential because the compatibility modulus need
not choose one of the radii produced by inflation. -/
structure AgreementData (X : Type*) [MetricSpace X] (f : X → X) (β : ℝ) where
  Agree : ℝ → X → X → Prop
  restrict : ∀ {r R : ℝ} {x y : X},
    0 < r → r ≤ R → Agree R x y → Agree r x y
  inflate : ∀ {R : ℝ} {x y : X},
    0 < R → Agree R x y → Agree (β * R) (f x) (f y)
  controls_dist : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ x y : X, Agree R x y → dist x y < ε

/-- Two periodic points whose forward-orbit distance tends to zero are equal.
This metric fact needs no local-agreement data or expansion hypothesis: evaluate the
convergence estimate at arbitrarily late multiples of a common positive period. -/
theorem eq_of_periodic_of_distance_tendsto_zero {X : Type*} [MetricSpace X]
    {f : X → X} {x y : X} (hx : x ∈ periodicPts f) (hy : y ∈ periodicPts f)
    (h : Tendsto (fun n : ℕ => dist (f^[n] x) (f^[n] y)) atTop (𝓝 0)) : x = y := by
  by_contra hxy
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨p, hp, hxp, hyp, _⟩ :=
    Psc.PeriodicPartner.common_period_three f hx hy hy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (dist x y) hdist
  have hxN : f^[p * N] x = x := (IsPeriodicPt.mul_const hxp N).eq
  have hyN : f^[p * N] y = y := (IsPeriodicPt.mul_const hyp N).eq
  have hbad := hN (p * N) (Nat.le_mul_of_pos_left N hp)
  simp only [hxN, hyN, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg,
    lt_self_iff_false] at hbad

namespace AgreementData

variable {X : Type*} [MetricSpace X] {f : X → X} {β : ℝ}
variable (D : AgreementData X f β)

/-- A positive common patch inflates to a patch of radius `β ^ n * R`. -/
theorem agreement_iterate (hβ : 0 < β) {R : ℝ} (hR : 0 < R) {x y : X}
    (h : D.Agree R x y) (n : ℕ) :
    D.Agree (β ^ n * R) (f^[n] x) (f^[n] y) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hstep := D.inflate (mul_pos (pow_pos hβ n) hR) ih
    simpa only [pow_succ', mul_assoc, iterate_succ_apply'] using hstep

/-- Expansion of a positive common patch forces the distance between the two
unshifted forward orbits to tend to zero. -/
theorem distance_tendsto_zero (hβ : 1 < β) {R : ℝ} (hR : 0 < R) {x y : X}
    (h : D.Agree R x y) :
    Tendsto (fun n : ℕ => dist (f^[n] x) (f^[n] y)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr, hclose⟩ := D.controls_dist ε hε
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (r / R) hβ
  refine ⟨N, fun n hn => ?_⟩
  have hbound : r ≤ β ^ n * R :=
    ((div_lt_iff₀ hR).mp (hN.trans_le (pow_le_pow_right₀ hβ.le hn))).le
  have hagree := D.restrict hr hbound
    (D.agreement_iterate (zero_lt_one.trans hβ) hR h n)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
    hclose (f^[n] x) (f^[n] y) hagree

/-- The same conclusion holds when a positive common patch first appears after
any fixed number of substitutions. -/
theorem distance_tendsto_zero_of_eventual_agreement (hβ : 1 < β) {R : ℝ}
    (hR : 0 < R) {x y : X} (m : ℕ)
    (h : D.Agree R (f^[m] x) (f^[m] y)) :
    Tendsto (fun n : ℕ => dist (f^[n] x) (f^[n] y)) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat m).mp
  simpa only [iterate_add_apply] using D.distance_tendsto_zero hβ hR h

/-- Any existing two coordinate limits along the same cofinal reindexing agree.
This assertion neither assumes nor proves compactness or existence of a limit. -/
theorem common_subsequence_limits_eq (hβ : 1 < β) {R : ℝ} (hR : 0 < R)
    {x y : X} (m : ℕ) (h : D.Agree R (f^[m] x) (f^[m] y))
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) {u v : X}
    (hx : Tendsto (fun n => f^[k n] x) atTop (𝓝 u))
    (hy : Tendsto (fun n => f^[k n] y) atTop (𝓝 v)) : u = v := by
  have hcollapse := (D.distance_tendsto_zero_of_eventual_agreement hβ hR m h).comp hk
  exact tendsto_nhds_unique (hx.congr_dist hcollapse) hy

/-- Two periodic points cannot collapse to one another unless they were equal.
The proof samples arbitrarily late multiples of a common positive period. -/
theorem eq_of_periodic_of_eventual_agreement (hβ : 1 < β) {R : ℝ} (hR : 0 < R)
    {x y : X} (m : ℕ) (h : D.Agree R (f^[m] x) (f^[m] y))
    (hx : x ∈ periodicPts f) (hy : y ∈ periodicPts f) : x = y :=
  eq_of_periodic_of_distance_tendsto_zero hx hy
    (D.distance_tendsto_zero_of_eventual_agreement hβ hR m h)

end AgreementData

/-- Primitive geometric facts for a common right ray and labelled tiles ending at zero.
This is a partial endpoint relation on the whole space, with no label assigned to an
interior-origin tiling.  The `common_patch` field is the explicit local geometric input:
one common tile to the left of zero together with the common right ray yields a centred
patch of its positive length. -/
structure RightEndpointData {X : Type*} [MetricSpace X] {f : X → X} {β : ℝ}
    (D : AgreementData X f β) (α : Type*) (g : α → α) where
  CommonRightRay : X → X → Prop
  EndsAtZero : X → α → Prop
  tileLength : α → ℝ
  tileLength_pos : ∀ a, 0 < tileLength a
  ray_inflate : ∀ {x y}, CommonRightRay x y → CommonRightRay (f x) (f y)
  endpoint_inflate : ∀ {x a}, EndsAtZero x a → EndsAtZero (f x) (g a)
  common_patch : ∀ {x y a}, CommonRightRay x y → EndsAtZero x a → EndsAtZero y a →
    D.Agree (tileLength a) x y

namespace RightEndpointData

variable {X α : Type*} [MetricSpace X] {f : X → X} {β : ℝ}
variable {D : AgreementData X f β} {g : α → α}
variable (E : RightEndpointData D α g)

/-- A common right ray remains common after any number of inflations. -/
theorem ray_iterate {x y : X} (h : E.CommonRightRay x y) (n : ℕ) :
    E.CommonRightRay (f^[n] x) (f^[n] y) := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa only [iterate_succ_apply'] using E.ray_inflate ih

/-- Origin endpoint labels follow the given finite or infinite alphabet map. -/
theorem endpoint_iterate {x : X} {a : α} (h : E.EndsAtZero x a) (n : ℕ) :
    E.EndsAtZero (f^[n] x) (g^[n] a) := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa only [iterate_succ_apply'] using E.endpoint_inflate ih

/-- Equal iterated endpoint labels, combined with the common right ray, supply the
positive common patch required by the analytic collapse theorem. -/
theorem agreement_of_endpoint_merge {x y : X} {a b : α}
    (hray : E.CommonRightRay x y) (hx : E.EndsAtZero x a) (hy : E.EndsAtZero y b)
    (m : ℕ) (hmerge : g^[m] a = g^[m] b) :
    D.Agree (E.tileLength (g^[m] a)) (f^[m] x) (f^[m] y) := by
  apply E.common_patch (E.ray_iterate hray m) (E.endpoint_iterate hx m)
  rw [hmerge]
  exact E.endpoint_iterate hy m

/-- Lemma M under explicit local tiling geometry: an endpoint merge causes
unshifted inflation to collapse the two leaves in the metric. -/
theorem distance_tendsto_zero_of_endpoint_merge (hβ : 1 < β) {x y : X} {a b : α}
    (hray : E.CommonRightRay x y) (hx : E.EndsAtZero x a) (hy : E.EndsAtZero y b)
    (m : ℕ) (hmerge : g^[m] a = g^[m] b) :
    Tendsto (fun n : ℕ => dist (f^[n] x) (f^[n] y)) atTop (𝓝 0) :=
  D.distance_tendsto_zero_of_eventual_agreement hβ (E.tileLength_pos _) m
    (E.agreement_of_endpoint_merge hray hx hy m hmerge)

/-- Distinct periodic leaves sharing a right ray have endpoint labels that never merge.
This gives the non-merging direction of the periodic endpoint criterion from the same
local geometry, without a zero-fibre or asymptotic-periodicization premise. -/
theorem endpoint_persistent_of_periodic (hβ : 1 < β) {x y : X} {a b : α}
    (hray : E.CommonRightRay x y) (hx : E.EndsAtZero x a) (hy : E.EndsAtZero y b)
    (hxy : x ≠ y) (hpx : x ∈ periodicPts f) (hpy : y ∈ periodicPts f) :
    ∀ m : ℕ, g^[m] a ≠ g^[m] b := by
  intro m hmerge
  exact hxy (D.eq_of_periodic_of_eventual_agreement hβ (E.tileLength_pos _) m
    (E.agreement_of_endpoint_merge hray hx hy m hmerge) hpx hpy)

end RightEndpointData

end Psc.PeriodicPartnerCollapse
