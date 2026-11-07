import Mathlib
import Lean.Util.CollectAxioms

/-!
# Route R2: positive-mass obstruction from oriented discrepancies

Finite and exact. This does NOT establish that a strict PIP component
admits a common nonnegative separating functional or positive-density
good returns. Those are adversarially tested open hypotheses.
-/
namespace PscRoutes.R2

variable {ι : Type*} [DecidableEq ι]

/-- A nonnegative family with `good` coordinates at least delta
has total mass at least card(good)*delta. The density limit and the
orientation functional are intentionally outside this theorem. -/
theorem good_mass_lower_bound
    (allIndices good : Finset ι) (value : ι → ℚ) (delta : ℚ)
    (hsub : good ⊆ allIndices)
    (hnonneg : ∀ i ∈ allIndices, 0 ≤ value i)
    (hgood : ∀ i ∈ good, delta ≤ value i) :
    (good.card : ℚ) * delta ≤ ∑ i ∈ allIndices, value i := by
  calc
    (good.card : ℚ) * delta = ∑ _i ∈ good, delta := by simp
    _ ≤ ∑ i ∈ good, value i :=
      Finset.sum_le_sum (by intro i hi; exact hgood i hi)
    _ ≤ ∑ i ∈ allIndices, value i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (by intro i hi _; exact hnonneg i hi)

/-- Algebraic contradiction once an independently proved lower
density bound exceeds a certified upper bound for the average. -/
theorem positive_density_contradiction
    (rho delta mean : ℚ) (hpositive : 0 < rho * delta)
    (hlower : rho * delta ≤ mean)
    (hupper : mean < rho * delta) : False := by
  linarith


/-- A universal nonnegative separator over a side-swap symmetric domain
must vanish on every represented defect. We require the actual side-swap
identity as a hypothesis, not as a property of normalized state labels. -/
theorem symmetric_orientation_forces_zero
    {V : Type*} [AddCommGroup V] (h : V →+ ℚ) (x : V)
    (hforward : 0 ≤ h x) (hreversed : 0 ≤ h (-x)) : h x = 0 := by
  rw [map_neg] at hreversed
  linarith

/-- A strict positive separator on both orientations is impossible. -/
theorem no_two_sided_strict_positive_separator
    {V : Type*} [AddCommGroup V] (h : V →+ ℚ) (x : V)
    (hforward : 0 < h x) (hreversed : 0 ≤ h (-x)) : False := by
  have hzero := symmetric_orientation_forces_zero h x (le_of_lt hforward) hreversed
  linarith


/-- Finite source-bound density gate: a uniform positive density of
strictly oriented good indices is incompatible with a sufficiently
small nonnegative mean. Both the actual sign certificate and the
mean control are external hypotheses requiring independent proof. -/
theorem density_excludes_small_mean
    (allIndices good : Finset ι) (value : ι → ℚ)
    (delta rho eps : ℚ)
    (hsubset : good ⊆ allIndices)
    (hvalue : ∀ i ∈ allIndices, 0 ≤ value i)
    (hgood : ∀ i ∈ good, delta ≤ value i)
    (hdelta : 0 ≤ delta)
    (hnonempty : 0 < (allIndices.card : ℚ))
    (hdensity : rho * (allIndices.card : ℚ) ≤ (good.card : ℚ))
    (hmean : (∑ i ∈ allIndices, value i) ≤
        eps * (allIndices.card : ℚ))
    (hgap : eps < rho * delta) : False := by
  have hcount := good_mass_lower_bound allIndices good value delta
    hsubset hvalue hgood
  have hscale : (rho * (allIndices.card : ℚ)) * delta ≤
      (good.card : ℚ) * delta :=
    mul_le_mul_of_nonneg_right hdensity hdelta
  have hupper : (good.card : ℚ) * delta ≤
      eps * (allIndices.card : ℚ) := le_trans hcount hmean
  have hstrict :
      eps * (allIndices.card : ℚ) <
      (rho * delta) * (allIndices.card : ℚ) :=
    mul_lt_mul_of_pos_right hgap hnonempty
  nlinarith


/-- An occurrence-wise deck involution reverses signed Parikh defects.
If every oriented lift belongs to the same tested support and an
additive rational functional is nonnegative throughout it, the
functional vanishes on every defect. Therefore no sign-blind *strict*
separator exists on a support closed under this deck action. -/
theorem deck_symmetric_separator_vanishes
    {State V : Type*} [AddCommGroup V]
    (deck : State → State) (defect : State → V) (h : V →+ ℚ)
    (hdeck : ∀ s, defect (deck s) = -defect s)
    (hnonneg : ∀ s, 0 ≤ h (defect s)) (s : State) :
    h (defect s) = 0 := by
  have hswap := hnonneg (deck s)
  rw [hdeck s, map_neg] at hswap
  have hhere := hnonneg s
  linarith


/-- The orientation-indexed functional is *even* under the simultaneous
deck transform (orientation reversal, defect negation). Unlike a
sign-blind functional, it can consistently retain strictly positive
values on an orientation pair. This is only an algebraic interface;
it is not a source-valid positive-density certificate. -/
def orientedScore {V : Type*} [AddCommGroup V]
    (h : V →+ ℚ) (orientation : Bool) (x : V) : ℚ :=
  if orientation then h x else -(h x)

/-- Orientation and defect must be transformed simultaneously. -/
theorem orientedScore_deck_invariant
    {V : Type*} [AddCommGroup V]
    (h : V →+ ℚ) (orientation : Bool) (x : V) :
    orientedScore h (!orientation) (-x) = orientedScore h orientation x := by
  cases orientation <;> simp [orientedScore, map_neg]

/-- A positive orientation-dependent potential on one lift remains
positive on the deck-reversed lift, in contrast to an ordinary
nonnegative separator over both signed defects. -/
theorem orientedScore_deck_positivity
    {V : Type*} [AddCommGroup V]
    (h : V →+ ℚ) (orientation : Bool) (x : V)
    (hpos : 0 < orientedScore h orientation x) :
    0 < orientedScore h (!orientation) (-x) := by
  rw [orientedScore_deck_invariant]
  exact hpos


/-- A decisive negative control for the orientation-indexed rescue:
two opposite defects cancel in the *ordinary* (B′-style) average, yet
their deck-invariant, orientation-indexed scores add rather than cancel.
Thus an orientation-indexed potential cannot inherit B′ frequency
averaging without a separate orientation-frequency bridge. -/
theorem deck_score_average_counterexample
    (h : ℚ →+ ℚ) (hone : h (1 : ℚ) = 1) :
    orientedScore h true (1 : ℚ) +
      orientedScore h false (-1 : ℚ) = 2 ∧
    ((1 : ℚ) + (-1 : ℚ)) = 0 := by
  constructor
  · simp [orientedScore, map_neg, hone]
  · norm_num


/-- An orientation-dependent score can inherit a zero-average limit
from a linear displacement score only when its discrepancy is a
bounded-state *coboundary* (or something comparably controlled).
This exact telescoping identity is a required reusable interface. -/
theorem coboundary_telescoping
    {State : Type*} (potential : State → ℚ) (states : ℕ → State) (K : ℕ) :
    (∑ k ∈ Finset.range K,
      (potential (states (k + 1)) - potential (states k))) =
      potential (states K) - potential (states 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- If a source-valid oriented score equals a source-linear
displacement score plus a potential difference at each step,
the total discrepancy is a single endpoint term. A separate
boundedness/frequency theorem must still make that endpoint
term negligible in a Cesàro average. -/
theorem oriented_score_coboundary_sum
    {State : Type*} (linearScore orientedScore : ℕ → ℚ)
    (potential : State → ℚ) (states : ℕ → State) (K : ℕ)
    (hdecomp : ∀ k, orientedScore k =
      linearScore k + potential (states (k + 1)) - potential (states k)) :
    (∑ k ∈ Finset.range K, orientedScore k) =
      (∑ k ∈ Finset.range K, linearScore k) +
      (potential (states K) - potential (states 0)) := by
  calc
    (∑ k ∈ Finset.range K, orientedScore k) =
        ∑ k ∈ Finset.range K,
          (linearScore k +
            (potential (states (k + 1)) - potential (states k))) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hdecomp k]
              ring
    _ = (∑ k ∈ Finset.range K, linearScore k) +
        ∑ k ∈ Finset.range K,
          (potential (states (k + 1)) - potential (states k)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ k ∈ Finset.range K, linearScore k) +
        (potential (states K) - potential (states 0)) := by
          rw [coboundary_telescoping]


/-- A closed occurrence-state cycle with zero *linear* total and
positive *oriented* total cannot realize the proposed orientation
correction as a finite-state potential coboundary. The actual cyclic
occurrence relation remains a separate source-bound obligation. -/
theorem positive_closed_cycle_refutes_coboundary
    {State : Type*} (linearScore orientedScore : ℕ → ℚ)
    (potential : State → ℚ) (states : ℕ → State) (period : ℕ)
    (hclosed : states period = states 0)
    (hlinear : (∑ k ∈ Finset.range period, linearScore k) = 0)
    (hpositive : 0 < (∑ k ∈ Finset.range period, orientedScore k))
    (hdecomp : ∀ k, orientedScore k =
      linearScore k + potential (states (k + 1)) - potential (states k)) :
    False := by
  have hsum := oriented_score_coboundary_sum
    linearScore orientedScore potential states period hdecomp
  rw [hlinear, hclosed] at hsum
  simp at hsum
  linarith

end PscRoutes.R2

#print axioms PscRoutes.R2.good_mass_lower_bound
#print axioms PscRoutes.R2.positive_density_contradiction
#print axioms PscRoutes.R2.symmetric_orientation_forces_zero
#print axioms PscRoutes.R2.no_two_sided_strict_positive_separator
#print axioms PscRoutes.R2.density_excludes_small_mean
#print axioms PscRoutes.R2.deck_symmetric_separator_vanishes
#print axioms PscRoutes.R2.orientedScore_deck_invariant
#print axioms PscRoutes.R2.orientedScore_deck_positivity
#print axioms PscRoutes.R2.deck_score_average_counterexample
#print axioms PscRoutes.R2.coboundary_telescoping
#print axioms PscRoutes.R2.oriented_score_coboundary_sum
#print axioms PscRoutes.R2.positive_closed_cycle_refutes_coboundary

/- Fail-closed exact-declaration axiom audit for this standalone branch.
   All declared helper theorems must use only the standard Lean axioms.
   This does not establish a full substitution-to-Lemma refinement. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R2.good_mass_lower_bound, `PscRoutes.R2.positive_density_contradiction, `PscRoutes.R2.symmetric_orientation_forces_zero, `PscRoutes.R2.no_two_sided_strict_positive_separator, `PscRoutes.R2.density_excludes_small_mean, `PscRoutes.R2.deck_symmetric_separator_vanishes, `PscRoutes.R2.orientedScore_deck_invariant, `PscRoutes.R2.orientedScore_deck_positivity, `PscRoutes.R2.deck_score_average_counterexample, `PscRoutes.R2.coboundary_telescoping, `PscRoutes.R2.oriented_score_coboundary_sum, `PscRoutes.R2.positive_closed_cycle_refutes_coboundary] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_ROUTE_AXIOMS_OK\t{name}"
