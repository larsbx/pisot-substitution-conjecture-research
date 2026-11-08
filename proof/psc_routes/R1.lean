import Mathlib
import Lean.Util.CollectAxioms

/-!
# Route R1: correction-free ancestry rigidity

Only the explicitly quantified height-growth and bounded-orbit exclusion
are proved here. The nonvanishing height of an actual integral ancestry
defect, and production of long zero-correction stretches from strictness,
remain separate open bindings. No universal PSC claim is discharged.
-/
namespace PscRoutes.R1

variable {State : Type*}

/-- Iterating a Perron-height recurrence on a correction-free orbit. -/
theorem height_on_orbit (beta : ℝ) (x : ℕ → State) (height : State → ℝ)
    (hstep : ∀ k, height (x (k + 1)) = beta * height (x k))
    (n : ℕ) :
    height (x n) = beta ^ n * height (x 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hstep n, ih, pow_succ]
      ring

/-- A finite-state height cap forbids an excessively long
correction-free segment with nonzero initial Perron height.
The explicit separation epsilon and cap B are assumptions, not
a Pisot/irreducibility theorem. -/
theorem correction_free_run_exclusion
    (beta epsilon cap : ℝ) (x : ℕ → State) (height : State → ℝ)
    (n : ℕ)
    (hbeta : 1 < beta)
    (hstep : ∀ k, height (x (k + 1)) = beta * height (x k))
    (hseparated : epsilon ≤ |height (x 0)|)
    (hcap : |height (x n)| ≤ cap)
    (hlarge : cap < beta ^ n * epsilon) : False := by
  have hnonneg : 0 ≤ beta ^ n := pow_nonneg (by linarith) n
  have hgrowth := height_on_orbit beta x height hstep n
  rw [hgrowth, abs_mul, abs_of_nonneg hnonneg] at hcap
  have hbound : beta ^ n * epsilon ≤ beta ^ n * |height (x 0)| :=
    mul_le_mul_of_nonneg_left hseparated hnonneg
  linarith


/-- One-step return to an identical nonzero Perron height requires
a nonzero affine correction when the Perron multiplier is expanding.
This blocks using a forced cycle as a correction-free contradiction. -/
theorem nonzero_fixed_height_requires_forcing
    (beta h correction : ℝ)
    (hbeta : 1 < beta)
    (hfixed : h = beta * h + correction)
    (hnonzero : h ≠ 0) : correction ≠ 0 := by
  intro hzero
  have hprod : (beta - 1) * h = 0 := by
    rw [hzero] at hfixed
    nlinarith [hfixed]
  rcases mul_eq_zero.mp hprod with hβ | hh
  · linarith
  · exact hnonzero hh

/-- The explicit integer affine toy control is a real forcing cycle,
not a correction-free transition. -/
example : ((1 : ℤ) = 2 * 1 - 1) := by omega


/-- Exact accumulated correction in a forced scalar ancestry orbit,
using only the base field operations; intended for a later algebraic-number
certificate for the actual Perron embedding. -/
def forcedDigitSum (beta : ℝ) (digit : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => beta * forcedDigitSum beta digit n + digit n

/-- Every forced ancestry walk has this exact digit identity. The digit
sequence has **not** yet been bound to literal substituted-word offsets. -/
theorem forced_orbit_expansion
    (beta : ℝ) (height correction : ℕ → ℝ)
    (hstep : ∀ n, height (n + 1) = beta * height n + correction n)
    (n : ℕ) :
    height n = beta ^ n * height 0 + forcedDigitSum beta correction n := by
  induction n with
  | zero => simp [forcedDigitSum]
  | succ n ih =>
      rw [hstep n, ih, forcedDigitSum, pow_succ]
      ring

/-- A repeated Perron height imposes a signed digit-polynomial equation.
This is a directly checkable necessary condition for an *actual* closed
ancestry cycle, once its correction digits are independently extracted. -/
theorem period_forcing_certificate
    (beta : ℝ) (height correction : ℕ → ℝ)
    (hstep : ∀ k, height (k + 1) = beta * height k + correction k)
    (n : ℕ) (hperiod : height n = height 0) :
    (beta ^ n - 1) * height 0 + forcedDigitSum beta correction n = 0 := by
  have heq := forced_orbit_expansion beta height correction hstep n
  calc
    (beta ^ n - 1) * height 0 + forcedDigitSum beta correction n =
      (beta ^ n * height 0 + forcedDigitSum beta correction n) - height 0 := by ring
    _ = height n - height 0 := by rw [← heq]
    _ = 0 := by rw [hperiod]; ring


/-- The accumulated scalar corrections are nonnegative when each correction
is nonnegative and the Perron multiplier is nonnegative. This is an
algebraic condition; no claim about actual ordered source digit signs. -/
theorem forcedDigitSum_nonneg (beta : ℝ) (correction : ℕ → ℝ)
    (hbeta : 0 ≤ beta) (hdigits : ∀ k, 0 ≤ correction k) (n : ℕ) :
    0 ≤ forcedDigitSum beta correction n := by
  induction n with
  | zero => simp [forcedDigitSum]
  | succ n ih =>
      simp only [forcedDigitSum]
      exact add_nonneg (mul_nonneg hbeta ih) (hdigits n)

/-- Strictly positive Perron height, expanding growth over a full period,
and nonnegative *all* forced corrections exclude a periodic ancestry.
The signed-correction premise is precisely the open occurrence-order
obligation. The theorem does not assert that Pisot strict components
satisfy that premise. -/
theorem no_positive_periodic_orbit_with_nonnegative_digits
    (beta : ℝ) (height correction : ℕ → ℝ) (n : ℕ)
    (hbeta : 0 ≤ beta)
    (hstep : ∀ k, height (k + 1) = beta * height k + correction k)
    (hpow : 1 < beta ^ n) (hstart : 0 < height 0)
    (hdigits : ∀ k, 0 ≤ correction k)
    (hperiod : height n = height 0) : False := by
  have hsum : 0 ≤ forcedDigitSum beta correction n :=
    forcedDigitSum_nonneg beta correction hbeta hdigits n
  have heq := period_forcing_certificate beta height correction hstep n hperiod
  have hpositive : 0 < (beta ^ n - 1) * height 0 :=
    mul_pos (by linarith) hstart
  linarith

/-- The forced-digit accumulation is additive in its correction
alphabet. Proving this independently avoids accidentally inducting
on a period together with unrelated period hypotheses. -/
theorem forcedDigitSum_neg
    (beta : ℝ) (correction : ℕ → ℝ) (n : ℕ) :
    forcedDigitSum beta (fun k => -(correction k)) n =
      -(forcedDigitSum beta correction n) := by
  induction n with
  | zero => simp [forcedDigitSum]
  | succ n ih =>
      simp only [forcedDigitSum, ih]
      ring

/-- Dual negative orientation case; the digit sum remains nonpositive.
This is distinct from a globally symmetric orientation claim. -/
theorem no_negative_periodic_orbit_with_nonpositive_digits
    (beta : ℝ) (height correction : ℕ → ℝ) (n : ℕ)
    (hbeta : 0 ≤ beta)
    (hstep : ∀ k, height (k + 1) = beta * height k + correction k)
    (hpow : 1 < beta ^ n) (hstart : height 0 < 0)
    (hdigits : ∀ k, correction k ≤ 0)
    (hperiod : height n = height 0) : False := by
  have hsum : 0 ≤ forcedDigitSum beta (fun k => -(correction k)) n :=
    forcedDigitSum_nonneg beta (fun k => -(correction k)) hbeta
      (by intro k; exact neg_nonneg.mpr (hdigits k)) n
  have hsign := forcedDigitSum_neg beta correction n
  have heq := period_forcing_certificate beta height correction hstep n hperiod
  have hnegative : (beta ^ n - 1) * height 0 < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hstart
  rw [hsign] at hsum
  linarith


/-- Actual Tribonacci incidence action for 1↦12, 2↦13, 3↦1
with an integral first-coordinate correction. This *finite* negative
control checks the exact recurrence from the existing ancestry notes;
it does not by itself construct an indefinitely repeating strict PIP
component or certify literal descendant occurrence addresses. -/
def tribonacciAncestryStep (x : ℤ × ℤ × ℤ) (digit : ℤ) :
    ℤ × ℤ × ℤ :=
  (x.1 + x.2.1 + x.2.2 + digit, x.1, x.2.1)

/-- The three-step nonzero defect cycle requires both signs of a
source-prefix correction; it is an explicit counter-calibration to
an unrestricted nonnegative-digit premise. -/
theorem tribonacci_three_step_signed_forcing :
    tribonacciAncestryStep (1, -1, 0) 0 = (0, 1, -1) ∧
    tribonacciAncestryStep (0, 1, -1) (-1) = (-1, 0, 1) ∧
    tribonacciAncestryStep (-1, 0, 1) 1 = (1, -1, 0) := by
  norm_num [tribonacciAncestryStep]


/-- An algebraic arbitrary-alphabet word-mass valuation. Picking
the standard integral basis gives the word's Parikh vector. -/
def wordMass {Letter V : Type*} [AddCommGroup V]
    (label : Letter → V) : List Letter → V
  | [] => 0
  | a :: tail => label a + wordMass label tail

theorem wordMass_append {Letter V : Type*} [AddCommGroup V]
    (label : Letter → V) (u v : List Letter) :
    wordMass label (u ++ v) =
      wordMass label u + wordMass label v := by
  induction u with
  | nil => simp [wordMass]
  | cons a u ih =>
      simp only [List.cons_append, wordMass, ih]
      abel

/-- Exact incidence/word bridge, assuming the given endomorphism
matches the actual substitution images on every letter. -/
theorem wordMass_substitution
    {Letter V : Type*} [AddCommGroup V]
    (label : Letter → V) (subst : Letter → List Letter)
    (M : V →+ V)
    (hcols : ∀ a, M (label a) = wordMass label (subst a))
    (word : List Letter) :
    M (wordMass label word) =
      wordMass label (word.flatMap subst) := by
  induction word with
  | nil => simp [wordMass]
  | cons a tail ih =>
      change M (label a + wordMass label tail) =
        wordMass label (subst a ++ tail.flatMap subst)
      rw [map_add, hcols a, ih, wordMass_append]

/-- Exact source-level asynchronous inflation identity.
The two local segments are literal supplied word fragments.
Binding them to proper image prefixes and legal indices is still
a distinct occurrence-address obligation. -/
theorem asynchronous_word_mass_transport
    {Letter V : Type*} [AddCommGroup V]
    (label : Letter → V) (subst : Letter → List Letter)
    (M : V →+ V)
    (hcols : ∀ a, M (label a) = wordMass label (subst a))
    (topSource bottomSource topLocal bottomLocal : List Letter) :
    wordMass label (topSource.flatMap subst ++ topLocal) -
    wordMass label (bottomSource.flatMap subst ++ bottomLocal) =
    M (wordMass label topSource - wordMass label bottomSource) +
    (wordMass label topLocal - wordMass label bottomLocal) := by
  rw [wordMass_append, wordMass_append]
  rw [← wordMass_substitution label subst M hcols topSource,
      ← wordMass_substitution label subst M hcols bottomSource]
  rw [map_sub]
  abel

end PscRoutes.R1

#print axioms PscRoutes.R1.height_on_orbit
#print axioms PscRoutes.R1.correction_free_run_exclusion
#print axioms PscRoutes.R1.nonzero_fixed_height_requires_forcing
#print axioms PscRoutes.R1.forced_orbit_expansion
#print axioms PscRoutes.R1.period_forcing_certificate
#print axioms PscRoutes.R1.forcedDigitSum_nonneg
#print axioms PscRoutes.R1.no_positive_periodic_orbit_with_nonnegative_digits
#print axioms PscRoutes.R1.forcedDigitSum_neg
#print axioms PscRoutes.R1.no_negative_periodic_orbit_with_nonpositive_digits
#print axioms PscRoutes.R1.tribonacci_three_step_signed_forcing
#print axioms PscRoutes.R1.wordMass_append
#print axioms PscRoutes.R1.wordMass_substitution
#print axioms PscRoutes.R1.asynchronous_word_mass_transport

/- Fail-closed exact-declaration axiom audit for this standalone branch.
   All declared helper theorems must use only the standard Lean axioms.
   This does not establish a full substitution-to-Lemma refinement. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R1.height_on_orbit, `PscRoutes.R1.correction_free_run_exclusion, `PscRoutes.R1.nonzero_fixed_height_requires_forcing, `PscRoutes.R1.forced_orbit_expansion, `PscRoutes.R1.period_forcing_certificate, `PscRoutes.R1.forcedDigitSum_nonneg, `PscRoutes.R1.no_positive_periodic_orbit_with_nonnegative_digits, `PscRoutes.R1.forcedDigitSum_neg, `PscRoutes.R1.no_negative_periodic_orbit_with_nonpositive_digits, `PscRoutes.R1.tribonacci_three_step_signed_forcing, `PscRoutes.R1.wordMass_append, `PscRoutes.R1.wordMass_substitution, `PscRoutes.R1.asynchronous_word_mass_transport] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_ROUTE_AXIOMS_OK\t{name}"
