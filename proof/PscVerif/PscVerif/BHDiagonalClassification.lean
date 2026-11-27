import PscVerif.BHNearDiagonalDescent

/-!
# Algebraic core of the diagonal away-digit classification

This module formalizes the completed-square identity and the elimination of
nonzero congruence integers in the written diagonal residual argument. Its
inputs are explicit arithmetic identities and inequalities; their derivation
from an actual diagonal family packet is not asserted by this module.

See `docs/bh-diagonal-residual-exit-2026-11-27.md` for that written derivation.
-/

namespace Psc.BHDiagonalClassification

/-- The normalized change after the unique away digit. -/
def change (k m z y : ℝ) : ℝ := k * (2*z+m) - z*(z+m) - y^2

theorem change_completed_square (k m z y : ℝ) :
    change k m z y =
      k^2 + m^2/4 - y^2 - (z+m/2-k)^2 := by
  unfold change
  ring

/-- Substituting the exact integer congruence identity makes the final
square independent of the error variable `k`. -/
theorem change_congruence_identity (k m z y q s u : ℝ)
    (hk : k = z+m+y*u-q*s) :
    change k m z y = k^2+m^2/4-y^2-(q*s-m/2-y*u)^2 := by
  rw [change_completed_square]
  rw [hk]
  ring

/-- Positive nonzero congruence integers cannot support a nondecreasing
away step. Here `u` represents `1/beta`. -/
theorem positive_congruence_bound {s u c q y : ℝ}
    (hs : 4 ≤ s) (hu : 0 < u) (hu' : u < 1/12)
    (hc : 0 ≤ c) (hc' : c < 1/3)
    (hratio : (s+1/3)*u < 3/8)
    (hq : 1 ≤ q) (hy : y = s+(q-c)/3) :
    (s+1)^2+1/4-y^2-(q*s-1/2-y*u)^2 < 0 := by
  let v : ℝ := q*s-1/2-y*u
  have hcoeff : 0 ≤ s-u/3 := by linarith
  have hmul := mul_nonneg (sub_nonneg.mpr hq) hcoeff
  have hcu := mul_nonneg hc hu.le
  have hv : s-7/8 < v := by
    dsimp [v]
    rw [hy]
    nlinarith only [hmul, hcu, hratio]
  have hy' : s < y := by rw [hy]; linarith
  have hysq : s^2 < y^2 := by
    have hp := mul_pos (show 0 < y-s by linarith) (show 0 < y+s by linarith)
    nlinarith only [hp]
  have hvsq : (s-7/8)^2 < v^2 := by
    have hp := mul_pos (show 0 < v-(s-7/8) by linarith)
      (show 0 < v+(s-7/8) by linarith)
    nlinarith only [hp]
  have hmargin : 0 < s^2-15*s/4-31/64 := by
    nlinarith [sq_nonneg (s-4)]
  change (s+1)^2+1/4-y^2-v^2 < 0
  nlinarith only [hysq, hvsq, hmargin]

/-- Negative nonzero congruence integers cannot support a nondecreasing
away step. The signed lower bound on `y` is retained explicitly. -/
theorem negative_congruence_bound {s u q y : ℝ}
    (hs : 4 ≤ s) (hu : 0 < u)
    (hq : q ≤ -1) (hy : s-3/2 < y) :
    (s+1)^2+1/4-y^2-(q*s-1/2-y*u)^2 < 0 := by
  let v : ℝ := q*s-1/2-y*u
  have hqs := mul_le_mul_of_nonneg_right hq (show 0 ≤ s by linarith)
  have hyu := mul_pos (show 0 < y by linarith) hu
  have hv : v < -s-1/2 := by dsimp [v]; nlinarith only [hqs, hyu]
  have hysq : (s-3/2)^2 < y^2 := by
    have hp := mul_pos (show 0 < y-(s-3/2) by linarith)
      (show 0 < y+(s-3/2) by linarith)
    nlinarith only [hp]
  have hvsq : (s+1/2)^2 < v^2 := by
    have hp := mul_pos (show 0 < -v-(s+1/2) by linarith)
      (show 0 < -v+(s+1/2) by linarith)
    nlinarith only [hp]
  have hmargin : 0 < s^2-4*s+5/4 := by
    nlinarith [sq_nonneg (s-4)]
  change (s+1)^2+1/4-y^2-v^2 < 0
  nlinarith only [hysq, hvsq, hmargin]

/-- After orienting the auxiliary digit to `m=1`, nondecrease forces
`q=3*y-r=0`. Every bridge hypothesis remains visible in the type. -/
theorem congruence_zero_of_nondec {s u c k z y : ℝ} (q : ℤ)
    (hs : 4 ≤ s) (hu : 0 < u) (hu' : u < 1/12)
    (hc : 0 ≤ c) (hc' : c < 1/3)
    (hratio : (s+1/3)*u < 3/8)
    (hy : y = s+((q : ℝ)-c)/3) (hylo : s-3/2 < y)
    (hk0 : 0 ≤ k) (hkhi : k < s+1)
    (hk : k = z+1+y*u-(q : ℝ)*s)
    (hnondec : 0 ≤ change k 1 z y) : q = 0 := by
  have hksq : k^2 < (s+1)^2 := by
    have hp := mul_pos (show 0 < s+1-k by linarith)
      (show 0 < s+1+k by linarith)
    nlinarith only [hp]
  have heq := change_congruence_identity k 1 z y (q : ℝ) s u hk
  by_contra hq
  have hsplit : 1 ≤ q ∨ q ≤ -1 := by omega
  rcases hsplit with hpos | hneg
  · have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hpos
    have hf := positive_congruence_bound hs hu hu' hc hc' hratio hqreal hy
    norm_num at heq
    nlinarith only [hnondec, heq, hksq, hf]
  · have hqreal : (q : ℝ) ≤ -1 := by exact_mod_cast hneg
    have hf := negative_congruence_bound hs hu hqreal hylo
    norm_num at heq
    nlinarith only [hnondec, heq, hksq, hf]

/-- The simultaneous sign change used to treat `m=-1` preserves the upper
bound, including the sign of the congruence integer. -/
theorem upper_bound_sign_symmetry (s u m q y : ℝ) :
    (s+1)^2+m^2/4-y^2-(q*s-m/2-y*u)^2 =
    (s+1)^2+(-m)^2/4-(-y)^2-((-q)*s-(-m)/2-(-y)*u)^2 := by
  ring

/-- Replacing the integer congruence variable by an arbitrary real would
make `congruence_zero_of_nondec` false, even with strict coefficient bounds.
This control is an arithmetic model, not a diagonal family packet. -/
theorem nonintegral_congruence_control :
    ∃ s u c k z y q : ℝ,
      4 < s ∧ 0 < u ∧ u < 1/12 ∧ 0 ≤ c ∧ c < 1/3 ∧
      (s+1/3)*u < 3/8 ∧ y = s+(q-c)/3 ∧ s-3/2 < y ∧
      0 ≤ k ∧ k < s+1 ∧ k = z+1+y*u-q*s ∧
      0 ≤ change k 1 z y ∧ 0 < q ∧ q < 1 := by
  refine ⟨5, 1/16, 1/4, 59/10, 467/80, 5, 1/4, ?_⟩
  norm_num [change]

end Psc.BHDiagonalClassification
