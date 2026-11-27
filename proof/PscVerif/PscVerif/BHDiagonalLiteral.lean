import PscVerif.BHNearDiagonalLiteral

/-!
# Literal selected digits for the diagonal family

This file separates the actual word occurrences from any assertion that a
digit-selection policy terminates. The near-diagonal quadratic `Window`
does not apply here: its inequality `b ≤ theta` is false when `k = r`.
The final unit-axis excursion deliberately leaves the central run window.
-/

namespace Psc.BHDiagonalLiteral

open Psc.Binomial Psc.Incidence Psc.OccurrenceTransport Psc.OccurrenceSuccessor
open Psc.OccurrenceNewborn Psc.BHNearDiagonalLiteral Matrix
open scoped BigOperators

structure Family (r : ℕ) (β : ℝ) : Prop where
  large : 12 ≤ r
  lower : (r : ℝ) < β
  upper : β < (r : ℝ) + 1
  cubic : β ^ 3 = (r : ℝ) * β ^ 2 + 2 * β + r

theorem Family.toRunFamily {r β} (h : Family r β) : RunFamily r r β :=
  ⟨by have := h.large; omega, h.lower, h.cubic⟩

theorem beta_pos {r β} (h : Family r β) : 0 < β := h.toRunFamily.beta_pos

theorem a_pos {r β} (h : Family r β) : 0 < β - r := sub_pos.mpr h.lower

theorem b_pos {r β} (h : Family r β) : 0 < (r : ℝ)/β := by
  apply div_pos _ (beta_pos h)
  have hr : 0 < r := by have := h.large; omega
  exact_mod_cast hr

theorem b_lt_one {r β} (h : Family r β) : (r : ℝ)/β < 1 :=
  (div_lt_one (beta_pos h)).mpr h.lower

theorem a_identity {r β} (h : Family r β) : (β-(r : ℝ))*β = 2+r/β := by
  nlinarith only [h.toRunFamily.quadratic_eq]

theorem a_small {r β} (h : Family r β) : β-(r : ℝ) < 1/4 := by
  have hr : (12 : ℝ) ≤ r := by exact_mod_cast h.large
  apply lt_of_mul_lt_mul_right _ (beta_pos h).le
  rw [a_identity h]
  linarith [b_lt_one h, h.lower]

theorem b_large {r β} (h : Family r β) : (48/49 : ℝ) < r/β := by
  apply (lt_div_iff₀ (beta_pos h)).mpr
  have hr : (12 : ℝ) ≤ r := by exact_mod_cast h.large
  linarith [a_small h]

theorem theta_bounds {r β} (h : Family r β) :
    (1/2 : ℝ) < ((r : ℝ)-1)/β ∧ ((r : ℝ)-1)/β < 1 := by
  constructor
  · apply (lt_div_iff₀ (beta_pos h)).mpr
    have hr : (12 : ℝ) ≤ r := by exact_mod_cast h.large
    linarith [h.upper]
  · exact (div_lt_one (beta_pos h)).mpr (by linarith [h.lower])

theorem theta_lt_b {r β} (h : Family r β) : ((r : ℝ)-1)/β < r/β :=
  (div_lt_div_iff_of_pos_right (beta_pos h)).mpr (by linarith)

/-- The previous energy-window contract cannot be used for this family. -/
theorem not_near_diagonal_window {r β} (h : Family r β) :
    ¬ Psc.BHNearDiagonalDescent.Window (β-r) (r/β) (((r : ℝ)-1)/β) := by
  intro hw
  exact (not_le_of_gt (theta_lt_b h)) hw.b_le_window

theorem gap_identity {r β} (h : Family r β) :
    1-(r : ℝ)/β = (β-r)/β := by
  field_simp [(beta_pos h).ne']

theorem small_gap {r β} (h : Family r β) :
    1-((r : ℝ)-1)/β < β-r := by
  apply (lt_of_mul_lt_mul_right _ (beta_pos h).le)
  rw [a_identity h]
  have hm : (((r : ℝ)-1)/β)*β = r-1 := div_mul_cancel₀ _ (beta_pos h).ne'
  nlinarith only [hm, a_small h, b_large h]

/-- A selected scalar digit produces the same full integral child, together
with both actual word occurrences and strict overlap. -/
theorem literal_rounding_step {r β} (h : Family r β) (x y z t : ℤ)
    (hsource : Central r r β (runPacket x y z))
    (ht : |(t : ℝ) + ((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β) :
    InteriorStep (sigma r r) (lengths r β) (runPacket x y z)
      (runPacket (y+(r : ℤ)*z) t y) ∧ Central r r β (runPacket (y+(r : ℤ)*z) t y) :=
  literal_rounding_step_of_runFamily h.toRunFamily x y z t hsource ht

/-- Vanishing projected coordinates still require one literal step to clear
the retained first integral coordinate. -/
theorem central_zero_pair_step {r β} (h : Family r β) (x : ℤ)
    (hx : Central r r β (runPacket x 0 0)) :
    InteriorStep (sigma r r) (lengths r β) (runPacket x 0 0) (runPacket 0 0 0) := by
  have ht : |(0 : ℝ) + ((β-r)*0+(r/β)*0)| ≤ ((r : ℝ)-1)/β := by
    simp only [mul_zero, add_zero, abs_zero]
    linarith [(theta_bounds h).1]
  simpa using (literal_rounding_step h x 0 0 0 hx
    (by simpa only [Int.cast_zero] using ht)).1

/-- The last run-to-run edge of the unit excursion is strict but is not a
central-window edge. Its ordinal difference is `r-2`. -/
theorem unit_saturation_step {r β} (h : Family r β) :
    InteriorStep (sigma r r) (lengths r β)
      (runPacket (1-(r : ℤ)) 0 1) (runPacket r 0 0) := by
  have hr : (0 : ℤ) < r := by have := h.large; omega
  have hc := literal_run_step h.toRunFamily (1-(r : ℤ)) 0 1 0
  have hl : -(r : ℤ) < 0 - ((1-(r : ℤ)) + (r : ℤ)*0 + 1) := by have := h.large; omega
  have hu : 0 - ((1-(r : ℤ)) + (r : ℤ)*0 + 1) < (r : ℤ) := by omega
  have hs : |offset (lengths r β) (runPacket (0+(r : ℤ)*1) 0 0).delta| < β := by
    simp only [offset_run, Int.cast_zero, Int.cast_natCast,
      mul_one, zero_add, mul_zero, add_zero]
    rw [abs_of_nonneg (Nat.cast_nonneg r)]
    exact h.lower
  simpa [sub_eq_add_neg] using hc hl hu hs

theorem unit_injection_step {r β} (h : Family r β) :
    InteriorStep (sigma r r) (lengths r β)
      (runPacket (-1) 1 (-1)) (runPacket (1-(r : ℤ)) 0 1) := by
  have hc := literal_run_step h.toRunFamily (-1) 1 (-1) 0
  have hl : -(r : ℤ) < 0 - (-1 + (r : ℤ)*1 + -1) := by omega
  have hu : 0 - (-1 + (r : ℤ)*1 + -1) < (r : ℤ) := by have := h.large; omega
  have hs : |offset (lengths r β) (runPacket (1+(r : ℤ)*(-1)) 0 1).delta| < β := by
    rw [offset_run]
    push_cast
    apply abs_lt.mpr
    constructor <;> linarith [h.lower, b_pos h, b_lt_one h,
      show (12 : ℝ) ≤ r by exact_mod_cast h.large]
  simpa [sub_eq_add_neg] using hc hl hu hs

def zero12 : Packet := ⟨1, 2, 0⟩
def zero00 : Packet := ⟨0, 0, 0⟩

private def firstRunMark (r : ℕ) (hr : 0 < r) : Mark (sigma r r 1) where
  before := [0]
  letter := 1
  after := List.replicate (r-1) 1 ++ [2]
  split := by
    have heq : r = r-1+1 := by omega
    conv_lhs => rw [sigma]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [heq, List.replicate_succ]
    simp

private def finalMark (r : ℕ) : Mark (sigma r r 1) where
  before := 0 :: List.replicate r 1
  letter := 2
  after := []
  split := by simp [sigma]

/-- At full displacement `(r,0,0)`, original ordinals `(1,r+1)` give
different letters at zero. They are not yet a labelled coincidence. -/
theorem saturation_to_zero12 {r β} (h : Family r β) :
    InteriorStep (sigma r r) (lengths r β) (runPacket r 0 0) zero12 := by
  have hr : 0 < r := by have := h.large; omega
  refine ⟨?_, ?_⟩
  · refine ⟨firstRunMark r hr, finalMark r, ?_⟩
    change zero12 = ⟨1, 2, incidenceZ (sigma r r) *ᵥ (runPacket r 0 0).delta +
      residual (firstRunMark r hr).before (finalMark r).before⟩
    apply congrArg (fun d => (⟨1, 2, d⟩ : Packet))
    funext a
    fin_cases a <;>
      simp [incidenceZ, inc, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        sigma, runPacket, OccurrenceTransport.residual, parikhZ, firstRunMark,
        finalMark, List.count_replicate]
  · apply (Packet.interior_iff_bounds (lengths r β)
      (fun a => zero_lt_one.trans_le (h.toRunFamily.lengths_ge_one a)) _).mpr
    simp only [zero12, offset, lengths, dotProduct, Pi.zero_apply, Int.cast_zero,
      mul_zero, Finset.sum_const_zero, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.cons_val_two, neg_lt_zero]
    constructor
    · exact beta_pos h
    · change 0 < 1 + (r : ℝ)/β
      linarith [b_pos h]

private def initialZero1 (r : ℕ) : Mark (sigma r r 1) where
  before := []
  letter := 0
  after := List.replicate r 1 ++ [2]
  split := by simp [sigma]

private def initialZero2 (r : ℕ) (hr : 0 < r) : Mark (sigma r r 2) where
  before := []
  letter := 0
  after := List.replicate (r-1) 0 ++ [1]
  split := by
    change List.replicate r 0 ++ [1] = 0 :: (List.replicate (r-1) 0 ++ [1])
    have heq : List.replicate r (0 : Fin 3) = 0 :: List.replicate (r-1) 0 := by
      conv_lhs => rw [show r = (r-1)+1 by omega, List.replicate_succ]
    rw [heq]
    rfl

/-- The two first zero letters supply the final labelled coincidence. -/
theorem zero12_to_zero00 {r β} (h : Family r β) :
    InteriorStep (sigma r r) (lengths r β) zero12 zero00 := by
  have hr : 0 < r := by have := h.large; omega
  refine ⟨?_, ?_⟩
  · refine ⟨initialZero1 r, initialZero2 r hr, ?_⟩
    change zero00 = ⟨0, 0, incidenceZ (sigma r r) *ᵥ zero12.delta +
      residual (initialZero1 r).before (initialZero2 r hr).before⟩
    simp [zero00, zero12, initialZero1, initialZero2, OccurrenceTransport.residual]
  · apply (Packet.interior_iff_bounds (lengths r β)
      (fun a => zero_lt_one.trans_le (h.toRunFamily.lengths_ge_one a)) _).mpr
    simp [zero00, offset, lengths]

theorem unit_saturation_hits_labelled_zero {r β} (h : Family r β) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket (1-(r : ℤ)) 0 1) zero00 :=
  ((Relation.ReflTransGen.single (unit_saturation_step h)).tail
    (saturation_to_zero12 h)).tail (zero12_to_zero00 h)

theorem unit_injection_hits_labelled_zero {r β} (h : Family r β) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket (-1) 1 (-1)) zero00 :=
  (Relation.ReflTransGen.single (unit_injection_step h)).trans
    (unit_saturation_hits_labelled_zero h)

/-- The strict final run packet lies outside the central window; callers
must not silently claim centrality is preserved by this excursion. -/
theorem saturation_not_central (r : ℕ) (β : ℝ) :
    ¬ Central r r β (runPacket r 0 0) := by
  intro hc
  have hw := hc.2.2
  rw [offset_run] at hw
  norm_num at hw

theorem saturation_not_zero {r β} (h : Family r β) : (runPacket r 0 0).delta ≠ 0 := by
  intro hz
  have hr := congrFun hz 0
  change (r : ℤ) = 0 at hr
  have := h.large
  omega

theorem zero12_not_labelled : zero12.top ≠ zero12.bottom := by decide

end Psc.BHDiagonalLiteral
