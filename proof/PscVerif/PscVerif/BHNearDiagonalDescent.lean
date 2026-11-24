import PscVerif.OccurrenceSuccessor
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Quadratic descent for constrained rounding of the two-coordinate offset

The two integer coordinates limit which rounding can be chosen. The chosen
integer must stay inside the symmetric window available to actual digits.
See docs/bh-near-diagonal-stop-go-2026-11-24.md.
-/

namespace Psc.BHNearDiagonalDescent

def energy (a b z y : ℝ) : ℝ := b * z ^ 2 + a * z * y + y ^ 2

structure Window (a b θ : ℝ) : Prop where
  a_nonneg : 0 ≤ a
  a_small : a < 1 / 4
  b_large : 4 / 5 < b
  b_lt_one : b < 1
  ab_ge_one : 1 ≤ a + b
  a_le_gap : a ≤ 3 * (1 - b)
  b_le_window : b ≤ θ
  window_lt_one : θ < 1

theorem energy_ge_half {a b θ : ℝ} (h : Window a b θ) (z y : ℝ) :
    (z ^ 2 + y ^ 2) / 2 ≤ energy a b z y := by
  unfold energy
  have h₁ := mul_nonneg h.a_nonneg (sq_nonneg (z + y))
  have h₂ := mul_nonneg (show 0 ≤ b - a/2 - 1/2 by linarith [h.a_small, h.b_large])
    (sq_nonneg z)
  have h₃ := mul_nonneg (show 0 ≤ 1 - a/2 - 1/2 by linarith [h.a_small]) (sq_nonneg y)
  nlinarith only [h₁, h₂, h₃]

private theorem energy_pos {a b θ z y : ℝ} (h : Window a b θ)
    (hne : z ≠ 0 ∨ y ≠ 0) : 0 < energy a b z y := by
  have hbound := energy_ge_half h z y
  rcases hne with hz | hy
  · nlinarith only [hbound, sq_pos_of_ne_zero hz, sq_nonneg y]
  · nlinarith only [hbound, sq_nonneg z, sq_pos_of_ne_zero hy]

private theorem zero_endpoint_decreases {a b θ z y : ℝ} (h : Window a b θ)
    (hne : z ≠ 0 ∨ y ≠ 0) : energy a b y 0 < energy a b z y := by
  have h₁ := mul_nonneg h.a_nonneg (sq_nonneg (z + y / 2))
  have hc : 0 < b - a := by linarith [h.b_large, h.a_small]
  have hd : 0 < 1 - b - a/4 := by linarith [h.b_lt_one, h.a_le_gap]
  unfold energy
  rcases hne with hz | hy
  · have hp := mul_pos hc (sq_pos_of_ne_zero hz)
    have hn := mul_nonneg hd.le (sq_nonneg y)
    nlinarith only [h₁, hp, hn]
  · have hp := mul_pos hd (sq_pos_of_ne_zero hy)
    have hn := mul_nonneg hc.le (sq_nonneg z)
    nlinarith only [h₁, hp, hn]

private theorem truncate_decreases {a b θ z y n : ℝ} (h : Window a b θ)
    (hne : z ≠ 0 ∨ y ≠ 0) (hn : 0 ≤ n) (hw : n ≤ a*y + b*z) :
    energy a b y (-n) < energy a b z y := by
  let w := a*y + b*z
  have hzero := zero_endpoint_decreases h hne
  by_cases hw0 : w = 0
  · have hn0 : n = 0 := le_antisymm (hw.trans_eq hw0) hn
    simpa only [hn0, neg_zero] using hzero
  have hwpos : 0 < w := lt_of_le_of_ne (hn.trans hw) (Ne.symm hw0)
  let fraction := n / w
  have hfraction : 0 ≤ fraction := div_nonneg hn hwpos.le
  have hfraction1 : fraction ≤ 1 := (div_le_one hwpos).mpr hw
  have hlw : fraction * w = n := div_mul_cancel₀ _ hwpos.ne'
  have hu : energy a b y (-w) = b * energy a b z y := by
    dsimp [energy, w]
    ring
  have hcon := mul_pos (sub_pos.mpr h.b_lt_one) (energy_pos h hne)
  have hlin : energy a b y (-w) < energy a b z y := by rw [hu]; nlinarith only [hcon]
  have hstrict : (1-fraction) * energy a b y 0 + fraction * energy a b y (-w) < energy a b z y := by
    have h₁ := mul_nonneg hfraction (sub_nonneg.mpr hlin.le)
    have h₂ := mul_nonneg (sub_nonneg.mpr hfraction1) (sub_nonneg.mpr hzero.le)
    by_cases hhalf : fraction ≤ 1 / 2
    · have hs := mul_pos (show 0 < 1 - fraction by linarith) (sub_pos.mpr hzero)
      nlinarith only [h₁, hs]
    · have hs := mul_pos (show 0 < fraction by linarith) (sub_pos.mpr hlin)
      nlinarith only [h₂, hs]
  have hconv : energy a b y (-(fraction * w)) ≤
      (1-fraction) * energy a b y 0 + fraction * energy a b y (-w) := by
    have hc := mul_nonneg (mul_nonneg hfraction (sub_nonneg.mpr hfraction1)) (sq_nonneg w)
    unfold energy
    nlinarith only [hc]
  rw [hlw] at hconv
  exact hconv.trans_lt hstrict

private theorem away_decreases {a b θ z y t : ℝ} (h : Window a b θ)
    (hbig : 4 < energy a b z y) (he : |t + (a*y + b*z)| ≤ 1-b) :
    energy a b y t < energy a b z y := by
  let E := energy a b z y
  let H := a*y + 2*b*z
  let e := t + (a*y + b*z)
  let d := 1 - b
  have hd : 0 < d := sub_pos.mpr h.b_lt_one
  have hcoeff : 0 ≤ 4*b - a^2 := by
    have ha := mul_nonneg h.a_nonneg (show 0 ≤ 1/4 - a by linarith [h.a_small])
    nlinarith only [ha, h.b_large, h.a_small]
  have hH : H^2 ≤ 4*b*E := by
    have hn := mul_nonneg hcoeff (sq_nonneg y)
    dsimp [H, E, energy]
    nlinarith only [hn]
  have hE : 4 < E := hbig
  have hdiff : 4*b*E < (E-d)^2 := by
    have hp := mul_pos (show 0 < E by linarith) (show 0 < E - 2*(1+b) by
      linarith [h.b_lt_one])
    dsimp [d]
    nlinarith only [hp, sq_nonneg (1-b)]
  have hp : 0 ≤ E-d := by dsimp [d]; linarith [h.b_large, hE]
  have habs : |H| < E-d := (sq_lt_sq₀ (abs_nonneg H) hp).mp
    (by rw [sq_abs]; exact hH.trans_lt hdiff)
  have hid : energy a b y t = b*E - H*e + e^2 := by
    dsimp [E, H, e, energy]
    ring
  have hmul : -(H*e) ≤ |H| * |e| := by simpa only [abs_mul] using neg_le_abs (H*e)
  have hsum : -(H*e) + e^2 ≤ d*(|H|+d) := by
    have h₁ := mul_le_mul_of_nonneg_left he (abs_nonneg H)
    have h₂ := pow_le_pow_left₀ (abs_nonneg e) he 2
    rw [sq_abs] at h₂
    nlinarith only [hmul, h₁, h₂]
  have hstrict := mul_lt_mul_of_pos_left (show |H|+d < E by linarith) hd
  rw [hid]
  dsimp [d] at hsum hstrict
  nlinarith only [hsum, hstrict]

private theorem small_truncation {a b θ : ℝ} (h : Window a b θ) (z y : ℤ)
    (hsmall : energy a b z y ≤ 4) (hw : 0 ≤ a*y + b*z) :
    ∃ n : ℤ, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ a*y + b*z ∧ a*y + b*z - (n : ℝ) ≤ θ := by
  have hbound := energy_ge_half h (z : ℝ) (y : ℝ)
  have hz : -2 ≤ z ∧ z ≤ 2 := by
    constructor
    · by_contra hl
      have hc : (z : ℝ) ≤ -3 := by exact_mod_cast (show z ≤ -3 by omega)
      nlinarith only [hbound, hsmall, hc, sq_nonneg ((z : ℝ) + 3), sq_nonneg (y : ℝ)]
    · by_contra hu
      have hc : (3 : ℝ) ≤ z := by exact_mod_cast (show 3 ≤ z by omega)
      nlinarith only [hbound, hsmall, hc, sq_nonneg ((z : ℝ) - 3), sq_nonneg (y : ℝ)]
  have hy : -2 ≤ y ∧ y ≤ 2 := by
    constructor
    · by_contra hl
      have hc : (y : ℝ) ≤ -3 := by exact_mod_cast (show y ≤ -3 by omega)
      nlinarith only [hbound, hsmall, hc, sq_nonneg ((y : ℝ) + 3), sq_nonneg (z : ℝ)]
    · by_contra hu
      have hc : (3 : ℝ) ≤ y := by exact_mod_cast (show 3 ≤ y by omega)
      nlinarith only [hbound, hsmall, hc, sq_nonneg ((y : ℝ) - 3), sq_nonneg (z : ℝ)]
  have ha := h.a_nonneg
  have ha' := h.a_small
  have hb := h.b_large
  have hb' := h.b_lt_one
  have hab := h.ab_ge_one
  have ht := h.b_le_window
  obtain ⟨hzl, hzh⟩ := hz
  obtain ⟨hyl, hyh⟩ := hy
  interval_cases z <;> interval_cases y <;> norm_num [energy] at hsmall hw ⊢
  all_goals first
    | refine ⟨0, ?_⟩
      (norm_num; repeat' constructor) <;> linarith
    | refine ⟨1, ?_⟩
      (norm_num; repeat' constructor) <;> linarith

private theorem rounding_nonneg {a b θ : ℝ} (h : Window a b θ) (z y : ℤ)
    (hne : z ≠ 0 ∨ y ≠ 0) (hw : 0 ≤ (a*y + b*z : ℝ)) :
    ∃ t : ℤ, |(t : ℝ) + (a*y + b*z)| ≤ θ ∧ energy a b y t < energy a b z y := by
  have hne' : (z : ℝ) ≠ 0 ∨ (y : ℝ) ≠ 0 := by exact_mod_cast hne
  by_cases hsmall : energy a b z y ≤ 4
  · obtain ⟨n, hn, hnw, he⟩ := small_truncation h z y hsmall hw
    refine ⟨-n, ?_, ?_⟩
    · rw [Int.cast_neg, abs_of_nonneg (by linarith)]
      linarith
    · simpa only [Int.cast_neg] using truncate_decreases h hne' hn hnw
  let w : ℝ := a*y + b*z
  let n : ℤ := ⌊w⌋
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Int.floor_nonneg.mpr hw)
  have hnw : (n : ℝ) ≤ w := Int.floor_le w
  by_cases he : w - (n : ℝ) ≤ θ
  · refine ⟨-n, ?_, ?_⟩
    · rw [Int.cast_neg, abs_of_nonneg (by linarith)]
      linarith
    · simpa only [Int.cast_neg] using truncate_decreases h hne' hn0 hnw
  have hf : w < (n : ℝ) + 1 := Int.lt_floor_add_one w
  let t : ℤ := -(n+1)
  have hh : |(t : ℝ) + w| ≤ 1-b := by
    simp only [t, Int.cast_neg, Int.cast_add, Int.cast_one]
    rw [abs_of_nonpos (by linarith)]
    linarith [h.b_le_window]
  refine ⟨t, hh.trans (by linarith [h.b_large, h.b_le_window]), ?_⟩
  exact away_decreases h (lt_of_not_ge hsmall) hh

/-- Some geometrically admissible integer choice strictly lowers the energy
unless the two integer coordinates already vanish. -/
theorem choose_rounding {a b θ : ℝ} (h : Window a b θ) (z y : ℤ)
    (hne : z ≠ 0 ∨ y ≠ 0) :
    ∃ t : ℤ, |(t : ℝ) + (a*y + b*z)| ≤ θ ∧ energy a b y t < energy a b z y := by
  by_cases hw : 0 ≤ (a*y+b*z : ℝ)
  · exact rounding_nonneg h z y hne hw
  have hn : -z ≠ 0 ∨ -y ≠ 0 := by simpa only [neg_ne_zero] using hne
  have hneg : 0 ≤ (a*(-y : ℤ) + b*(-z : ℤ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨t, ht, hE⟩ := rounding_nonneg h (-z) (-y) hn hneg
  refine ⟨-t, ?_, ?_⟩
  · push_cast at ht ⊢
    have hneg : -(t : ℝ) + (a*y+b*z) =
        -((t : ℝ) + (a*(-(y : ℝ)) + b*(-(z : ℝ)))) := by ring
    rwa [hneg, abs_neg]
  · push_cast at hE ⊢
    unfold energy at hE ⊢
    nlinarith only [hE]

end Psc.BHNearDiagonalDescent
