import PscVerif.BHDiagonalLiteral

/-!
# The diagonal residual axis block

The three digits `-z, 1, z-1` give an admissible block on the small
positive axis. For `2 ≤ z < r` the endpoint has strictly smaller energy.
At `z = 1` the same actual block joins the already proved labelled exit.
The first integral coordinate remains arbitrary at the initial packet.

See `docs/bh-diagonal-residual-exit-2026-11-27.md`.
-/

namespace Psc.BHDiagonalAxis

open Psc.OccurrenceTransport Psc.BHNearDiagonalLiteral
open Psc.BHNearDiagonalDescent

private theorem delta_identity {r β} (h : BHDiagonalLiteral.Family r β) :
    1-((r : ℝ)-1)/β = (1+(β-r))/β := by
  field_simp [(BHDiagonalLiteral.beta_pos h).ne']
  ring

theorem small_axis_gap {r β} (h : BHDiagonalLiteral.Family r β) (z : ℝ)
    (hz : (β-r)*z < 1+(β-r)) :
    (1-(r : ℝ)/β)*z < 1-((r : ℝ)-1)/β := by
  rw [BHDiagonalLiteral.gap_identity h, delta_identity h]
  have hid : ((β-(r : ℝ))/β)*z = ((β-r)*z)/β := by ring
  rw [hid]
  exact (div_lt_div_iff_of_pos_right (BHDiagonalLiteral.beta_pos h)).mpr hz

theorem axis_choices_of_bounds {a b θ z : ℝ}
    (ha : 0 < a) (ha' : a < 1/4) (hb : b < 1)
    (hθ : 1/2 < θ) (hθ' : θ < 1) (hδ : 1-θ < a)
    (hz : 1 ≤ z) (haz : a*z < 1+a) (hdz : (1-b)*z < 1-θ) :
    |(-z)+(a*0+b*z)| ≤ θ ∧
    |1+(a*(-z)+b*0)| ≤ θ ∧
    |(z-1)+(a*1+b*(-z))| ≤ θ := by
  have hd : 0 < (1-b)*z := mul_pos (by linarith) (by linarith)
  have hal : a ≤ a*z := by nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hz)]
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith only [hd, hdz, hθ]
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith only [haz, hal, hδ, ha', hθ]
  · apply abs_le.mpr
    constructor <;> nlinarith only [hd, hdz, hδ, ha', hθ, hθ']

theorem family_axis_choices {r β} (h : BHDiagonalLiteral.Family r β) (z : ℤ)
    (hz : 1 ≤ z) (hsmall : (β-r)*(z : ℝ) < 1+(β-r)) :
    |(-(z : ℝ))+((β-r)*0+(r/β)*z)| ≤ ((r : ℝ)-1)/β ∧
    |1+((β-r)*(-(z : ℝ))+(r/β)*0)| ≤ ((r : ℝ)-1)/β ∧
    |((z : ℝ)-1)+((β-r)*1+(r/β)*(-(z : ℝ)))| ≤ ((r : ℝ)-1)/β :=
  axis_choices_of_bounds (BHDiagonalLiteral.a_pos h) (BHDiagonalLiteral.a_small h)
    (BHDiagonalLiteral.b_lt_one h) (BHDiagonalLiteral.theta_bounds h).1
    (BHDiagonalLiteral.theta_bounds h).2 (BHDiagonalLiteral.small_gap h)
    (by exact_mod_cast hz) hsmall (small_axis_gap h z hsmall)

theorem gap_times_r {r β} (h : BHDiagonalLiteral.Family r β) :
    (1-(r : ℝ)/β)*r = (β-r)*(r/β) := by
  rw [BHDiagonalLiteral.gap_identity h]
  ring

theorem residual_axis_gap {r β} (h : BHDiagonalLiteral.Family r β) (z : ℝ)
    (hz : z < r) : (1-(r : ℝ)/β)*z < β-r := by
  have hd : 0 < 1-(r : ℝ)/β := sub_pos.mpr (BHDiagonalLiteral.b_lt_one h)
  calc
    (1-(r : ℝ)/β)*z < (1-(r : ℝ)/β)*r := mul_lt_mul_of_pos_left hz hd
    _ = (β-r)*(r/β) := gap_times_r h
    _ < (β-r)*1 := mul_lt_mul_of_pos_left (BHDiagonalLiteral.b_lt_one h)
      (BHDiagonalLiteral.a_pos h)
    _ = β-r := mul_one _

theorem axis_decreases_of_bounds {a b z : ℝ}
    (ha : 0 < a) (ha' : a < 1/4) (hb : b < 1)
    (hz : 2 ≤ z) (hdz : (1-b)*z < a) :
    energy a b 1 (z-1) < energy a b z 0 := by
  have hzp : 0 < z := by linarith
  have hsq := mul_lt_mul_of_pos_right hdz hzp
  have haq := mul_lt_mul_of_pos_right ha' hzp
  have he : energy a b 1 (z-1) - energy a b z 0 =
      (1-b)*z^2+a*z-2*z+2-(1-b)-a := by unfold energy; ring
  nlinarith only [hsq, haq, he, hz, ha, hb]

theorem family_axis_decreases {r β} (h : BHDiagonalLiteral.Family r β) (z : ℤ)
    (hz : 2 ≤ z) (hzr : z < (r : ℤ)) :
    energy (β-r) (r/β) 1 ((z : ℝ)-1) < energy (β-r) (r/β) z 0 :=
  axis_decreases_of_bounds (BHDiagonalLiteral.a_pos h) (BHDiagonalLiteral.a_small h)
    (BHDiagonalLiteral.b_lt_one h) (by exact_mod_cast hz)
    (residual_axis_gap h z (by exact_mod_cast hzr))

/-- All three scalar choices are realized on the same full packet, with
strict overlap and the central window at every edge. -/
theorem axis_path {r β} (h : BHDiagonalLiteral.Family r β) (x z : ℤ)
    (hs : Central r r β (runPacket x 0 z)) (hz : 1 ≤ z)
    (hsmall : (β-r)*(z : ℝ) < 1+(β-r)) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket x 0 z) (runPacket (1-(r : ℤ)*z) (z-1) 1) ∧
      Central r r β (runPacket (1-(r : ℤ)*z) (z-1) 1) := by
  obtain ⟨ht₁, ht₂, ht₃⟩ := family_axis_choices h z hz hsmall
  have h₁ := BHDiagonalLiteral.literal_rounding_step h x 0 z (-z) hs
    (by simpa only [Int.cast_neg, Int.cast_zero] using ht₁)
  simp only [zero_add] at h₁
  have h₂ := BHDiagonalLiteral.literal_rounding_step h ((r : ℤ)*z) (-z) 0 1 h₁.2
    (by simpa only [Int.cast_one, Int.cast_neg, Int.cast_zero] using ht₂)
  simp only [mul_zero, add_zero] at h₂
  have h₃ := BHDiagonalLiteral.literal_rounding_step h (-z) 1 (-z) (z-1) h₂.2
    (by simpa only [Int.cast_sub, Int.cast_one, Int.cast_neg] using ht₃)
  constructor
  · simpa only [mul_neg, sub_eq_add_neg] using
      ((Relation.ReflTransGen.single h₁.1).tail h₂.1).tail h₃.1
  · simpa only [mul_neg, sub_eq_add_neg] using h₃.2

theorem axis_decreasing_path {r β} (h : BHDiagonalLiteral.Family r β) (x z : ℤ)
    (hs : Central r r β (runPacket x 0 z)) (hz : 2 ≤ z) (hzr : z < (r : ℤ))
    (hsmall : (β-r)*(z : ℝ) < 1+(β-r)) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket x 0 z) (runPacket (1-(r : ℤ)*z) (z-1) 1) ∧
      Central r r β (runPacket (1-(r : ℤ)*z) (z-1) 1) ∧
      energy (β-r) (r/β) 1 ((z : ℝ)-1) < energy (β-r) (r/β) z 0 := by
  obtain ⟨hp, hc⟩ := axis_path h x z hs (by omega) hsmall
  exact ⟨hp, hc, family_axis_decreases h z hz hzr⟩

/-- The positive unit axis has a labelled exit for every full first
coordinate permitted by the source window. -/
theorem unit_axis_hits_labelled_zero {r β} (h : BHDiagonalLiteral.Family r β) (x : ℤ)
    (hs : Central r r β (runPacket x 0 1)) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket x 0 1) BHDiagonalLiteral.zero00 := by
  have hsmall : (β-r)*((1 : ℤ) : ℝ) < 1+(β-r) := by norm_num
  have hp := (axis_path h x 1 hs (by omega) hsmall).1
  have hp' : Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket x 0 1) (runPacket (1-(r : ℤ)) 0 1) := by simpa using hp
  exact hp'.trans (BHDiagonalLiteral.unit_saturation_hits_labelled_zero h)

theorem large_axis_gap {r β} (h : BHDiagonalLiteral.Family r β) (z : ℝ)
    (hz : 1+(β-r) ≤ (β-r)*z) :
    1-((r : ℝ)-1)/β ≤ (1-(r : ℝ)/β)*z := by
  rw [BHDiagonalLiteral.gap_identity h, delta_identity h]
  have hid : ((β-(r : ℝ))/β)*z = ((β-r)*z)/β := by ring
  rw [hid]
  exact (div_le_div_iff_of_pos_right (BHDiagonalLiteral.beta_pos h)).mpr hz

theorem large_axis_choice {r β} (h : BHDiagonalLiteral.Family r β) (z : ℤ)
    (hzr : z < (r : ℤ)) (hlarge : 1+(β-r) ≤ (β-r)*(z : ℝ)) :
    |(1-(z : ℝ))+((β-r)*0+(r/β)*z)| ≤ ((r : ℝ)-1)/β := by
  have hl := large_axis_gap h z hlarge
  have hu := residual_axis_gap h z (by exact_mod_cast hzr)
  apply abs_le.mpr
  constructor <;> nlinarith only [hl, hu, BHDiagonalLiteral.a_small h,
    (BHDiagonalLiteral.theta_bounds h).1]

theorem toward_axis_decreases_of_bounds {a b z : ℝ}
    (ha : a < 1/4) (hz : 1 ≤ z) (hdz : (1-b)*z < a) :
    energy a b 0 (1-z) < energy a b z 0 := by
  have hzp : 0 < z := by linarith
  have hsq := mul_lt_mul_of_pos_right hdz hzp
  have haq := mul_lt_mul_of_pos_right ha hzp
  have he : energy a b 0 (1-z) - energy a b z 0 = (1-b)*z^2-2*z+1 := by
    unfold energy
    ring
  nlinarith only [hsq, haq, he, hz]

theorem family_toward_axis_decreases {r β} (h : BHDiagonalLiteral.Family r β) (z : ℤ)
    (hz : 1 ≤ z) (hzr : z < (r : ℤ)) :
    energy (β-r) (r/β) 0 (1-(z : ℝ)) < energy (β-r) (r/β) z 0 :=
  toward_axis_decreases_of_bounds (BHDiagonalLiteral.a_small h)
    (by exact_mod_cast hz) (residual_axis_gap h z (by exact_mod_cast hzr))

theorem large_axis_step {r β} (h : BHDiagonalLiteral.Family r β) (x z : ℤ)
    (hs : Central r r β (runPacket x 0 z)) (hzr : z < (r : ℤ))
    (hlarge : 1+(β-r) ≤ (β-r)*(z : ℝ)) :
    InteriorStep (sigma r r) (lengths r β)
      (runPacket x 0 z) (runPacket ((r : ℤ)*z) (1-z) 0) ∧
      Central r r β (runPacket ((r : ℤ)*z) (1-z) 0) := by
  have ht := large_axis_choice h z hzr hlarge
  simpa only [zero_add] using BHDiagonalLiteral.literal_rounding_step h x 0 z (1-z) hs
    (by simpa only [Int.cast_sub, Int.cast_one, Int.cast_zero] using ht)

/-- Every positive residual-axis packet either has a labelled exit or an
actual central path to strictly smaller pair energy. -/
theorem positive_axis_progress {r β} (h : BHDiagonalLiteral.Family r β) (x z : ℤ)
    (hs : Central r r β (runPacket x 0 z)) (hz : 1 ≤ z) (hzr : z < (r : ℤ)) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket x 0 z) BHDiagonalLiteral.zero00 ∨
    ∃ q : Packet, Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket x 0 z) q ∧ Central r r β q ∧
      energy (β-r) (r/β) (q.delta 2) (q.delta 1) < energy (β-r) (r/β) z 0 := by
  by_cases hz1 : z = 1
  · subst z
    exact Or.inl (unit_axis_hits_labelled_zero h x hs)
  have hz2 : 2 ≤ z := by omega
  by_cases hsmall : (β-r)*(z : ℝ) < 1+(β-r)
  · obtain ⟨hp, hc, he⟩ := axis_decreasing_path h x z hs hz2 hzr hsmall
    refine Or.inr ⟨runPacket (1-(r : ℤ)*z) (z-1) 1, hp, hc, ?_⟩
    simpa [runPacket] using he
  · obtain ⟨hp, hc⟩ := large_axis_step h x z hs hzr (le_of_not_gt hsmall)
    refine Or.inr ⟨runPacket ((r : ℤ)*z) (1-z) 0, .single hp, hc, ?_⟩
    simpa [runPacket] using family_toward_axis_decreases h z hz hzr

end Psc.BHDiagonalAxis
