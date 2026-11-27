import PscVerif.BHDiagonalLiteral

/-!
# Outer descent for the literal diagonal family

The square-root-free cutoff `4 * (1 + 1 / A)^2` is slightly larger than
the written outer threshold. It still lies strictly inside the residual
disk, after using the lower bound on the quadratic energy. All rounding
choices are subsequently lifted to full integral packets.
-/

namespace Psc.BHDiagonalOuter

open Psc.OccurrenceTransport Psc.OccurrenceSuccessor
open Psc.BHNearDiagonalLiteral Psc.BHNearDiagonalDescent
open Psc.BHDiagonalLiteral

theorem square_identity {r β} (h : Family r β) :
    (β-r)^2 = (1-(r : ℝ)/β)*(2+r/β) := by
  have hd : (1-(r : ℝ)/β)*β = β-r := by
    rw [gap_identity h, div_mul_cancel₀ _ (beta_pos h).ne']
  apply mul_right_cancel₀ (beta_pos h).ne'
  calc
    (β-(r : ℝ))^2*β = (β-r)*((β-r)*β) := by ring
    _ = (β-r)*(2+r/β) := by rw [a_identity h]
    _ = ((1-r/β)*β)*(2+r/β) := by rw [hd]
    _ = ((1-r/β)*(2+r/β))*β := by ring

theorem a_times_r {r β} (h : Family r β) :
    (β-r)*(r : ℝ) = (r/β)*(2+r/β) := by
  calc
    (β-(r : ℝ))*r = (β-r)*((r/β)*β) := by
      rw [div_mul_cancel₀ _ (beta_pos h).ne']
    _ = (r/β)*((β-r)*β) := by ring
    _ = (r/β)*(2+r/β) := by rw [a_identity h]

theorem energy_ge_disk {r β} (h : Family r β) (z y : ℝ) :
    (81/100 : ℝ)*(z^2+y^2) ≤ energy (β-r) (r/β) z y := by
  have h₁ := mul_nonneg (a_pos h).le (sq_nonneg (z+y))
  have h₂ := mul_nonneg (show 0 ≤ (r : ℝ)/β-(β-r)/2-81/100 by
    linarith [a_small h, b_large h]) (sq_nonneg z)
  have h₃ := mul_nonneg (show 0 ≤ 1-(β-(r : ℝ))/2-81/100 by
    linarith [a_small h]) (sq_nonneg y)
  unfold energy
  nlinarith only [h₁, h₂, h₃]

theorem energy_ge_half {r β} (h : Family r β) (z y : ℝ) :
    (z^2+y^2)/2 ≤ energy (β-r) (r/β) z y := by
  have hb := energy_ge_disk h z y
  nlinarith only [hb, sq_nonneg z, sq_nonneg y]

theorem energy_pos {r β} (h : Family r β) (z y : ℝ)
    (hne : z ≠ 0 ∨ y ≠ 0) : 0 < energy (β-r) (r/β) z y := by
  have hb := energy_ge_half h z y
  rcases hne with hz | hy
  · nlinarith only [hb, sq_pos_of_ne_zero hz, sq_nonneg y]
  · nlinarith only [hb, sq_nonneg z, sq_pos_of_ne_zero hy]

/-- The zero digit is below every nonzero source energy, whether or not it
is geometrically admissible at that source. -/
theorem zero_endpoint_decreases {r β} (h : Family r β) (z y : ℝ)
    (hne : z ≠ 0 ∨ y ≠ 0) :
    energy (β-r) (r/β) y 0 < energy (β-r) (r/β) z y := by
  let a := β-(r : ℝ)
  let b := (r : ℝ)/β
  have hb : 0 < b := b_pos h
  have hc : 0 < 4*b*(1-b)-a^2 := by
    have hp := mul_pos (sub_pos.mpr (b_lt_one h))
      (show 0 < 3*b-2 by dsimp [b]; linarith [b_large h])
    have hid : a^2 = (1-b)*(2+b) := square_identity h
    nlinarith only [hp, hid]
  by_cases hy : y = 0
  · have hz : z ≠ 0 := by tauto
    have hp := mul_pos hb (sq_pos_of_ne_zero hz)
    simpa [energy, hy, b] using hp
  · have hp := mul_pos hc (sq_pos_of_ne_zero hy)
    have hs := sq_nonneg (2*b*z+a*y)
    have hdiff : 0 < 4*b*(energy a b z y-energy a b y 0) := by
      unfold energy
      nlinarith only [hp, hs]
    exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity : 0 < 4*b)).mp hdiff)

/-- Every real digit between zero and the exact unrounded digit lowers
energy. This is also used by the residual classification. -/
theorem truncate_decreases {r β} (h : Family r β) (z y n : ℝ)
    (hn : 0 ≤ n) (hw : n ≤ (β-r)*y+(r/β)*z)
    (hne : z ≠ 0 ∨ y ≠ 0) :
    energy (β-r) (r/β) y (-n) < energy (β-r) (r/β) z y := by
  let a := β-(r : ℝ)
  let b := (r : ℝ)/β
  let w := a*y+b*z
  have hzero := zero_endpoint_decreases h z y hne
  by_cases hw0 : w = 0
  · have hn0 : n = 0 := le_antisymm (hw.trans_eq hw0) hn
    simpa only [hn0, neg_zero] using hzero
  have hwpos : 0 < w := lt_of_le_of_ne (hn.trans hw) (Ne.symm hw0)
  let fraction := n/w
  have hf : 0 ≤ fraction := div_nonneg hn hwpos.le
  have hf1 : fraction ≤ 1 := (div_le_one hwpos).mpr hw
  have hfw : fraction*w = n := div_mul_cancel₀ _ hwpos.ne'
  have hu : energy a b y (-w) = b*energy a b z y := by
    dsimp [energy, w]
    ring
  have hc := mul_pos (sub_pos.mpr (b_lt_one h)) (energy_pos h z y hne)
  have hlin : energy a b y (-w) < energy a b z y := by
    rw [hu]
    nlinarith only [hc]
  have hstrict : (1-fraction)*energy a b y 0 + fraction*energy a b y (-w) <
      energy a b z y := by
    have h₁ := mul_nonneg hf (sub_nonneg.mpr hlin.le)
    have h₂ := mul_nonneg (sub_nonneg.mpr hf1) (sub_nonneg.mpr hzero.le)
    by_cases hhalf : fraction ≤ 1/2
    · have hs := mul_pos (show 0 < 1-fraction by linarith) (sub_pos.mpr hzero)
      nlinarith only [h₁, hs]
    · have hs := mul_pos (show 0 < fraction by linarith) (sub_pos.mpr hlin)
      nlinarith only [h₂, hs]
  have hconv : energy a b y (-(fraction*w)) ≤
      (1-fraction)*energy a b y 0 + fraction*energy a b y (-w) := by
    have hc := mul_nonneg (mul_nonneg hf (sub_nonneg.mpr hf1)) (sq_nonneg w)
    unfold energy
    nlinarith only [hc]
  rw [hfw] at hconv
  exact hconv.trans_lt hstrict

/-- The scale of the away-rounding error is `(1-B) * (1+1/A)`. -/
theorem window_gap_scale {r β} (h : Family r β) :
    1-((r : ℝ)-1)/β = (1-r/β)*(1+1/(β-r)) := by
  have hd : (1-(r : ℝ)/β)*β = β-r := by
    rw [gap_identity h, div_mul_cancel₀ _ (beta_pos h).ne']
  have ht := div_mul_cancel₀ ((r : ℝ)-1) (beta_pos h).ne'
  have ha : (β-(r : ℝ))*(1+1/(β-r)) = 1+(β-r) := by
    field_simp [(a_pos h).ne']
    ring
  apply mul_right_cancel₀ (beta_pos h).ne'
  calc
    (1-((r : ℝ)-1)/β)*β = 1+(β-r) := by nlinarith only [ht]
    _ = (β-r)*(1+1/(β-r)) := ha.symm
    _ = ((1-r/β)*β)*(1+1/(β-r)) := by rw [hd]
    _ = ((1-r/β)*(1+1/(β-r)))*β := by ring

noncomputable def cutoff (r : ℕ) (β : ℝ) : ℝ := 4*(1+1/(β-r))^2

theorem scale_lt_radius {r β} (h : Family r β) :
    1+1/(β-r) < (9/20 : ℝ)*r := by
  have ha : (β-(r : ℝ))*(1+1/(β-r)) = 1+(β-r) := by
    field_simp [(a_pos h).ne']
    ring
  apply lt_of_mul_lt_mul_left (a := β-(r : ℝ)) _ (a_pos h).le
  rw [ha]
  calc
    1+(β-(r : ℝ)) < (9/20)*((r/β)*(2+r/β)) := by
      nlinarith only [a_small h, b_large h, sq_nonneg ((r : ℝ)/β-1)]
    _ = (β-r)*((9/20)*r) := by rw [← a_times_r h]; ring

theorem cutoff_lt_disk_bound {r β} (h : Family r β) :
    cutoff r β < (81/100 : ℝ)*(r : ℝ)^2 := by
  have hapos := a_pos h
  have hk : 0 ≤ 1+1/(β-(r : ℝ)) := by positivity
  have hr : 0 ≤ (9/20 : ℝ)*r := by positivity
  have hs := (sq_lt_sq₀ hk hr).mpr (scale_lt_radius h)
  unfold cutoff
  nlinarith only [hs]

/-- The formal outer cutoff is still entirely within the disk used by the
uniform residual classification. -/
theorem cutoff_implies_disk {r β} (h : Family r β) (z y : ℝ)
    (he : energy (β-r) (r/β) z y ≤ cutoff r β) :
    z^2+y^2 < (r : ℝ)^2 := by
  have hl := energy_ge_disk h z y
  have hu := cutoff_lt_disk_bound h
  nlinarith only [hl, he, hu]

private theorem away_decreases_of_bounds {a b K z y t : ℝ}
    (hbpos : 0 < b) (hb : b < 1) (hcoeff : 0 ≤ 4*b-a^2) (hK : 0 < K)
    (hbig : 4*K^2 < energy a b z y)
    (he : |t+(a*y+b*z)| ≤ (1-b)*K) :
    energy a b y t < energy a b z y := by
  let E := energy a b z y
  let H := a*y+2*b*z
  let e := t+(a*y+b*z)
  let d := 1-b
  have hd : 0 < d := sub_pos.mpr hb
  have hH : H^2 ≤ 4*b*E := by
    have hn := mul_nonneg hcoeff (sq_nonneg y)
    dsimp [H, E, energy]
    nlinarith only [hn]
  have hE : 4*K^2 < E := hbig
  have hEpos : 0 < E := by nlinarith only [hE, sq_nonneg K]
  have hdiff : 4*b*E*K^2 < (E-d*K^2)^2 := by
    have hgap := mul_pos (sub_pos.mpr hb) (sq_pos_of_pos hK)
    have hp := mul_pos hEpos (show 0 < E-2*(1+b)*K^2 by
      nlinarith only [hE, hgap])
    dsimp [d]
    nlinarith only [hp, sq_nonneg ((1-b)*K^2)]
  have hp : 0 ≤ E-d*K^2 := by
    have hm := mul_nonneg hbpos.le (sq_nonneg K)
    dsimp [d]
    nlinarith only [hE, hm, sq_nonneg K]
  have habs : |H| * K < E-d*K^2 := by
    apply (sq_lt_sq₀ (mul_nonneg (abs_nonneg H) hK.le) hp).mp
    rw [mul_pow, sq_abs]
    exact (mul_le_mul_of_nonneg_right hH (sq_nonneg K)).trans_lt hdiff
  have hid : energy a b y t = b*E-H*e+e^2 := by
    dsimp [E, H, e, energy]
    ring
  have hmul : -(H*e) ≤ |H| * |e| := by
    simpa only [abs_mul] using neg_le_abs (H*e)
  have hsum : -(H*e)+e^2 ≤ d*(|H| * K+d*K^2) := by
    have h₁ := mul_le_mul_of_nonneg_left he (abs_nonneg H)
    have h₂ := pow_le_pow_left₀ (abs_nonneg e) he 2
    rw [sq_abs] at h₂
    dsimp [d]
    nlinarith only [hmul, h₁, h₂]
  have hstrict := mul_lt_mul_of_pos_left
    (show |H| * K+d*K^2 < E by linarith only [habs]) hd
  rw [hid]
  dsimp [d] at hsum hstrict
  nlinarith only [hsum, hstrict]

/-- Outside the cutoff, the alternate integer also decreases energy if
its error is at most the complement of the admissibility window. -/
theorem away_decreases {r β} (h : Family r β) (z y t : ℝ)
    (hbig : cutoff r β < energy (β-r) (r/β) z y)
    (he : |t+((β-r)*y+(r/β)*z)| ≤ 1-((r : ℝ)-1)/β) :
    energy (β-r) (r/β) y t < energy (β-r) (r/β) z y := by
  have hapos := a_pos h
  have hcoeff : 0 ≤ 4*((r : ℝ)/β)-(β-r)^2 := by
    have ha := mul_nonneg (a_pos h).le (show 0 ≤ 1/4-(β-(r : ℝ)) by
      linarith [a_small h])
    nlinarith only [ha, b_large h, a_small h]
  have hK : 0 < 1+1/(β-(r : ℝ)) := by positivity
  rw [window_gap_scale h] at he
  exact away_decreases_of_bounds (b_pos h) (b_lt_one h) hcoeff hK hbig he

private theorem rounding_nonneg {r β} (h : Family r β) (z y : ℤ)
    (hbig : cutoff r β < energy (β-r) (r/β) z y)
    (hw : 0 ≤ (β-r)*y+(r/β)*z) :
    ∃ t : ℤ, |(t : ℝ)+((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β ∧
      energy (β-r) (r/β) y t < energy (β-r) (r/β) z y := by
  have hEpos : 0 < energy (β-r) (r/β) z y :=
    lt_of_le_of_lt (by unfold cutoff; positivity) hbig
  have hne : (z : ℝ) ≠ 0 ∨ (y : ℝ) ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [energy, hn.1, hn.2] at hEpos
  let w : ℝ := (β-r)*y+(r/β)*z
  let n : ℤ := ⌊w⌋
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Int.floor_nonneg.mpr hw)
  have hnw : (n : ℝ) ≤ w := Int.floor_le w
  by_cases he : w-(n : ℝ) ≤ ((r : ℝ)-1)/β
  · refine ⟨-n, ?_, ?_⟩
    · rw [Int.cast_neg, abs_of_nonneg (by linarith only [hnw])]
      linarith only [he]
    · simpa only [Int.cast_neg] using truncate_decreases h z y n hn0 hnw hne
  have hf : w < (n : ℝ)+1 := Int.lt_floor_add_one w
  let t : ℤ := -(n+1)
  have hh : |(t : ℝ)+w| ≤ 1-((r : ℝ)-1)/β := by
    simp only [t, Int.cast_neg, Int.cast_add, Int.cast_one]
    rw [abs_of_nonpos (by linarith only [hf])]
    linarith only [he]
  refine ⟨t, hh.trans (by linarith [(theta_bounds h).1]), ?_⟩
  exact away_decreases h z y t hbig hh

/-- Above the cutoff there is an admissible strict energy decrease, with
no sign restriction on the full pair. -/
theorem choose_rounding {r β} (h : Family r β) (z y : ℤ)
    (hbig : cutoff r β < energy (β-r) (r/β) z y) :
    ∃ t : ℤ, |(t : ℝ)+((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β ∧
      energy (β-r) (r/β) y t < energy (β-r) (r/β) z y := by
  by_cases hw : 0 ≤ (β-r)*y+(r/β)*z
  · exact rounding_nonneg h z y hbig hw
  have hn : 0 ≤ (β-r)*(-y : ℤ)+(r/β)*(-z : ℤ) := by
    push_cast
    linarith only [hw]
  have hbig' : cutoff r β < energy (β-r) (r/β) (-z : ℤ) (-y : ℤ) := by
    simpa [energy] using hbig
  obtain ⟨t, ht, hE⟩ := rounding_nonneg h (-z) (-y) hbig' hn
  refine ⟨-t, ?_, ?_⟩
  · push_cast at ht ⊢
    have hneg : -(t : ℝ)+((β-r)*y+(r/β)*z) =
        -((t : ℝ)+((β-r)*(-(y : ℝ))+(r/β)*(-(z : ℝ)))) := by ring
    rwa [hneg, abs_neg]
  · push_cast at hE ⊢
    unfold energy at hE ⊢
    nlinarith only [hE]

/-- The outer decrease is an actual strict occurrence edge and retains the
first integral coordinate `y+r*z`. -/
theorem outer_step {r β} (h : Family r β) (x y z : ℤ)
    (hc : Central r r β (runPacket x y z))
    (hbig : cutoff r β < energy (β-r) (r/β) z y) :
    ∃ t : ℤ,
      InteriorStep (sigma r r) (lengths r β) (runPacket x y z)
        (runPacket (y+(r : ℤ)*z) t y) ∧
      Central r r β (runPacket (y+(r : ℤ)*z) t y) ∧
      energy (β-r) (r/β) y t < energy (β-r) (r/β) z y := by
  obtain ⟨t, ht, hE⟩ := choose_rounding h z y hbig
  obtain ⟨hs, hc'⟩ := BHDiagonalLiteral.literal_rounding_step h x y z t hc ht
  exact ⟨t, hs, hc', hE⟩

end Psc.BHDiagonalOuter
