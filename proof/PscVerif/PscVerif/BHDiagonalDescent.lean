import PscVerif.BHDiagonalLiteral

/-!
# Two-step exits from the diagonal resonant pairs

For `r = 3*q`, the pairs `(q-1,q)` and `(q+2,-q)` need not admit a
single energy-decreasing digit. Two admissible digits strictly lower the
quadratic energy. This file does not assert that these are the only
obstructions to single-step decrease.
-/

namespace Psc.BHDiagonalDescent

open Psc.OccurrenceTransport Psc.BHNearDiagonalLiteral
open Psc.BHNearDiagonalDescent

structure BlockParameters (a b q θ : ℝ) : Prop where
  a_pos : 0 < a
  a_small : a < 1/4
  b_large : 48/49 < b
  b_lt_one : b < 1
  q_large : 4 ≤ q
  aq_lower : 3/4 < a*q
  aq_upper : a*q < 1
  dq_lower : 0 < (1-b)*q
  dq_upper : (1-b)*q < 1/12
  theta_large : 1/2 < θ

theorem family_block_parameters {q : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family (3*q) β) :
    BlockParameters (β-(3*q : ℕ)) ((3*q : ℕ)/β) (q : ℝ)
      (((3*q : ℕ)-1)/β) := by
  let a : ℝ := β-(3*q : ℕ)
  let b : ℝ := (3*q : ℕ)/β
  have ha : 0 < a := BHDiagonalLiteral.a_pos h
  have ha' : a < 1/4 := BHDiagonalLiteral.a_small h
  have hb : 48/49 < b := BHDiagonalLiteral.b_large h
  have hb' : b < 1 := BHDiagonalLiteral.b_lt_one h
  have hq : (4 : ℝ) ≤ q := by
    have hq' : 4 ≤ q := by have := h.large; omega
    exact_mod_cast hq'
  have hrel : 3*a*(q : ℝ) = 2+b-a^2 := by
    have hid := BHDiagonalLiteral.a_identity h
    have hae : a = β-3*(q : ℝ) := by dsimp [a]; push_cast; ring
    change a*β = 2+b at hid
    have hmul := congrArg (fun v : ℝ => a*v) hae
    nlinarith only [hid, hmul]
  have haqhi : a*(q : ℝ) < 1 := by
    nlinarith only [hrel, hb', sq_nonneg a]
  have haqlo : 3/4 < a*(q : ℝ) := by
    have hsq := mul_pos ha (sub_pos.mpr ha')
    nlinarith only [hrel, hb, hsq, ha']
  have hdp : 0 < (1-b)*(q : ℝ) := mul_pos (by linarith) (by linarith)
  have hbeta : 0 < β := BHDiagonalLiteral.beta_pos h
  have hprod : ((1-b)*(q : ℝ))*β = a*(q : ℝ) := by
    have hid : (1-b)*β = a := by
      dsimp [a,b]
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hbeta.ne']
    calc
      ((1-b)*(q : ℝ))*β = ((1-b)*β)*(q : ℝ) := by ring
      _ = a*(q : ℝ) := by rw [hid]
  have hdhi : (1-b)*(q : ℝ) < 1/12 := by
    apply lt_of_mul_lt_mul_right _ hbeta.le
    rw [hprod]
    have hr : (12 : ℝ) ≤ (3*q : ℕ) := by exact_mod_cast h.large
    linarith [h.lower]
  exact ⟨ha,ha',hb,hb',hq,haqlo,haqhi,hdp,hdhi,
    (BHDiagonalLiteral.theta_bounds h).1⟩

theorem first_pair_choices {a b q θ : ℝ} (h : BlockParameters a b q θ) :
    |(-q)+(a*q+b*(q-1))| ≤ θ ∧
    |(1-q)+(a*(-q)+b*q)| ≤ θ := by
  have hd : 0 < 1-b := by linarith [h.b_lt_one]
  have hd' : 1-b < 1/49 := by linarith [h.b_large]
  constructor <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [h.aq_lower,h.aq_upper,h.dq_lower,h.dq_upper,h.theta_large]

theorem first_pair_decreases {a b q θ : ℝ} (h : BlockParameters a b q θ) :
    energy a b (-q) (1-q) < energy a b (q-1) q := by
  have hp := mul_pos (show 0 < 1-b by linarith [h.b_lt_one])
    (show 0 < 2*q-1 by linarith [h.q_large])
  have he : energy a b (-q) (1-q) - energy a b (q-1) q =
      -(1-b)*(2*q-1) := by unfold energy; ring
  linarith

theorem second_pair_choices {a b q θ : ℝ} (h : BlockParameters a b q θ) :
    |(-q-1)+(a*(-q)+b*(q+2))| ≤ θ ∧
    |(q+1)+(a*(-q-1)+b*(-q))| ≤ θ := by
  have hd : 0 < 1-b := by linarith [h.b_lt_one]
  have hd' : 1-b < 1/49 := by linarith [h.b_large]
  constructor <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [h.a_pos,h.a_small,h.aq_lower,h.aq_upper,h.dq_lower,h.dq_upper,
      h.theta_large]

theorem second_pair_decreases {a b q θ : ℝ} (h : BlockParameters a b q θ) :
    energy a b (-q-1) (q+1) < energy a b (q+2) (-q) := by
  have he : energy a b (-q-1) (q+1) - energy a b (q+2) (-q) =
      (1-b)*(2*q+3)-2-a := by unfold energy; ring
  have hd' : 1-b < 1/49 := by linarith [h.b_large]
  nlinarith [h.dq_upper,h.a_pos]

/-- Two scalar choices reconstruct the full intermediate and final packets.
The initial first coordinate is arbitrary within the run window. -/
theorem two_selected_steps {r : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family r β) (x y z t u : ℤ)
    (hc : Central r r β (runPacket x y z))
    (ht : |(t : ℝ)+((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β)
    (hu : |(u : ℝ)+((β-r)*t+(r/β)*y)| ≤ ((r : ℝ)-1)/β) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket x y z) (runPacket (t+(r : ℤ)*y) u t) ∧
      Central r r β (runPacket (t+(r : ℤ)*y) u t) := by
  obtain ⟨hs,hc'⟩ := BHDiagonalLiteral.literal_rounding_step h x y z t hc ht
  obtain ⟨hs',hc''⟩ := BHDiagonalLiteral.literal_rounding_step h
    (y+(r : ℤ)*z) t y u hc' hu
  exact ⟨(Relation.ReflTransGen.single hs).tail hs',hc''⟩

theorem first_pair_literal_path {q : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family (3*q) β) (x : ℤ)
    (hc : Central (3*q) (3*q) β (runPacket x q ((q : ℤ)-1))) :
    Relation.ReflTransGen (InteriorStep (sigma (3*q) (3*q)) (lengths (3*q) β))
      (runPacket x q ((q : ℤ)-1))
      (runPacket (-(q : ℤ)+(3*q : ℕ)*(q : ℤ)) (1-(q : ℤ)) (-(q : ℤ))) ∧
      Central (3*q) (3*q) β
        (runPacket (-(q : ℤ)+(3*q : ℕ)*(q : ℤ)) (1-(q : ℤ)) (-(q : ℤ))) := by
  have ht := first_pair_choices (family_block_parameters h)
  apply two_selected_steps h x q ((q : ℤ)-1) (-(q : ℤ)) (1-(q : ℤ)) hc
  · simpa only [Int.cast_neg, Int.cast_sub, Int.cast_natCast, Int.cast_one] using ht.1
  · simpa only [Int.cast_neg, Int.cast_sub, Int.cast_natCast, Int.cast_one] using ht.2

theorem second_pair_literal_path {q : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family (3*q) β) (x : ℤ)
    (hc : Central (3*q) (3*q) β (runPacket x (-(q : ℤ)) ((q : ℤ)+2))) :
    Relation.ReflTransGen (InteriorStep (sigma (3*q) (3*q)) (lengths (3*q) β))
      (runPacket x (-(q : ℤ)) ((q : ℤ)+2))
      (runPacket (-(q : ℤ)-1+(3*q : ℕ)*(-(q : ℤ))) ((q : ℤ)+1) (-(q : ℤ)-1)) ∧
      Central (3*q) (3*q) β
        (runPacket (-(q : ℤ)-1+(3*q : ℕ)*(-(q : ℤ))) ((q : ℤ)+1) (-(q : ℤ)-1)) := by
  have ht := second_pair_choices (family_block_parameters h)
  apply two_selected_steps h x (-(q : ℤ)) ((q : ℤ)+2) (-(q : ℤ)-1) ((q : ℤ)+1) hc
  · simpa only [Int.cast_neg, Int.cast_sub, Int.cast_add, Int.cast_natCast,
      Int.cast_one, Int.cast_ofNat] using ht.1
  · simpa only [Int.cast_neg, Int.cast_sub, Int.cast_add, Int.cast_natCast,
      Int.cast_one, Int.cast_ofNat] using ht.2

end Psc.BHDiagonalDescent
