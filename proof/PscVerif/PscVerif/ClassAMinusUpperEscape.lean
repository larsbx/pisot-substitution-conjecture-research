/-
# Actual exits from the minus-Class-A alternating packets

All transitions use the literal FIRST/RUN marks. Strictness pulls back
along their original ordinal transcript from equal-letter integral zero.
-/
import PscVerif.ClassAMinusUpperRecurrence

namespace Psc.ClassAMinusUpperEscape

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport Matrix
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusCentralBridge
open Psc.ClassAMinusPrefixAssembly Psc.ClassAMinusUpperRecurrence
open Psc.ClassAMinusUpperEntry Psc.ClassAMinusLiteralArithmetic

private def K (n d : ℕ) : ℤ := 2*(n : ℤ)-(d : ℤ)
private def third (n d : ℕ) (p q r : ℤ) : ℤ :=
  (3*(n : ℤ)-K n d)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r

private theorem first_first (n d : ℕ) (a b : Fin 3) (p q r : ℤ) :
    IndexedDigitStep (sigma n d) (packet a b p q r) 0 0
      (packet (first a) (first b) (2*p+q+r) (q+r) (third n d p q r)) := by
  refine ⟨firstMark n d a, firstMark n d b, rfl, rfl, ?_⟩
  apply congrArg (fun v : Fin 3 → ℤ => Packet.mk (first a) (first b) v)
  funext z
  fin_cases z <;>
    simp [packet, incidenceZ, inc, sigma, runLength, first, last, third, K,
      OccurrenceTransport.residual, firstMark, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, List.count_replicate] <;> ring

private theorem first_run (n d : ℕ) (a b : Fin 3) (j : ℤ)
    (hj0 : 1 ≤ j) (hj : j ≤ (runLength n d b : ℤ)) (p q r : ℤ) :
    IndexedDigitStep (sigma n d) (packet a b p q r) 0 j.toNat
      (packet (first a) 2
        (2*p+q+r+(if b=1 then 0 else 1)) (q+r+(if b=1 then 1 else 0))
        (third n d p q r+j-1)) := by
  have hj' : j.toNat-1 < runLength n d b := by omega
  have hindex : j.toNat-1+1 = j.toNat := by omega
  have hcast : ((j.toNat-1 : ℕ) : ℤ) = j-1 := by omega
  refine ⟨firstMark n d a, runMark n d b (j.toNat-1) hj', rfl, ?_, ?_⟩
  · exact (runMark_index n d b (j.toNat-1) hj').trans hindex
  · apply congrArg (fun v : Fin 3 → ℤ => Packet.mk (first a) 2 v)
    funext z
    fin_cases z <;> fin_cases b <;>
      simp [packet, incidenceZ, inc, sigma, runLength, first, last, third, K,
        OccurrenceTransport.residual, parikhZ, firstMark, runMark, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, List.count_replicate, hcast] <;> ring

private theorem run_first (n d : ℕ) (a b : Fin 3) (i : ℤ)
    (hi0 : 1 ≤ i) (hi : i ≤ (runLength n d a : ℤ)) (p q r : ℤ) :
    IndexedDigitStep (sigma n d) (packet a b p q r) i.toNat 0
      (packet 2 (first b)
        (2*p+q+r-(if a=1 then 0 else 1)) (q+r-(if a=1 then 1 else 0))
        (third n d p q r-i+1)) := by
  have hi' : i.toNat-1 < runLength n d a := by omega
  have hindex : i.toNat-1+1 = i.toNat := by omega
  have hcast : ((i.toNat-1 : ℕ) : ℤ) = i-1 := by omega
  refine ⟨runMark n d a (i.toNat-1) hi', firstMark n d b, ?_, rfl, ?_⟩
  · exact (runMark_index n d a (i.toNat-1) hi').trans hindex
  · apply congrArg (fun v : Fin 3 → ℤ => Packet.mk 2 (first b) v)
    funext z
    fin_cases z <;> fin_cases a <;>
      simp [packet, incidenceZ, inc, sigma, runLength, first, last, third, K,
        OccurrenceTransport.residual, parikhZ, firstMark, runMark, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, List.count_replicate, hcast] <;> ring

private theorem run_run (n d : ℕ) (hn : 1 ≤ n) (a b : Fin 3) (i j : ℤ)
    (hi0 : 1 ≤ i) (hi : i ≤ (runLength n d a : ℤ))
    (hj0 : 1 ≤ j) (hj : j ≤ (runLength n d b : ℤ)) (p q r : ℤ) :
    IndexedDigitStep (sigma n d) (packet a b p q r) i.toNat j.toNat
      (packet 2 2 (2*p+q+r-delta a b) (q+r+delta a b)
        (third n d p q r+j-i)) := by
  have hi' : i.toNat-1 < runLength n d a := by omega
  have hj' : j.toNat-1 < runLength n d b := by omega
  have hindexi : i.toNat-1+1 = i.toNat := by omega
  have hindexj : j.toNat-1+1 = j.toNat := by omega
  have hcasti : ((i.toNat-1 : ℕ) : ℤ) = i-1 := by omega
  have hcastj : ((j.toNat-1 : ℕ) : ℤ) = j-1 := by omega
  have he := positive_step n d hn a b (i.toNat-1) (j.toNat-1) hi'.le hj'.le p q r
  have hthird : ((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+(j-1)-(i-1) =
      third n d p q r+j-i := by push_cast; simp only [third, K]; ring
  simpa only [hindexi, hindexj, hcasti, hcastj, hthird,
    positiveMark_letter_of_lt n d a (i.toNat-1) hi',
    positiveMark_letter_of_lt n d b (j.toNat-1) hj'] using he

private abbrev Path (n d : ℕ) := Relation.ReflTransGen (DigitStep (sigma n d))
private def P (H : ℤ) : Packet := packet 0 2 H (3*H+1) (-6*H)
private def Q (H : ℤ) : Packet := packet 2 0 (-H) (1-3*H) (6*H-3)
private def W (H : ℤ) : Packet := packet 2 2 H (3*H) (-6*H)

private theorem unit_base (n d : ℕ) (hn : 9 ≤ n) (hd : n+8 ≤ d) :
    Path n d (P 0) zeroYy := by
  have hn1 : 1 ≤ n := by omega
  have e₁ := run_first n d 0 2 (n+2 : ℤ) (by omega)
    (by simp [runLength]; omega) 0 1 0
  have e₂ := run_run n d hn1 2 0 2 1 (by omega)
    (by simp [runLength]; omega) (by omega) (by simp [runLength]; omega) 0 1 (-1)
  have h₁ : IndexedDigitStep (sigma n d) (P 0) (n+2) 0 (packet 2 0 0 1 (-1)) := by
    convert e₁ using 2 <;> norm_num [P, first, third] <;> omega
  have h₂ : IndexedDigitStep (sigma n d) (packet 2 0 0 1 (-1)) 2 1 zeroYy := by
    convert e₂ using 2 <;> norm_num [zeroYy, delta, third, Nat.cast_sub hn1]
  exact (Relation.ReflTransGen.single h₁.digitStep).tail h₂.digitStep

private theorem unit_transfers (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (H : ℤ) (hH : 1 ≤ H) (hcap : K n d*H ≤ (n : ℤ)-2) :
    ∃ i j, IndexedDigitStep (sigma n d) (P H) i 0 (Q H) ∧
      IndexedDigitStep (sigma n d) (Q H) 0 j (P (H-1)) := by
  have hn1 : 1 ≤ n := by omega
  have hκ : 0 < K n d := by unfold K; omega
  have hm := mul_nonneg hκ.le (show 0 ≤ H by omega)
  let i := (n : ℤ)+4-K n d*H
  let j := 2*(n : ℤ)+4-K n d*H
  have ei := run_first n d 0 2 i (by dsimp [i]; omega)
    (by simp [runLength, i]; omega) H (3*H+1) (-6*H)
  have ej := first_run n d 2 0 j (by dsimp [j]; omega)
    (by simp [runLength, j]; omega) (-H) (1-3*H) (6*H-3)
  refine ⟨i.toNat, j.toNat, ?_, ?_⟩
  · convert ei using 2 <;> simp [P, Q, first, third, Nat.cast_sub hn1, i] <;> ring
  · convert ej using 2 <;> simp [P, Q, first, third, Nat.cast_sub hn1, j] <;> ring

private theorem unit_path (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (H : ℕ) (hcap : K n d*(H : ℤ) ≤ (n : ℤ)-2) :
    Path n d (P (H : ℤ)) zeroYy := by
  induction H with
  | zero => exact unit_base n d (by omega) hd
  | succ H ih =>
    have hr : 0 ≤ K n d := by unfold K; omega
    have hsmall : K n d*(H : ℤ) ≤ (n : ℤ)-2 := by
      exact (mul_le_mul_of_nonneg_left (by omega : (H : ℤ) ≤ (H+1 : ℕ)) hr).trans hcap
    obtain ⟨_,_,e₁,e₂⟩ := unit_transfers n d hd hnd ((H+1 : ℕ) : ℤ) (by omega) hcap
    rw [show (((H+1 : ℕ) : ℤ)-1) = H by omega] at e₂
    exact ((Relation.ReflTransGen.single e₁.digitStep).tail e₂.digitStep).trans (ih hsmall)

private theorem swap_zero {n d : ℕ} {p : Packet} (hp : Path n d p zeroYy) :
    Path n d p.swap zeroYy := by
  simpa [zeroYy, ClassAMinusConstantRecurrence.packet_swap] using
    ClassAMinusConstantRecurrence.digit_path_swap hp

private theorem cycle_large (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (H : ℤ) (hH : 1 ≤ H) (hlo : 4 ≤ K n d*H) (hcap : K n d*H ≤ (n : ℤ)-2) :
    Path n d (W H) zeroYy := by
  have hn1 : 1 ≤ n := by omega
  have e₁ := run_run n d hn1 2 2 1 (K n d*H) (by omega)
    (by simp [runLength]; omega) (by omega) (by simp [runLength]; omega) H (3*H) (-6*H)
  have e₂ := first_run n d 2 2 ((n+3 : ℤ)-K n d*H) (by omega)
    (by simp [runLength]; omega) (-H) (-3*H) (6*H-1)
  have e₁' : IndexedDigitStep (sigma n d) (W H) 1 (K n d*H).toNat
      (packet 2 2 (-H) (-3*H) (6*H-1)) := by
    convert e₁ using 2 <;> simp [W, delta, third, Nat.cast_sub hn1] <;> ring
  have e₂' : IndexedDigitStep (sigma n d) (packet 2 2 (-H) (-3*H) (6*H-1))
      0 ((n+3 : ℤ)-K n d*H).toNat (Q H).swap := by
    rw [show (Q H).swap = packet 0 2 H (3*H-1) (3-6*H) by
      simp only [Q, ClassAMinusConstantRecurrence.packet_swap, neg_neg]
      congr 1 <;> ring]
    convert e₂ using 2 <;> simp [first, third, Nat.cast_sub hn1] <;> ring
  obtain ⟨_,_,_,eq⟩ := unit_transfers n d hd hnd H hH hcap
  have hκ : 0 ≤ K n d := by unfold K; omega
  have hsub : ((H-1).toNat : ℤ) = H-1 := by omega
  have hsmall : K n d*((H-1).toNat : ℤ) ≤ (n : ℤ)-2 := by
    rw [hsub]
    exact (mul_le_mul_of_nonneg_left (by omega : H-1 ≤ H) hκ).trans hcap
  have hs := unit_path n d hd hnd (H-1).toNat hsmall
  rw [hsub] at hs
  exact ((Relation.ReflTransGen.single e₁'.digitStep).tail e₂'.digitStep).trans
    (swap_zero (hs.head eq.digitStep))

private theorem cycle_one_low (n d : ℕ) (hn : 9 ≤ n) (hk : K n d = 1)
    (H : ℤ) (hH : 1 ≤ H) (hH2 : H ≤ 2) : Path n d (W H) zeroYy := by
  have hn1 : 1 ≤ n := by omega
  have hK : (d : ℤ) = 2*(n : ℤ)-1 := by unfold K at hk; omega
  have e₁ := first_first n d 2 2 H (3*H) (-6*H)
  have e₂ := run_run n d hn1 0 0 1 (1+((n : ℤ)+2)*H)
    (by omega) (by simp [runLength]; omega)
    (by interval_cases H <;> omega)
    (by simp [runLength]; interval_cases H <;> omega) (-H) (-3*H) (5*H)
  have e₃ := run_run n d hn1 2 2 (2*H+1) 1 (by omega)
    (by simp [runLength]; omega) (by omega) (by simp [runLength]; omega) 0 (2*H) (-2*H)
  have h₁ : IndexedDigitStep (sigma n d) (W H) 0 0 (packet 0 0 (-H) (-3*H) (5*H)) := by
    convert e₁ using 2 <;> simp [W, first, third, hk, Nat.cast_sub hn1] <;> ring
  have h₂ : IndexedDigitStep (sigma n d) (packet 0 0 (-H) (-3*H) (5*H))
      1 (1+((n : ℤ)+2)*H).toNat (packet 2 2 0 (2*H) (-2*H)) := by
    convert e₂ using 2 <;> simp [delta, third, hk, Nat.cast_sub hn1] <;> ring
  have h₃ : IndexedDigitStep (sigma n d) (packet 2 2 0 (2*H) (-2*H))
      (2*H+1).toNat 1 zeroYy := by
    convert e₃ using 2 <;> simp [zeroYy, delta, third, Nat.cast_sub hn1] <;> ring
  exact ((Relation.ReflTransGen.single h₁.digitStep).tail h₂.digitStep).tail h₃.digitStep

private theorem cycle_two (n d : ℕ) (hn : 9 ≤ n) (hk : K n d = 2) :
    Path n d (W 1) zeroYy := by
  have hn1 : 1 ≤ n := by omega
  have hK : (d : ℤ) = 2*(n : ℤ)-2 := by unfold K at hk; omega
  have e₁ := first_first n d 2 2 1 3 (-6)
  have e₂ := first_run n d 0 0 (2*(n : ℤ)+2) (by omega)
    (by simp [runLength]; omega) (-1) (-3) 4
  have e₃ := run_run n d hn1 0 2 2 1 (by omega)
    (by simp [runLength]; omega) (by omega) (by simp [runLength]; omega) 0 1 (-1)
  have h₁ : IndexedDigitStep (sigma n d) (W 1) 0 0 (packet 0 0 (-1) (-3) 4) := by
    convert e₁ using 2 <;> norm_num [W, first, third, hk, Nat.cast_sub hn1] <;> ring
  have h₂ : IndexedDigitStep (sigma n d) (packet 0 0 (-1) (-3) 4)
      0 (2*(n : ℤ)+2).toNat (packet 0 2 0 1 (-1)) := by
    convert e₂ using 2 <;> norm_num [first, third, hk, Nat.cast_sub hn1] <;> ring
  have h₃ : IndexedDigitStep (sigma n d) (packet 0 2 0 1 (-1)) 2 1 zeroYy := by
    convert e₃ using 2 <;> norm_num [zeroYy, delta, third, Nat.cast_sub hn1] <;> ring
  exact ((Relation.ReflTransGen.single h₁.digitStep).tail h₂.digitStep).tail h₃.digitStep

private theorem cycle_three (n d : ℕ) (hn : 9 ≤ n) (hk : K n d = 3) :
    Path n d (W 1) zeroYy := by
  have hn1 : 1 ≤ n := by omega
  have e₁ := first_run n d 2 2 1 (by omega) (by simp [runLength]; omega) 1 3 (-6)
  have e₂ := run_run n d hn1 0 2 1 4 (by omega)
    (by simp [runLength]; omega) (by omega) (by simp [runLength]; omega) 0 (-3) 3
  have h₁ : IndexedDigitStep (sigma n d) (W 1) 0 1 (packet 0 2 0 (-3) 3) := by
    convert e₁ using 2 <;> norm_num [W, first, third, hk, Nat.cast_sub hn1] <;> ring
  have h₂ : IndexedDigitStep (sigma n d) (packet 0 2 0 (-3) 3) 1 4 zeroYy := by
    convert e₂ using 2 <;> norm_num [zeroYy, delta, third, Nat.cast_sub hn1] <;> ring
  exact (Relation.ReflTransGen.single h₁.digitStep).tail h₂.digitStep

private theorem cycle_one_high (n d : ℕ) (hn : 9 ≤ n) (hk : K n d = 1) :
    Path n d (W 3) zeroYy := by
  have hn1 : 1 ≤ n := by omega
  have hK : (d : ℤ) = 2*(n : ℤ)-1 := by unfold K at hk; omega
  have e₁ := first_run n d 2 2 1 (by omega) (by simp [runLength]; omega) 3 9 (-18)
  have e₂ := first_run n d 0 2 1 (by omega) (by simp [runLength]; omega) (-2) (-9) 15
  have e₃ := run_first n d 0 2 (2*(n : ℤ)) (by omega)
    (by simp [runLength]; omega) 3 6 (-13)
  have e₄ := run_run n d hn1 2 0 1 (2*(n : ℤ)+6) (by omega)
    (by simp [runLength]; omega) (by omega) (by simp [runLength]; omega) (-2) (-7) 11
  have e₅ := run_run n d hn1 2 2 5 1 (by omega)
    (by simp [runLength]; omega) (by omega) (by simp [runLength]; omega) 0 4 (-4)
  have h₁ : IndexedDigitStep (sigma n d) (W 3) 0 1 (packet 0 2 (-2) (-9) 15) := by
    convert e₁ using 2 <;> norm_num [W, first, third, hk, Nat.cast_sub hn1] <;> ring
  have h₂ : IndexedDigitStep (sigma n d) (packet 0 2 (-2) (-9) 15) 0 1
      (packet 0 2 3 6 (-13)) := by
    convert e₂ using 2 <;> norm_num [first, third, hk, Nat.cast_sub hn1] <;> ring
  have h₃ : IndexedDigitStep (sigma n d) (packet 0 2 3 6 (-13)) (2*(n : ℤ)).toNat 0
      (packet 2 0 (-2) (-7) 11) := by
    convert e₃ using 2 <;> norm_num [first, third, hk, Nat.cast_sub hn1] <;> ring
  have h₄ : IndexedDigitStep (sigma n d) (packet 2 0 (-2) (-7) 11) 1
      (2*(n : ℤ)+6).toNat (packet 2 2 0 4 (-4)) := by
    convert e₄ using 2 <;> norm_num [delta, third, hk, Nat.cast_sub hn1] <;> ring
  have h₅ : IndexedDigitStep (sigma n d) (packet 2 2 0 4 (-4)) 5 1 zeroYy := by
    convert e₅ using 2 <;> norm_num [zeroYy, delta, third, Nat.cast_sub hn1] <;> ring
  exact ((((Relation.ReflTransGen.single h₁.digitStep).tail h₂.digitStep).tail
    h₃.digitStep).tail h₄.digitStep).tail h₅.digitStep

private theorem cycle_nonnegative (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (H : ℤ) (hH : 0 ≤ H) (hcap : K n d*H ≤ (n : ℤ)-2) :
    Path n d (W H) zeroYy := by
  by_cases hz : H = 0
  · subst H
    exact .refl
  have hn : 9 ≤ n := by omega
  have hp : 1 ≤ H := by omega
  have hk : 1 ≤ K n d := by unfold K; omega
  by_cases hlarge : 4 ≤ K n d*H
  · exact cycle_large n d hd hnd H hp hlarge hcap
  have hs : K n d*H ≤ 3 := by omega
  have hfirst : K n d ≤ 3 := by
    have hb := mul_le_mul_of_nonneg_left hp (show 0 ≤ K n d by omega)
    linarith
  have hsecond : H ≤ 3 := by
    have hb := mul_le_mul_of_nonneg_right hk hH
    linarith
  rcases (show K n d = 1 ∨ K n d = 2 ∨ K n d = 3 by omega) with hk' | hk' | hk'
  · by_cases hsmall : H ≤ 2
    · exact cycle_one_low n d hn hk' H hp hsmall
    · have he : H = 3 := by omega
      subst H
      exact cycle_one_high n d hn hk'
  · rw [hk'] at hlarge
    have he : H = 1 := by omega
    subst H
    exact cycle_two n d hn hk'
  · rw [hk'] at hlarge
    have he : H = 1 := by omega
    subst H
    exact cycle_three n d hn hk'

/-- Every central integral source in the upper arithmetic region reaches
typed zero by a path of original occurrence pairs. -/
theorem central_to_zero (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (β : ℝ) (hroot : UpperRoot n d β) (z : IntegralState)
    (hc : |shift n β z| ≤ 1/2) :
    ∃ xs, OrderedInteriorPath (sigma n d) (lengths n β) z.toPacket xs zeroYy := by
  obtain ⟨m,H,hH,hcap,hstate⟩ := reaches_alternating n d hd hnd β hroot z
  have hp := selected_path n d hd hnd β hroot z hc (m+1)
  have he := cycle_nonnegative n d hd hnd H hH hcap
  have hf : Path n d z.toPacket zeroYy := by
    rcases hstate with hh | hh
    · rw [hh] at hp
      exact hp.trans he
    · rw [hh] at hp
      have hs := swap_zero he
      simp only [W, ClassAMinusConstantRecurrence.packet_swap] at hs
      have hx : -(3*H) = -3*H := by ring
      have hy : -(-6*H) = 6*H := by ring
      rw [hx, hy] at hs
      exact hp.trans hs
  obtain ⟨xs,hxs⟩ := digit_path_has_ordered_path hf
  have hpos := lengths_upper n d hd hnd β hroot
  have hβ : 0 < β := by linarith [hroot.lower, Nat.cast_nonneg (α := ℝ) n]
  exact ⟨xs, ordered_path_indexed_interior _ _ β hpos hβ
    (scaling_upper n d (by omega) β hβ.ne' hroot.cubic_eq_zero)
    hxs (zero_packet_interior _ hpos 2 2)⟩

/-- The complement closes at literal finite occurrence level. The same
positive bracketed root works for every strict integral source. -/
theorem complement_to_zero (k t : ℕ) (ht : 6 ≤ t) :
    let n := k+t+3
    let d := k+2*t+5
    ∃ β : ℝ, UpperRoot n d β ∧ ∀ p : Packet, p.Interior (lengths n β) →
      ∃ xs, OrderedInteriorPath (sigma n d) (lengths n β) p xs zeroYy := by
  obtain ⟨hd,hnd⟩ := complement_parameters k t ht
  obtain ⟨β,hroot,hentry⟩ := complement_central_entry k t ht
  refine ⟨β,hroot,?_⟩
  intro p hp
  obtain ⟨z,xs,hxs,hc⟩ := hentry p hp
  obtain ⟨ys,hys⟩ := central_to_zero _ _ hd hnd β hroot z hc
  have hpos := lengths_upper _ _ hd hnd β hroot
  have hβ : 0 < β := by linarith [hroot.lower, Nat.cast_nonneg (α := ℝ) (k+t+3)]
  exact ⟨xs ++ ys, ordered_path_indexed_interior _ _ β hpos hβ
    (scaling_upper _ _ (by omega) β hβ.ne' hroot.cubic_eq_zero)
    (hxs.orderedPath.trans hys.orderedPath) (zero_packet_interior _ hpos 2 2)⟩

end Psc.ClassAMinusUpperEscape
