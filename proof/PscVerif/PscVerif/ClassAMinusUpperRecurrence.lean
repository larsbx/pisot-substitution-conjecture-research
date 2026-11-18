/-
# Literal alternating recurrence on the minus-Class-A upper region

The selected orbit runs at original RUN indices and reconstructs all three
coordinates of its eventual alternating packet. The nonzero alternatives
are genuine exit obligations.
-/
import PscVerif.ClassAMinusUpperEntry
import PscVerif.ClassAMinusCentralBridge

namespace Psc.ClassAMinusUpperRecurrence

open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusLiteralArithmetic Psc.ClassAMinusUpperEntry
open Psc.ClassAMinusCentralBridge Psc.ClassAMinusNoHalfUnit Polynomial

/-- The lower-chamber irreducibility argument applies whenever `d < 2*n`.
The evaluation at -1 is the strict upper guard. -/
theorem upper_cubic_irreducible (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n) :
    Irreducible (polyQ n d) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [polyQ_degree]
    decide
  · intro x hx
    have hx' : aeval x (polyZ n d) = 0 := by
      have h0 : eval x (polyQ n d) = 0 := hx
      simpa [polyQ, polyZ, map_ofNat] using h0
    obtain ⟨z, rfl, hz⟩ := exists_integer_of_is_root_of_monic (polyZ_monic n d) hx'
    have hc : (polyZ n d).coeff 0 = 2 := by simp [polyZ]
    rw [hc] at hz
    have he : z^3-((n : ℤ)+2)*z^2+((n : ℤ)-(d : ℤ)-1)*z+2 = 0 := by
      have hh := hx'
      simp [polyZ, map_ofNat] at hh
      exact_mod_cast hh
    have hb : z.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num)
      (Int.natAbs_dvd_natAbs.mpr hz)
    have h1 : -2 ≤ z := by omega
    have h2 : z ≤ 2 := by omega
    have hd' : (n : ℤ)+8 ≤ d := by exact_mod_cast hd
    have hn' : (d : ℤ) < 2*(n : ℤ) := by exact_mod_cast hnd
    interval_cases z <;> norm_num at he <;> omega

private theorem quadratic_zero (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (β : ℝ) (hroot : UpperRoot n d β) (a b c : ℤ)
    (he : (a : ℝ)*β^2+(b : ℝ)*β+(c : ℝ) = 0) : b = 0 := by
  let q : ℚ[X] := C (a : ℚ)*X^2+C (b : ℚ)*X+C (c : ℚ)
  have hqdeg : q.natDegree ≤ 2 := by dsimp [q]; compute_degree!
  have hqev : aeval β q = 0 := by simpa [q] using he
  have hroot' : aeval β (polyQ n d) = 0 := by
    simpa [polyQ, cubic] using hroot.cubic_eq_zero
  have hdvd := ((upper_cubic_irreducible n d hd hnd).dvd_iff_aeval_eq_zero hroot').mp hqev
  have hq : q = 0 := by
    by_contra hne
    have hh := natDegree_le_of_dvd hdvd hne
    rw [polyQ_degree] at hh
    omega
  have hb := congrArg (fun p : ℚ[X] => p.coeff 1) hq
  have hc : (c : ℚ[X]).coeff 1 = 0 := by
    rw [← C_eq_intCast]
    simp only [coeff_C, one_ne_zero, if_false]
  simpa [q, hc] using hb

theorem no_half_unit (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (β : ℝ) (hroot : UpperRoot n d β) : NoHalfUnit n β := by
  intro s
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hβ : β ≠ 0 := ne_of_gt (by linarith [hroot.lower])
  have hh (j : ℤ) : shift n β s ≠ (j : ℝ)+1/2 := by
    intro he
    have hpoly : ((2*s.p : ℤ) : ℝ)*β^2+
        ((2*(s.q+s.r-(n : ℤ)*s.p)-2*j-1 : ℤ) : ℝ)*β+
        ((2*(s.q-s.p) : ℤ) : ℝ) = 0 := by
      unfold shift at he
      push_cast
      field_simp at he
      nlinarith [he]
    have hz := quadratic_zero n d hd hnd β hroot _ _ _ hpoly
    omega
  intro he
  by_cases h : 0 ≤ shift n β s
  · rw [abs_of_nonneg h] at he
    exact hh 0 (by simpa using he)
  · rw [abs_of_neg (lt_of_not_ge h)] at he
    apply hh (-1)
    norm_num only [Int.cast_neg, Int.cast_one]
    linarith

private theorem advance_physical_upper (n d : ℕ) (hn : 1 ≤ n)
    (β : ℝ) (hroot : UpperRoot n d β) (g : ℤ) (s : IntegralState) :
    shift n β (advance n d g s) = β*shift n β s+(g : ℝ) := by
  have hβ : β ≠ 0 := ne_of_gt (by linarith [hroot.lower, Nat.cast_nonneg (α := ℝ) n])
  have hc := hroot.cubic_eq_zero
  dsimp [cubic] at hc
  dsimp [shift, advance]
  push_cast [Nat.cast_sub hn]
  field_simp
  nlinarith [mul_eq_zero_of_left hc (s.p : ℝ)]

theorem advance_central_upper (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (β : ℝ) (hroot : UpperRoot n d β) (s : IntegralState) :
    |shift n β (advance n d (nearestGap n β s) s)| < 1/2 := by
  apply lt_of_le_of_ne
  · rw [advance_physical_upper n d (by omega) β hroot]
    exact nearestGap_error n β s
  · exact no_half_unit n d hd hnd β hroot _

theorem upper_run_step (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (β : ℝ) (hroot : UpperRoot n d β)
    (s : IntegralState) (hs : |shift n β s| < 1/2) :
    IndexedDigitStep (sigma n d) s.toPacket
      ((-nearestGap n β s).toNat+1) ((nearestGap n β s).toNat+1)
      (advance n d (nearestGap n β s) s).toPacket := by
  have hβ : 0 < β := by linarith [hroot.lower, Nat.cast_nonneg (α := ℝ) n]
  have ht := advance_central_upper n d hd hnd β hroot s
  rw [advance_physical_upper n d (by omega) β hroot] at ht
  obtain ⟨hlo, hhi⟩ := ClassACentralRecurrence.central_gap_in_run n
    (by omega) β (shift n β s) hβ hroot.upper hs (nearestGap n β s) ht
  exact ClassACentralRecurrence.run_gap_digit_step n d (by omega)
    s.p s.q s.r (nearestGap n β s) hlo hhi

theorem selected_path (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (β : ℝ) (hroot : UpperRoot n d β)
    (s : IntegralState) (hs : |shift n β s| ≤ 1/2) (k : ℕ) :
    Relation.ReflTransGen (DigitStep (sigma n d)) s.toPacket
      (orbit n d β s k).toPacket := by
  have hc : ∀ m, |shift n β (orbit n d β s m)| < 1/2 := by
    intro m
    cases m with
    | zero => exact lt_of_le_of_ne hs (no_half_unit n d hd hnd β hroot s)
    | succ m => exact advance_central_upper n d hd hnd β hroot _
  induction k with
  | zero => exact .refl
  | succ k ih =>
    exact ih.tail (upper_run_step n d hd hnd β hroot _ (hc k)).digitStep

theorem reserve {n d : ℕ} {β : ℝ} (hroot : UpperRoot n d β) :
    1-(β-((n : ℝ)+2))-2*(1/β) = (2*(n : ℝ)-d)/(β+1) := by
  have hp : 0 < β := by linarith [hroot.lower, Nat.cast_nonneg (α := ℝ) n]
  have hc := hroot.cubic_eq_zero
  unfold cubic at hc
  apply (eq_div_iff (show β+1 ≠ 0 by positivity)).2
  field_simp
  linear_combination -hc

/-- Exact reconstruction of the two signed packets, with the integral
guard required by the escape digits. `H=0` is the typed zero case. -/
theorem reaches_alternating (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (β : ℝ) (hroot : UpperRoot n d β) (s : IntegralState) :
    ∃ N : ℕ, ∃ H : ℤ, 0 ≤ H ∧ (2*(n : ℤ)-(d : ℤ))*H ≤ (n : ℤ)-2 ∧
      (orbit n d β s (N+1) = ⟨H,3*H,-6*H⟩ ∨
       orbit n d β s (N+1) = ⟨-H,-3*H,6*H⟩) := by
  have hn : (9 : ℝ) ≤ n := by exact_mod_cast (show 9 ≤ n by omega)
  have hp : 0 < β := by linarith [hroot.lower]
  have hpos : 0 < 1/β := div_pos (by norm_num) hp
  have hsmall : 1/β < 1/8 := (div_lt_iff₀ hp).2 (by linarith [hroot.lower])
  have hkap : 0 < (2*(n : ℝ)-d)/(β+1) := by
    apply div_pos _ (by positivity)
    have : (d : ℝ) < 2*(n : ℝ) := by exact_mod_cast hnd
    linarith
  have hres := reserve hroot
  let u : ℕ → IntegralState := orbit n d β s
  have hnext (k : ℕ) : (u (k+1)).p = 2*(u k).p+(u k).q+(u k).r := rfl
  have hrec (k : ℕ) :
      |((u (k+2)).p : ℝ)-(2*(1/β)*((u k).p : ℝ)-
        (β-((n : ℝ)+2))*((u (k+1)).p : ℝ))| < 1/2 := by
    have hh : |shift n β (u (k+1))| < 1/2 :=
      advance_central_upper n d hd hnd β hroot (u k)
    have he : shift n β (u (k+1)) =
        ((2*(u (k+1)).p+(u (k+1)).q+(u (k+1)).r : ℤ) : ℝ) -
          (2/β*((u k).p : ℝ)+((n : ℝ)+2-β)*((u (k+1)).p : ℝ)) :=
      advance_recurrence_identity n d β (nearestGap n β (u k)) (u k)
    rw [he] at hh
    rw [hnext (k+1)]
    convert hh using 2 <;> ring
  obtain ⟨N,H,hH,hamp,htail,halt⟩ :=
    ClassACentralRecurrence.eventual_alternating_tail (1/β) (β-((n : ℝ)+2))
      hpos hsmall (sub_pos.mpr hroot.lower) (by linarith only [hres, hkap])
      (fun k => (u k).p) hrec
  have hr : (2*(n : ℝ)-d)*(H : ℝ) < (n : ℝ)-1 := by
    rw [hres, div_mul_eq_mul_div] at hamp
    have hh := (div_lt_iff₀ (show 0 < β+1 by positivity)).mp hamp
    linarith [hroot.upper]
  have hi : (2*(n : ℤ)-(d : ℤ))*H < (n : ℤ)-1 := by exact_mod_cast hr
  refine ⟨N,H,hH,by omega,?_⟩
  have h01 : (u (N+1)).p = -(u N).p := halt 0
  have h12 : (u (N+2)).p = -(u (N+1)).p := halt 1
  have hq : (u (N+1)).q = (u (N+1)).p-2*(u N).p := orbit_second n d β s N
  have hr' : (u (N+2)).p = 2*(u (N+1)).p+(u (N+1)).q+(u (N+1)).r := hnext (N+1)
  change u (N+1) = _ ∨ u (N+1) = _
  rcases htail 1 with h | h
  · left
    apply IntegralState.ext <;> simp only <;> omega
  · right
    apply IntegralState.ext <;> simp only <;> omega

end Psc.ClassAMinusUpperRecurrence
