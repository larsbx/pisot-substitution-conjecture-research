import PscVerif.BHDiagonalClassification
import PscVerif.BHDiagonalDescent
import PscVerif.BHDiagonalOuter

/-!
# Actual diagonal-family residual classification

All arithmetic inputs of the congruence argument are derived here from
`BHDiagonalLiteral.Family`. No finite census or assumed classification is
used. The endpoint classifies the only possible failures of an admissible
one-step energy decrease in the residual disk.
-/

namespace Psc.BHDiagonalClassificationFull

open Psc.BHNearDiagonalDescent Psc.BHDiagonalClassification

private structure Arithmetic (r a b θ s u c : ℝ) : Prop where
  r_large : 12 ≤ r
  a_pos : 0 < a
  a_small : a < 1/4
  b_large : 48/49 < b
  b_lt : b < 1
  theta_large : 1/2 < θ
  theta_lt : θ < 1
  s_large : 4 < s
  u_pos : 0 < u
  u_small : u < 1/12
  c_nonneg : 0 ≤ c
  c_small : c < 1/3
  as_eq : a*s = 1
  au_eq : a*u = 1-b
  ru_eq : r*u = b
  a_eq : a = (2+b)*u
  c_eq : c = a+u
  r_eq : r = 3*s-c
  a_sq : a^2 = (1-b)*(2+b)
  ar_eq : a*r = b*(2+b)
  dr_eq : (1-b)*r = a*b
  gap_eq : 1-θ = (1-b)*(s+1)
  gap_small : 1-θ < a
  ratio : (s+1/3)*u < 3/8
  gap_s : (1-θ)*s < 1/2

private theorem family_arithmetic {r : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family r β) :
    Arithmetic (r : ℝ) (β-r) (r/β) (((r : ℝ)-1)/β)
      (1/(β-r)) (1/β) ((β-r)+1/β) := by
  let a : ℝ := β-r
  let b : ℝ := r/β
  let s : ℝ := 1/a
  let u : ℝ := 1/β
  let c : ℝ := a+u
  let θ : ℝ := ((r : ℝ)-1)/β
  have hr : (12 : ℝ) ≤ r := by exact_mod_cast h.large
  have hβ := BHDiagonalLiteral.beta_pos h
  have ha : 0 < a := BHDiagonalLiteral.a_pos h
  have ha' : a < 1/4 := BHDiagonalLiteral.a_small h
  have hb : 48/49 < b := BHDiagonalLiteral.b_large h
  have hb' : b < 1 := BHDiagonalLiteral.b_lt_one h
  have hu : 0 < u := one_div_pos.mpr hβ
  have hu' : u < 1/12 := by
    apply (div_lt_div_iff₀ (show (0 : ℝ) < β from hβ) (by norm_num : (0 : ℝ)<12)).mpr
    linarith [h.lower]
  have has : a*s = 1 := mul_one_div_cancel ha.ne'
  have hsu : 0 < s := one_div_pos.mpr ha
  have hs : 4 < s := by
    apply (lt_div_iff₀ ha).mpr
    linarith
  have hau : a*u = 1-b := by
    dsimp [a,u,b]
    field_simp [hβ.ne']
  have hru : (r : ℝ)*u = b := by dsimp [u,b]; ring
  have hab : a*β = 2+b := BHDiagonalLiteral.a_identity h
  have hae : a = (2+b)*u := by
    dsimp [u]
    rw [mul_one_div]
    exact (eq_div_iff hβ.ne').mpr hab
  have haq : a^2 = (1-b)*(2+b) := by
    calc
      a^2 = (a*u)*(a*β) := by dsimp [u]; field_simp [hβ.ne']
      _ = (1-b)*(2+b) := by rw [hau,hab]
  have har : a*(r : ℝ) = b*(2+b) := by
    have hr' : (r : ℝ) = β-a := by dsimp [a]; ring
    rw [hr',mul_sub,hab,← pow_two,haq]
    ring
  have hdr : (1-b)*(r : ℝ) = a*b := by
    rw [← hau,← hru]
    ring
  have hds : (1-b)*s = u := by
    calc
      (1-b)*s = (a*s)*u := by rw [← hau]; ring
      _ = u := by rw [has,one_mul]
  have hrid : (r : ℝ) = 3*s-c := by
    apply (mul_left_cancel₀ ha.ne')
    calc
      a*(r : ℝ) = 2+b-a^2 := by
        have he : a*(r : ℝ) = a*β-a^2 := by dsimp [a]; ring
        rw [he,hab]
      _ = a*(3*s-c) := by dsimp [c]; nlinarith only [has,hau]
  have hgap : 1-θ = (1-b)*(s+1) := by
    have he : 1-θ = (1+a)*u := by dsimp [θ,a,u]; field_simp [hβ.ne']; ring
    rw [he,mul_add,mul_one,hds]
    linarith only [hau]
  have hsuid : (s*u)*(2+b) = 1 := by
    calc
      (s*u)*(2+b) = ((2+b)*u)*s := by ring
      _ = 1 := by rw [← hae,has]
  have hsulo : 0 < s*u := mul_pos hsu hu
  have hsuh : s*u < 11/32 := by
    have hp := mul_pos hsulo (show 0 < (2+b)-32/11 by linarith)
    nlinarith only [hp,hsuid]
  have hratio : (s+1/3)*u < 3/8 := by nlinarith only [hsuh,hu']
  have hgap_s : (1-θ)*s < 1/2 := by
    have he : (1-θ)*s = s*u+u := by
      rw [hgap]
      calc
        (1-b)*(s+1)*s = ((1-b)*s)*(s+1) := by ring
        _ = u*(s+1) := by rw [hds]
        _ = s*u+u := by ring
    rw [he]
    linarith
  exact ⟨hr,ha,ha',hb,hb',(BHDiagonalLiteral.theta_bounds h).1,
    (BHDiagonalLiteral.theta_bounds h).2,hs,hu,hu',
    by change 0 ≤ a+u; linarith,
    by change a+u < 1/3; linarith,
    has,hau,hru,hae,rfl,hrid,haq,har,hdr,hgap,
    BHDiagonalLiteral.small_gap h,hratio,hgap_s⟩


private theorem Arithmetic.ds_eq {r a b θ s u c : ℝ}
    (h : Arithmetic r a b θ s u c) : (1-b)*s = u := by
  calc
    (1-b)*s = (a*s)*u := by rw [← h.au_eq]; ring
    _ = u := by rw [h.as_eq,one_mul]

private theorem Arithmetic.du_eq {r a b θ s u c : ℝ}
    (h : Arithmetic r a b θ s u c) : (1-b)*u = 3*u-a := by
  linarith [h.a_eq]

private theorem disk_bounds {r z y : ℝ} (hr : 0 < r)
    (hd : z^2+y^2 < r^2) : |z| < r ∧ |y| < r := by
  constructor
  · apply (sq_lt_sq₀ (abs_nonneg z) hr.le).mp
    rw [sq_abs]
    nlinarith only [hd,sq_nonneg y]
  · apply (sq_lt_sq₀ (abs_nonneg y) hr.le).mp
    rw [sq_abs]
    nlinarith only [hd,sq_nonneg z]

private theorem away_change (a b z y m k : ℝ)
    (hk : (1-b)*k = m-a*y+(1-b)*z) :
    energy a b y (-z-m)-energy a b z y = (1-b)*change k m z y := by
  have he := congrArg (fun v : ℝ => v*(2*z+m)) hk
  unfold energy change
  nlinarith only [he]

private theorem congruence_from_square {r a b θ s u c : ℝ}
    (h : Arithmetic r a b θ s u c) (m q : ℤ) (k z y : ℝ)
    (hm : m = 1 ∨ m = -1)
    (hy : y = (m : ℝ)*s+((q : ℝ)-(m : ℝ)*c)/3)
    (hylo : s-3/2 < (m : ℝ)*y)
    (hk0 : 0 ≤ k) (hkhi : k < s+1)
    (hk : k = z+(m : ℝ)+y*u-(q : ℝ)*s)
    (hnondec : 0 ≤ change k m z y) : q = 0 := by
  rcases hm with hm | hm
  · subst m
    apply congruence_zero_of_nondec q h.s_large.le h.u_pos h.u_small
      h.c_nonneg h.c_small h.ratio
    · simpa using hy
    · simpa using hylo
    · exact hk0
    · exact hkhi
    · simpa using hk
    · simpa using hnondec
  · subst m
    have hksq : k^2 < (s+1)^2 := by
      have hp := mul_pos (show 0 < s+1-k by linarith) (show 0 < s+1+k by linarith [h.s_large])
      nlinarith only [hp]
    have heq := change_congruence_identity k (-1) z y q s u (by simpa using hk)
    have hsquare : (s+1)^2+1/4-(-y)^2-((-(q : ℝ))*s-1/2-(-y)*u)^2 > 0 := by
      norm_num at hnondec heq
      nlinarith only [heq,hnondec,hksq]
    have hyn : -y = s+((-(q : ℝ))-c)/3 := by norm_num at hy; linarith only [hy]
    have hynlo : s-3/2 < -y := by simpa using hylo
    by_contra hq
    have hsplit : 1 ≤ -q ∨ -q ≤ -1 := by omega
    rcases hsplit with hpos | hneg
    · have hqreal : (1 : ℝ) ≤ -(q : ℝ) := by exact_mod_cast hpos
      have hf := positive_congruence_bound h.s_large.le h.u_pos h.u_small
        h.c_nonneg h.c_small h.ratio hqreal hyn
      linarith
    · have hqreal : -(q : ℝ) ≤ -1 := by exact_mod_cast hneg
      have hf := negative_congruence_bound h.s_large.le h.u_pos hqreal hynlo
      linarith


private theorem away_resonant {r : ℕ} {a b θ s u c : ℝ}
    (h : Arithmetic r a b θ s u c) (z y m : ℤ)
    (hdisk : (z : ℝ)^2+(y : ℝ)^2 < (r : ℝ)^2)
    (hy0 : y ≠ 0) (hn : 0 < z+m)
    (he0 : 0 < (m : ℝ)-a*y+(1-b)*z)
    (hehi : (m : ℝ)-a*y+(1-b)*z < 1-θ)
    (hnondec : energy a b z y ≤ energy a b y (-(z : ℝ)-m)) :
    ∃ N : ℕ, r = 3*N ∧
      ((z = (N : ℤ)-1 ∧ y = N) ∨ (z = (N : ℤ)+2 ∧ y = -(N : ℤ))) := by
  let d : ℝ := 1-b
  let e : ℝ := (m : ℝ)-a*y+d*z
  let k : ℝ := e/d
  let q : ℤ := 3*y-m*(r : ℤ)
  have hd : 0 < d := by dsimp [d]; linarith [h.b_lt]
  have he : 0 < e := he0
  have he' : e < 1-θ := hehi
  have hdk : d*k = e := by dsimp [k]; field_simp [hd.ne']
  have hk0 : 0 < k := div_pos he hd
  have hkhi : k < s+1 := (div_lt_iff₀ hd).mpr (by simpa [d,mul_comm] using he'.trans_eq h.gap_eq)
  have heenergy := away_change a b z y m k hdk
  have hchange : 0 ≤ change k m z y := by
    by_contra hh
    have hp := mul_neg_of_pos_of_neg hd (lt_of_not_ge hh)
    dsimp [d] at hp
    linarith only [hp,hnondec,heenergy]
  have hbounds := disk_bounds (show (0 : ℝ) < r by linarith [h.r_large]) hdisk
  have hzu : |(z : ℝ)*u| < 1 := by
    rw [abs_mul,abs_of_pos h.u_pos]
    calc
      |(z : ℝ)| * u < (r : ℝ)*u := mul_lt_mul_of_pos_right hbounds.1 h.u_pos
      _ = b := h.ru_eq
      _ < 1 := h.b_lt
  have hzul := (abs_lt.mp hzu).1
  have hzuh := (abs_lt.mp hzu).2
  have hes : 0 < e*s := mul_pos he (by linarith [h.s_large])
  have hes' : e*s < 1/2 :=
    (mul_lt_mul_of_pos_right he' (by linarith [h.s_large])).trans h.gap_s
  have hyes : e*s = (m : ℝ)*s-(y : ℝ)+(z : ℝ)*u := by
    calc
      e*s = (m : ℝ)*s-(a*s)*(y : ℝ)+(d*s)*(z : ℝ) := by dsimp [e]; ring
      _ = (m : ℝ)*s-(y : ℝ)+(z : ℝ)*u := by rw [h.as_eq,show d*s = u from h.ds_eq]; ring
  have hylo : -3/2 < (y : ℝ)-(m : ℝ)*s := by linarith only [hyes,hzul,hes']
  have hyhi : (y : ℝ)-(m : ℝ)*s < 1 := by linarith only [hyes,hzuh,hes]
  have har : a*(r : ℝ) < 3 := by
    rw [h.ar_eq]
    have hp := mul_pos (show 0 < 1-b by linarith [h.b_lt])
      (show 0 < 1+b by linarith [h.b_large])
    nlinarith only [hp,h.b_lt]
  have hdr : d*(r : ℝ) < 1/4 := by
    calc
      d*(r : ℝ) = a*b := h.dr_eq
      _ < a*1 := mul_lt_mul_of_pos_left h.b_lt h.a_pos
      _ < 1/4 := by simpa using h.a_small
  have hg : |a*(y : ℝ)-d*(z : ℝ)| < 13/4 := by
    calc
      |a*(y : ℝ)-d*(z : ℝ)| ≤ |a*(y : ℝ)|+|d*(z : ℝ)| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (a*(y : ℝ)) 0 (d*(z : ℝ))
      _ = a* |(y : ℝ)|+d* |(z : ℝ)| := by rw [abs_mul,abs_mul,abs_of_pos h.a_pos,abs_of_pos hd]
      _ < a*(r : ℝ)+d*(r : ℝ) := add_lt_add
        (mul_lt_mul_of_pos_left hbounds.2 h.a_pos) (mul_lt_mul_of_pos_left hbounds.1 hd)
      _ < 13/4 := by linarith
  have hml : (-4 : ℝ) < m := by
    have hg' := (abs_lt.mp hg).1
    dsimp [e] at he
    linarith only [hg',he]
  have hmh : (m : ℝ) < 4 := by
    have hg' := (abs_lt.mp hg).2
    have he'' : e < 1/4 := he'.trans (h.gap_small.trans h.a_small)
    dsimp [e] at he''
    linarith only [hg',he'']
  have hml' : -4 < m := by exact_mod_cast hml
  have hmh' : m < 4 := by exact_mod_cast hmh
  have hmabs : (-3 : ℝ) ≤ m ∧ (m : ℝ) ≤ 3 := by
    constructor
    · exact_mod_cast (show -3 ≤ m by omega)
    · exact_mod_cast (show m ≤ 3 by omega)
  have hmsq : (m : ℝ)^2 ≤ 9 := by
    have hp := mul_nonneg (show 0 ≤ (m : ℝ)+3 by linarith [hmabs.1])
      (show 0 ≤ 3-(m : ℝ) by linarith [hmabs.2])
    nlinarith only [hp]
  have hksq : k^2 < (s+1)^2 := by
    have hp := mul_pos (show 0 < s+1-k by linarith) (show 0 < s+1+k by linarith [h.s_large])
    nlinarith only [hp]
  have hysq : (y : ℝ)^2 < (s+1)^2+9/4 := by
    have hsquare := change_completed_square k m z y
    nlinarith only [hchange,hsquare,hksq,hmsq,sq_nonneg ((z : ℝ)+(m : ℝ)/2-k)]
  have hsmallm : -1 ≤ m ∧ m ≤ 1 := by
    by_contra hnot
    have hsplit : 2 ≤ m ∨ m ≤ -2 := by omega
    have hgap : (s+1)^2+9/4 < (2*s-3/2)^2 := by
      nlinarith [h.s_large,sq_nonneg (s-4)]
    rcases hsplit with hp | hn
    · have hpr : (2 : ℝ) ≤ m := by exact_mod_cast hp
      have hmul := mul_le_mul_of_nonneg_right hpr (show 0 ≤ s by linarith [h.s_large])
      have hy : 2*s-3/2 < (y : ℝ) := by linarith only [hylo,hmul]
      have hprod := mul_pos (show 0 < (y : ℝ)-(2*s-3/2) by linarith)
        (show 0 < (y : ℝ)+(2*s-3/2) by linarith [h.s_large])
      nlinarith only [hprod,hgap,hysq]
    · have hnr : (m : ℝ) ≤ -2 := by exact_mod_cast hn
      have hmul := mul_le_mul_of_nonneg_right hnr (show 0 ≤ s by linarith [h.s_large])
      have hy : (y : ℝ) < -(2*s-3/2) := by linarith only [hyhi,hmul]
      have hprod := mul_pos (show 0 < -(y : ℝ)-(2*s-3/2) by linarith)
        (show 0 < -(y : ℝ)+(2*s-3/2) by linarith [h.s_large])
      nlinarith only [hprod,hgap,hysq]
  have hmzero : m ≠ 0 := by
    intro hm
    have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
    have hzu0 := mul_pos hzpos h.u_pos
    have hyrlo : (-1 : ℝ) < y := by norm_num [hm] at hyes; linarith only [hyes,hzu0,hes']
    have hyrhi : (y : ℝ) < 1 := by norm_num [hm] at hyhi; exact hyhi
    have hyil : -1 < y := by exact_mod_cast hyrlo
    have hyih : y < 1 := by exact_mod_cast hyrhi
    exact hy0 (by omega)
  have hm : m = 1 ∨ m = -1 := by omega
  have hq : (q : ℝ) = 3*(y : ℝ)-(m : ℝ)*(r : ℝ) := by dsimp [q]; push_cast; ring
  have hk : k = (z : ℝ)+(m : ℝ)+(y : ℝ)*u-(q : ℝ)*s := by
    apply (mul_left_cancel₀ hd.ne')
    rw [hdk]
    calc
      e = d*(z : ℝ)+d*(m : ℝ)+(3*u-a)*(y : ℝ)-u*(q : ℝ) := by
        rw [hq]
        have hru := congrArg (fun v : ℝ => v*(m : ℝ)) h.ru_eq
        dsimp [e,d]
        nlinarith only [hru]
      _ = d*((z : ℝ)+(m : ℝ)+(y : ℝ)*u-(q : ℝ)*s) := by
        have hds := h.ds_eq
        have hdu := h.du_eq
        change d*s = u at hds
        change d*u = 3*u-a at hdu
        calc
          d*(z : ℝ)+d*(m : ℝ)+(3*u-a)*(y : ℝ)-u*(q : ℝ) =
              d*(z : ℝ)+d*(m : ℝ)+(d*u)*(y : ℝ)-(d*s)*(q : ℝ) := by rw [hdu,hds]
          _ = d*((z : ℝ)+(m : ℝ)+(y : ℝ)*u-(q : ℝ)*s) := by ring
  have hyrel : (y : ℝ) = (m : ℝ)*s+((q : ℝ)-(m : ℝ)*c)/3 := by
    rw [hq,h.r_eq]
    ring
  have hymlo : s-3/2 < (m : ℝ)*(y : ℝ) := by
    rcases hm with hh | hh <;> norm_num [hh] at hylo hyhi ⊢ <;> linarith
  have hqzero : q = 0 := congruence_from_square h m q k z y hm hyrel hymlo hk0.le hkhi hk hchange
  have hqy : 3*y = m*(r : ℤ) := by dsimp [q] at hqzero; omega
  -- Convert the two remaining congruence cases to literal integer shapes.
  rcases hm with hm | hm
  · subst m
    have hr3 : (r : ℝ) = 3*(y : ℝ) := by exact_mod_cast (show (r : ℤ) = 3*y by omega)
    have hyfour : (4 : ℝ) ≤ y := by linarith [h.r_large]
    have hypos : 0 ≤ y := by exact_mod_cast (show (0 : ℝ) ≤ y by linarith)
    let N := y.toNat
    have hNy : (N : ℤ) = y := Int.toNat_of_nonneg hypos
    have hrN : r = 3*N := by exact_mod_cast (show (r : ℤ) = 3*(N : ℤ) by omega)
    have hyu : (y : ℝ)*u = b/3 := by
      have hp := congrArg (fun v : ℝ => v*u) hr3
      nlinarith only [hp,h.ru_eq]
    have hsr : s = (y : ℝ)+c/3 := by linarith only [h.r_eq,hr3]
    have hk' : k = (z : ℝ)+1+b/3 := by simpa [hqzero,hyu] using hk
    have hzlo : 0 ≤ z := by omega
    have hzupper : (z : ℝ) < y := by
      have hcb : c < b := by linarith [h.c_small,h.b_large]
      linarith only [hkhi,hk',hsr,hcb]
    have hzupper' : z < y := by exact_mod_cast hzupper
    have hshape : z = y-1 := by
      by_contra hh
      have hzy : z ≤ y-2 := by omega
      have hzreal : (0 : ℝ) ≤ z := by exact_mod_cast hzlo
      have hzyreal : (z : ℝ) ≤ (y : ℝ)-2 := by exact_mod_cast hzy
      let C : ℝ := 1+b/3
      have hC : 1 < C ∧ C < 4/3 := by dsimp [C]; constructor <;> linarith [h.b_large,h.b_lt]
      have hprod := mul_nonneg (show 0 ≤ (y : ℝ)-2-z by linarith)
        (show 0 ≤ (y : ℝ)-2+z+2*C by linarith)
      have hscale := mul_nonneg (show 0 ≤ 4-2*C by linarith)
        (show 0 ≤ (y : ℝ)-4 by linarith)
      have heq : change k 1 z y = (z : ℝ)^2+2*C*z+C-(y : ℝ)^2 := by
        unfold change
        rw [hk']
        dsimp [C]
        ring
      norm_num at hchange
      nlinarith only [hchange,heq,hprod,hscale,hC.1,hC.2]
    exact ⟨N,hrN,Or.inl ⟨by omega,by omega⟩⟩
  · subst m
    have hr3 : (r : ℝ) = -3*(y : ℝ) := by exact_mod_cast (show (r : ℤ) = -3*y by omega)
    have hyfour : (4 : ℝ) ≤ -(y : ℝ) := by linarith [h.r_large]
    have hypos : 0 ≤ -y := by exact_mod_cast (show (0 : ℝ) ≤ -(y : ℝ) by linarith)
    let N := (-y).toNat
    have hNy : (N : ℤ) = -y := Int.toNat_of_nonneg hypos
    have hrN : r = 3*N := by exact_mod_cast (show (r : ℤ) = 3*(N : ℤ) by omega)
    have hyu : (y : ℝ)*u = -b/3 := by
      have hp := congrArg (fun v : ℝ => v*u) hr3
      nlinarith only [hp,h.ru_eq]
    have hsr : s = -(y : ℝ)+c/3 := by linarith only [h.r_eq,hr3]
    have hk' : k = (z : ℝ)-1-b/3 := by
      have ht := hk
      norm_num [hqzero,hyu] at ht
      linarith only [ht]
    have hzlo : (1 : ℝ) < z := by linarith [hk0,hk',h.b_large]
    have hzlo' : 2 ≤ z := by
      have hi : 1 < z := by exact_mod_cast hzlo
      omega
    have hzupper : (z : ℝ) < -(y : ℝ)+3 := by linarith [hkhi,hk',hsr,h.c_small,h.b_lt]
    have hzupper' : z < -y+3 := by exact_mod_cast hzupper
    have hshape : z = -y+2 := by
      by_contra hh
      have hzy : z ≤ -y+1 := by omega
      have hzreal : (2 : ℝ) ≤ z := by exact_mod_cast hzlo'
      have hzyreal : (z : ℝ) ≤ -(y : ℝ)+1 := by exact_mod_cast hzy
      let C : ℝ := 1+b/3
      have hC : 1 < C ∧ C < 4/3 := by dsimp [C]; constructor <;> linarith [h.b_large,h.b_lt]
      have hprod := mul_nonneg (show 0 ≤ -(y : ℝ)+1-z by linarith)
        (show 0 ≤ -(y : ℝ)+1+z-2*C by linarith)
      have hscale := mul_pos (show 0 < C-1 by linarith)
        (show 0 < -2*(y : ℝ)+1 by linarith)
      have heq : change k (-1) z y = (z : ℝ)^2-2*C*z+C-(y : ℝ)^2 := by
        unfold change
        rw [hk']
        dsimp [C]
        ring
      norm_num at hchange
      nlinarith only [hchange,heq,hprod,hscale]
    exact ⟨N,hrN,Or.inr ⟨by omega,by omega⟩⟩


/-- With the recurrence oriented to nonnegative scalar offset, the only
nonaxis failures of one-step descent are the two positive-frame shapes. -/
theorem nonnegative_residual_classification {r : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family r β) (z y : ℤ)
    (hdisk : (z : ℝ)^2+(y : ℝ)^2 < (r : ℝ)^2) (hy0 : y ≠ 0)
    (hw : 0 ≤ (β-r)*(y : ℝ)+(r/β)*(z : ℝ)) :
    (∃ t : ℤ, |(t : ℝ)+((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β ∧
      energy (β-r) (r/β) y t < energy (β-r) (r/β) z y) ∨
    ∃ N : ℕ, r = 3*N ∧
      ((z = (N : ℤ)-1 ∧ y = N) ∨ (z = (N : ℤ)+2 ∧ y = -(N : ℤ))) := by
  let a : ℝ := β-r
  let b : ℝ := r/β
  let θ : ℝ := ((r : ℝ)-1)/β
  let w : ℝ := a*y+b*z
  let n : ℤ := ⌊w⌋
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Int.floor_nonneg.mpr hw)
  have hnw : (n : ℝ) ≤ w := Int.floor_le w
  have hwn : w < (n : ℝ)+1 := Int.lt_floor_add_one w
  by_cases ht : w-(n : ℝ) ≤ θ
  · refine Or.inl ⟨-n,?_,?_⟩
    · push_cast
      rw [abs_of_nonneg (by change 0 ≤ -(n : ℝ)+w; linarith)]
      change -(n : ℝ)+w ≤ θ
      linarith
    · have hne : (z : ℝ) ≠ 0 ∨ (y : ℝ) ≠ 0 := Or.inr (by exact_mod_cast hy0)
      simpa only [Int.cast_neg] using
        BHDiagonalOuter.truncate_decreases h z y n hn0 hnw hne
  let m : ℤ := n+1-z
  have hmcast : (m : ℝ) = (n : ℝ)+1-(z : ℝ) := by dsimp [m]; push_cast; ring
  have he0 : 0 < (m : ℝ)-a*y+(1-b)*z := by
    rw [hmcast]
    dsimp [w] at hwn
    linarith only [hwn]
  have hehi : (m : ℝ)-a*y+(1-b)*z < 1-θ := by
    rw [hmcast]
    dsimp [w] at ht
    linarith only [lt_of_not_ge ht]
  have hn : 0 < z+m := by
    have hni : 0 ≤ n := by exact_mod_cast hn0
    dsimp [m]
    omega
  have hadmissible : |((-(z+m) : ℤ) : ℝ)+(a*y+b*z)| ≤ θ := by
    push_cast
    apply abs_le.mpr
    constructor <;> linarith only [he0,hehi,(BHDiagonalLiteral.theta_bounds h).1]
  by_cases hdec : energy a b y (-(z : ℝ)-m) < energy a b z y
  · refine Or.inl ⟨-(z+m),hadmissible,?_⟩
    push_cast
    simpa only [a,b,sub_eq_add_neg,neg_add_rev,add_comm] using hdec
  exact Or.inr (away_resonant (family_arithmetic h) z y m hdisk hy0 hn he0 hehi
    (le_of_not_gt hdec))

/-- Actual-family residual classification. The only alternatives to an
admissible one-step strict quadratic decrease are the axis and the four
signed resonant pairs, with the parameter equality retained. -/
theorem residual_classification {r : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family r β) (z y : ℤ)
    (hdisk : (z : ℝ)^2+(y : ℝ)^2 < (r : ℝ)^2) :
    (∃ t : ℤ, |(t : ℝ)+((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β ∧
      energy (β-r) (r/β) y t < energy (β-r) (r/β) z y) ∨
    y = 0 ∨
    ∃ N : ℕ, r = 3*N ∧
      ((z = (N : ℤ)-1 ∧ y = N) ∨
       (z = (N : ℤ)+2 ∧ y = -(N : ℤ)) ∨
       (z = 1-(N : ℤ) ∧ y = -(N : ℤ)) ∨
       (z = -(N : ℤ)-2 ∧ y = N)) := by
  by_cases hy0 : y = 0
  · exact Or.inr (Or.inl hy0)
  by_cases hw : 0 ≤ (β-r)*(y : ℝ)+(r/β)*(z : ℝ)
  · rcases nonnegative_residual_classification h z y hdisk hy0 hw with hstep | hres
    · exact Or.inl hstep
    · obtain ⟨N,hrN,hshape⟩ := hres
      refine Or.inr (Or.inr ⟨N,hrN,?_⟩)
      rcases hshape with h₁ | h₂
      · exact Or.inl h₁
      · exact Or.inr (Or.inl h₂)
  · have hdneg : ((-z : ℤ) : ℝ)^2+((-y : ℤ) : ℝ)^2 < (r : ℝ)^2 := by simpa using hdisk
    have hyneg : -y ≠ 0 := by simpa using hy0
    have hwneg : 0 ≤ (β-r)*((-y : ℤ) : ℝ)+(r/β)*((-z : ℤ) : ℝ) := by
      push_cast
      linarith
    rcases nonnegative_residual_classification h (-z) (-y) hdneg hyneg hwneg with hstep | hres
    · obtain ⟨t,ht,he⟩ := hstep
      refine Or.inl ⟨-t,?_,?_⟩
      · push_cast at ht ⊢
        have hi : -(t : ℝ)+((β-r)*y+(r/β)*z) =
            -((t : ℝ)+((β-r)*(-(y : ℝ))+(r/β)*(-(z : ℝ)))) := by ring
        rw [hi,abs_neg]
        exact ht
      · push_cast at he ⊢
        unfold energy at he ⊢
        nlinarith only [he]
    · obtain ⟨N,hrN,hshape⟩ := hres
      refine Or.inr (Or.inr ⟨N,hrN,?_⟩)
      rcases hshape with h₁ | h₂
      · exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega,by omega⟩))

end Psc.BHDiagonalClassificationFull
