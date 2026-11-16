/-
# The upper plus-Class-A central recurrence

The cubic/root hypotheses are explicit.  The forward integer bound is
derived from both initial coordinates, using ordinary contraction for
J >= 5 and a sheared box for J <= 4.  A selected recurrence is not a zero
hit; arbitrary-source central entry and productive occurrence exits remain
separate interfaces.

Pre-code gate: docs/bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md.
-/
import PscVerif.ClassAPlusUpperCycles

namespace Psc.ClassAPlusUpperRecurrence

abbrev Nearest := ClassAPlusConstantRecurrence.Nearest

noncomputable def A (β : ℝ) : ℝ := 2 / β
def C (n : ℕ) (β : ℝ) : ℝ := β - ((n : ℝ) + 4)
noncomputable def V (n : ℕ) (β : ℝ) : ℝ := 1 + A β - C n β

/-- The actual upper family, expressed without truncated natural subtraction. -/
structure Family (n J : ℕ) (β : ℝ) : Prop where
  n_lower : 7 ≤ n
  J_lower : 1 ≤ J
  J_upper : J ≤ n + 7
  root_lower : (n : ℝ) + 4 < β
  root_upper : β < (n : ℝ) + 6
  root_eq : β^3 - ((n : ℝ)+4)*β^2 + ((J : ℝ)-(n : ℝ)-7)*β - 2 = 0

theorem Family.beta_gt_eleven {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    11 < β := by
  have hn : (7 : ℝ) ≤ n := by exact_mod_cast hp.n_lower
  linarith [hp.root_lower]

theorem Family.beta_pos {n J : ℕ} {β : ℝ} (hp : Family n J β) : 0 < β :=
  lt_trans (by norm_num) hp.beta_gt_eleven

theorem Family.A_pos {n J : ℕ} {β : ℝ} (hp : Family n J β) : 0 < A β :=
  div_pos (by norm_num) hp.beta_pos

theorem Family.A_lt_quarter {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    A β < 1/4 := by
  unfold A
  apply (div_lt_iff₀ hp.beta_pos).2
  linarith [hp.beta_gt_eleven]

theorem Family.A_mul_beta {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    A β * β = 2 := by
  simp [A, ne_of_gt hp.beta_pos]

theorem Family.C_pos {n J : ℕ} {β : ℝ} (hp : Family n J β) : 0 < C n β := by
  unfold C
  linarith [hp.root_lower]

/-- The reserve identity is derived from the actual cubic, not a supplied
floating-point approximation or an abstract stability assumption. -/
theorem Family.reserve_identity {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    V n β = (J : ℝ) / (β+1) := by
  have hb : β ≠ 0 := ne_of_gt hp.beta_pos
  have hb1 : β+1 ≠ 0 := by linarith [hp.beta_pos]
  unfold V A C
  field_simp
  nlinarith [hp.root_eq]

theorem Family.V_pos {n J : ℕ} {β : ℝ} (hp : Family n J β) : 0 < V n β := by
  rw [hp.reserve_identity]
  have hJ : (0 : ℝ) < J := by exact_mod_cast hp.J_lower
  exact div_pos hJ (by linarith [hp.beta_pos])

theorem Family.reserve_scale {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    1 < V n β * ((n : ℝ)+7) := by
  rw [hp.reserve_identity, div_mul_eq_mul_div]
  apply (lt_div_iff₀ (show 0 < β+1 by linarith [hp.beta_pos])).2
  have hJ : (1 : ℝ) ≤ J := by exact_mod_cast hp.J_lower
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [hp.root_upper, mul_nonneg (sub_nonneg.mpr hJ) (show 0 ≤ (n : ℝ)+7 by positivity)]

/-- For J >= 5 the absolute coefficient sum contracts, with an explicit
rounding reserve large enough for the displayed initial-data box. -/
theorem Family.high_contraction {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (hJ : 5 ≤ J) :
    A β + C n β < 1 ∧ 1/2 < (1-A β-C n β)*((n : ℝ)+7) := by
  have hv : V n β * (β+1) = (J : ℝ) := by
    rw [hp.reserve_identity]
    exact div_mul_cancel₀ _ (by linarith [hp.beta_pos])
  have ha := hp.A_mul_beta
  have hj : (5 : ℝ) ≤ J := by exact_mod_cast hJ
  have hid : (1-A β-C n β)*(β+1) = (J : ℝ)-4-2*A β := by
    dsimp [V] at hv
    nlinarith [ha]
  have hprod : 1/2 < (1-A β-C n β)*(β+1) := by
    rw [hid]
    linarith [hp.A_lt_quarter]
  have hpos : 0 < 1-A β-C n β := by
    by_contra hh
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh)
      (show 0 ≤ β+1 by linarith [hp.beta_pos])
    linarith
  constructor
  · linarith
  · nlinarith [mul_pos hpos (show 0 < (n : ℝ)+7-(β+1) by linarith [hp.root_upper])]

/-- The small-J family has nonnegative sheared coefficients.  Its stronger
separation also places it in the strict cyclic-energy classification branch. -/
theorem Family.low_shear {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (hJ : J ≤ 4) : 1/2 + 2*A β < C n β ∧ 3*A β < C n β := by
  have hj : (J : ℝ) ≤ 4 := by exact_mod_cast hJ
  have hvsmall : V n β < 1/3 := by
    rw [hp.reserve_identity]
    apply (div_lt_iff₀ (show 0 < β+1 by linarith [hp.beta_pos])).2
    linarith [hp.beta_gt_eleven]
  have hn : (7 : ℝ) ≤ n := by exact_mod_cast hp.n_lower
  have hb : (23 : ℝ)/2 < β := by
    dsimp [V, C] at hvsmall
    linarith [hp.A_pos]
  have ha : A β < 4/23 := by
    unfold A
    apply (div_lt_iff₀ hp.beta_pos).2
    linarith
  have hv : V n β < 8/25 := by
    rw [hp.reserve_identity]
    apply (div_lt_iff₀ (show 0 < β+1 by linarith [hp.beta_pos])).2
    linarith
  dsimp [V] at hv
  constructor <;> linarith [hp.A_lt_quarter]

/-- The box retains both initial integer coordinates. -/
def initialBound (n : ℕ) (a b : ℤ) : ℤ :=
  ((n : ℤ)+7) * (|a|+|b|+1)

theorem initial_bound_covers (n : ℕ) (hn : 7 ≤ n) (a b : ℤ) :
    |a| ≤ initialBound n a b ∧ |b| ≤ initialBound n a b ∧
    |2*b-a| ≤ initialBound n a b ∧ (n : ℤ)+7 ≤ initialBound n a b := by
  have hn' : (7 : ℤ) ≤ n := by exact_mod_cast hn
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hsum : 0 ≤ |a|+|b|+1 := by omega
  have htwo : 2*(|a|+|b|+1) ≤ initialBound n a b :=
    mul_le_mul_of_nonneg_right (by omega) hsum
  have hs : |2*b-a| ≤ 2*|b|+|a| := by
    calc
      |2*b-a| ≤ |2*b|+|a| := abs_sub _ _
      _ = 2*|b|+|a| := by norm_num [abs_mul]
  have hbase : (n : ℤ)+7 ≤ initialBound n a b := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ |a|+|b|+1 by omega)
      (show 0 ≤ (n : ℤ)+7 by omega)
    simpa [initialBound] using hh
  exact ⟨by omega, by omega, by omega, hbase⟩

/-- Elementary finite sheared-box invariant.  No spectral-radius, impulse
kernel, bounded-orbit or finite-graph assumption occurs here. -/
theorem shear_bound (A C B : ℝ) (hA : 0 ≤ A)
    (hshear : 1/2+2*A ≤ C) (hreserve : 1 ≤ 2*(1+A-C)*B)
    (u : ℕ → ℤ) (hrec : ∀ k, Nearest A C (u k) (u (k+1)) (u (k+2)))
    (hzero : |(u 0 : ℝ)| ≤ B)
    (hszero : |2*(u 1 : ℝ)-(u 0 : ℝ)| ≤ B) :
    ∀ k, |(u k : ℝ)| ≤ B := by
  have hleft : 0 ≤ C-1/2-2*A := by linarith
  have hright : 0 ≤ C-1/2 := by linarith
  have pair : ∀ k, |(u k : ℝ)| ≤ B ∧ |2*(u (k+1) : ℝ)-(u k : ℝ)| ≤ B := by
    intro k
    induction k with
    | zero => exact ⟨hzero, hszero⟩
    | succ k ih =>
      obtain ⟨hxlo, hxhi⟩ := abs_le.mp ih.1
      obtain ⟨hylo, hyhi⟩ := abs_le.mp ih.2
      have hn : |(u (k+1) : ℝ)| ≤ B := by
        apply abs_le.mpr
        constructor <;> linarith
      have he := hrec k
      change |(u (k+2) : ℝ)-(-A*(u k : ℝ)+C*(u (k+1) : ℝ))| < 1/2 at he
      obtain ⟨helo, hehi⟩ := abs_lt.mp he
      have hs : |2*(u (k+2) : ℝ)-(u (k+1) : ℝ)| ≤ B := by
        apply abs_le.mpr
        constructor
        · nlinarith [mul_nonneg hleft (show 0 ≤ (u k : ℝ)+B by linarith),
            mul_nonneg hright (show 0 ≤ 2*(u (k+1) : ℝ)-(u k : ℝ)+B by linarith)]
        · nlinarith [mul_nonneg hleft (show 0 ≤ B-(u k : ℝ) by linarith),
            mul_nonneg hright (show 0 ≤ B-(2*(u (k+1) : ℝ)-(u k : ℝ)) by linarith)]
      exact ⟨hn, by simpa [Nat.add_assoc] using hs⟩
  exact fun k => (pair k).1

/-- Complete actual-family forward bound, derived from both initial values.
The integer bound is valid for every recurrence index. -/
theorem family_forward_bound (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (u : ℕ → ℤ)
    (hrec : ∀ k, Nearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) :
    ∀ k, |u k| ≤ initialBound n (u 0) (u 1) := by
  let B := initialBound n (u 0) (u 1)
  obtain ⟨hzero, hone, hszero, hbase⟩ := initial_bound_covers n hp.n_lower (u 0) (u 1)
  have hz : |(u 0 : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hzero
  have ho : |(u 1 : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hone
  have hs : |2*(u 1 : ℝ)-(u 0 : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hszero
  have hb : (n : ℝ)+7 ≤ (B : ℝ) := by exact_mod_cast hbase
  have bound : ∀ k, |(u k : ℝ)| ≤ (B : ℝ) := by
    by_cases hJ : 5 ≤ J
    · obtain ⟨hc, hr⟩ := hp.high_contraction hJ
      have hparams : ClassAPlusConstantRecurrence.Parameters (A β) (C n β) :=
        ⟨hp.A_pos.le, lt_trans hp.A_lt_quarter (by norm_num), hp.C_pos, hc⟩
      have hround : (A β+C n β)*(B : ℝ)+1/2 ≤ B := by
        nlinarith [mul_nonneg (show 0 ≤ 1-A β-C n β by linarith)
          (sub_nonneg.mpr hb)]
      exact ClassAPlusConstantRecurrence.recurrence_bounded hparams u hrec B hround hz ho
    · have hJ' : J ≤ 4 := by omega
      have hres : 1 ≤ 2*(1+A β-C n β)*(B : ℝ) := by
        have hh := hp.reserve_scale
        have hm := mul_nonneg hp.V_pos.le (sub_nonneg.mpr hb)
        dsimp [V] at hh hm
        nlinarith
      exact shear_bound (A β) (C n β) B hp.A_pos.le (hp.low_shear hJ').1.le hres u hrec hz hs
  intro k
  exact_mod_cast bound k

/-- Repeated actual integer pairs give a positive period of a forward tail.
The finite range is derived from `family_forward_bound`. -/
theorem family_eventually_periodic (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (u : ℕ → ℤ)
    (hrec : ∀ k, Nearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) :
    ∃ N T : ℕ, 0 < T ∧ ∀ m, u (N+(m+T)) = u (N+m) := by
  classical
  let B := initialBound n (u 0) (u 1)
  have hbound := family_forward_bound n J β hp u hrec
  let S : Finset ℤ := Finset.Icc (-B) B
  have hmem : ∀ k, u k ∈ S := fun k => Finset.mem_Icc.mpr (abs_le.mp (hbound k))
  let pairs : ℕ → ({z : ℤ // z ∈ S} × {z : ℤ // z ∈ S}) :=
    fun k => (⟨u k, hmem k⟩, ⟨u (k+1), hmem (k+1)⟩)
  obtain ⟨i, j, hij, hpairs⟩ := Finite.exists_ne_map_eq_of_infinite pairs
  have hfirst : u i = u j := congrArg (fun z => z.1.val) hpairs
  have hsecond : u (i+1) = u (j+1) := congrArg (fun z => z.2.val) hpairs
  have hc : ∀ k, ClassACentralRecurrence.Nearest (-(A β)/2) (-(C n β))
      (u k) (u (k+1)) (u (k+2)) :=
    fun k => (ClassAPlusConstantRecurrence.nearest_central_iff _ _ _ _ _).1 (hrec k)
  have build : ∀ i j : ℕ, i < j → u i = u j → u (i+1) = u (j+1) →
      ∃ N T : ℕ, 0 < T ∧ ∀ m, u (N+(m+T)) = u (N+m) := by
    intro i j hlt hi hj
    refine ⟨i, j-i, by omega, ?_⟩
    intro m
    have hh := (ClassACentralRecurrence.repeated_pair_tail u hc hi hj m).1.symm
    simpa only [show i+(m+(j-i)) = j+m by omega] using hh
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact build i j hlt hfirst hsecond
  · exact build j i hlt hfirst.symm hsecond.symm

/-- Cyclic summation retains the wraparound term explicitly. -/
theorem periodic_sum_shift (f : ℕ → ℝ) (T : ℕ) (hf : Function.Periodic f T) :
    (∑ k ∈ Finset.range T, f (k+1)) = ∑ k ∈ Finset.range T, f k := by
  have hleft := Finset.sum_range_succ f T
  have hright := Finset.sum_range_succ' f T
  have hend : f T = f 0 := by simpa using hf 0
  linarith

theorem sum_half (f : ℕ → ℝ) (T : ℕ) :
    (∑ k ∈ Finset.range T, f k/2) = (∑ k ∈ Finset.range T, f k)/2 := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

def difference (u : ℕ → ℤ) (k : ℕ) : ℤ := u (k+1)-u k
def roundingError (A C : ℝ) (u : ℕ → ℤ) (k : ℕ) : ℝ :=
  (u (k+2) : ℝ)-C*(u (k+1) : ℝ)+A*(u k : ℝ)

theorem periodic_difference (u : ℕ → ℤ) (T : ℕ) (hp : Function.Periodic u T) :
    Function.Periodic (difference u) T := by
  intro k
  unfold difference
  rw [show k+T+1 = (k+1)+T by omega, hp (k+1), hp k]

/-- Integer nonzero differences turn strict half-unit rounding into a
strict quadratic bound, including negative differences. -/
theorem integer_rounding_product_lt (ε : ℝ) (he : |ε| < 1/2)
    (d : ℤ) (hd : d ≠ 0) : ε*(d : ℝ) < (d : ℝ)^2/2 := by
  obtain ⟨helo, hehi⟩ := abs_lt.mp he
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hdi : d ≤ -1 := by omega
    have hdr : (d : ℝ) ≤ -1 := by exact_mod_cast hdi
    nlinarith [mul_pos (show 0 < ε+1/2 by linarith) (show 0 < -(d : ℝ) by linarith),
      mul_nonneg (show 0 ≤ -(d : ℝ) by linarith) (show 0 ≤ -(d : ℝ)-1 by linarith)]
  · have hdi : 1 ≤ d := by omega
    have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hdi
    nlinarith [mul_pos (show 0 < 1/2-ε by linarith) (show 0 < (d : ℝ) by linarith),
      mul_nonneg (show 0 ≤ (d : ℝ) by linarith) (show 0 ≤ (d : ℝ)-1 by linarith)]

theorem integer_rounding_product_le (ε : ℝ) (he : |ε| < 1/2)
    (d : ℤ) : ε*(d : ℝ) ≤ (d : ℝ)^2/2 := by
  by_cases hd : d = 0
  · simp [hd]
  · exact (integer_rounding_product_lt ε he d hd).le

/-- A periodic transformed recurrence is constant throughout the energy
region C >= 3A.  Strict rounding handles the equality face; no extremum,
sign pattern, energy identity or constancy premise is supplied. -/
theorem energy_periodic_constant (A C : ℝ) (hA : 0 ≤ A) (hC : 3*A ≤ C)
    (u : ℕ → ℤ) (T : ℕ) (hT : 0 < T) (hp : Function.Periodic u T)
    (hrec : ∀ k, Nearest A C (u k) (u (k+1)) (u (k+2))) :
    ∃ H : ℤ, |(1+A-C)*(H : ℝ)| < 1/2 ∧ ∀ k, u k = H := by
  let x : ℕ → ℝ := fun k => (u k : ℝ)
  let d : ℕ → ℝ := fun k => (difference u k : ℝ)
  let ε : ℕ → ℝ := roundingError A C u
  let S : ℝ := ∑ k ∈ Finset.range T, (d k)^2
  let R : ℝ := ∑ k ∈ Finset.range T, d k*d (k+1)
  let E : ℝ := ∑ k ∈ Finset.range T, ε k*d (k+1)
  have hd : ∀ k, d k = x (k+1)-x k := by intro k; simp [d, x, difference]
  have hxp : Function.Periodic x T := by intro k; simp [x, hp k]
  have hdp : Function.Periodic d T := by
    intro k
    simp only [d, (periodic_difference u T hp) k]
  have hε : ∀ k, |ε k| < 1/2 := by
    intro k
    have hh := hrec k
    change |(u (k+2) : ℝ)-(-A*(u k : ℝ)+C*(u (k+1) : ℝ))| < 1/2 at hh
    convert hh using 1 <;> dsimp [ε, roundingError] <;> congr 1 <;> ring
  have hshiftD : (∑ k ∈ Finset.range T, (d (k+1))^2) = S :=
    periodic_sum_shift (fun k => (d k)^2) T (fun k => by
      change (d (k+T))^2 = (d k)^2
      rw [hdp k])
  have hshiftX : (∑ k ∈ Finset.range T, (x (k+2))^2) =
      ∑ k ∈ Finset.range T, (x (k+1))^2 := by
    have hxper : Function.Periodic (fun k => (x (k+1))^2) T := by
      intro k
      change (x (k+T+1))^2 = (x (k+1))^2
      rw [show k+T+1 = (k+1)+T by omega, hxp (k+1)]
    simpa [Nat.add_assoc] using periodic_sum_shift (fun k => (x (k+1))^2) T hxper
  have hcross : (∑ k ∈ Finset.range T, x (k+1)*d (k+1)) = -S/2 := by
    calc
      (∑ k ∈ Finset.range T, x (k+1)*d (k+1)) =
          ∑ k ∈ Finset.range T, ((x (k+2))^2-(x (k+1))^2-(d (k+1))^2)/2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hd (k+1)]
        simp only [Nat.add_assoc]
        ring
      _ = ((∑ k ∈ Finset.range T, (x (k+2))^2)-
          (∑ k ∈ Finset.range T, (x (k+1))^2)-
          (∑ k ∈ Finset.range T, (d (k+1))^2))/2 := by
        simp only [sum_half, Finset.sum_sub_distrib]
      _ = -S/2 := by rw [hshiftX, hshiftD]; ring
  have hR : R ≤ S := by
    have hnonneg : 0 ≤ ∑ k ∈ Finset.range T, (d (k+1)-d k)^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hid : (∑ k ∈ Finset.range T, (d (k+1)-d k)^2) = 2*S-2*R := by
      calc
        (∑ k ∈ Finset.range T, (d (k+1)-d k)^2) =
            ∑ k ∈ Finset.range T, ((d (k+1))^2+(d k)^2-2*(d k*d (k+1))) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = (∑ k ∈ Finset.range T, (d (k+1))^2)+
            (∑ k ∈ Finset.range T, (d k)^2)-2*(∑ k ∈ Finset.range T, d k*d (k+1)) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        _ = 2*S-2*R := by rw [hshiftD]; dsimp [S, R]; ring
    linarith
  have henergy : E = (1-(1+A-C)/2)*S-A*R := by
    have heq : ∀ k, ε k = d (k+1)-A*d k+(1+A-C)*x (k+1) := by
      intro k
      rw [hd (k+1), hd k]
      dsimp [ε, roundingError, x]
      simp only [Nat.add_assoc]
      ring
    calc
      E = ∑ k ∈ Finset.range T,
          ((d (k+1))^2-A*(d k*d (k+1))+(1+A-C)*(x (k+1)*d (k+1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [heq k]
        ring
      _ = (∑ k ∈ Finset.range T, (d (k+1))^2)-
          A*(∑ k ∈ Finset.range T, d k*d (k+1))+
          (1+A-C)*(∑ k ∈ Finset.range T, x (k+1)*d (k+1)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (1-(1+A-C)/2)*S-A*R := by rw [hshiftD, hcross]; dsimp [R]; ring
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hElo : S/2 ≤ E := by
    rw [henergy]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hR),
      mul_nonneg (show 0 ≤ C-3*A by linarith) hSnonneg]
  have hSzero : S = 0 := by
    by_contra hne
    have hSpos : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hne)
    have hex : ∃ k ∈ Finset.range T, difference u (k+1) ≠ 0 := by
      by_contra hh
      push_neg at hh
      have hz : (∑ k ∈ Finset.range T, (d (k+1))^2) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp [d, hh k hk]
      rw [hshiftD] at hz
      linarith
    have hElt : E < ∑ k ∈ Finset.range T, (d (k+1))^2/2 := by
      apply Finset.sum_lt_sum
      · intro k hk
        exact integer_rounding_product_le (ε k) (hε k) (difference u (k+1))
      · obtain ⟨k, hk, hkn⟩ := hex
        exact ⟨k, hk, integer_rounding_product_lt (ε k) (hε k) (difference u (k+1)) hkn⟩
    rw [sum_half, hshiftD] at hElt
    linarith
  have hzeroRange : ∀ k ∈ Finset.range T, difference u k = 0 := by
    intro k hk
    have hi : (d k)^2 ≤ S := Finset.single_le_sum (fun i _ => sq_nonneg (d i)) hk
    have hdk : d k = 0 := by nlinarith [sq_nonneg (d k)]
    change ((difference u k : ℤ) : ℝ) = 0 at hdk
    exact_mod_cast hdk
  have hzero : ∀ k, difference u k = 0 := by
    intro k
    have hh := hzeroRange (k%T) (Finset.mem_range.mpr (Nat.mod_lt k hT))
    rwa [(periodic_difference u T hp).map_mod_nat] at hh
  have hconstant : ∀ k, u k = u 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hh := hzero k
      dsimp [difference] at hh
      omega
  refine ⟨u 0, ?_, hconstant⟩
  apply (ClassAPlusConstantRecurrence.constant_nearest_iff A C (u 0)).1
  simpa only [hconstant 1, hconstant 2, zero_add] using hrec 0

/-- Actual-family transformed tails are constant.  The high-J branch reuses
the accepted contraction result; the low-J branch derives its bound and
positive period before applying the finite cyclic-energy contradiction. -/
theorem family_eventual_constant (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (u : ℕ → ℤ)
    (hrec : ∀ k, Nearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) :
    ∃ N : ℕ, ∃ H : ℤ, |V n β*(H : ℝ)| < 1/2 ∧ ∀ m, u (N+m) = H := by
  by_cases hJ : 5 ≤ J
  · exact ClassAPlusConstantRecurrence.eventual_constant_tail (A β) (C n β)
      hp.A_pos.le (lt_trans hp.A_lt_quarter (by norm_num)) hp.C_pos
      (hp.high_contraction hJ).1 u hrec
  · have hJ' : J ≤ 4 := by omega
    obtain ⟨N, T, hT, hperiod⟩ := family_eventually_periodic n J β hp u hrec
    let v : ℕ → ℤ := fun m => u (N+m)
    have hvp : Function.Periodic v T := hperiod
    have hvr : ∀ m, Nearest (A β) (C n β) (v m) (v (m+1)) (v (m+2)) := by
      intro m
      simpa only [v, Nat.add_assoc] using hrec (N+m)
    obtain ⟨H, hamp, hconst⟩ := energy_periodic_constant (A β) (C n β)
      hp.A_pos.le (hp.low_shear hJ').2.le v T hT hvp hvr
    exact ⟨N, H, hamp, hconst⟩

/-- Original first-coordinate recurrence before the parity change. -/
def OriginalNearest (A C : ℝ) (a b c : ℤ) : Prop :=
  |(c : ℝ)+A*(a : ℝ)+C*(b : ℝ)| < 1/2

def twist (u : ℕ → ℤ) (k : ℕ) : ℤ := (-1)^k*u k

theorem twist_abs (u : ℕ → ℤ) (k : ℕ) : |twist u k| = |u k| := by
  simp only [twist, abs_mul, abs_neg_one_pow, one_mul]

theorem original_nearest_iff (A C : ℝ) (a b c : ℤ) :
    OriginalNearest A C a b c ↔ Nearest A C a (-b) c := by
  unfold OriginalNearest Nearest ClassAPlusConstantRecurrence.Nearest
  push_cast
  have heq : (c : ℝ)-(-A*(a : ℝ)+C*-(b : ℝ)) =
      (c : ℝ)+A*(a : ℝ)+C*(b : ℝ) := by ring
  rw [heq]

/-- Parity transfer uses only the strict relation; it does not assign
an asymmetric floor convention at an excluded half-integer tie. -/
theorem twist_recurrence (A C : ℝ) (u : ℕ → ℤ)
    (hrec : ∀ k, OriginalNearest A C (u k) (u (k+1)) (u (k+2))) :
    ∀ k, Nearest A C (twist u k) (twist u (k+1)) (twist u (k+2)) := by
  intro k
  have hh := (original_nearest_iff A C _ _ _).1 (hrec k)
  rcases neg_one_pow_eq_or ℤ k with hs | hs
  · simpa [twist, pow_add, hs] using hh
  · simpa [twist, pow_add, hs] using hh.neg

theorem twist_next_eq_iff (u : ℕ → ℤ) (k : ℕ) :
    twist u (k+1) = twist u k ↔ u (k+1) = -u k := by
  rcases neg_one_pow_eq_or ℤ k with hs | hs <;>
    simp [twist, pow_add, hs] <;> omega

theorem family_original_bound (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (u : ℕ → ℤ)
    (hrec : ∀ k, OriginalNearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) :
    ∀ k, |u k| ≤ initialBound n (u 0) (u 1) := by
  intro k
  have hh := family_forward_bound n J β hp (twist u)
    (twist_recurrence (A β) (C n β) u hrec) k
  simpa only [initialBound, twist_abs] using hh

/-- Original scalar tails alternate with a nonnegative amplitude.  Zero
is included, and no claim of a nonzero selector cycle hitting zero is made. -/
theorem family_eventual_alternating (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (u : ℕ → ℤ)
    (hrec : ∀ k, OriginalNearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) :
    ∃ N : ℕ, ∃ H : ℤ, 0 ≤ H ∧ V n β*(H : ℝ) < 1/2 ∧
      (∀ m, |u (N+m)| = H) ∧ (∀ m, u (N+m+1) = -u (N+m)) := by
  obtain ⟨N, H, hamp, hconst⟩ := family_eventual_constant n J β hp (twist u)
    (twist_recurrence (A β) (C n β) u hrec)
  refine ⟨N, |H|, abs_nonneg H, ?_, ?_, ?_⟩
  · simpa only [Int.cast_abs, abs_mul, abs_of_pos hp.V_pos] using hamp
  · intro m
    have hh := congrArg (fun z : ℤ => |z|) (hconst m)
    simpa only [twist_abs] using hh
  · intro m
    apply (twist_next_eq_iff u (N+m)).1
    rw [show N+m+1 = N+(m+1) by omega, hconst (m+1), hconst m]

/-- Public actual-family endpoint: no bound, positive period, terminal
height or recurrence classification is supplied as a hypothesis. -/
theorem eventual_alternating_tail (n J : ℕ) (β : ℝ)
    (hn : 7 ≤ n) (hJlo : 1 ≤ J) (hJhi : J ≤ n+7)
    (hβlo : (n : ℝ)+4 < β) (hβhi : β < (n : ℝ)+6)
    (hroot : β^3-((n : ℝ)+4)*β^2+((J : ℝ)-(n : ℝ)-7)*β-2 = 0)
    (u : ℕ → ℤ)
    (hrec : ∀ k, |(u (k+2) : ℝ)+(2/β)*(u k : ℝ)+
      (β-((n : ℝ)+4))*(u (k+1) : ℝ)| < 1/2) :
    ∃ N : ℕ, ∃ H : ℤ, 0 ≤ H ∧ (J : ℝ)/(β+1)*(H : ℝ) < 1/2 ∧
      (∀ m, |u (N+m)| = H) ∧ (∀ m, u (N+m+1) = -u (N+m)) := by
  let hp : Family n J β := ⟨hn, hJlo, hJhi, hβlo, hβhi, hroot⟩
  have hh := family_eventual_alternating n J β hp u hrec
  simpa only [hp.reserve_identity] using hh

theorem forward_integer_bound (n J : ℕ) (β : ℝ)
    (hn : 7 ≤ n) (hJlo : 1 ≤ J) (hJhi : J ≤ n+7)
    (hβlo : (n : ℝ)+4 < β) (hβhi : β < (n : ℝ)+6)
    (hroot : β^3-((n : ℝ)+4)*β^2+((J : ℝ)-(n : ℝ)-7)*β-2 = 0)
    (u : ℕ → ℤ)
    (hrec : ∀ k, |(u (k+2) : ℝ)+(2/β)*(u k : ℝ)+
      (β-((n : ℝ)+4))*(u (k+1) : ℝ)| < 1/2) :
    ∀ k, |u k| ≤ ((n : ℤ)+7)*(|u 0|+|u 1|+1) :=
  family_original_bound n J β ⟨hn, hJlo, hJhi, hβlo, hβhi, hroot⟩ u hrec

/-- Public coefficient transfer exposes the actual family/root hypotheses
and both alternatives used by the forward proof. -/
theorem family_coefficients (n J : ℕ) (β : ℝ)
    (hn : 7 ≤ n) (hJlo : 1 ≤ J) (hJhi : J ≤ n+7)
    (hβlo : (n : ℝ)+4 < β) (hβhi : β < (n : ℝ)+6)
    (hroot : β^3-((n : ℝ)+4)*β^2+((J : ℝ)-(n : ℝ)-7)*β-2 = 0) :
    0 < 2/β ∧ 2/β < 1/4 ∧ 0 < β-((n : ℝ)+4) ∧
    0 < (J : ℝ)/(β+1) ∧
    1+2/β-(β-((n : ℝ)+4)) = (J : ℝ)/(β+1) ∧
    (5 ≤ J → 2/β+(β-((n : ℝ)+4)) < 1) ∧
    (J ≤ 4 → 1/2+2*(2/β) < β-((n : ℝ)+4)) := by
  let hp : Family n J β := ⟨hn, hJlo, hJhi, hβlo, hβhi, hroot⟩
  exact ⟨hp.A_pos, hp.A_lt_quarter, hp.C_pos,
    by simpa only [hp.reserve_identity] using hp.V_pos,
    hp.reserve_identity, fun hJ => (hp.high_contraction hJ).1,
    fun hJ => (hp.low_shear hJ).1⟩

/-- Public transformed endpoint, with no orbit-bound or periodic-tail
hypothesis hidden in a coefficient structure. -/
theorem eventual_constant_tail (n J : ℕ) (β : ℝ)
    (hn : 7 ≤ n) (hJlo : 1 ≤ J) (hJhi : J ≤ n+7)
    (hβlo : (n : ℝ)+4 < β) (hβhi : β < (n : ℝ)+6)
    (hroot : β^3-((n : ℝ)+4)*β^2+((J : ℝ)-(n : ℝ)-7)*β-2 = 0)
    (u : ℕ → ℤ)
    (hrec : ∀ k, |(u (k+2) : ℝ)-(-(2/β)*(u k : ℝ)+
      (β-((n : ℝ)+4))*(u (k+1) : ℝ))| < 1/2) :
    ∃ N : ℕ, ∃ H : ℤ, |(J : ℝ)/(β+1)*(H : ℝ)| < 1/2 ∧
      ∀ m, u (N+m) = H := by
  let hp : Family n J β := ⟨hn, hJlo, hJhi, hβlo, hβhi, hroot⟩
  have hh := family_eventual_constant n J β hp u hrec
  simpa only [hp.reserve_identity] using hh

open Psc.ClassAZeroDefectEscape Psc.OccurrenceNewborn Psc.OccurrenceTransport

/-- Full next packet recovered from three successive first coordinates. -/
def reconstructedPacket (a b c : ℤ) : Packet :=
  packet 2 2 b (b-2*a) (c-3*b+2*a)

theorem alternating_packet_shape (a b c : ℤ) (hab : b = -a) (hbc : c = -b) :
    reconstructedPacket a b c = packet 2 2 b (3*b) (-6*b) := by
  have hq : b-2*a = 3*b := by omega
  have hr : c-3*b+2*a = -6*b := by omega
  simp only [reconstructedPacket, hq, hr]

/-- Scalar tail entry at N gives the full W-shape at N+1.  The complete
reconstruction hypothesis is explicit and is not replaced by a projection. -/
theorem reconstruction_delay (u : ℕ → ℤ) (w : ℕ → Packet) (N : ℕ)
    (hshape : ∀ k, w (k+1) = reconstructedPacket (u k) (u (k+1)) (u (k+2)))
    (halt : ∀ m, u (N+m+1) = -u (N+m)) :
    ∀ m, w (N+m+1) = packet 2 2 (u (N+m+1)) (3*u (N+m+1)) (-6*u (N+m+1)) := by
  intro m
  rw [hshape (N+m)]
  apply alternating_packet_shape
  · exact halt m
  · simpa only [Nat.add_assoc] using halt (m+1)

/-- The actual plus lengths turn centrality of the complete next packet
into the original scalar strict-nearest relation. -/
theorem central_coordinate_recurrence (A C : ℝ) (a b r : ℤ)
    (hc : |(2+C+A/2)*(b : ℝ)+(1-A/2)*((b-2*a : ℤ) : ℝ)+(r : ℝ)| < 1/2) :
    OriginalNearest A C a b (3*b-2*a+r) := by
  unfold OriginalNearest
  push_cast at *
  convert hc using 1
  congr 1
  ring

/-- The upper half-unit selector remains within the actual y-run. -/
theorem central_gap_in_run (n : ℕ) (hn : 7 ≤ n) (β θ : ℝ)
    (hβ : 0 < β) (hβhi : β < (n : ℝ)+6)
    (hθ : |θ| < 1/2) (e : ℤ) (he : |β*θ-(e : ℝ)| < 1/2) :
    -(n : ℤ) ≤ e ∧ e ≤ (n : ℤ) := by
  obtain ⟨hθlo, hθhi⟩ := abs_lt.mp hθ
  obtain ⟨helo, hehi⟩ := abs_lt.mp he
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hlo : -(n : ℝ) < e := by
    nlinarith [mul_pos hβ (show 0 < θ+1/2 by linarith)]
  have hhi : (e : ℝ) < n := by
    nlinarith [mul_pos hβ (show 0 < 1/2-θ by linarith)]
  exact ⟨by exact_mod_cast hlo.le, by exact_mod_cast hhi.le⟩

/-- A nearest gap is realized by two literal RUN occurrences, retaining
their original ordinals and all integral coordinates. -/
theorem run_gap_digit_step (n d : ℕ) (p q r e : ℤ)
    (helo : -(n : ℤ) ≤ e) (hehi : e ≤ (n : ℤ)) :
    IndexedDigitStep (ClassAPlusConstantRecurrence.sigma n d) (packet 2 2 p q r)
      (e.toNat+1) ((-e).toNat+1)
      (packet 2 2 (2*p+q+r) (q+r)
        (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n+1 : ℕ) : ℤ)*r-e)) := by
  have hi : e.toNat+1 ≤ n+1 := by omega
  have hj : (-e).toNat+1 ≤ n+1 := by omega
  have hh := ClassAPlusConstantRecurrence.yy_run_digit_step n d (e.toNat+1)
    ((-e).toNat+1) (by omega) hi (by omega) hj p q r
  have heq : (((-e).toNat+1 : ℕ) : ℤ)-((e.toNat+1 : ℕ) : ℤ) = -e := by omega
  convert hh using 1
  congr 1
  omega

theorem nonzero_upper_cycle_control :
    (1 : ℝ) < 1/8+1 ∧ Nearest (1/8) 1 1 1 1 ∧
      OriginalNearest (1/8) 1 1 (-1) 1 ∧ (1 : ℤ) ≠ 0 := by
  norm_num [Nearest, ClassAPlusConstantRecurrence.Nearest, OriginalNearest]

theorem half_tie_control : ¬Nearest (1/8) 1 4 0 0 := by
  norm_num [Nearest, ClassAPlusConstantRecurrence.Nearest]

end Psc.ClassAPlusUpperRecurrence
