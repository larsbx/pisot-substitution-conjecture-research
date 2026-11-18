/-
# Constant nearest-integer tails and literal minus-Class-A descent

The real recurrence is proved for its displayed coefficient inequalities.
The literal RUN decrement retains both original occurrence ordinals and all
three integral coordinates. Perron-root identification, arbitrary-overlap
entry into the central slice and assembly of original nested prefixes are
separate interfaces, not hypotheses hidden in these recurrence theorems.

Pre-code source gate:
`docs/bh-class-a-minus-constant-stop-go-2026-11-14.md`.
-/
import PscVerif.ClassACentralRecurrence

namespace Psc.ClassAMinusConstantRecurrence

/-- A strict nearest-integer update. No choice of a half-integer tie is used. -/
def Nearest (A B : ℝ) (a b c : ℤ) : Prop :=
  |(c : ℝ) - (A * (a : ℝ) + B * (b : ℝ))| < 1 / 2

structure Parameters (A B : ℝ) : Prop where
  anonneg : 0 ≤ A
  asmall : A < 1 / 2
  bpos : 0 < B
  contraction : A + B < 1

/-- The old sign convention can supply rounding uniqueness without any
of its alternating-region parameter assumptions. -/
theorem nearest_central_iff (A B : ℝ) (a b c : ℤ) :
    Nearest A B a b c ↔
      ClassACentralRecurrence.Nearest (A / 2) (-B) a b c := by
  unfold Nearest ClassACentralRecurrence.Nearest
  have heq : 2 * (A / 2) * (a : ℝ) - -B * (b : ℝ) =
      A * (a : ℝ) + B * (b : ℝ) := by ring
  rw [heq]

theorem Nearest.neg {A B : ℝ} {a b c : ℤ} (he : Nearest A B a b c) :
    Nearest A B (-a) (-b) (-c) :=
  (nearest_central_iff A B (-a) (-b) (-c)).2
    ((nearest_central_iff A B a b c).1 he).neg

theorem Nearest.unique {A B : ℝ} {a b c d : ℤ}
    (hc : Nearest A B a b c) (hd : Nearest A B a b d) : c = d :=
  ((nearest_central_iff A B a b c).1 hc).unique
    ((nearest_central_iff A B a b d).1 hd)

/-- An invariant real box absorbs both the contraction and rounding error. -/
theorem nearest_bound {A B : ℝ} (hp : Parameters A B) {a b c : ℤ} {C : ℝ}
    (ha : |(a : ℝ)| ≤ C) (hb : |(b : ℝ)| ≤ C)
    (hC : (A + B) * C + 1 / 2 ≤ C)
    (he : Nearest A B a b c) : |(c : ℝ)| ≤ C := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  obtain ⟨he₁, he₂⟩ := abs_lt.mp he
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hp.anonneg (sub_nonneg.mpr ha₁),
      mul_nonneg hp.bpos.le (sub_nonneg.mpr hb₁)]
  · nlinarith [mul_nonneg hp.anonneg (sub_nonneg.mpr ha₂),
      mul_nonneg hp.bpos.le (sub_nonneg.mpr hb₂)]

theorem recurrence_bounded {A B : ℝ} (hp : Parameters A B)
    (u : ℕ → ℤ) (hrec : ∀ n, Nearest A B (u n) (u (n+1)) (u (n+2)))
    (C : ℝ) (hC : (A+B)*C+1/2 ≤ C)
    (hzero : |(u 0 : ℝ)| ≤ C) (hone : |(u 1 : ℝ)| ≤ C) :
    ∀ n, |(u n : ℝ)| ≤ C := by
  have pair : ∀ n, |(u n : ℝ)| ≤ C ∧ |(u (n+1) : ℝ)| ≤ C := by
    intro n
    induction n with
    | zero => exact ⟨hzero, hone⟩
    | succ n ih =>
      exact ⟨ih.2, by simpa [Nat.add_assoc] using nearest_bound hp ih.1 ih.2 hC (hrec n)⟩
  exact fun n => (pair n).1

/-- The finite integer bound is derived from the initial pair and the
coefficient contraction, not supplied by a finite graph. -/
theorem recurrence_has_integer_bound {A B : ℝ} (hp : Parameters A B)
    (u : ℕ → ℤ) (hrec : ∀ n, Nearest A B (u n) (u (n+1)) (u (n+2))) :
    ∃ C : ℕ, ∀ n, |u n| ≤ (C : ℤ) := by
  have hden : 0 < 2 * (1-A-B) := by linarith [hp.contraction]
  obtain ⟨C, hC⟩ := exists_nat_gt
    (max |(u 0 : ℝ)| (max |(u 1 : ℝ)| (1 / (2 * (1-A-B)))))
  have hzero : |(u 0 : ℝ)| ≤ C := (le_max_left _ _).trans hC.le
  have hone : |(u 1 : ℝ)| ≤ C :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hC.le
  have hreserve : 1 / (2 * (1-A-B)) < (C : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hmul := (div_lt_iff₀ hden).1 hreserve
  have hround : (A+B)*(C : ℝ)+1/2 ≤ C := by nlinarith
  have hall := recurrence_bounded hp u hrec (C : ℝ) hround hzero hone
  refine ⟨C, fun n => ?_⟩
  have hh := hall n
  exact_mod_cast hh

/-- A positive integer maximum forces the immediately preceding value to
be the same maximum. The bound on A is the decisive strict inequality. -/
theorem maximum_predecessor {A B : ℝ} (hp : Parameters A B)
    {a b H : ℤ} (hH : 0 < H) (ha : a ≤ H) (hb : b ≤ H)
    (he : Nearest A B a b H) : b = H := by
  by_contra hne
  have hb' : b ≤ H-1 := by omega
  have haR : (a : ℝ) ≤ H := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ (H : ℝ)-1 := by exact_mod_cast hb'
  have hHR : 1 ≤ (H : ℝ) := by exact_mod_cast (show 1 ≤ H by omega)
  have hδ : 0 ≤ 1-A-B := by linarith [hp.contraction]
  have he' := (abs_lt.mp he).2
  nlinarith [mul_nonneg hp.anonneg (sub_nonneg.mpr haR),
    mul_nonneg hp.bpos.le (sub_nonneg.mpr hbR),
    mul_nonneg hδ (sub_nonneg.mpr hHR), hp.asmall]

/-- Exact amplitude criterion for a constant integer triple, including
zero and either sign of H. -/
theorem constant_nearest_iff (A B : ℝ) (H : ℤ) :
    Nearest A B H H H ↔ |(1-A-B)*(H : ℝ)| < 1/2 := by
  unfold Nearest
  have heq : (H : ℝ) - (A*(H : ℝ)+B*(H : ℝ)) =
      (1-A-B)*(H : ℝ) := by ring
  rw [heq]

/-- An attained positive global maximum forces the entire two-sided
recurrence to be constant. Backward propagation supplies an actual
constant triple, and strict nearest uniqueness propagates forwards. -/
theorem positive_maximum_constant {A B : ℝ} (hp : Parameters A B)
    (u : ℤ → ℤ)
    (hrec : ∀ z, Nearest A B (u z) (u (z+1)) (u (z+2)))
    (H i : ℤ) (hH : 0 < H) (hupper : ∀ z, u z ≤ H) (hi : u i = H) :
    |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ z, u z = H := by
  have pred : ∀ z, u z = H → u (z-1) = H := by
    intro z hz
    have he : Nearest A B (u (z-2)) (u (z-1)) H := by
      simpa only [show z-2+1 = z-1 by omega,
        show z-2+2 = z by omega, hz] using hrec (z-2)
    exact maximum_predecessor hp hH (hupper _) (hupper _) he
  have hprev := pred i hi
  have hprev₂ := pred (i-1) hprev
  have hprev₂' : u (i-2) = H := by
    simpa only [show i-1-1 = i-2 by omega] using hprev₂
  have hfixed : Nearest A B H H H := by
    have he := hrec (i-2)
    simpa only [show i-2+1 = i-1 by omega,
      show i-2+2 = i by omega, hprev₂', hprev, hi] using he
  have past : ∀ m : ℕ, u (i-m) = H := by
    intro m
    induction m with
    | zero => simpa using hi
    | succ m ih =>
      have hh := pred (i-m) ih
      simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hh
  have future : ∀ m : ℕ, u (i+m-1) = H ∧ u (i+m) = H := by
    intro m
    induction m with
    | zero => simpa using And.intro hprev hi
    | succ m ih =>
      have he : Nearest A B H H (u (i+m+1)) := by
        have hh := hrec (i+m-1)
        simpa only [show i+m-1+1 = i+m by omega,
          show i+m-1+2 = i+m+1 by omega, ih.1, ih.2] using hh
      have hh := he.unique hfixed
      have eqi : i + ((m+1 : ℕ) : ℤ) = i+m+1 := by push_cast; ring
      rw [eqi]
      constructor
      · simpa only [add_sub_cancel_right] using ih.2
      · exact hh
  refine ⟨(constant_nearest_iff A B H).1 hfixed, ?_⟩
  intro z
  by_cases hz : i ≤ z
  · have heq : i+((z-i).toNat : ℤ) = z := by
      rw [Int.toNat_of_nonneg (by omega)]; omega
    simpa only [heq] using (future (z-i).toNat).2
  · have heq : i-((i-z).toNat : ℤ) = z := by
      rw [Int.toNat_of_nonneg (by omega)]; omega
    simpa only [heq] using past (i-z).toNat

/-- Every bounded two-sided recurrence is constant. An attained largest
absolute value handles positive, negative, zero and mixed-sign sequences
without a one-sided sign hypothesis. -/
theorem bounded_two_sided_constant {A B : ℝ} (hp : Parameters A B)
    (u : ℤ → ℤ)
    (hrec : ∀ z, Nearest A B (u z) (u (z+1)) (u (z+2)))
    (hbdd : ∃ C : ℤ, ∀ z, |u z| ≤ C) :
    ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ z, u z = H := by
  classical
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨H, ⟨i, hi⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun v => ∃ z, |u z| = v)
    ⟨C, by rintro v ⟨z, rfl⟩; exact hC z⟩ ⟨|u 0|, 0, rfl⟩
  have hH : 0 ≤ H := by simpa only [hi] using abs_nonneg (u i)
  have hbound : ∀ z, |u z| ≤ H := fun z => hmax _ ⟨z, rfl⟩
  by_cases hz : H = 0
  · refine ⟨0, by norm_num, ?_⟩
    intro z
    have hh := abs_le.mp (hbound z)
    omega
  have hpos : 0 < H := by omega
  by_cases hi0 : 0 ≤ u i
  · have hieq : u i = H := by simpa only [abs_of_nonneg hi0] using hi
    exact ⟨H, positive_maximum_constant hp u hrec H i hpos
      (fun z => (abs_le.mp (hbound z)).2) hieq⟩
  · have hieq : -u i = H := by
      simpa only [abs_of_neg (show u i < 0 by omega)] using hi
    have hupp : ∀ z, -u z ≤ H := by
      intro z
      have hh := (abs_le.mp (hbound z)).1
      omega
    obtain ⟨hamp, hconst⟩ := positive_maximum_constant hp (fun z => -u z)
      (fun z => (hrec z).neg) H i hpos hupp hieq
    refine ⟨-H, ?_, ?_⟩
    · simpa only [Int.cast_neg, mul_neg, abs_neg] using hamp
    · intro z
      have hh := hconst z
      omega

/-- Periodicity supplies boundedness, including all wraparound triples. -/
theorem periodic_recurrence_classification {A B : ℝ} (hp : Parameters A B)
    (u : ℤ → ℤ) (T : ℤ) (hT : 0 < T) (hperiod : Function.Periodic u T)
    (hrec : ∀ z, Nearest A B (u z) (u (z+1)) (u (z+2))) :
    ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ z, u z = H := by
  classical
  apply bounded_two_sided_constant hp u hrec
  refine ⟨∑ z ∈ Finset.Ico 0 T, |u z|, ?_⟩
  intro z
  have hmod : u (z % T) = u z := by
    have hh := (hperiod.int_mul (z / T)) (z % T)
    simpa [Int.emod_add_ediv_mul] using hh.symm
  have hm : z % T ∈ Finset.Ico 0 T := Finset.mem_Ico.mpr
    ⟨Int.emod_nonneg _ (ne_of_gt hT), Int.emod_lt_of_pos _ hT⟩
  rw [← hmod]
  exact Finset.single_le_sum (fun i _ => abs_nonneg (u i)) hm

/-- A repeated actual integer pair supplies a positive period of a tail.
The finite range is derived from the preceding contraction theorem. -/
theorem recurrence_eventually_periodic {A B : ℝ} (hp : Parameters A B)
    (u : ℕ → ℤ)
    (hrec : ∀ n, Nearest A B (u n) (u (n+1)) (u (n+2))) :
    ∃ N T : ℕ, 0 < T ∧ ∀ m, u (N+(m+T)) = u (N+m) := by
  classical
  obtain ⟨C, hC⟩ := recurrence_has_integer_bound hp u hrec
  let S : Finset ℤ := Finset.Icc (-(C : ℤ)) (C : ℤ)
  have hmem : ∀ n, u n ∈ S := fun n => Finset.mem_Icc.mpr (abs_le.mp (hC n))
  let pairs : ℕ → ({z : ℤ // z ∈ S} × {z : ℤ // z ∈ S}) :=
    fun n => (⟨u n, hmem n⟩, ⟨u (n+1), hmem (n+1)⟩)
  obtain ⟨i, j, hij, hpairs⟩ := Finite.exists_ne_map_eq_of_infinite pairs
  have hfirst : u i = u j := congrArg (fun z => z.1.val) hpairs
  have hsecond : u (i+1) = u (j+1) := congrArg (fun z => z.2.val) hpairs
  have hc : ∀ n, ClassACentralRecurrence.Nearest (A/2) (-B)
      (u n) (u (n+1)) (u (n+2)) :=
    fun n => (nearest_central_iff A B _ _ _).1 (hrec n)
  have build : ∀ i j : ℕ, i < j → u i = u j → u (i+1) = u (j+1) →
      ∃ N T : ℕ, 0 < T ∧ ∀ m, u (N+(m+T)) = u (N+m) := by
    intro i j hlt hfirst hsecond
    refine ⟨i, j-i, by omega, ?_⟩
    intro m
    have hh := (ClassACentralRecurrence.repeated_pair_tail u hc hfirst hsecond m).1.symm
    have heq : i+(m+(j-i)) = j+m := by omega
    simpa only [heq] using hh
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact build i j hlt hfirst hsecond
  · exact build j i hlt hfirst.symm hsecond.symm

/-- A periodic forward word extends in both directions while preserving
the recurrence at every residue, including the wraparound. -/
theorem nat_periodic_classification {A B : ℝ} (hp : Parameters A B)
    (v : ℕ → ℤ) (T : ℕ) (hT : 0 < T) (hperiod : Function.Periodic v T)
    (hrec : ∀ n, Nearest A B (v n) (v (n+1)) (v (n+2))) :
    ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ n, v n = H := by
  let w : ℤ → ℤ := fun z => v ((z % (T : ℤ)).toNat)
  have wshift : ∀ (z : ℤ) (m : ℕ), w (z+m) = v ((z % (T : ℤ)).toNat+m) := by
    intro z m
    dsimp [w]
    rw [ClassACentralRecurrence.periodic_residue_shift T hT z m, hperiod.map_mod_nat]
  have wnat : ∀ n : ℕ, w n = v n := by
    intro n
    dsimp [w]
    rw [← Int.natCast_emod, Int.toNat_natCast, hperiod.map_mod_nat]
  have wp : Function.Periodic w (T : ℤ) := by
    intro z
    dsimp [w]
    rw [Int.add_emod_right]
  have wr : ∀ z, Nearest A B (w z) (w (z+1)) (w (z+2)) := by
    intro z
    have h1 := wshift z 1
    have h2 := wshift z 2
    norm_num only [Nat.cast_one, Nat.cast_ofNat] at h1 h2
    rw [h1, h2]
    exact hrec ((z % (T : ℤ)).toNat)
  obtain ⟨H, hamp, hconst⟩ := periodic_recurrence_classification
    hp w (T : ℤ) (by exact_mod_cast hT) wp wr
  exact ⟨H, hamp, fun n => by simpa only [wnat] using hconst n⟩

/-- Explicit-hypothesis endpoint for the forward integer bound. -/
theorem forward_integer_bound (A B : ℝ) (hA : 0 ≤ A) (hsmall : A < 1/2)
    (hB : 0 < B) (hcontract : A+B < 1) (u : ℕ → ℤ)
    (hrec : ∀ n, |(u (n+2) : ℝ)-(A*(u n : ℝ)+B*(u (n+1) : ℝ))| < 1/2) :
    ∃ C : ℕ, ∀ n, |u n| ≤ (C : ℤ) :=
  recurrence_has_integer_bound ⟨hA, hsmall, hB, hcontract⟩ u hrec

theorem bounded_two_sided_classification (A B : ℝ) (hA : 0 ≤ A) (hsmall : A < 1/2)
    (hB : 0 < B) (hcontract : A+B < 1) (u : ℤ → ℤ)
    (hrec : ∀ z, |(u (z+2) : ℝ)-(A*(u z : ℝ)+B*(u (z+1) : ℝ))| < 1/2)
    (hbdd : ∃ C : ℤ, ∀ z, |u z| ≤ C) :
    ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ z, u z = H :=
  bounded_two_sided_constant ⟨hA, hsmall, hB, hcontract⟩ u hrec hbdd

theorem periodic_cycle_classification (A B : ℝ) (hA : 0 ≤ A) (hsmall : A < 1/2)
    (hB : 0 < B) (hcontract : A+B < 1) (u : ℤ → ℤ) (T : ℤ)
    (hT : 0 < T) (hperiod : Function.Periodic u T)
    (hrec : ∀ z, |(u (z+2) : ℝ)-(A*(u z : ℝ)+B*(u (z+1) : ℝ))| < 1/2) :
    ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ z, u z = H :=
  periodic_recurrence_classification ⟨hA, hsmall, hB, hcontract⟩ u T hT hperiod hrec

/-- Every forward integer recurrence eventually becomes constant.
Boundedness, finite pair repetition and the tail's positive period are
derived, rather than added as recurrence hypotheses. -/
theorem eventual_constant_tail (A B : ℝ) (hA : 0 ≤ A) (hsmall : A < 1/2)
    (hB : 0 < B) (hcontract : A+B < 1) (u : ℕ → ℤ)
    (hrec : ∀ n, |(u (n+2) : ℝ)-(A*(u n : ℝ)+B*(u (n+1) : ℝ))| < 1/2) :
    ∃ N : ℕ, ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ m, u (N+m) = H := by
  let hp : Parameters A B := ⟨hA, hsmall, hB, hcontract⟩
  obtain ⟨N, T, hT, hperiod⟩ := recurrence_eventually_periodic hp u hrec
  let v : ℕ → ℤ := fun m => u (N+m)
  have hvp : Function.Periodic v T := hperiod
  have hvr : ∀ m, Nearest A B (v m) (v (m+1)) (v (m+2)) := by
    intro m
    simpa only [Nearest, v, Nat.add_assoc] using hrec (N+m)
  obtain ⟨H, hamp, hconst⟩ := nat_periodic_classification hp v T hT hvp hvr
  exact ⟨N, H, hamp, hconst⟩

/-- A valid nonzero constant is not a zero hit; an occurrence exit is still
necessary after the recurrence has settled. -/
theorem nonzero_constant_control :
    Parameters (1/8) (3/4) ∧ Nearest (1/8) (3/4) 1 1 1 ∧ (1 : ℤ) ≠ 0 := by
  constructor
  · constructor <;> norm_num
  · norm_num [Nearest]

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAZeroDefectEscape Matrix

/-- A selected pair strictly inside the two literal y-runs. The displayed
ordinals are actual positions in the original images, with FIRST at zero. -/
theorem yy_run_digit_step (n d : ℕ) (hn : 2 ≤ n) (i j : ℕ)
    (hi0 : 1 ≤ i) (hi : i < n) (hj0 : 1 ≤ j) (hj : j < n)
    (p q r : ℤ) :
    IndexedDigitStep (sigma n d) (packet 2 2 p q r) i j
      (packet 2 2 (2*p+q+r) (q+r)
        (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+(j : ℤ)-i)) := by
  have hi' : i-1 < runLength n d 2 := by simp [runLength]; omega
  have hj' : j-1 < runLength n d 2 := by simp [runLength]; omega
  have he := positive_step n d (by omega) 2 2 (i-1) (j-1) hi'.le hj'.le p q r
  have hg : ((j-1 : ℕ) : ℤ)-((i-1 : ℕ) : ℤ) = (j : ℤ)-i := by
    rw [Nat.cast_sub hj0, Nat.cast_sub hi0]
    norm_num
  have ht : ((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+
      ((j-1 : ℕ) : ℤ)-((i-1 : ℕ) : ℤ) =
      ((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+(j : ℤ)-i := by
    linarith
  simpa only [Nat.sub_add_cancel hi0, Nat.sub_add_cancel hj0,
    positiveMark_letter_of_lt n d 2 (i-1) hi',
    positiveMark_letter_of_lt n d 2 (j-1) hj', delta,
    show (2 : Fin 3) ≠ 1 by decide, ite_false, sub_self, sub_zero, add_zero, ht] using he

/-- The three genuine RUN pairs decrease a positive integral constant
height by one. The final gap is top-minus-bottom; the packet convention
negates the native bottom-minus-top coordinates. -/
theorem three_run_decrement (n d H : ℕ) (hd : 5 ≤ d) (hH : 1 ≤ H)
    (hn : 2*d*H ≤ n) :
    IndexedDigitStep (sigma n d) (packet 2 2 (H : ℤ) (-(H : ℤ)) 0)
      (d*H+2) 1 (packet 2 2 (H : ℤ) (-(H : ℤ)) (-1)) ∧
    IndexedDigitStep (sigma n d) (packet 2 2 (H : ℤ) (-(H : ℤ)) (-1))
      1 (n+2-d*H) (packet 2 2 ((H : ℤ)-1) (-(H : ℤ)-1) 2) ∧
    IndexedDigitStep (sigma n d) (packet 2 2 ((H : ℤ)-1) (-(H : ℤ)-1) 2)
      (((d : ℤ)*((H : ℤ)-1)-2).toNat+1)
      ((2-(d : ℤ)*((H : ℤ)-1)).toNat+1)
      (packet 2 2 ((H : ℤ)-1) (-(H : ℤ)+1) 0) := by
  have hdH : 5 ≤ d*H := (hd.trans (by simpa using Nat.mul_le_mul_left d hH))
  have hn' : 2*(d*H) ≤ n := by nlinarith [hn]
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hfirst : d*H+2 < n := by omega
  have hsecond0 : 1 ≤ n+2-d*H := by omega
  have hsecond : n+2-d*H < n := by omega
  have hsub : d*H ≤ n+2 := by omega
  have e1 := yy_run_digit_step n d hn2 (d*H+2) 1 (by omega) hfirst
    (by omega) (by omega) (H : ℤ) (-(H : ℤ)) 0
  have e2 := yy_run_digit_step n d hn2 1 (n+2-d*H) (by omega) (by omega)
    hsecond0 hsecond (H : ℤ) (-(H : ℤ)) (-1)
  have hHcast : 1 ≤ (H : ℤ) := by exact_mod_cast hH
  have hdcast : 5 ≤ (d : ℤ) := by exact_mod_cast hd
  have hncast : 2*(d : ℤ)*(H : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hnsub : ((n-2 : ℕ) : ℤ) = (n : ℤ)-2 := by
    rw [Nat.cast_sub hn2]
    norm_num
  have hglo : -((n-2 : ℕ) : ℤ) ≤ 2-(d : ℤ)*((H : ℤ)-1) := by
    rw [hnsub]
    nlinarith
  have hghi : 2-(d : ℤ)*((H : ℤ)-1) ≤ ((n-2 : ℕ) : ℤ) := by
    rw [hnsub]
    nlinarith [mul_nonneg (show 0 ≤ (d : ℤ) by omega) (show 0 ≤ (H : ℤ)-1 by omega)]
  have e3 := ClassACentralRecurrence.run_gap_digit_step n d hn2
    ((H : ℤ)-1) (-(H : ℤ)-1) 2 (2-(d : ℤ)*((H : ℤ)-1)) hglo hghi
  rw [show -(2-(d : ℤ)*((H : ℤ)-1)) = (d : ℤ)*((H : ℤ)-1)-2 by ring] at e3
  constructor
  · convert e1 using 1
    push_cast
    congr 1 <;> ring
  constructor
  · convert e2 using 1
    simp only [Nat.cast_sub hn1, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    congr 1 <;> ring
  · convert e3 using 1
    simp only [Nat.cast_sub hn1, Nat.cast_add, Nat.cast_one]
    congr 1 <;> ring

/-- Iterating the three indexed decrements supplies a finite actual digit
path for every nonnegative height in the displayed run range. -/
theorem nonnegative_constant_digit_path (n d H : ℕ) (hd : 5 ≤ d)
    (hn : 2*d*H ≤ n) :
    Relation.ReflTransGen (DigitStep (sigma n d))
      (packet 2 2 (H : ℤ) (-(H : ℤ)) 0) (packet 2 2 0 0 0) := by
  induction H with
  | zero => simpa using (Relation.ReflTransGen.refl (a := packet 2 2 0 0 0))
  | succ H ih =>
    have hprev : 2*d*H ≤ n := by nlinarith [hn]
    have hp := ih hprev
    obtain ⟨e1, e2, e3⟩ := three_run_decrement n d (H+1) hd (by omega) hn
    have hlast : packet 2 2 (((H+1 : ℕ) : ℤ)-1) (-((H+1 : ℕ) : ℤ)+1) 0 =
        packet 2 2 (H : ℤ) (-(H : ℤ)) 0 := by
      congr 1 <;> push_cast <;> ring
    rw [hlast] at e3
    exact (Relation.ReflTransGen.single e1.digitStep).trans
      ((Relation.ReflTransGen.single e2.digitStep).trans
        ((Relation.ReflTransGen.single e3.digitStep).trans hp))

theorem packet_swap (a b : Fin 3) (p q r : ℤ) :
    (packet a b p q r).swap = packet b a (-p) (-q) (-r) := by
  apply congrArg (Packet.mk b a)
  funext c
  fin_cases c <;> rfl

theorem digit_path_swap {s : Fin 3 → Word} {p q : Packet}
    (hp : Relation.ReflTransGen (DigitStep s) p q) :
    Relation.ReflTransGen (DigitStep s) p.swap q.swap := by
  induction hp with
  | refl => exact .refl
  | tail _ he ih => exact ih.tail he.swap

/-- Reversing the two actual occurrence tracks handles negative heights. -/
theorem constant_digit_path (n d : ℕ) (hd : 5 ≤ d) (H : ℤ)
    (hn : 2*(d : ℤ)*|H| ≤ (n : ℤ)) :
    Relation.ReflTransGen (DigitStep (sigma n d))
      (packet 2 2 H (-H) 0) (packet 2 2 0 0 0) := by
  have hn' : 2*d*H.natAbs ≤ n := by
    have hh : 2*(d : ℤ)*(H.natAbs : ℤ) ≤ (n : ℤ) := by
      simpa only [Int.natCast_natAbs] using hn
    exact_mod_cast hh
  have hp := nonnegative_constant_digit_path n d H.natAbs hd hn'
  by_cases hH : 0 ≤ H
  · simpa only [Int.natCast_natAbs, abs_of_nonneg hH] using hp
  · have hh := digit_path_swap hp
    simpa only [packet_swap, Int.natCast_natAbs, abs_of_neg (show H < 0 by omega),
      neg_neg, neg_zero] using hh

/-- Strictness propagates backwards along every actual digit edge from a
strict target. The same selected edges then form an interior path. -/
theorem digit_path_interior (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a)
    {p q : Packet} (hp : Relation.ReflTransGen (DigitStep s) p q)
    (hq : q.Interior ℓ) :
    p.Interior ℓ ∧ Relation.ReflTransGen (InteriorStep s ℓ) p q := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨hq, .refl⟩
  | head he _ ih =>
    exact ⟨interior_source_of_digitStep s ℓ β hpos hβ hscale he ih.1,
      ih.2.head ⟨he, ih.1⟩⟩

/-- Every signed constant packet in the explicit run range reaches typed
zero by a finite composable path of actual child occurrences. Only the
literal substitution scaling is assumed; no source interior or zero-hit
premise is supplied. This does not prove arbitrary-overlap central entry. -/
theorem constant_composable_path (n d : ℕ) (hd : 5 ≤ d) (H : ℤ)
    (hn : 2*(d : ℤ)*|H| ≤ (n : ℤ))
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (sigma n d a) = β*ℓ a) :
    (packet 2 2 H (-H) 0).Interior ℓ ∧
      Relation.ReflTransGen (InteriorStep (sigma n d) ℓ)
        (packet 2 2 H (-H) 0) (packet 2 2 0 0 0) :=
  digit_path_interior (sigma n d) ℓ β hpos hβ hscale
    (constant_digit_path n d hd H hn) (zero_packet_interior ℓ hpos 2 2)

end Psc.ClassAMinusConstantRecurrence
