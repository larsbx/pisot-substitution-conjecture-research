/-
# The central Class-A nearest-integer recurrence

The hard finite-cycle argument is independent of a floating-point choice of
the Perron root.  `Nearest` retains the strict half-unit error; ties must be
excluded by the arithmetic adapter before using this result.

Source review: `docs/bh-class-a-central-entry-stop-go-2026-11-14.md`.
-/
import PscVerif.ClassAZeroDefectEscape
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Fintype.Pigeonhole

namespace Psc.ClassACentralRecurrence

/-- A strict nearest-integer update, with no unspecified tie convention. -/
def Nearest (h α : ℝ) (a b c : ℤ) : Prop :=
  |(c : ℝ) - (2 * h * (a : ℝ) - α * (b : ℝ))| < 1 / 2

/-- The parameter inequalities supplied by the minus-Class-A Perron root
when the common run has at least five letters. -/
structure Parameters (h α : ℝ) : Prop where
  hpos : 0 < h
  hsmall : h < 1 / 8
  apos : 0 < α
  contraction : α + 2 * h < 1

theorem Nearest.neg {h α : ℝ} {a b c : ℤ} (he : Nearest h α a b c) :
    Nearest h α (-a) (-b) (-c) := by
  unfold Nearest at *
  push_cast
  have heq : -(c : ℝ) - (2 * h * -(a : ℝ) - α * -(b : ℝ)) =
      -((c : ℝ) - (2 * h * (a : ℝ) - α * (b : ℝ))) := by ring
  rw [heq, abs_neg]
  exact he

/-- Strict nearest representatives are unique. -/
theorem Nearest.unique {h α : ℝ} {a b c d : ℤ}
    (hc : Nearest h α a b c) (hd : Nearest h α a b d) : c = d := by
  obtain ⟨hc₁, hc₂⟩ := abs_lt.mp hc
  obtain ⟨hd₁, hd₂⟩ := abs_lt.mp hd
  have hcd : (c : ℝ) - d < 1 := by linarith
  have hdc : (d : ℝ) - c < 1 := by linarith
  have hcd' : c - d < 1 := by exact_mod_cast hcd
  have hdc' : d - c < 1 := by exact_mod_cast hdc
  omega

/-- A single update stays inside any real box whose radius absorbs rounding. -/
theorem nearest_bound {h α : ℝ} (hp : Parameters h α) {a b c : ℤ} {C : ℝ}
    (ha : |(a : ℝ)| ≤ C) (hb : |(b : ℝ)| ≤ C)
    (hC : (α + 2 * h) * C + 1 / 2 ≤ C)
    (he : Nearest h α a b c) : |(c : ℝ)| ≤ C := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  obtain ⟨he₁, he₂⟩ := abs_lt.mp he
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hp.hpos.le (sub_nonneg.mpr ha₁),
      mul_nonneg hp.apos.le (sub_nonneg.mpr hb₂)]
  · nlinarith [mul_nonneg hp.hpos.le (sub_nonneg.mpr ha₂),
      mul_nonneg hp.apos.le (sub_nonneg.mpr hb₁)]

/-- Every forward recurrence is bounded once its initial pair and rounding
reserve fit in the displayed box. No finite-search hypothesis is used. -/
theorem recurrence_bounded {h α : ℝ} (hp : Parameters h α)
    (u : ℕ → ℤ) (hrec : ∀ n, Nearest h α (u n) (u (n + 1)) (u (n + 2)))
    (C : ℝ) (hC : (α + 2 * h) * C + 1 / 2 ≤ C)
    (hzero : |(u 0 : ℝ)| ≤ C) (hone : |(u 1 : ℝ)| ≤ C) :
    ∀ n, |(u n : ℝ)| ≤ C := by
  have pair : ∀ n, |(u n : ℝ)| ≤ C ∧ |(u (n + 1) : ℝ)| ≤ C := by
    intro n
    induction n with
    | zero => exact ⟨hzero, hone⟩
    | succ n ih =>
      exact ⟨ih.2, by simpa [Nat.add_assoc] using nearest_bound hp ih.1 ih.2 hC (hrec n)⟩
  exact fun n => (pair n).1

/-- The extremal inequality at an occurrence of the global maximum. -/
theorem maximum_inequality {h α : ℝ} (hp : Parameters h α)
    {a b A B : ℤ} (ha : a ≤ A) (hb : -B ≤ b)
    (he : Nearest h α a b A) : (1 - 2 * h) * (A : ℝ) - α * B < 1 / 2 := by
  have ha' : (a : ℝ) ≤ A := by exact_mod_cast ha
  have hb' : -(B : ℝ) ≤ b := by exact_mod_cast hb
  have he' := (abs_lt.mp he).2
  nlinarith [mul_nonneg hp.hpos.le (sub_nonneg.mpr ha'),
    mul_nonneg hp.apos.le (sub_nonneg.mpr hb')]

/-- Integer extrema of a bounded two-sided recurrence have equal magnitude. -/
theorem extrema_equal {h α : ℝ} (hp : Parameters h α)
    {A B : ℤ} (hab : -B ≤ A)
    (hA : (1 - 2 * h) * (A : ℝ) - α * B < 1 / 2)
    (hB : (1 - 2 * h) * (B : ℝ) - α * A < 1 / 2) : A = B := by
  have hγ : 0 < 1 - α - 2 * h := by linarith [hp.contraction]
  have oneSide : ∀ X Y : ℤ, -Y ≤ X →
      (1 - 2 * h) * (X : ℝ) - α * Y < 1 / 2 → X ≤ Y := by
    intro X Y hxy hx
    by_contra hh
    have hstep : Y + 1 ≤ X := by omega
    have hX : 1 ≤ X := by omega
    have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hstep' : (Y : ℝ) + 1 ≤ X := by exact_mod_cast hstep
    nlinarith [mul_nonneg hγ.le (sub_nonneg.mpr hX'),
      mul_nonneg hp.apos.le (show 0 ≤ (X : ℝ) - Y - 1 by linarith), hp.hsmall]
  have hAB := oneSide A B hab hA
  have hBA := oneSide B A (by omega) hB
  omega

/-- A nonzero maximum forces the preceding integer to be its negative.
The small-alpha branch uses the integer gap: its amplitude is then one. -/
theorem extreme_predecessor {h α : ℝ} (hp : Parameters h α)
    {a b H : ℤ} (hH : 0 < H) (ha : a ≤ H) (hb : -H ≤ b)
    (hamp : (1 - α - 2 * h) * (H : ℝ) < 1 / 2)
    (he : Nearest h α a b H) : b = -H := by
  by_contra hne
  have hb1 : -H + 1 ≤ b := by omega
  have hb1' : -(H : ℝ) + 1 ≤ b := by exact_mod_cast hb1
  have ha' : (a : ℝ) ≤ H := by exact_mod_cast ha
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  have he' := (abs_lt.mp he).2
  have hγ : 0 < 1 - α - 2 * h := by linarith [hp.contraction]
  by_cases hα : 1 / 2 ≤ α
  · nlinarith [mul_nonneg hp.hpos.le (sub_nonneg.mpr ha'),
      mul_nonneg hp.apos.le (sub_nonneg.mpr hb1'),
      mul_pos hγ (show 0 < (H : ℝ) by exact_mod_cast hH)]
  · have hα' : α < 1 / 2 := by linarith
    have hH2 : (H : ℝ) < 2 := by nlinarith [hp.hsmall]
    have hHi : H < 2 := by exact_mod_cast hH2
    have hHeq : H = 1 := by omega
    have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast (show 0 ≤ b by omega)
    have ha1 : (a : ℝ) ≤ 1 := by simpa [hHeq] using ha'
    subst H
    norm_num at he'
    nlinarith [mul_nonneg hp.hpos.le (sub_nonneg.mpr ha1),
      mul_nonneg hp.apos.le hb0, hp.hsmall]

/-- The alternating pair has precisely the stated strict rounding reserve. -/
theorem alternating_nearest {h α : ℝ} (hp : Parameters h α)
    {H : ℤ} (hH : 0 ≤ H)
    (hamp : (1 - α - 2 * h) * (H : ℝ) < 1 / 2) :
    Nearest h α H (-H) H ∧ Nearest h α (-H) H (-H) := by
  have hz : 0 ≤ (1 - α - 2 * h) * (H : ℝ) :=
    mul_nonneg (by linarith [hp.contraction]) (by exact_mod_cast hH)
  have first : Nearest h α H (-H) H := by
    unfold Nearest
    push_cast
    have heq : (H : ℝ) - (2 * h * H - α * -(H : ℝ)) =
        (1 - α - 2 * h) * H := by ring
    rw [heq, abs_of_nonneg hz]
    exact hamp
  exact ⟨first, by simpa using first.neg⟩

/-- Every bounded two-sided nearest recurrence is already an alternating
cycle. This proves the cycle classification without assuming an extremal
amplitude, a sign pattern, or a preselected return state. -/
theorem bounded_two_sided_alternates {h α : ℝ} (hp : Parameters h α)
    (u : ℤ → ℤ)
    (hrec : ∀ z, Nearest h α (u z) (u (z + 1)) (u (z + 2)))
    (hbdd : ∃ C : ℤ, ∀ z, |u z| ≤ C) :
    ∃ H : ℤ, 0 ≤ H ∧ (1 - α - 2 * h) * (H : ℝ) < 1 / 2 ∧
      (∀ z, u z = H ∨ u z = -H) ∧ (∀ z, u (z + 1) = -u z) := by
  classical
  obtain ⟨C, hC⟩ := hbdd
  have hinh : ∃ v : ℤ, ∃ z : ℤ, u z = v := ⟨u 0, 0, rfl⟩
  obtain ⟨A, ⟨iA, hiA⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun v => ∃ z, u z = v)
    ⟨C, by rintro v ⟨z, rfl⟩; exact (abs_le.mp (hC z)).2⟩ hinh
  obtain ⟨L, ⟨iL, hiL⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun v => ∃ z, u z = v)
    ⟨-C, by rintro v ⟨z, rfl⟩; exact (abs_le.mp (hC z)).1⟩ hinh
  have hupper : ∀ z, u z ≤ A := fun z => hmax _ ⟨z, rfl⟩
  have hlower : ∀ z, L ≤ u z := fun z => hmin _ ⟨z, rfl⟩
  have hAe : Nearest h α (u (iA - 2)) (u (iA - 1)) A := by
    simpa only [show iA - 2 + 1 = iA - 1 by omega,
      show iA - 2 + 2 = iA by omega, hiA] using hrec (iA - 2)
  have hLe : Nearest h α (-(u (iL - 2))) (-(u (iL - 1))) (-L) := by
    have h := (hrec (iL - 2)).neg
    simpa only [show iL - 2 + 1 = iL - 1 by omega,
      show iL - 2 + 2 = iL by omega, hiL] using h
  have hAi := maximum_inequality hp (hupper (iA - 2))
    (show -(-L) ≤ u (iA - 1) by simpa using hlower (iA - 1)) hAe
  have hLi := maximum_inequality hp
    (show -(u (iL - 2)) ≤ -L by have := hlower (iL - 2); omega)
    (show -A ≤ -(u (iL - 1)) by have := hupper (iL - 1); omega) hLe
  have hAL : A = -L := extrema_equal hp (by simpa [hiA] using hlower iA) hAi hLi
  have hH : 0 ≤ A := by have := hlower iA; omega
  have hamp : (1 - α - 2 * h) * (A : ℝ) < 1 / 2 := by
    rw [← hAL] at hAi
    nlinarith [hAi]
  have hbounds : ∀ z, -A ≤ u z ∧ u z ≤ A := by
    intro z
    constructor
    · have := hlower z; omega
    · exact hupper z
  refine ⟨A, hH, hamp, ?_⟩
  by_cases hzero : A = 0
  · have hu : ∀ z, u z = 0 := by intro z; have := hbounds z; omega
    exact ⟨fun z => Or.inl (by simp [hu, hzero]), fun z => by simp [hu]⟩
  have hpos : 0 < A := by omega
  have pred_pos : ∀ z, u z = A → u (z - 1) = -A := by
    intro z hz
    have he : Nearest h α (u (z - 2)) (u (z - 1)) A := by
      simpa only [show z - 2 + 1 = z - 1 by omega,
        show z - 2 + 2 = z by omega, hz] using hrec (z - 2)
    exact extreme_predecessor hp hpos (hbounds _).2 (hbounds _).1 hamp he
  have pred_neg : ∀ z, u z = -A → u (z - 1) = A := by
    intro z hz
    have he : Nearest h α (-(u (z - 2))) (-(u (z - 1))) A := by
      have hh := (hrec (z - 2)).neg
      simpa only [show z - 2 + 1 = z - 1 by omega,
        show z - 2 + 2 = z by omega, hz, neg_neg] using hh
    have hh := extreme_predecessor hp hpos
      (show -(u (z - 2)) ≤ A by have := hbounds (z - 2); omega)
      (show -A ≤ -(u (z - 1)) by have := hbounds (z - 1); omega) hamp he
    omega
  have back : ∀ z, (u z = A ∨ u z = -A) →
      (u (z - 1) = A ∨ u (z - 1) = -A) ∧ u (z - 1) = -u z := by
    intro z hz
    rcases hz with hz | hz
    · have hpz := pred_pos z hz
      exact ⟨Or.inr hpz, by rw [hz, hpz]⟩
    · have hpz := pred_neg z hz
      exact ⟨Or.inl hpz, by rw [hz, hpz, neg_neg]⟩
  have forward : ∀ z, (u z = A ∨ u z = -A) → u (z - 1) = -u z →
      (u (z + 1) = A ∨ u (z + 1) = -A) ∧ u (z + 1) = -u z := by
    intro z hz hpz
    have he : Nearest h α (u (z - 1)) (u z) (u (z + 1)) := by
      simpa only [show z - 1 + 1 = z by omega,
        show z - 1 + 2 = z + 1 by omega] using hrec (z - 1)
    obtain ⟨hplus, hminus⟩ := alternating_nearest hp hH hamp
    rcases hz with hz | hz
    · have he' : Nearest h α (-A) A (u (z + 1)) := by simpa [hpz, hz] using he
      have heq := he'.unique hminus
      exact ⟨Or.inr heq, by simpa [hz] using heq⟩
    · have he' : Nearest h α A (-A) (u (z + 1)) := by simpa [hpz, hz] using he
      have heq := he'.unique hplus
      exact ⟨Or.inl heq, by simpa [hz] using heq⟩
  have future : ∀ m : ℕ,
      (u (iA + m) = A ∨ u (iA + m) = -A) ∧
      u (iA + m + 1) = -u (iA + m) := by
    intro m
    induction m with
    | zero =>
      have ha : u iA = A ∨ u iA = -A := Or.inl hiA
      have hf := forward iA ha (back iA ha).2
      simpa using And.intro ha hf.2
    | succ m ih =>
      have hz : u (iA + m + 1) = A ∨ u (iA + m + 1) = -A := by
        rcases ih.1 with hh | hh
        · exact Or.inr (by rw [ih.2, hh])
        · exact Or.inl (by rw [ih.2, hh, neg_neg])
      have hpz : u (iA + m + 1 - 1) = -u (iA + m + 1) := by
        rw [show iA + m + 1 - 1 = iA + m by omega, ih.2, neg_neg]
      have hf := forward (iA + m + 1) hz hpz
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using And.intro hz hf.2
  have past : ∀ m : ℕ,
      (u (iA - m) = A ∨ u (iA - m) = -A) ∧
      u (iA - m + 1) = -u (iA - m) := by
    intro m
    induction m with
    | zero => simpa using future 0
    | succ m ih =>
      have hb := back (iA - m) ih.1
      have eqi : iA - ((m + 1 : ℕ) : ℤ) = iA - m - 1 := by push_cast; ring
      rw [eqi]
      refine ⟨hb.1, ?_⟩
      rw [show iA - m - 1 + 1 = iA - m by omega, hb.2, neg_neg]
  have hall : ∀ z, (u z = A ∨ u z = -A) ∧ u (z + 1) = -u z := by
    intro z
    by_cases hz : iA ≤ z
    · have heq : iA + ((z - iA).toNat : ℤ) = z := by
        rw [Int.toNat_of_nonneg (by omega)]; omega
      simpa only [heq] using future (z - iA).toNat
    · have heq : iA - ((iA - z).toNat : ℤ) = z := by
        rw [Int.toNat_of_nonneg (by omega)]; omega
      simpa only [heq] using past (iA - z).toNat
  exact ⟨fun z => (hall z).1, fun z => (hall z).2⟩

/-- A forward recurrence has a finite integer bound, obtained from
contraction and its initial pair rather than from a supplied finite graph. -/
theorem recurrence_has_integer_bound {h α : ℝ} (hp : Parameters h α)
    (u : ℕ → ℤ) (hrec : ∀ n, Nearest h α (u n) (u (n + 1)) (u (n + 2))) :
    ∃ C : ℕ, ∀ n, |u n| ≤ (C : ℤ) := by
  have hden : 0 < 2 * (1 - α - 2 * h) := by linarith [hp.contraction]
  obtain ⟨C, hC⟩ := exists_nat_gt
    (max |(u 0 : ℝ)| (max |(u 1 : ℝ)| (1 / (2 * (1 - α - 2 * h)))))
  have hzero : |(u 0 : ℝ)| ≤ C := (le_max_left _ _).trans hC.le
  have hone : |(u 1 : ℝ)| ≤ C := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hC.le
  have hreserve : 1 / (2 * (1 - α - 2 * h)) < (C : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hmul := (div_lt_iff₀ hden).1 hreserve
  have hround : (α + 2 * h) * (C : ℝ) + 1 / 2 ≤ C := by nlinarith
  have hall := recurrence_bounded hp u hrec (C : ℝ) hround hzero hone
  refine ⟨C, fun n => ?_⟩
  have hh := hall n
  exact_mod_cast hh

/-- A genuine finite periodic recurrence has only the zero cycle or one
alternating pair. Boundedness and the extrema are derived here. -/
theorem periodic_recurrence_classification {h α : ℝ} (hp : Parameters h α)
    (u : ℤ → ℤ) (T : ℤ) (hT : 0 < T) (hperiod : Function.Periodic u T)
    (hrec : ∀ z, Nearest h α (u z) (u (z + 1)) (u (z + 2))) :
    ∃ H : ℤ, 0 ≤ H ∧ (1 - α - 2 * h) * (H : ℝ) < 1 / 2 ∧
      (∀ z, u z = H ∨ u z = -H) ∧ (∀ z, u (z + 1) = -u z) := by
  classical
  apply bounded_two_sided_alternates hp u hrec
  refine ⟨∑ z ∈ Finset.Ico 0 T, |u z|, ?_⟩
  intro z
  have hmod : u (z % T) = u z := by
    have hh := (hperiod.int_mul (z / T)) (z % T)
    simpa [Int.emod_add_ediv_mul] using hh.symm
  have hm : z % T ∈ Finset.Ico 0 T := Finset.mem_Ico.mpr
    ⟨Int.emod_nonneg _ (ne_of_gt hT), Int.emod_lt_of_pos _ hT⟩
  rw [← hmod]
  exact Finset.single_le_sum (fun i _ => abs_nonneg (u i)) hm

/-- The half-unit selector fits inside the two literal y-runs already at
`n = 6`. Its numeric ordinals therefore cannot silently become LAST. -/
theorem central_gap_in_run (n : ℕ) (hn : 6 ≤ n) (β θ : ℝ)
    (hβ : 0 < β) (hβhi : β < (n : ℝ) + 3)
    (hθ : |θ| < 1 / 2) (g : ℤ) (hg : |β * θ + (g : ℝ)| < 1 / 2) :
    -((n - 2 : ℕ) : ℤ) ≤ g ∧ g ≤ ((n - 2 : ℕ) : ℤ) := by
  obtain ⟨hθlo, hθhi⟩ := abs_lt.mp hθ
  obtain ⟨hglo, hghi⟩ := abs_lt.mp hg
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hlo : -((n : ℝ) - 1) < g := by
    nlinarith [mul_pos hβ (show 0 < 1 / 2 - θ by linarith)]
  have hhi : (g : ℝ) < (n : ℝ) - 1 := by
    nlinarith [mul_pos hβ (show 0 < θ + 1 / 2 by linarith)]
  have hlo' : -((n : ℤ) - 1) < g := by exact_mod_cast hlo
  have hhi' : g < (n : ℤ) - 1 := by exact_mod_cast hhi
  omega

open ClassAZeroDefectEscape in
/-- The rounded gap is realized by its original two positive RUN ordinals,
with all three integral coordinates retained. -/
theorem run_gap_digit_step (n d : ℕ) (hn : 2 ≤ n) (p q r g : ℤ)
    (hglo : -((n - 2 : ℕ) : ℤ) ≤ g)
    (hghi : g ≤ ((n - 2 : ℕ) : ℤ)) :
    IndexedDigitStep (sigma n d) (packet 2 2 p q r)
      ((-g).toNat + 1) (g.toNat + 1)
      (packet 2 2 (2*p+q+r) (q+r)
        (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+g)) := by
  have hn1 : 1 ≤ n := by omega
  have hi : (-g).toNat < runLength n d 2 := by simp [runLength]; omega
  have hj : g.toNat < runLength n d 2 := by simp [runLength]; omega
  have hh : (g.toNat : ℤ) - ((-g).toNat : ℤ) = g := by omega
  have he := positive_step n d hn1 2 2 (-g).toNat g.toNat hi.le hj.le p q r
  have ht : ((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+
      (g.toNat : ℤ)-((-g).toNat : ℤ) =
      ((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+g := by omega
  simpa only [positiveMark_letter_of_lt n d 2 (-g).toNat hi,
    positiveMark_letter_of_lt n d 2 g.toNat hj, delta, ite_false,
    show (2 : Fin 3) ≠ 1 by decide, sub_self, sub_zero, add_zero, ht] using he

/-- After one literal RUN step, the next first coordinate is the nearest
recurrence: the central physical error is exactly its rounding error. -/
theorem central_coordinate_recurrence (h α : ℝ) (a b r : ℤ)
    (hc : |(2 + α - h) * (b : ℝ) + (1 + h) * ((b - 2*a : ℤ) : ℝ) + r|
      < 1 / 2) : Nearest h α a b (3*b-2*a+r) := by
  unfold Nearest
  push_cast at *
  convert hc using 1
  congr 1
  ring

/-- Public bound endpoint with every real-parameter hypothesis explicit. -/
theorem forward_integer_bound (h α : ℝ) (hpos : 0 < h) (hsmall : h < 1 / 8)
    (apos : 0 < α) (hcontract : α + 2 * h < 1)
    (u : ℕ → ℤ)
    (hrec : ∀ n, |(u (n+2) : ℝ) - (2*h*(u n : ℝ)-α*(u (n+1) : ℝ))| < 1/2) :
    ∃ C : ℕ, ∀ n, |u n| ≤ (C : ℤ) :=
  recurrence_has_integer_bound ⟨hpos, hsmall, apos, hcontract⟩ u hrec

/-- Public periodic endpoint with no unrecorded graph, extremum, sign,
or finiteness premise. A positive period is the only cycle hypothesis. -/
theorem periodic_cycle_classification (h α : ℝ) (hpos : 0 < h) (hsmall : h < 1 / 8)
    (apos : 0 < α) (hcontract : α + 2 * h < 1)
    (u : ℤ → ℤ) (T : ℤ) (hT : 0 < T) (hperiod : ∀ z, u (z+T) = u z)
    (hrec : ∀ z, |(u (z+2) : ℝ) - (2*h*(u z : ℝ)-α*(u (z+1) : ℝ))| < 1/2) :
    ∃ H : ℤ, 0 ≤ H ∧ (1-α-2*h)*(H : ℝ) < 1/2 ∧
      (∀ z, u z = H ∨ u z = -H) ∧ (∀ z, u (z+1) = -u z) :=
  periodic_recurrence_classification ⟨hpos, hsmall, apos, hcontract⟩ u T hT hperiod hrec

/-- The stronger two-sided endpoint exposes its genuine boundedness
premise; it does not replace the unconditional forward bound above. -/
theorem bounded_two_sided_classification (h α : ℝ) (hpos : 0 < h)
    (hsmall : h < 1 / 8) (apos : 0 < α) (hcontract : α + 2 * h < 1)
    (u : ℤ → ℤ)
    (hrec : ∀ z, |(u (z+2) : ℝ) - (2*h*(u z : ℝ)-α*(u (z+1) : ℝ))| < 1/2)
    (hbdd : ∃ C : ℤ, ∀ z, |u z| ≤ C) :
    ∃ H : ℤ, 0 ≤ H ∧ (1-α-2*h)*(H : ℝ) < 1/2 ∧
      (∀ z, u z = H ∨ u z = -H) ∧ (∀ z, u (z+1) = -u z) :=
  bounded_two_sided_alternates ⟨hpos, hsmall, apos, hcontract⟩ u hrec hbdd

/-- Contraction and the central selector do admit nonzero cycles. A separate
actual-occurrence exit is necessary; boundedness is not a zero-hit proof. -/
theorem nonzero_cycle_control :
    Parameters (1/16) (3/4) ∧
      Nearest (1/16) (3/4) 1 (-1) 1 ∧
      Nearest (1/16) (3/4) (-1) 1 (-1) ∧ (1 : ℤ) ≠ 0 := by
  constructor
  · constructor <;> norm_num
  · norm_num [Nearest]

/-- A repeated integer pair forces equality of the complete forward tails.
Strict nearest-integer uniqueness is the only determinism premise. -/
theorem repeated_pair_tail {h α : ℝ} (u : ℕ → ℤ)
    (hrec : ∀ n, Nearest h α (u n) (u (n+1)) (u (n+2)))
    {i j : ℕ} (hfirst : u i = u j) (hsecond : u (i+1) = u (j+1)) :
    ∀ m, u (i+m) = u (j+m) ∧ u (i+m+1) = u (j+m+1) := by
  intro m
  induction m with
  | zero => simpa using And.intro hfirst hsecond
  | succ m ih =>
    have hi := hrec (i+m)
    have hj := hrec (j+m)
    rw [ih.1, ih.2] at hi
    have heq := hi.unique hj
    simpa only [Nat.add_assoc] using And.intro ih.2 heq

/-- The finite pair range is derived from the contraction bound. Its
pigeonhole repetition supplies an actual positive period of a tail. -/
theorem recurrence_eventually_periodic {h α : ℝ} (hp : Parameters h α)
    (u : ℕ → ℤ)
    (hrec : ∀ n, Nearest h α (u n) (u (n+1)) (u (n+2))) :
    ∃ N T : ℕ, 0 < T ∧ ∀ m, u (N+(m+T)) = u (N+m) := by
  classical
  obtain ⟨C, hC⟩ := recurrence_has_integer_bound hp u hrec
  let S : Finset ℤ := Finset.Icc (-(C : ℤ)) (C : ℤ)
  have hmem : ∀ n, u n ∈ S := by
    intro n
    exact Finset.mem_Icc.mpr (abs_le.mp (hC n))
  let pairs : ℕ → ({z : ℤ // z ∈ S} × {z : ℤ // z ∈ S}) :=
    fun n => (⟨u n, hmem n⟩, ⟨u (n+1), hmem (n+1)⟩)
  obtain ⟨i, j, hij, hpairs⟩ := Finite.exists_ne_map_eq_of_infinite pairs
  have hfirst : u i = u j := congrArg (fun z => z.1.val) hpairs
  have hsecond : u (i+1) = u (j+1) := congrArg (fun z => z.2.val) hpairs
  have build : ∀ i j : ℕ, i < j → u i = u j → u (i+1) = u (j+1) →
      ∃ N T : ℕ, 0 < T ∧ ∀ m, u (N+(m+T)) = u (N+m) := by
    intro i j hlt hfirst hsecond
    refine ⟨i, j-i, by omega, ?_⟩
    intro m
    have hh := (repeated_pair_tail u hrec hfirst hsecond m).1.symm
    have heq : i + (m + (j-i)) = j+m := by omega
    simpa only [heq] using hh
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact build i j hlt hfirst hsecond
  · exact build j i hlt hfirst.symm hsecond.symm

/-- The residue identity used to extend a finite periodic word in both
directions. The modulus is the actual positive period. -/
theorem periodic_residue_shift (T : ℕ) (hT : 0 < T) (z : ℤ) (m : ℕ) :
    ((z + (m : ℤ)) % (T : ℤ)).toNat = ((z % (T : ℤ)).toNat + m) % T := by
  have hz : 0 ≤ z % (T : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hT))
  have heq : (z + (m : ℤ)) % (T : ℤ) =
      ((((z % (T : ℤ)).toNat + m) : ℕ) : ℤ) % (T : ℤ) := by
    simp only [Nat.cast_add, Int.toNat_of_nonneg hz, Int.add_emod, Int.emod_emod]
  rw [heq, ← Int.natCast_emod, Int.toNat_natCast]

/-- Classification of a genuinely periodic forward word. The two-sided
extension preserves every recurrence triple, including the wraparound. -/
theorem nat_periodic_classification {h α : ℝ} (hp : Parameters h α)
    (v : ℕ → ℤ) (T : ℕ) (hT : 0 < T) (hperiod : Function.Periodic v T)
    (hrec : ∀ n, Nearest h α (v n) (v (n+1)) (v (n+2))) :
    ∃ H : ℤ, 0 ≤ H ∧ (1-α-2*h)*(H : ℝ) < 1/2 ∧
      (∀ n, v n = H ∨ v n = -H) ∧ (∀ n, v (n+1) = -v n) := by
  let w : ℤ → ℤ := fun z => v ((z % (T : ℤ)).toNat)
  have wshift : ∀ (z : ℤ) (m : ℕ), w (z + m) = v ((z % (T : ℤ)).toNat + m) := by
    intro z m
    dsimp [w]
    rw [periodic_residue_shift T hT z m, hperiod.map_mod_nat]
  have wnat : ∀ n : ℕ, w n = v n := by
    intro n
    dsimp [w]
    rw [← Int.natCast_emod, Int.toNat_natCast, hperiod.map_mod_nat]
  have wp : Function.Periodic w (T : ℤ) := by
    intro z
    dsimp [w]
    rw [Int.add_emod_right]
  have wr : ∀ z, Nearest h α (w z) (w (z+1)) (w (z+2)) := by
    intro z
    have h1 := wshift z 1
    have h2 := wshift z 2
    norm_num only [Nat.cast_one, Nat.cast_ofNat] at h1 h2
    rw [h1, h2]
    exact hrec ((z % (T : ℤ)).toNat)
  obtain ⟨H, hH, hamp, hsign, halt⟩ := periodic_recurrence_classification
    hp w (T : ℤ) (by exact_mod_cast hT) wp wr
  refine ⟨H, hH, hamp, ?_, ?_⟩
  · intro n
    simpa only [wnat] using hsign n
  · intro n
    have hh := halt (n : ℤ)
    simpa only [← Nat.cast_add_one, wnat] using hh

/-- Every forward recurrence eventually reaches an alternating tail.
Boundedness, pair repetition, the positive tail period and the cycle shape
are all proved; none is an extra input hypothesis. -/
theorem eventual_alternating_tail (h α : ℝ) (hpos : 0 < h) (hsmall : h < 1/8)
    (apos : 0 < α) (hcontract : α+2*h < 1) (u : ℕ → ℤ)
    (hrec : ∀ n, |(u (n+2) : ℝ)-(2*h*(u n : ℝ)-α*(u (n+1) : ℝ))| < 1/2) :
    ∃ N : ℕ, ∃ H : ℤ, 0 ≤ H ∧ (1-α-2*h)*(H : ℝ) < 1/2 ∧
      (∀ m, u (N+m) = H ∨ u (N+m) = -H) ∧
      (∀ m, u (N+m+1) = -u (N+m)) := by
  let hp : Parameters h α := ⟨hpos, hsmall, apos, hcontract⟩
  obtain ⟨N, T, hT, hperiod⟩ := recurrence_eventually_periodic hp u hrec
  let v : ℕ → ℤ := fun m => u (N+m)
  have hvp : Function.Periodic v T := hperiod
  have hvr : ∀ m, Nearest h α (v m) (v (m+1)) (v (m+2)) := by
    intro m
    simpa only [Nearest, v, Nat.add_assoc] using hrec (N+m)
  obtain ⟨H, hH, hamp, hsign, halt⟩ := nat_periodic_classification hp v T hT hvp hvr
  exact ⟨N, H, hH, hamp, hsign, by simpa only [v, Nat.add_assoc] using halt⟩

end Psc.ClassACentralRecurrence
