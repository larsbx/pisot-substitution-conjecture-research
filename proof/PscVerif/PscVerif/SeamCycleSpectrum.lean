/-
# The cyclotomic step of the one-track seam theorem, and Lemma A

`docs/c4-one-track-seam-spectrum-2026-11-17.md` (theorem *cycle correction*) and
`docs/c4-neutral-rank-seam-ceiling-2026-11-18.md` (Lemma A).

**Spectral step.**  Index the `D`-th roots of unity by `k : ZMod D` through
`ZMod.stdAddChar`.  A virtual multiplicity `a : ZMod D → ℂ` has power sums
`vtrace a n = ∑ₖ a k · χ(k n)`.  A list `S` of cycle lengths dividing `D` has fixed-point
count `cyc S n = ∑_{q ∈ S, q ∣ n} q` at power `n`, and multiplicity
`mult S k = #{q ∈ S | ord k ∣ q}`.  Proved here:
* `eq_of_vtrace`: power sums at `n = 1, …, D` determine the multiplicities (injectivity of
  `ZMod.dft`);
* `sum_kernel`: `∑_{q k = 0} χ(k n) = q · [q ∣ n]` for `q ∣ D`;
* `vtrace_mult`: `vtrace (mult S) = cyc S`;
* **`cycle_correction`**: if the power sums of two virtual multiplicities differ by
  `cyc U − cyc L − cyc R` at every `n ≥ 1`, their difference at every `k` is
  `mult U k − mult L k − mult R k`; `mult_eq_card_order` rewrites `mult` as the number of
  cycle lengths divisible by the order `d` of the root.  This is the formula
  `b_d = #{q ∈ U, d ∣ q} − #{q ∈ L, d ∣ q} − #{q ∈ R, d ∣ q}` of the seam note.

**Lemma A.**
* `iterate_shift`, **`isPeriodicPt_shift_iff`**, **`minimalPeriod_shift`**: for
  `φ (e, i) = (π e, i + 1)` on `E × ZMod p`, the point `(e, i)` is `φ`-periodic at `n` iff
  `p ∣ n` and `e` is `π`-periodic at `n`, and its minimal period is `p · minimalPeriod (π^p) e`;
  so an orbit of length `k` of `π^p` in the base copy is an orbit of length `p k` of `φ`, and
  `d` divides it iff `d ∣ p k`.
* **`ceiling_bounds`**: a sum over interior cycles of per-cycle values of admissible subgraphs
  lies between the sums of the per-cycle minima and maxima.

**Not proved here.**  The trace identities of #598 that make the difference of the bigon and
overlap power sums equal to `cyc U − cyc L − cyc R` (the hypothesis of `cycle_correction`),
and the agreement of their spectra away from roots of unity; the embedding of the seam graph
into copied bigram graphs (#601) that makes the actual seam graph admissible.
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Dynamics.PeriodicPts.Defs

namespace Psc.SeamCycleSpectrum

open Complex ZMod Finset

/-! ### Power sums on the roots of unity -/

section Spectrum

variable {D : ℕ} [NeZero D]

/-- Power sums of a virtual multiplicity on the `D`-th roots of unity. -/
noncomputable def vtrace (a : ZMod D → ℂ) (n : ℕ) : ℂ := ∑ k, a k * stdAddChar (k * (n : ZMod D))

theorem vtrace_eq_dft (a : ZMod D → ℂ) (n : ℕ) : vtrace a n = 𝓕 a (-(n : ZMod D)) := by
  simp only [vtrace, dft_apply, smul_eq_mul, mul_neg, neg_neg]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem vtrace_sub (a b : ZMod D → ℂ) (n : ℕ) : vtrace (a - b) n = vtrace a n - vtrace b n := by
  simp only [vtrace, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem vtrace_period (a : ZMod D → ℂ) : vtrace a D = vtrace a 0 := by
  simp [vtrace]

/-- **Power sums determine multiplicities.** -/
theorem eq_of_vtrace {a b : ZMod D → ℂ} (h : ∀ n : ℕ, vtrace a n = vtrace b n) : a = b := by
  apply (dft (N := D) (E := ℂ)).injective
  funext k
  have hk : k = -(((-k).val : ℕ) : ZMod D) := by rw [ZMod.natCast_zmod_val, neg_neg]
  rw [hk, ← vtrace_eq_dft, ← vtrace_eq_dft, h]

/-! ### The character sum over a cyclic kernel -/

theorem kernel_iff {q : ℕ} (hq : 0 < q) (hqD : q ∣ D) (k : ZMod D) :
    (q : ZMod D) * k = 0 ↔ ∃ j < q, k = ((j * (D / q) : ℕ) : ZMod D) := by
  obtain ⟨r, hr⟩ := hqD
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hr0 : 0 < r := Nat.pos_of_ne_zero fun h => by simp [h] at hr; omega
  have hDq : D / q = r := by rw [hr, Nat.mul_div_cancel_left _ hq]
  rw [hDq]
  constructor
  · intro h
    rw [← ZMod.natCast_zmod_val k, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
    have h' : q * r ∣ q * k.val := by rw [← hr]; exact h
    obtain ⟨j, hj⟩ := (Nat.mul_dvd_mul_iff_left hq).1 h'
    have hlt := ZMod.val_lt k
    refine ⟨j, ?_, ?_⟩
    · by_contra hge
      push Not at hge
      have : r * q ≤ r * j := Nat.mul_le_mul_left r hge
      rw [mul_comm r q, ← hr, ← hj] at this
      omega
    · rw [← ZMod.natCast_zmod_val k, hj, mul_comm]
  · rintro ⟨j, -, rfl⟩
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, hr]
    exact ⟨j, by ring⟩

theorem geom_root_sum {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∑ j ∈ range q, exp (2 * (Real.pi : ℂ) * I * n / q) ^ j = if q ∣ n then (q : ℂ) else 0 := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have : exp (2 * (Real.pi : ℂ) * I * ((q * m : ℕ) : ℂ) / q) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * I * ((q * m : ℕ) : ℂ) / q = (m : ℂ) * (2 * (Real.pi : ℂ) * I) by
        push_cast; field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I m
    push_cast at this ⊢
    simp [this]
  · set w := exp (2 * (Real.pi : ℂ) * I * n / q)
    have hw : w ≠ 1 := by
      intro hw
      obtain ⟨t, ht⟩ := Complex.exp_eq_one_iff.1 hw
      have hnt : (n : ℂ) = t * q := by
        have h2 : (2 * (Real.pi : ℂ) * I : ℂ) ≠ 0 := by simp [I_ne_zero]
        field_simp at ht
        linear_combination ht
      have : (n : ℤ) = t * q := by exact_mod_cast hnt
      exact hdvd (Int.natCast_dvd_natCast.1 ⟨t, by rw [this, mul_comm]⟩)
    have hwq : w ^ q = 1 := by
      rw [← Complex.exp_nat_mul, show (q : ℂ) * (2 * (Real.pi : ℂ) * I * n / q) = (n : ℂ) * (2 * (Real.pi : ℂ) * I) by
        field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I n
    rw [geom_sum_eq hw, hwq, sub_self, zero_div]

/-- **Character sum over the `q`-torsion**: `∑_{q k = 0} χ(k n) = q · [q ∣ n]`. -/
theorem sum_kernel {q : ℕ} (hq : 0 < q) (hqD : q ∣ D) (n : ℕ) :
    ∑ k ∈ univ.filter (fun k : ZMod D => (q : ZMod D) * k = 0), stdAddChar (k * (n : ZMod D)) =
      if q ∣ n then (q : ℂ) else 0 := by
  classical
  obtain ⟨r, hr⟩ := hqD
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hr0 : 0 < r := Nat.pos_of_ne_zero fun h => by simp [h] at hr; omega
  have hDq : D / q = r := by rw [hr, Nat.mul_div_cancel_left _ hq]
  have hset : univ.filter (fun k : ZMod D => (q : ZMod D) * k = 0) =
      (range q).image (fun j => ((j * r : ℕ) : ZMod D)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range,
      kernel_iff hq ⟨r, hr⟩, hDq]
    exact ⟨fun ⟨j, hj, hk⟩ => ⟨j, hj, hk.symm⟩, fun ⟨j, hj, hk⟩ => ⟨j, hj, hk.symm⟩⟩
  have hinj : Set.InjOn (fun j => ((j * r : ℕ) : ZMod D)) (range q) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    have hi' : i * r < D := by rw [hr]; nlinarith
    have hj' : j * r < D := by rw [hr]; nlinarith
    have := congrArg ZMod.val hij
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at this
    exact Nat.eq_of_mul_eq_mul_right hr0 this
  rw [hset, sum_image hinj, ← geom_root_sum hq n]
  refine sum_congr rfl fun j _ => ?_
  rw [← Nat.cast_mul, show ((j * r * n : ℕ) : ZMod D) = (((j * r * n : ℕ) : ℤ) : ZMod D) by
    push_cast; rfl, stdAddChar_coe, ← Complex.exp_nat_mul]
  congr 1
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hr' : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr0.ne'
  rw [hr]
  push_cast
  field_simp

/-! ### Cycle lists -/

/-- Fixed-point count of disjoint cycles of the given lengths at power `n`. -/
noncomputable def cyc (S : Multiset ℕ) (n : ℕ) : ℂ :=
  (S.map fun q => if q ∣ n then (q : ℂ) else 0).sum

/-- Multiplicity at the root indexed by `k`: cycles whose length the order of `k` divides. -/
noncomputable def mult (S : Multiset ℕ) (k : ZMod D) : ℂ :=
  ((S.filter fun q : ℕ => (q : ZMod D) * k = 0).card : ℂ)

omit [NeZero D] in
theorem mult_eq_card_order (S : Multiset ℕ) (k : ZMod D) :
    mult S k = ((S.filter fun q : ℕ => addOrderOf k ∣ q).card : ℂ) := by
  simp only [mult]
  congr 2
  exact Multiset.filter_congr fun q _ => by rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_mul]

theorem vtrace_mult (S : Multiset ℕ) (hS : ∀ q ∈ S, 0 < q ∧ q ∣ D) (n : ℕ) :
    vtrace (mult (D := D) S) n = cyc S n := by
  classical
  induction S using Multiset.induction_on with
  | empty => simp [vtrace, mult, cyc]
  | cons q S ih =>
    have hq := hS q (Multiset.mem_cons_self q S)
    have ih' := ih fun p hp => hS p (Multiset.mem_cons_of_mem hp)
    have hsplit : ∀ k : ZMod D, mult (q ::ₘ S) k =
        (if (q : ZMod D) * k = 0 then 1 else 0) + mult S k := by
      intro k
      simp only [mult, Multiset.filter_cons]
      split_ifs <;> simp [add_comm]
    simp only [vtrace] at ih' ⊢
    simp only [hsplit, add_mul, sum_add_distrib, ih', cyc, Multiset.map_cons, Multiset.sum_cons]
    congr 1
    rw [← sum_kernel hq.1 hq.2 n, sum_filter]
    exact sum_congr rfl fun k _ => by split_ifs <;> simp

/-- **The cyclotomic step of the seam theorem.** -/
theorem cycle_correction (a b : ZMod D → ℂ) (U L R : Multiset ℕ)
    (hU : ∀ q ∈ U, 0 < q ∧ q ∣ D) (hL : ∀ q ∈ L, 0 < q ∧ q ∣ D) (hR : ∀ q ∈ R, 0 < q ∧ q ∣ D)
    (h : ∀ n, 1 ≤ n → vtrace a n - vtrace b n = cyc U n - cyc L n - cyc R n) (k : ZMod D) :
    a k - b k = mult U k - mult L k - mult R k := by
  have hall : ∀ n, vtrace (a - b) n = vtrace (mult (D := D) U - mult L - mult R) n := by
    intro n
    have key : ∀ m, 1 ≤ m →
        vtrace (a - b) m = vtrace (mult (D := D) U - mult L - mult R) m := fun m hm => by
      rw [vtrace_sub, vtrace_sub, vtrace_sub, vtrace_mult U hU, vtrace_mult L hL,
        vtrace_mult R hR, h m hm]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [← vtrace_period, ← vtrace_period]
      exact key D (Nat.pos_of_ne_zero (NeZero.ne D))
    · exact key n hn
  have := congrFun (eq_of_vtrace hall) k
  simpa using this

end Spectrum

/-! ### Lemma A: copies over an interior cycle -/

section Copies

variable {E : Type*} (g : E → E) (p : ℕ)

/-- `φ (e, i) = (g e, i + 1)` on `E × ZMod p`. -/
def shift (x : E × ZMod p) : E × ZMod p := (g x.1, x.2 + 1)

theorem iterate_shift (n : ℕ) (x : E × ZMod p) :
    (shift g p)^[n] x = (g^[n] x.1, x.2 + n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [shift, Function.iterate_succ_apply]
    ring

theorem isPeriodicPt_shift_iff (n : ℕ) (x : E × ZMod p) :
    Function.IsPeriodicPt (shift g p) n x ↔ p ∣ n ∧ Function.IsPeriodicPt g n x.1 := by
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, iterate_shift, Prod.ext_iff,
    add_eq_left, ZMod.natCast_eq_zero_iff]
  exact and_comm

/-- **Orbit law**: the minimal period of `(e, i)` is `p · minimalPeriod (g^p) e`. -/
theorem minimalPeriod_shift [NeZero p] (x : E × ZMod p) :
    Function.minimalPeriod (shift g p) x = p * Function.minimalPeriod (g^[p]) x.1 := by
  set m := Function.minimalPeriod g x.1
  have hlcm : Function.minimalPeriod (shift g p) x = Nat.lcm p m := by
    apply Nat.dvd_antisymm
    · apply Function.IsPeriodicPt.minimalPeriod_dvd
      rw [isPeriodicPt_shift_iff]
      exact ⟨Nat.dvd_lcm_left _ _,
        (Function.isPeriodicPt_minimalPeriod g x.1).trans_dvd (Nat.dvd_lcm_right p m)⟩
    · have h := (isPeriodicPt_shift_iff g p _ x).1 (Function.isPeriodicPt_minimalPeriod _ x)
      exact Nat.lcm_dvd h.1 h.2.minimalPeriod_dvd
  rw [hlcm, Function.minimalPeriod_iterate_eq_div_gcd (NeZero.ne p), Nat.lcm, Nat.gcd_comm,
    Nat.mul_div_assoc _ (Nat.gcd_dvd_left m p)]

/-- An orbit of length `k` of `g^p` gives an orbit whose length `d` divides iff `d ∣ p k`. -/
theorem dvd_minimalPeriod_shift_iff [NeZero p] (x : E × ZMod p) (d : ℕ) :
    d ∣ Function.minimalPeriod (shift g p) x ↔ d ∣ p * Function.minimalPeriod (g^[p]) x.1 := by
  rw [minimalPeriod_shift]

end Copies

/-! ### Lemma A: the ceiling -/

/-- **Ceiling and floor.**  If each interior cycle `γ` contributes the value of an admissible
seam subgraph `S γ ∈ adm γ`, the total lies between the sums of per-cycle minima and maxima. -/
theorem ceiling_bounds {Γ X : Type*} (G : Finset Γ) (adm : Γ → Finset (Finset X))
    (hne : ∀ γ, (adm γ).Nonempty) (w : Γ → Finset X → ℤ) (S : Γ → Finset X)
    (hS : ∀ γ ∈ G, S γ ∈ adm γ) :
    ∑ γ ∈ G, (adm γ).inf' (hne γ) (w γ) ≤ ∑ γ ∈ G, w γ (S γ) ∧
      ∑ γ ∈ G, w γ (S γ) ≤ ∑ γ ∈ G, (adm γ).sup' (hne γ) (w γ) :=
  ⟨sum_le_sum fun γ hγ => inf'_le _ (hS γ hγ), sum_le_sum fun γ hγ => le_sup' _ (hS γ hγ)⟩

end Psc.SeamCycleSpectrum
