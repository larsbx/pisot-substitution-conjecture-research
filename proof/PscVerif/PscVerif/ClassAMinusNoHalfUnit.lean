/-
# Half-unit exclusion for the literal minus-Class-A root

The monic integral cubic has no rational root in the lower chamber. Its
irreducibility rules out a nonzero rational quadratic at the bracketed root,
including the odd-coefficient polynomial forced by a half-unit displacement.

Pre-code scope: `docs/bh-class-a-literal-lean-stop-go-2026-11-14.md`.
-/
import PscVerif.ClassAMinusLiteralArithmetic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.ComputeDegree

namespace Psc.ClassAMinusNoHalfUnit

open Polynomial Psc.ClassAMinusLiteralArithmetic

noncomputable def polyZ (n d : ℕ) : ℤ[X] :=
  X^3-C ((n : ℤ)+2)*X^2+C ((n : ℤ)-(d : ℤ)-1)*X+C 2

noncomputable def polyQ (n d : ℕ) : ℚ[X] :=
  X^3-C ((n : ℚ)+2)*X^2+C ((n : ℚ)-(d : ℚ)-1)*X+C 2

theorem polyZ_monic (n d : ℕ) : (polyZ n d).Monic := by
  unfold polyZ
  monicity!

theorem polyQ_monic (n d : ℕ) : (polyQ n d).Monic := by
  unfold polyQ
  monicity!

theorem polyQ_degree (n d : ℕ) : (polyQ n d).natDegree = 3 := by
  unfold polyQ
  compute_degree!

theorem polyQ_irreducible (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n) :
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
    have hd' : (5 : ℤ) ≤ d := by exact_mod_cast hd
    have hn' : (d : ℤ)+1 ≤ n := by exact_mod_cast hn
    interval_cases z <;> norm_num at he <;> omega

theorem polyQ_aeval_root {n d : ℕ} {β : ℝ} (hroot : RootData n d β) :
    aeval β (polyQ n d) = 0 := by
  simpa [polyQ, cubic] using hroot.cubic_eq_zero

/-- The literal bracketed root satisfies no nonzero rational quadratic. -/
theorem rational_quadratic_zero (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (a b c : ℚ)
    (he : (a : ℝ)*β^2+(b : ℝ)*β+(c : ℝ) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  let q : ℚ[X] := C a*X^2+C b*X+C c
  have hqdeg : q.natDegree ≤ 2 := by dsimp [q]; compute_degree!
  have hqev : aeval β q = 0 := by simpa [q] using he
  have hdvd : polyQ n d ∣ q :=
    ((polyQ_irreducible n d hd hn).dvd_iff_aeval_eq_zero
      (polyQ_aeval_root hroot)).mp hqev
  have hq : q = 0 := by
    by_contra hne
    have hh := natDegree_le_of_dvd hdvd hne
    rw [polyQ_degree] at hh
    omega
  have ha := congrArg (fun p : ℚ[X] => p.coeff 2) hq
  have hb := congrArg (fun p : ℚ[X] => p.coeff 1) hq
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) hq
  simpa [q] using And.intro ha (And.intro hb hc)

theorem integral_quadratic_zero (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (a b c : ℤ)
    (he : (a : ℝ)*β^2+(b : ℝ)*β+(c : ℝ) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hh := rational_quadratic_zero n d hd hn β hroot (a : ℚ) (b : ℚ) (c : ℚ)
    (by exact_mod_cast he)
  exact_mod_cast hh

/-- Every odd half-integer is excluded for every full integral displacement. -/
theorem physical_shift_ne_half_integer (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (p q r j : ℤ) :
    (β-(n : ℝ)-1/β)*(p : ℝ)+(1+1/β)*(q : ℝ)+(r : ℝ) ≠ (j : ℝ)+1/2 := by
  intro he
  have hβ : β ≠ 0 := ne_of_gt (root_pos hroot)
  have hpoly : ((2*p : ℤ) : ℝ)*β^2+
      ((2*(q+r-(n : ℤ)*p)-2*j-1 : ℤ) : ℝ)*β+((2*(q-p) : ℤ) : ℝ) = 0 := by
    push_cast
    field_simp at he
    nlinarith [he]
  have hz := (integral_quadratic_zero n d hd hn β hroot (2*p)
    (2*(q+r-(n : ℤ)*p)-2*j-1) (2*(q-p)) hpoly).2.1
  omega

/-- Exact no-half-unit interface for the central selector. -/
theorem physical_abs_ne_half (n d : ℕ) (hd : 5 ≤ d) (hn : d+1 ≤ n)
    (β : ℝ) (hroot : RootData n d β) (p q r : ℤ) :
    |(β-(n : ℝ)-1/β)*(p : ℝ)+(1+1/β)*(q : ℝ)+(r : ℝ)| ≠ 1/2 := by
  intro he
  by_cases hu : 0 ≤ (β-(n : ℝ)-1/β)*(p : ℝ)+(1+1/β)*(q : ℝ)+(r : ℝ)
  · rw [abs_of_nonneg hu] at he
    apply physical_shift_ne_half_integer n d hd hn β hroot p q r 0
    simpa using he
  · rw [abs_of_neg (lt_of_not_ge hu)] at he
    apply physical_shift_ne_half_integer n d hd hn β hroot p q r (-1)
    norm_num only [Int.cast_neg, Int.cast_one]
    linarith

end Psc.ClassAMinusNoHalfUnit
