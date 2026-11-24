/-
# Half-integer exclusion for the literal upper plus-Class-A family

The integral monic cubic has no rational root throughout the actual upper
parameter chamber.  Its irreducibility rules out every nonzero rational
quadratic at the given root.  Clearing an odd half-integer displacement
produces just such a quadratic, with an odd coefficient of the root.

The displacement uses all three integral coordinates, in (x,c,y) order.
This specializes the existing reviewed entry contract; see
`docs/class-a-plus-upper-all-source-entry-2026-11-16.md` and its recurrence
source gate `docs/bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md`.
-/
import PscVerif.ClassAPlusUpperRecurrence
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.ComputeDegree
import Mathlib.Topology.Order.IntermediateValue

namespace Psc.ClassAPlusUpperNoHalfTies

open Polynomial
open Psc.ClassAPlusUpperRecurrence (Family)

noncomputable def polyZ (n J : ℕ) : ℤ[X] :=
  X^3-C ((n : ℤ)+4)*X^2+C ((J : ℤ)-(n : ℤ)-7)*X-C 2

noncomputable def polyQ (n J : ℕ) : ℚ[X] :=
  X^3-C ((n : ℚ)+4)*X^2+C ((J : ℚ)-(n : ℚ)-7)*X-C 2

theorem polyZ_monic (n J : ℕ) : (polyZ n J).Monic := by
  unfold polyZ
  monicity!

theorem polyQ_monic (n J : ℕ) : (polyQ n J).Monic := by
  unfold polyQ
  monicity!

theorem polyQ_degree (n J : ℕ) : (polyQ n J).natDegree = 3 := by
  unfold polyQ
  compute_degree!

/-- No irreducibility assumption is supplied: the upper chamber rules out
each possible integral root of the monic cubic with constant term -2. -/
theorem polyQ_irreducible (n J : ℕ) (hn : 7 ≤ n)
    (hJlo : 1 ≤ J) (hJhi : J ≤ n+7) : Irreducible (polyQ n J) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [polyQ_degree]
    decide
  · intro x hx
    have hx' : aeval x (polyZ n J) = 0 := by
      have h0 : eval x (polyQ n J) = 0 := hx
      simpa [polyQ, polyZ, map_ofNat] using h0
    obtain ⟨z, rfl, hz⟩ := exists_integer_of_is_root_of_monic (polyZ_monic n J) hx'
    have hc : (polyZ n J).coeff 0 = -2 := by simp [polyZ]
    rw [hc] at hz
    have he : z^3-((n : ℤ)+4)*z^2+((J : ℤ)-(n : ℤ)-7)*z-2 = 0 := by
      have hh := hx'
      simp [polyZ, map_ofNat] at hh
      exact_mod_cast hh
    have hb : z.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num)
      (Int.natAbs_dvd_natAbs.mpr hz)
    have h1 : -2 ≤ z := by omega
    have h2 : z ≤ 2 := by omega
    have hn' : (7 : ℤ) ≤ n := by exact_mod_cast hn
    have hJlo' : (1 : ℤ) ≤ J := by exact_mod_cast hJlo
    have hJhi' : (J : ℤ) ≤ (n : ℤ)+7 := by exact_mod_cast hJhi
    interval_cases z <;> norm_num at he <;> omega

theorem polyQ_aeval_root {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    aeval β (polyQ n J) = 0 := by
  simpa [polyQ] using hp.root_eq

/-- The actual upper-family root has no nonzero rational quadratic relation. -/
theorem rational_quadratic_zero (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (a b c : ℚ) (he : (a : ℝ)*β^2+(b : ℝ)*β+(c : ℝ) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  let q : ℚ[X] := C a*X^2+C b*X+C c
  have hqdeg : q.natDegree ≤ 2 := by dsimp [q]; compute_degree!
  have hqev : aeval β q = 0 := by simpa [q] using he
  have hdvd : polyQ n J ∣ q :=
    ((polyQ_irreducible n J hp.n_lower hp.J_lower hp.J_upper).dvd_iff_aeval_eq_zero
      (polyQ_aeval_root hp)).mp hqev
  have hq : q = 0 := by
    by_contra hne
    have hh := natDegree_le_of_dvd hdvd hne
    rw [polyQ_degree] at hh
    omega
  have ha := congrArg (fun p : ℚ[X] => p.coeff 2) hq
  have hb := congrArg (fun p : ℚ[X] => p.coeff 1) hq
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) hq
  simpa [q] using And.intro ha (And.intro hb hc)

theorem integral_quadratic_zero (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (a b c : ℤ) (he : (a : ℝ)*β^2+(b : ℝ)*β+(c : ℝ) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hh := rational_quadratic_zero n J β hp (a : ℚ) (b : ℚ) (c : ℚ)
    (by exact_mod_cast he)
  exact_mod_cast hh

/-- Every odd half-integer is excluded for every full integral offset.
The middle coefficient after multiplication by 2β is odd. -/
theorem physical_shift_ne_half_integer (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (p q r z : ℤ) :
    (β-(n : ℝ)-2+1/β)*(p : ℝ)+(1-1/β)*(q : ℝ)+(r : ℝ) ≠
      (z : ℝ)+1/2 := by
  intro he
  have hβ : β ≠ 0 := ne_of_gt hp.beta_pos
  have hpoly : ((2*p : ℤ) : ℝ)*β^2+
      ((2*(q+r-((n : ℤ)+2)*p)-2*z-1 : ℤ) : ℝ)*β+
      ((2*(p-q) : ℤ) : ℝ) = 0 := by
    push_cast
    field_simp at he
    nlinarith [he]
  have hz := (integral_quadratic_zero n J β hp (2*p)
    (2*(q+r-((n : ℤ)+2)*p)-2*z-1) (2*(p-q)) hpoly).2.1
  omega

/-- The vector interface retains every coordinate of the integral offset. -/
theorem vector_shift_ne_half_integer (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (w : Fin 3 → ℤ) (z : ℤ) :
    (β-(n : ℝ)-2+1/β)*(w 0 : ℝ)+(1-1/β)*(w 1 : ℝ)+(w 2 : ℝ) ≠
      (z : ℝ)+1/2 :=
  physical_shift_ne_half_integer n J β hp (w 0) (w 1) (w 2) z

/-- Exact strict-half-unit interface for the central selector. -/
theorem physical_abs_ne_half (n J : ℕ) (β : ℝ) (hp : Family n J β)
    (p q r : ℤ) :
    |(β-(n : ℝ)-2+1/β)*(p : ℝ)+(1-1/β)*(q : ℝ)+(r : ℝ)| ≠ 1/2 := by
  intro he
  by_cases hu : 0 ≤ (β-(n : ℝ)-2+1/β)*(p : ℝ)+(1-1/β)*(q : ℝ)+(r : ℝ)
  · rw [abs_of_nonneg hu] at he
    apply physical_shift_ne_half_integer n J β hp p q r 0
    simpa using he
  · rw [abs_of_neg (lt_of_not_ge hu)] at he
    apply physical_shift_ne_half_integer n J β hp p q r (-1)
    norm_num only [Int.cast_neg, Int.cast_one]
    linarith

/-- The original parameter interval supplies the recurrence family's reserve
parameter; the natural subtraction is justified before any cast. -/
theorem family_of_parameters (n d : ℕ) (β : ℝ)
    (hn : 7 ≤ n) (hdlo : n+5 ≤ d) (hdhi : d ≤ 2*n+11)
    (hβlo : (n : ℝ)+4 < β) (hβhi : β < (n : ℝ)+6)
    (hroot : β^3-((n : ℝ)+4)*β^2+((n : ℝ)-(d : ℝ)+5)*β-2 = 0) :
    Family n (2*n+12-d) β := by
  refine ⟨hn, by omega, by omega, hβlo, hβhi, ?_⟩
  rw [Nat.cast_sub (show d ≤ 2*n+12 by omega)]
  push_cast
  nlinarith [hroot]

/-- The bracketed cubic root exists for every upper-family parameter pair.
This is algebraic root existence; it does not invoke a spectral theorem. -/
theorem family_root_exists (n J : ℕ) (hn : 7 ≤ n)
    (hJlo : 1 ≤ J) (hJhi : J ≤ n+7) : ∃ β : ℝ, Family n J β := by
  let f : ℝ → ℝ := fun x =>
    x^3-((n : ℝ)+4)*x^2+((J : ℝ)-(n : ℝ)-7)*x-2
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hJloR : (1 : ℝ) ≤ J := by exact_mod_cast hJlo
  have hJhiR : (J : ℝ) ≤ (n : ℝ)+7 := by exact_mod_cast hJhi
  have hlo : f ((n : ℝ)+4) = ((J : ℝ)-(n : ℝ)-7)*((n : ℝ)+4)-2 := by
    dsimp [f]
    ring
  have hhi : f ((n : ℝ)+6) = ((n : ℝ)+(J : ℝ)+5)*((n : ℝ)+6)-2 := by
    dsimp [f]
    ring
  have hloneg : f ((n : ℝ)+4) < 0 := by
    rw [hlo]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg
      (show (J : ℝ)-(n : ℝ)-7 ≤ 0 by linarith)
      (show 0 ≤ (n : ℝ)+4 by linarith)]
  have hhipos : 0 < f ((n : ℝ)+6) := by
    rw [hhi]
    nlinarith [mul_nonneg (show 0 ≤ (J : ℝ)-1 by linarith)
      (show 0 ≤ (n : ℝ)+6 by linarith), sq_nonneg ((n : ℝ)+6)]
  have hcont : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨β, hβ, hc⟩ := intermediate_value_Ioo
    (show (n : ℝ)+4 ≤ (n : ℝ)+6 by linarith) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (f ((n : ℝ)+4)) (f ((n : ℝ)+6)) from
      ⟨hloneg, hhipos⟩)
  exact ⟨β, hn, hJlo, hJhi, hβ.1, hβ.2, hc⟩

/-- Direct API in the literal n,d parameterization. -/
theorem literal_shift_ne_half_integer (n d : ℕ) (β : ℝ)
    (hn : 7 ≤ n) (hdlo : n+5 ≤ d) (hdhi : d ≤ 2*n+11)
    (hβlo : (n : ℝ)+4 < β) (hβhi : β < (n : ℝ)+6)
    (hroot : β^3-((n : ℝ)+4)*β^2+((n : ℝ)-(d : ℝ)+5)*β-2 = 0)
    (w : Fin 3 → ℤ) (z : ℤ) :
    (β-(n : ℝ)-2+1/β)*(w 0 : ℝ)+(1-1/β)*(w 1 : ℝ)+(w 2 : ℝ) ≠
      (z : ℝ)+1/2 :=
  vector_shift_ne_half_integer n (2*n+12-d) β
    (family_of_parameters n d β hn hdlo hdhi hβlo hβhi hroot) w z

end Psc.ClassAPlusUpperNoHalfTies
