/-
Unique halving on the actual inverse-limit solenoid when the integer incidence
matrix has a third power divisible by two. This is an algebraic property of the
base, not an exclusion of the stack covering: its deck map fixes this base.

Source decision and the integral-index negative control are recorded in
`docs/c4-even-solenoid-2026-11-19.md` before this module was implemented.
-/
import PscVerif.PeriodicPartnerRealization
import Mathlib.Data.ZMod.Basic

namespace Psc.PeriodicPartnerEvenSolenoid

open Function Matrix Psc.PeriodicPartnerHull Psc.PeriodicPartnerRealization

variable {α : Type*} [Fintype α] [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## The coordinate inverse -/

section Coordinate

variable (S : LengthSubst α) (B : Torus α →+ Torus α)
variable (hcomm : ∀ x, torusMap S (B x) = B (torusMap S x))

/-- The proposed half uses the coordinate three levels farther into the inverse limit. -/
def half (z : Solenoid S) : Solenoid S :=
  ⟨fun n => B (z.1 (n + 3)), by
    intro n
    change torusMap S (B (z.1 (n + 1 + 3))) = B (z.1 (n + 3))
    rw [hcomm, show n + 1 + 3 = (n + 3) + 1 by omega, z.2 (n + 3)]⟩

theorem half_add (z w : Solenoid S) :
    half S B hcomm (z + w) = half S B hcomm z + half S B hcomm w := by
  apply Subtype.ext
  funext n
  exact B.map_add _ _

theorem half_zero : half S B hcomm 0 = 0 := by
  apply Subtype.ext
  funext n
  exact B.map_zero

variable (hfactor : ∀ x, (torusMap S)^[3] x = (2 : ℕ) • B x)
include hcomm hfactor

/-- Doubling the proposed half returns the original solenoid point. -/
theorem two_smul_half (z : Solenoid S) :
    (2 : ℕ) • half S B hcomm z = z := by
  apply Subtype.ext
  funext n
  change (2 : ℕ) • B (z.1 (n + 3)) = z.1 n
  rw [← hfactor, iterate_coord S z 3 n]

/-- The proposed half also cancels doubling on its input. -/
theorem half_two_smul (z : Solenoid S) :
    half S B hcomm ((2 : ℕ) • z) = z := by
  apply Subtype.ext
  funext n
  change B ((2 : ℕ) • z.1 (n + 3)) = z.1 n
  rw [map_nsmul, ← hfactor, iterate_coord S z 3 n]

/-- Doubling on the constructed solenoid is a bijection. -/
theorem two_smul_bijective : Bijective fun z : Solenoid S => (2 : ℕ) • z := by
  constructor
  · intro z w h
    have h' := congrArg (half S B hcomm) h
    simpa only [half_two_smul S B hcomm hfactor] using h'
  · intro z
    exact ⟨half S B hcomm z, two_smul_half S B hcomm hfactor z⟩

/-- No nonzero point of order two exists on this solenoid. -/
theorem no_two_torsion (z : Solenoid S) (hz : (2 : ℕ) • z = 0) : z = 0 := by
  apply (two_smul_bijective S B hcomm hfactor).injective
  simpa only [smul_zero] using hz

theorem unique_half (z : Solenoid S) : ∃! w : Solenoid S, (2 : ℕ) • w = z := by
  refine ⟨half S B hcomm z, two_smul_half S B hcomm hfactor z, ?_⟩
  intro w hw
  apply (two_smul_bijective S B hcomm hfactor).injective
  change (2 : ℕ) • w = (2 : ℕ) • half S B hcomm z
  rw [hw, two_smul_half S B hcomm hfactor]

omit hfactor in
/-- Halving commutes with the solenoid shift. -/
theorem half_shift (z : Solenoid S) :
    half S B hcomm (shiftS S z) = shiftS S (half S B hcomm z) := by
  apply Subtype.ext
  funext n
  exact (hcomm (z.1 (n + 3))).symm

end Coordinate

/-! ## Integer matrices act on the torus -/

/-- The incidence matrix with integer entries, before passage to the real torus. -/
def incidence (S : LengthSubst α) : Matrix α α ℤ :=
  fun b a => ((S.σ a).count b : ℤ)

/-- An integer matrix acts on real coordinate vectors. -/
def intMatHom (B : Matrix α α ℤ) : (α → ℝ) →+ (α → ℝ) :=
  (Matrix.mulVecLin (B.map (Int.castRingHom ℝ))).toAddMonoidHom

theorem intMatHom_mem_lattice (B : Matrix α α ℤ) {v : α → ℝ}
    (hv : v ∈ lattice α) : intMatHom B v ∈ lattice α := by
  intro b
  choose n hn using hv
  refine ⟨∑ a, B b a * n a, ?_⟩
  simp [intMatHom, mulVec, dotProduct, hn]

/-- The torus homomorphism induced by an arbitrary integer matrix. -/
def intTorusMap (B : Matrix α α ℤ) : Torus α →+ Torus α :=
  QuotientAddGroup.map _ _ (intMatHom B) fun _ hv => intMatHom_mem_lattice B hv

theorem intTorusMap_mk (B : Matrix α α ℤ) (v : α → ℝ) :
    intTorusMap B (v : Torus α) =
      ((B.map (Int.castRingHom ℝ) *ᵥ v : α → ℝ) : Torus α) := rfl

theorem intTorusMap_add (A B : Matrix α α ℤ) (x : Torus α) :
    intTorusMap (A + B) x = intTorusMap A x + intTorusMap B x := by
  induction x using Quotient.inductionOn'
  rename_i v
  change (((A + B).map (Int.castRingHom ℝ) *ᵥ v : α → ℝ) : Torus α) = _
  have hmap : (A + B).map (Int.castRingHom ℝ) =
      A.map (Int.castRingHom ℝ) + B.map (Int.castRingHom ℝ) := by ext; simp
  rw [hmap, add_mulVec]
  rfl

theorem intTorusMap_mul (A B : Matrix α α ℤ) (x : Torus α) :
    intTorusMap (A * B) x = intTorusMap A (intTorusMap B x) := by
  induction x using Quotient.inductionOn'
  rename_i v
  change (((A * B).map (Int.castRingHom ℝ) *ᵥ v : α → ℝ) : Torus α) = _
  simp only [Matrix.map_mul, ← mulVec_mulVec]
  rfl

theorem intTorusMap_one (x : Torus α) : intTorusMap (1 : Matrix α α ℤ) x = x := by
  induction x using Quotient.inductionOn'
  rename_i v
  change (((1 : Matrix α α ℤ).map (Int.castRingHom ℝ) *ᵥ v : α → ℝ) : Torus α) = _
  simp

theorem intTorusMap_pow (A : Matrix α α ℤ) (k : ℕ) (x : Torus α) :
    intTorusMap (A ^ k) x = (intTorusMap A)^[k] x := by
  induction k with
  | zero => simpa using intTorusMap_one x
  | succ k ih => rw [pow_succ', intTorusMap_mul, ih, iterate_succ_apply']

theorem intTorusMap_incidence (S : LengthSubst α) :
    intTorusMap (incidence S) = torusMap S := by
  apply AddMonoidHom.ext
  intro x
  induction x using Quotient.inductionOn'
  rename_i v
  change (((incidence S).map (Int.castRingHom ℝ) *ᵥ v : α → ℝ) : Torus α) =
    (((mat S) *ᵥ v : α → ℝ) : Torus α)
  congr 2

/-- The half-power factor commutes with the original integer matrix. -/
theorem commutes_of_cube_eq_double (A B : Matrix α α ℤ) (h : A ^ 3 = B + B) :
    A * B = B * A := by
  have hsum : A * B + A * B = B * A + B * A := by
    calc
      A * B + A * B = A * (B + B) := (mul_add A B B).symm
      _ = A * A ^ 3 := by rw [h]
      _ = A ^ 3 * A := (pow_succ' A 3).symm.trans (pow_succ A 3)
      _ = (B + B) * A := by rw [h]
      _ = B * A + B * A := add_mul B B A
  ext i j
  have hij := congrFun (congrFun hsum i) j
  change (A * B) i j + (A * B) i j = (B * A) i j + (B * A) i j at hij
  omega

/-- Integer cube-divisibility supplies the commuting torus maps and the exact factorization. -/
theorem torus_factor_of_cube_eq_double (S : LengthSubst α) (B : Matrix α α ℤ)
    (h : incidence S ^ 3 = B + B) :
    (∀ x, torusMap S (intTorusMap B x) = intTorusMap B (torusMap S x)) ∧
      (∀ x, (torusMap S)^[3] x = (2 : ℕ) • intTorusMap B x) := by
  have hcomm := commutes_of_cube_eq_double (incidence S) B h
  constructor
  · intro x
    rw [← intTorusMap_incidence S, ← intTorusMap_mul, hcomm, intTorusMap_mul]
  · intro x
    rw [← intTorusMap_incidence S, ← intTorusMap_pow, h, intTorusMap_add, two_nsmul]

/-- The matrix hypothesis is on the actual incidence matrix used by the realization. -/
theorem incidence_unique_halving (S : LengthSubst α) (B : Matrix α α ℤ)
    (h : incidence S ^ 3 = B + B) :
    Bijective (fun z : Solenoid S => (2 : ℕ) • z) ∧
      (∀ z : Solenoid S, (2 : ℕ) • z = 0 → z = 0) := by
  obtain ⟨hcomm, hfactor⟩ := torus_factor_of_cube_eq_double S B h
  exact ⟨two_smul_bijective S (intTorusMap B) hcomm hfactor,
    no_two_torsion S (intTorusMap B) hcomm hfactor⟩

/-- Vanishing of the reduced cube produces its integer half, entry by entry. -/
theorem exists_cube_half_of_mod_two (A : Matrix α α ℤ)
    (h : (A.map (Int.castRingHom (ZMod 2))) ^ 3 = 0) :
    ∃ B : Matrix α α ℤ, A ^ 3 = B + B := by
  have heven : ∀ i j, Even ((A ^ 3) i j) := by
    intro i j
    apply ZMod.intCast_eq_zero_iff_even.mp
    have hij := congrFun (congrFun h i) j
    rw [← Matrix.map_pow] at hij
    exact hij
  choose B hB using heven
  exact ⟨B, funext fun i => funext fun j => hB i j⟩

/-- The actual nilpotent-parity residue implies unique halving without a chosen factor matrix. -/
theorem incidence_mod_two_unique_halving (S : LengthSubst α)
    (h : ((incidence S).map (Int.castRingHom (ZMod 2))) ^ 3 = 0) :
    Bijective (fun z : Solenoid S => (2 : ℕ) • z) ∧
      (∀ z : Solenoid S, (2 : ℕ) • z = 0 → z = 0) := by
  obtain ⟨B, hB⟩ := exists_cube_half_of_mod_two (incidence S) h
  exact incidence_unique_halving S B hB

/-! ## Control: unique halving is compatible with the Thue--Morse setting -/

/-- The familiar rank-two control has nilpotent reduced incidence, although it is not PIP3. -/
theorem thueMorse_mod_two_cube :
    ((incidence thueMorse).map (Int.castRingHom (ZMod 2))) ^ 3 = 0 := by
  decide

/-- Unique halving on the base therefore cannot by itself exclude the Thue--Morse cover. -/
theorem thueMorse_unique_halving :
    Bijective (fun z : Solenoid thueMorse => (2 : ℕ) • z) ∧
      (∀ z : Solenoid thueMorse, (2 : ℕ) • z = 0 → z = 0) :=
  incidence_mod_two_unique_halving thueMorse thueMorse_mod_two_cube

end Psc.PeriodicPartnerEvenSolenoid
