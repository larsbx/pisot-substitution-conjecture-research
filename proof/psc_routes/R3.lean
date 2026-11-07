import Mathlib

/-!
# Route R3: literal prefix shifts and block-discrepancy bounds

The lemmas are exact and computable. Uniform existence of the block cuts
for all substitution depths, and eventual coincidence/productivity,
remain open. No implication from balance alone is claimed.
-/
namespace PscRoutes.R3

/-- A two-track difference of coordinate prefix counts, each no
larger than the common block length, is bounded by that length. -/
theorem bounded_block_coordinate
    (blockLength topCount bottomCount : ℕ)
    (htop : topCount ≤ blockLength)
    (hbottom : bottomCount ≤ blockLength) :
    -(blockLength : ℤ) ≤ (topCount : ℤ) - bottomCount ∧
    (topCount : ℤ) - bottomCount ≤ (blockLength : ℤ) := by
  constructor <;> omega

/-- The B-prime shift/factor identity is algebraic, independent of
frequencies, primitivity, or assumptions about balanced cuts. -/
theorem shift_factor_identity (P : ℕ → ℤ) (t k : ℕ) :
    P k - (P (t + k) - P t) =
      P t - (P (k + t) - P k) := by
  rw [Nat.add_comm t k]
  ring

end PscRoutes.R3

#print axioms PscRoutes.R3.bounded_block_coordinate
#print axioms PscRoutes.R3.shift_factor_identity
