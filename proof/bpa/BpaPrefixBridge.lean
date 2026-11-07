/-- A small, standalone Lean 4/Mathlib interface for the shift/count identity
used in Proposition B′. This does not yet formalize block bounds, frequencies,
cyclic vectors or the spectral theorem. Do not count as a proof of B′. -/
import Mathlib

namespace PscVerif.BpaPrefixBridge

variable {V : Type*} [AddCommGroup V]

/-- Prefix-count cancellation identifies two presentations of the discrepancy
between a word and its shift by `t`: the left-hand side is the discrepancy
between *prefixes* of the two tracks, the right-hand side compares two factors
of length `t`. An arbitrary abelian-group-valued prefix count suffices. -/
theorem shift_factor_identity (P : ℕ → V) (t k : ℕ) :
    P k - (P (t + k) - P t) =
      P t - (P (k + t) - P k) := by
  rw [Nat.add_comm t k]
  abel

end PscVerif.BpaPrefixBridge

#print axioms PscVerif.BpaPrefixBridge.shift_factor_identity
