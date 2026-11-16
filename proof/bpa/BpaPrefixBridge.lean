import Mathlib

/-! A small, standalone Lean 4/Mathlib interface for the shift/count identity
used in Proposition B′. The `PscVerif` library restates it as
`Psc.BPrimeCore.shift_factor_identity` (`proof/PscVerif/PscVerif/BPrimeCore.lean`),
where the block bounds, the frequency-free averaging, cyclic vectors and the
spectral step are formalized; `Psc.BPrime` composes them with the
Sirvent–Solomyak binding into Proposition B′. This standalone file proves only
the identity below. Do not count it as a proof of B′. -/

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
