import PscVerif.ClassAMinusUpperEscape

open Psc.OccurrenceTransport
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusLiteralArithmetic
open Psc.ClassAMinusPrefixAssembly Psc.ClassAMinusUpperEntry Psc.ClassAMinusUpperRecurrence
open Psc.ClassAMinusUpperEscape

/-- Exact end-to-end contract. The source is an arbitrary strict integral
packet, and the conclusion uses the actual literal words and original
index pairs. -/
example (k t : ℕ) (ht : 6 ≤ t) :
    ∃ β : ℝ, UpperRoot (k+t+3) (k+2*t+5) β ∧ ∀ p : Packet,
      p.Interior (lengths (k+t+3) β) →
      ∃ xs : List (ℕ × ℕ),
        OrderedInteriorPath (sigma (k+t+3) (k+2*t+5)) (lengths (k+t+3) β)
          p xs (packet 2 2 0 0 0) :=
  complement_to_zero k t ht

/-- Touching unit intervals fail the strict source hypothesis. -/
example (w : Fin 3 → ℝ) (hy : w 2 = 1) : ¬ (packet 2 2 0 0 1).Interior w := by
  intro he
  obtain ⟨x,hx,hxt,hxb,_⟩ := he
  have hoff : offset w (packet 2 2 0 0 1).delta = -1 := by
    simp [offset, packet, dotProduct, Fin.sum_univ_three, hy]
  change x < w 2 at hxt
  rw [hy] at hxt
  rw [hoff] at hxb
  linarith

#print axioms upper_root_exists
#print axioms upper_central_entry
#print axioms upper_cubic_irreducible
#print axioms no_half_unit
#print axioms reaches_alternating
#print axioms central_to_zero
#print axioms complement_to_zero
