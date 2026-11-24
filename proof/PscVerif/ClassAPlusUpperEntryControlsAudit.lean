import PscVerif.ClassAPlusUpperEntryControls

open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusPrefixAssembly Psc.ClassAPlusUpperCycles
open Psc.ClassAPlusUpperRecurrence Psc.ClassAPlusUpperLiteralEntry
open Psc.ClassAPlusUpperEntryControls

/-- Independent exact-type check: the advertised ordinals and complete
source/middle/target coordinates are fixed in this fixture. -/
example (n d : ℕ) (hn : 2 ≤ n) :
    OrderedPath (plusSigma n d) (packet 2 1 0 1 0) [(n+2,0),(1,2)]
      (packet 2 2 0 0 0) := two_edge_path n d hn

example {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    OrderedInteriorPath (upperSigma n J) (lengths n β) (packet 2 1 0 1 0)
      [(n+2,0),(1,2)] (packet 2 2 0 0 0) := two_edge_strict_path hp

example {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (i j : ℕ) (q : Packet) :
    IndexedDigitStep (upperSigma n J) (packet 2 1 0 1 0) i j q →
      ¬(q.top = 2 ∧ q.bottom = 2 ∧ |shift n β q| < 1/2) :=
  one_edge_central_impossible hp i j q

example (n d : ℕ) :
    ¬IndexedDigitStep (plusSigma n d) (packet 2 1 0 1 0) (n+1) 0
      (packet 1 1 0 1 (-1)) := wrong_last_index_rejected n d _ rfl

#print axioms Psc.ClassAPlusUpperNoHalfTies.polyQ_irreducible
#print axioms Psc.ClassAPlusUpperNoHalfTies.vector_shift_ne_half_integer
#print axioms Psc.ClassAPlusUpperNoHalfTies.family_root_exists
#print axioms two_edge_path
#print axioms top_trace
#print axioms bottom_trace
#print axioms composed_offset_identity
#print axioms wrong_last_index_rejected
#print axioms one_edge_central_impossible
#print axioms two_edge_strict_path
