/-
# Literal upper-entry negative controls

The y/c source (0,1,0) reaches typed y/y zero in two literal substitution
edges.  The first top ordinal is LAST n+2; n+1 is a RUN y and cannot be
relabeled c.  Both complete original prefix tracks are retained.
-/
import PscVerif.ClassAPlusUpperCycles
import PscVerif.OccurrenceFinite
import PscVerif.ClassAPlusUpperLiteralEntry

namespace Psc.ClassAPlusUpperEntryControls

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusPrefixAssembly
open Psc.ClassAPlusUpperCycles Psc.OccurrenceFinite Matrix
open Psc.ClassAPlusUpperRecurrence Psc.ClassAPlusUpperLiteralEntry

def source : Packet := packet 2 1 0 1 0
def middle : Packet := packet 1 1 0 1 (-1)
def target : Packet := packet 2 2 0 0 0
def indices (n : ℕ) : List (ℕ × ℕ) := [(n+2,0),(1,2)]

/-- LAST y-image c against FIRST c-image c, with the full offset. -/
theorem first_edge (n d : ℕ) :
    IndexedDigitStep (plusSigma n d) source (n+2) 0 middle := by
  refine ⟨ClassAPlusUpperCycles.lastMark n d 2,
    ClassAPlusUpperCycles.firstMark n d 1, ?_, rfl, ?_⟩
  · simp [ClassAPlusUpperCycles.lastMark, Mark.index, plusRunLength,
      ClassAPlusConstantRecurrence.runLength]
  · apply congrArg (Packet.mk 1 1)
    funext z
    fin_cases z <;>
      simp [source, packet, incidenceZ, inc, plusSigma,
        ClassAPlusConstantRecurrence.sigma, plusRunLength,
        ClassAPlusConstantRecurrence.runLength, first, last,
        OccurrenceTransport.residual, parikhZ, ClassAPlusUpperCycles.lastMark,
        ClassAPlusUpperCycles.firstMark, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, List.count_replicate]

/-- Two distinct c-image RUN positions cancel all three coordinates. -/
theorem second_edge (n d : ℕ) (hn : 2 ≤ n) :
    IndexedDigitStep (plusSigma n d) middle 1 2 target := by
  have hi : 1 ≤ plusRunLength n d 1 := by
    simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]
    omega
  have hj : 2 ≤ plusRunLength n d 1 := by
    simpa [plusRunLength, ClassAPlusConstantRecurrence.runLength] using hn
  simpa [middle, target, delta, Nat.cast_add] using
    run_run_step n d 1 1 1 2 (by omega) hi (by omega) hj 0 1 (-1)

/-- This is exactly two substitution edges, with no orientation operation. -/
theorem two_edge_path (n d : ℕ) (hn : 2 ≤ n) :
    OrderedPath (plusSigma n d) source (indices n) target := by
  simpa [indices] using
    OrderedPath.snoc (OrderedPath.snoc (OrderedPath.nil source) (n+2) 0
      (first_edge n d)) 1 2 (second_edge n d hn)

def topPrefix (n d : ℕ) : Word :=
  subst (plusSigma n d) ([0] ++ List.replicate (n+1) 2) ++ [1]

def bottomPrefix : Word := [1,2]

/-- The complete top track follows the actual LAST c, then FIRST RUN y. -/
theorem top_trace (n d : ℕ) (hn : 2 ≤ n) :
    MarkTrace (plusSigma n d) 2 [n+2,1] (topPrefix n d) 2
      (List.replicate (n-1) 2 ++ [0]) := by
  have hroot : MarkTrace (plusSigma n d) 2 [] [] 2 [] := .root
  have ht : MarkTrace (plusSigma n d) 2 [n+2]
      ([0] ++ List.replicate (n+1) 2) 1 [] := by
    simpa [ClassAPlusUpperCycles.lastMark, Mark.index, plusRunLength,
      ClassAPlusConstantRecurrence.runLength, first, last, subst] using
      MarkTrace.snoc hroot (ClassAPlusUpperCycles.lastMark n d 2)
  have hr : 0 < plusRunLength n d 1 := by
    simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]
    omega
  simpa [topPrefix, plusRunMark, ClassAPlusConstantRecurrence.runMark,
    plusRunLength, ClassAPlusConstantRecurrence.runLength, first, last,
    Mark.index, subst] using MarkTrace.snoc ht (plusRunMark n d 1 0 hr)

/-- The complete bottom track follows FIRST c, then the second RUN y. -/
theorem bottom_trace (n d : ℕ) (hn : 2 ≤ n) :
    MarkTrace (plusSigma n d) 1 [0,2] bottomPrefix 2
      ((List.replicate (n-2) 2 ++ [0]) ++
        subst (plusSigma n d) (List.replicate n 2 ++ [0])) := by
  have hroot : MarkTrace (plusSigma n d) 1 [] [] 1 [] := .root
  have ht : MarkTrace (plusSigma n d) 1 [0] [] 1
      (List.replicate n 2 ++ [0]) := by
    simpa [ClassAPlusUpperCycles.firstMark, Mark.index, plusRunLength,
      ClassAPlusConstantRecurrence.runLength, first, last, subst] using
      MarkTrace.snoc hroot (ClassAPlusUpperCycles.firstMark n d 1)
  have hr : 1 < plusRunLength n d 1 := by
    simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]
    omega
  simpa [bottomPrefix, plusRunMark, ClassAPlusConstantRecurrence.runMark,
    plusRunLength, ClassAPlusConstantRecurrence.runLength, first, last,
    Mark.index, subst] using MarkTrace.snoc ht (plusRunMark n d 1 1 hr)

/-- Complete original top-prefix coordinates, not merely its physical length. -/
theorem top_prefix_coordinates (n d : ℕ) :
    parikhZ (topPrefix n d) =
      ![(n : ℤ)+3,(n : ℤ)+2,(n : ℤ)+(d : ℤ)+((n : ℤ)+1)^2] := by
  rw [topPrefix, parikhZ_append, parikhZ_subst]
  funext z
  fin_cases z <;>
    simp [parikhZ, incidenceZ, inc, plusSigma, ClassAPlusConstantRecurrence.sigma,
      ClassAPlusConstantRecurrence.runLength, first, last,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, List.count_replicate] <;> ring

theorem bottom_prefix_coordinates : parikhZ bottomPrefix = ![0,1,1] := by
  ext z
  fin_cases z <;> simp [parikhZ, bottomPrefix]

/-- The displayed original prefixes realize the full squared-incidence identity. -/
theorem composed_offset_identity (n d : ℕ) :
    incidenceZ (plusSigma n d)^2 *ᵥ ![0,1,0] =
      parikhZ (topPrefix n d)-parikhZ bottomPrefix := by
  rw [top_prefix_coordinates, bottom_prefix_coordinates, pow_two, ← Matrix.mulVec_mulVec]
  funext z
  fin_cases z <;>
    simp [incidenceZ, inc, plusSigma, ClassAPlusConstantRecurrence.sigma,
      ClassAPlusConstantRecurrence.runLength, first, last,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, List.count_replicate] <;> ring

/-- The wrong first ordinal denotes RUN y, so it cannot authenticate the
claimed intermediate c/c packet, whatever complete offset is supplied. -/
theorem wrong_last_index_rejected (n d : ℕ) (q : Packet) (hq : q.top = 1) :
    ¬IndexedDigitStep (plusSigma n d) source (n+1) 0 q := by
  intro he
  obtain ⟨dt, db, hi, _, htarget⟩ := he
  have hr : n < plusRunLength n d 2 := by
    simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]
  have hm : dt = plusRunMark n d 2 n hr := by
    apply mark_index_injective (plusSigma n d 2)
    simpa [plusRunMark, ClassAPlusConstantRecurrence.runMark, Mark.index] using hi
  have ht := congrArg Packet.top htarget
  rw [hq] at ht
  simp only [hm, plusRunMark, ClassAPlusConstantRecurrence.runMark] at ht
  exact (by decide : (1 : Fin 3) ≠ 2) ht

/-- Every y-labelled mark in a literal image is an actual RUN occurrence.
Both endpoints are excluded by their actual letters. -/
theorem y_mark_is_run (n d : ℕ) (a : Fin 3) (m : Mark (plusSigma n d a))
    (hy : m.letter = 2) :
    ∃ i : ℕ, ∃ hi : i < plusRunLength n d a, m = plusRunMark n d a i hi := by
  have hbound : m.index < plusRunLength n d a+2 := by
    simpa [plusSigma, ClassAPlusConstantRecurrence.sigma, List.length_append,
      Nat.add_assoc] using m.index_lt
  have hzero : m.index ≠ 0 := by
    intro hz
    have hm : m = ClassAPlusUpperCycles.firstMark n d a :=
      mark_index_injective _ hz
    rw [hm] at hy
    simp only [ClassAPlusUpperCycles.firstMark] at hy
    unfold first at hy
    split at hy <;> norm_num at hy
  have hlast : m.index ≠ plusRunLength n d a+1 := by
    intro hz
    have hm : m = ClassAPlusUpperCycles.lastMark n d a := by
      apply mark_index_injective _
      simpa [ClassAPlusUpperCycles.lastMark, Mark.index, Nat.add_comm] using hz
    rw [hm] at hy
    simp only [ClassAPlusUpperCycles.lastMark] at hy
    unfold last at hy
    split at hy <;> norm_num at hy
  have hr : m.index-1 < plusRunLength n d a := by omega
  refine ⟨m.index-1, hr, ?_⟩
  apply mark_index_injective _
  calc
    m.index = (m.index-1)+1 := by omega
    _ = (plusRunMark n d a (m.index-1) hr).index := by
      simp [plusRunMark, ClassAPlusConstantRecurrence.runMark, Mark.index, Nat.add_comm]

@[simp] theorem source_shift (n : ℕ) (β : ℝ) : shift n β source = cLength β := by
  simp [shift, source, packet, offset, dotProduct, Fin.sum_univ_three]

@[simp] theorem middle_shift (n : ℕ) (β : ℝ) : shift n β middle = cLength β-1 := by
  simp [shift, middle, packet, offset, dotProduct, Fin.sum_univ_three]
  ring

@[simp] theorem target_shift (n : ℕ) (β : ℝ) : shift n β target = 0 := by
  simp [shift, target, packet, offset, dotProduct, Fin.sum_univ_three]

theorem source_not_central (n : ℕ) (β : ℝ) : ¬Central n β source := by
  simp [Central, source, packet]

theorem source_strict {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    source.Interior (lengths n β) := by
  apply (interior_iff hp source).2
  obtain ⟨_, _, hlo, hhi⟩ := length_bounds hp
  rw [source_shift]
  change -cLength β < cLength β ∧ cLength β < 1
  exact ⟨by linarith, hhi⟩

/-- All possible literal one-edge y/y outputs remain at shift at least 2K.
This quantifies over every original index pair, not only the selector. -/
theorem one_edge_central_impossible {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (i j : ℕ) (q : Packet) :
    IndexedDigitStep (upperSigma n J) source i j q → ¬Central n β q := by
  rintro ⟨dt, db, _, _, rfl⟩ hc
  change Central n β (markedChild n J source dt db) at hc
  obtain ⟨a, ha, rfl⟩ := y_mark_is_run n (2*n+12-J) 2 dt hc.1
  obtain ⟨b, hb, rfl⟩ := y_mark_is_run n (2*n+12-J) 1 db hc.2.1
  have haN : a ≤ n := by
    simpa [plusRunLength, ClassAPlusConstantRecurrence.runLength] using
      (Nat.le_of_lt_succ ha)
  have haR : (a : ℝ) ≤ n := by exact_mod_cast haN
  have hbR : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hs := marked_shift hp source (plusRunMark n (2*n+12-J) 2 a ha)
    (plusRunMark n (2*n+12-J) 1 b hb)
  rw [source_shift, run_prefix_length, run_prefix_length] at hs
  simp [first] at hs
  have hx : β*cLength β+cLength β-xLength n β = (n : ℝ)+2*cLength β := by
    dsimp [cLength, xLength]
    field_simp [ne_of_gt hp.beta_pos]
    ring
  have hK := (length_bounds hp).2.2.1
  have hu := (abs_lt.mp hc.2.2).2
  linarith

/-- The two-edge control is strict at every level, using exactly the same
literal transcript and the complete middle offset. -/
theorem two_edge_strict_path {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    OrderedInteriorPath (upperSigma n J) (lengths n β) source (indices n) target := by
  have hn : 2 ≤ n := by have := hp.n_lower; omega
  have hm : middle.Interior (lengths n β) := by
    apply (interior_iff hp middle).2
    obtain ⟨_, _, hlo, hhi⟩ := length_bounds hp
    rw [middle_shift]
    change -cLength β < cLength β-1 ∧ cLength β-1 < cLength β
    constructor <;> linarith
  have ht : Central n β target := by
    refine ⟨rfl, rfl, ?_⟩
    simp
  simpa [upperSigma, indices] using
    OrderedInteriorPath.snoc
      (OrderedInteriorPath.snoc (OrderedInteriorPath.nil source (source_strict hp))
        (n+2) 0 (first_edge n (2*n+12-J)) hm)
      1 2 (second_edge n (2*n+12-J) hn) (central_interior hp ht)

end Psc.ClassAPlusUpperEntryControls
