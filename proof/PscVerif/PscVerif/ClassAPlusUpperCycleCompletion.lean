/-
# Complete original occurrence exits in the upper height range

The accepted eight-case module is imported unchanged. Its FIRST/RUN
decrement extends to every 3 <= J*H <= n-1. Recursion in the actual height
then reaches typed y/y zero using the same two three-edge bases. The
transcript is retained through both original MarkTrace witnesses and the
full incidence-power identity. Strictness follows backwards from typed
zero under explicit positive lengths and exact positive inflation.

No nearest-recurrence classification, source-entry premise or supplied
zero hit is assumed here. The arithmetic range is the theorem's scope.
Pre-code gate: docs/bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md.
-/
import PscVerif.ClassAPlusUpperCycles

namespace Psc.ClassAPlusUpperCycleCompletion

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusPrefixAssembly Psc.ClassAPlusUpperCycles Matrix

/-- The same two actual original index pairs lower every height in range. -/
theorem decrement_path (n J H : ℕ) (hn : 7 ≤ n) (hJ : 1 ≤ J)
    (hH : 1 ≤ H) (hlo : 3 ≤ J*H) (hhi : J*H ≤ n-1) :
    OrderedPath (upperSigma n J) (cyclePacket H) (decrementIndices J H)
      (cyclePacket (H-1)) := by
  have hJle : J ≤ J*H := by simpa using Nat.mul_le_mul_left J hH
  have hJsub : J ≤ 2*n+12 := by omega
  have hfirst : J*H-2 ≤ plusRunLength n (2*n+12-J) 2 := by
    simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]
    omega
  have hsecond : J*(H-1)+4 ≤ plusRunLength n (2*n+12-J) 0 := by
    simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]
    have hm : J*(H-1) ≤ J*H := Nat.mul_le_mul_left J (Nat.sub_le H 1)
    omega
  have e1 := first_run_step n (2*n+12-J) 2 2 (J*H-2)
    (by omega) hfirst (H : ℤ) (3*(H : ℤ)) (-6*(H : ℤ))
  have he1 : IndexedDigitStep (upperSigma n J) (cyclePacket H) 0 (J*H-2)
      (packet 0 2 (1-(H : ℤ)) (-3*(H : ℤ)) (6*(H : ℤ)-3)) := by
    convert e1 using 1 <;>
      simp [upperSigma, cyclePacket, first, Nat.cast_sub hJsub,
        Nat.cast_sub (show 2 ≤ J*H by omega), Nat.cast_add, Nat.cast_mul] <;>
      congr 1 <;> ring
  have e2 := run_run_step n (2*n+12-J) 0 2 (J*(H-1)+4) 1
    (by omega) hsecond (by omega) (by simp [plusRunLength,
      ClassAPlusConstantRecurrence.runLength])
    (1-(H : ℤ)) (-3*(H : ℤ)) (6*(H : ℤ)-3)
  have he2 : IndexedDigitStep (upperSigma n J)
      (packet 0 2 (1-(H : ℤ)) (-3*(H : ℤ)) (6*(H : ℤ)-3))
      (J*(H-1)+4) 1 (cyclePacket (H-1)) := by
    convert e2 using 1 <;>
      simp [upperSigma, cyclePacket, delta, Nat.cast_sub hJsub, Nat.cast_sub hH,
        Nat.cast_add, Nat.cast_mul] <;> congr 1 <;> ring
  simpa [decrementIndices] using
    OrderedPath.snoc (OrderedPath.snoc (OrderedPath.nil (cyclePacket H)) _ _ he1) _ _ he2

/-- Height zero stops immediately. Positive heights use an actual decrement
until one of the accepted three-edge base templates applies. -/
def allIndices (n J H : ℕ) : List (ℕ × ℕ) :=
  Nat.rec [] (fun k path =>
    if 3 ≤ J*(k+1) then decrementIndices J (k+1) ++ path
    else if J=1 then baseOneIndices n (k+1) else baseTwoIndices n) H

/-- Literal completion for all heights in the stated integral range. -/
theorem all_ordered_paths (n J H : ℕ) (hn : 7 ≤ n)
    (hJ : 1 ≤ J) (hJhi : J ≤ n+7) (hhi : J*H ≤ n-1) :
    OrderedPath (upperSigma n J) (cyclePacket H) (allIndices n J H) zeroPacket := by
  revert hhi
  induction H with
  | zero =>
    intro _
    simpa [allIndices, cyclePacket, zeroPacket] using
      (OrderedPath.nil (s := upperSigma n J) zeroPacket)
  | succ H ih =>
    intro hhi
    by_cases hlarge : 3 ≤ J*(H+1)
    · have hprev : J*H ≤ n-1 :=
        (Nat.mul_le_mul_left J (Nat.le_succ H)).trans hhi
      have hd := decrement_path n J (H+1) hn hJ (by omega) hlarge hhi
      simpa only [allIndices, hlarge, ↓reduceIte, Nat.add_sub_cancel] using
        hd.trans (ih hprev)
    · have hprod : J*(H+1) ≤ 2 := by omega
      have hJsmall : J ≤ 2 := by
        have hm := Nat.mul_le_mul_left J (show 1 ≤ H+1 by omega)
        simpa using hm.trans hprod
      by_cases hj1 : J=1
      · subst J
        have hsmall : H+1 ≤ 2 := by simpa using hprod
        simpa only [allIndices, hlarge, ↓reduceIte] using
          base_one_path n (H+1) hn (by omega) hsmall
      · have hj2 : J=2 := by omega
        subst J
        have hzero : H=0 := by omega
        subst H
        simpa [allIndices] using base_two_path n hn

/-- Genuine reversal swaps each pair of original occurrence ordinals. -/
def allSignedIndices (reversed : Bool) (n J H : ℕ) : List (ℕ × ℕ) :=
  if reversed then (allIndices n J H).map Prod.swap else allIndices n J H

theorem all_signed_ordered_paths (n J H : ℕ) (hn : 7 ≤ n)
    (hJ : 1 ≤ J) (hJhi : J ≤ n+7) (hhi : J*H ≤ n-1) (reversed : Bool) :
    OrderedPath (upperSigma n J) (signedSource reversed H)
      (allSignedIndices reversed n J H) zeroPacket := by
  have hp := all_ordered_paths n J H hn hJ hJhi hhi
  cases reversed
  · exact hp
  · have hz : zeroPacket.swap = zeroPacket := by
      simpa [zeroPacket] using ClassAMinusConstantRecurrence.packet_swap 2 2 0 0 0
    simpa only [signedSource, allSignedIndices, Bool.true_eq, ↓reduceIte, hz] using
      ordered_path_swap hp

/-- Both original full prefix witnesses follow exactly this same transcript.
Positive length/scaling hypotheses supply every strict edge by pullback. -/
theorem all_traced_strict_prefixes (n J H : ℕ) (hn : 7 ≤ n)
    (hJ : 1 ≤ J) (hJhi : J ≤ n+7) (hhi : J*H ≤ n-1) (reversed : Bool)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (upperSigma n J a) = β*ℓ a) :
    OrderedInteriorPath (upperSigma n J) ℓ (signedSource reversed H)
      (allSignedIndices reversed n J H) zeroPacket ∧
    ∃ (top : Mark ((subst (upperSigma n J))^[(allSignedIndices reversed n J H).length]
        [(signedSource reversed H).top]))
      (bottom : Mark ((subst (upperSigma n J))^[(allSignedIndices reversed n J H).length]
        [(signedSource reversed H).bottom])),
      MarkTrace (upperSigma n J) (signedSource reversed H).top
        ((allSignedIndices reversed n J H).map Prod.fst) top.before top.letter top.after ∧
      MarkTrace (upperSigma n J) (signedSource reversed H).bottom
        ((allSignedIndices reversed n J H).map Prod.snd) bottom.before bottom.letter bottom.after ∧
      top.letter = 2 ∧ bottom.letter = 2 ∧
      incidenceZ (upperSigma n J) ^ (allSignedIndices reversed n J H).length *ᵥ
          (-(signedSource reversed H).delta) = parikhZ top.before-parikhZ bottom.before := by
  have hp := all_signed_ordered_paths n J H hn hJ hJhi hhi reversed
  have hz : zeroPacket.delta = 0 := by
    funext a
    fin_cases a <;> rfl
  exact ⟨ordered_path_indexed_interior (upperSigma n J) ℓ β hpos hβ hscale hp
      (zero_packet_interior ℓ hpos 2 2),
    ordered_path_traced_zero_original_prefixes hp hz⟩

end Psc.ClassAPlusUpperCycleCompletion
