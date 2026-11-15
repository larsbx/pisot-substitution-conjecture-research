/-
# Original occurrence exits for eight upper plus-Class-A cycle packets

The parameter n is unbounded. The eight (J,H) rows have literal ordered
FIRST/RUN paths, complete integral offsets, and both original prefix tracks.
Strictness is pulled back along the same transcript from typed zero using
positive substitution scaling. No recurrence or all-source entry is assumed.

Pre-code gate: docs/bh-class-a-plus-upper-cycles-stop-go-2026-11-15.md.
The generic traced-prefix module is reused byte-for-byte from PR #582.
-/
import PscVerif.ClassAPlusConstantRecurrence
import PscVerif.ClassAMinusPrefixAssembly

namespace Psc.ClassAPlusUpperCycles

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusPrefixAssembly Matrix

abbrev plusSigma := ClassAPlusConstantRecurrence.sigma
abbrev plusRunLength := ClassAPlusConstantRecurrence.runLength
abbrev plusRunMark := ClassAPlusConstantRecurrence.runMark

def firstMark (n d : ℕ) (a : Fin 3) : Mark (plusSigma n d a) where
  before := []
  letter := first a
  after := List.replicate (plusRunLength n d a) 2 ++ [last a]
  split := by simp [plusSigma, ClassAPlusConstantRecurrence.sigma]

def lastMark (n d : ℕ) (a : Fin 3) : Mark (plusSigma n d a) where
  before := [first a] ++ List.replicate (plusRunLength n d a) 2
  letter := last a
  after := []
  split := by simp [plusSigma, ClassAPlusConstantRecurrence.sigma]

/-- Full affine update for two actual RUN positions of any source types. -/
theorem run_run_step (n d : ℕ) (a b : Fin 3) (i j : ℕ)
    (hi0 : 1 ≤ i) (hi : i ≤ plusRunLength n d a)
    (hj0 : 1 ≤ j) (hj : j ≤ plusRunLength n d b) (p q r : ℤ) :
    IndexedDigitStep (plusSigma n d) (packet a b p q r) i j
      (packet 2 2 (2*p+q+r-delta a b) (q+r+delta a b)
        (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n+1 : ℕ) : ℤ)*r+(j : ℤ)-i)) := by
  have hi' : i-1 < plusRunLength n d a := by omega
  have hj' : j-1 < plusRunLength n d b := by omega
  refine ⟨plusRunMark n d a (i-1) hi', plusRunMark n d b (j-1) hj', ?_, ?_, ?_⟩
  · simp [plusRunMark, ClassAPlusConstantRecurrence.runMark, Mark.index]
    omega
  · simp [plusRunMark, ClassAPlusConstantRecurrence.runMark, Mark.index]
    omega
  · apply congrArg (fun v : Fin 3 → ℤ => Packet.mk 2 2 v)
    funext z
    fin_cases z <;> fin_cases a <;> fin_cases b <;>
      simp [packet, incidenceZ, inc, plusSigma, ClassAPlusConstantRecurrence.sigma,
        plusRunLength, ClassAPlusConstantRecurrence.runLength, first, last,
        OccurrenceTransport.residual, parikhZ, plusRunMark,
        ClassAPlusConstantRecurrence.runMark, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, delta, List.count_replicate,
        Nat.cast_sub hi0, Nat.cast_sub hj0] <;> ring

/-- FIRST on the top and an original RUN position on the bottom. -/
theorem first_run_step (n d : ℕ) (a b : Fin 3) (j : ℕ)
    (hj0 : 1 ≤ j) (hj : j ≤ plusRunLength n d b) (p q r : ℤ) :
    IndexedDigitStep (plusSigma n d) (packet a b p q r) 0 j
      (packet (first a) 2
        (2*p+q+r+(if b=1 then 0 else 1))
        (q+r+(if b=1 then 1 else 0))
        (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n+1 : ℕ) : ℤ)*r+(j : ℤ)-1)) := by
  have hj' : j-1 < plusRunLength n d b := by omega
  refine ⟨firstMark n d a, plusRunMark n d b (j-1) hj', rfl, ?_, ?_⟩
  · simp [plusRunMark, ClassAPlusConstantRecurrence.runMark, Mark.index]
    omega
  · apply congrArg (fun v : Fin 3 → ℤ => Packet.mk (first a) 2 v)
    funext z
    fin_cases z <;> fin_cases b <;>
      simp [packet, incidenceZ, inc, plusSigma, ClassAPlusConstantRecurrence.sigma,
        plusRunLength, ClassAPlusConstantRecurrence.runLength, first, last,
        OccurrenceTransport.residual, parikhZ, firstMark, plusRunMark,
        ClassAPlusConstantRecurrence.runMark, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, List.count_replicate, Nat.cast_sub hj0] <;> ring

/-- Both FIRST indices are zero and have the literal empty prefixes. -/
theorem first_first_step (n d : ℕ) (a b : Fin 3) (p q r : ℤ) :
    IndexedDigitStep (plusSigma n d) (packet a b p q r) 0 0
      (packet (first a) (first b) (2*p+q+r) (q+r)
        (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n+1 : ℕ) : ℤ)*r)) := by
  refine ⟨firstMark n d a, firstMark n d b, rfl, rfl, ?_⟩
  apply congrArg (fun v : Fin 3 → ℤ => Packet.mk (first a) (first b) v)
  funext z
  fin_cases z <;>
    simp [packet, incidenceZ, inc, plusSigma, ClassAPlusConstantRecurrence.sigma,
      plusRunLength, ClassAPlusConstantRecurrence.runLength, first, last,
      OccurrenceTransport.residual, parikhZ, firstMark, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, List.count_replicate] <;> ring

def upperSigma (n J : ℕ) : Fin 3 → Word := plusSigma n (2*n+12-J)
def cyclePacket (H : ℕ) : Packet := packet 2 2 (H : ℤ) (3*(H : ℤ)) (-6*(H : ℤ))
def zeroPacket : Packet := packet 2 2 0 0 0

def decrementIndices (J H : ℕ) : List (ℕ × ℕ) :=
  [(0,J*H-2),(J*(H-1)+4,1)]

/-- The replacement two-edge decrement uses FIRST/RUN and RUN/RUN.
It includes the formerly false JH=4 RUN-only proposal without relabelling
its LAST c: these are different actual occurrences. -/
theorem small_decrement (n J H : ℕ) (hn : 7 ≤ n) (hJ : 1 ≤ J)
    (hH : 1 ≤ H) (hlo : 3 ≤ J*H) (hhi : J*H ≤ 4) :
    OrderedPath (upperSigma n J) (cyclePacket H) (decrementIndices J H)
      (cyclePacket (H-1)) := by
  have hJ4 : J ≤ 4 := by nlinarith
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

def baseOneIndices (n H : ℕ) : List (ℕ × ℕ) :=
  [(0,0),(1,1+(n+4)*H),(1,2*H+1)]

/-- At J=1, heights one and two have the same three-edge template. -/
theorem base_one_path (n H : ℕ) (hn : 7 ≤ n) (hlo : 1 ≤ H) (hhi : H ≤ 2) :
    OrderedPath (upperSigma n 1) (cyclePacket H) (baseOneIndices n H) zeroPacket := by
  have e1 := first_first_step n (2*n+12-1) 2 2
    (H : ℤ) (3*(H : ℤ)) (-6*(H : ℤ))
  have he1 : IndexedDigitStep (upperSigma n 1) (cyclePacket H) 0 0
      (packet 0 0 (-(H : ℤ)) (-3*(H : ℤ)) (5*(H : ℤ))) := by
    convert e1 using 1 <;>
      simp [upperSigma, cyclePacket, first, Nat.cast_sub (show 1 ≤ 2*n+12 by omega),
        Nat.cast_add, Nat.cast_mul] <;> congr 1 <;> ring
  have hr : 1+(n+4)*H ≤ plusRunLength n (2*n+12-1) 0 := by
    simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]
    nlinarith [Nat.sub_add_cancel (show 1 ≤ 2*n+12 by omega)]
  have e2 := run_run_step n (2*n+12-1) 0 0 1 (1+(n+4)*H)
    (by omega) (by simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]; omega)
    (by omega) hr (-(H : ℤ)) (-3*(H : ℤ)) (5*(H : ℤ))
  have he2 : IndexedDigitStep (upperSigma n 1)
      (packet 0 0 (-(H : ℤ)) (-3*(H : ℤ)) (5*(H : ℤ))) 1 (1+(n+4)*H)
      (packet 2 2 0 (2*(H : ℤ)) (-2*(H : ℤ))) := by
    convert e2 using 1 <;>
      simp [upperSigma, delta, Nat.cast_sub (show 1 ≤ 2*n+12 by omega),
        Nat.cast_add, Nat.cast_mul] <;> congr 1 <;> ring
  have e3 := run_run_step n (2*n+12-1) 2 2 1 (2*H+1)
    (by omega) (by simp [plusRunLength, ClassAPlusConstantRecurrence.runLength])
    (by omega) (by simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]; omega)
    0 (2*(H : ℤ)) (-2*(H : ℤ))
  have he3 : IndexedDigitStep (upperSigma n 1)
      (packet 2 2 0 (2*(H : ℤ)) (-2*(H : ℤ))) 1 (2*H+1) zeroPacket := by
    convert e3 using 1 <;>
      simp [upperSigma, zeroPacket, delta, Nat.cast_add, Nat.cast_mul] <;>
      congr 1 <;> ring
  simpa [baseOneIndices] using
    OrderedPath.snoc (OrderedPath.snoc (OrderedPath.snoc
      (OrderedPath.nil (cyclePacket H)) _ _ he1) _ _ he2) _ _ he3

def baseTwoIndices (n : ℕ) : List (ℕ × ℕ) := [(0,0),(0,2*n+6),(1,2)]

/-- The remaining J=2,H=1 base uses the actual top FIRST x twice. -/
theorem base_two_path (n : ℕ) (hn : 7 ≤ n) :
    OrderedPath (upperSigma n 2) (cyclePacket 1) (baseTwoIndices n) zeroPacket := by
  have e1 := first_first_step n (2*n+12-2) 2 2 1 3 (-6)
  have he1 : IndexedDigitStep (upperSigma n 2) (cyclePacket 1) 0 0
      (packet 0 0 (-1) (-3) 4) := by
    convert e1 using 1 <;>
      simp [upperSigma, cyclePacket, first, Nat.cast_sub (show 2 ≤ 2*n+12 by omega),
        Nat.cast_add, Nat.cast_mul] <;> congr 1 <;> ring
  have e2 := first_run_step n (2*n+12-2) 0 0 (2*n+6)
    (by omega) (by simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]; omega)
    (-1) (-3) 4
  have he2 : IndexedDigitStep (upperSigma n 2) (packet 0 0 (-1) (-3) 4)
      0 (2*n+6) (packet 0 2 0 1 (-1)) := by
    convert e2 using 1 <;>
      simp [upperSigma, first, Nat.cast_sub (show 2 ≤ 2*n+12 by omega),
        Nat.cast_add, Nat.cast_mul] <;> congr 1 <;> ring
  have e3 := run_run_step n (2*n+12-2) 0 2 1 2
    (by omega) (by simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]; omega)
    (by omega) (by simp [plusRunLength, ClassAPlusConstantRecurrence.runLength]; omega)
    0 1 (-1)
  have he3 : IndexedDigitStep (upperSigma n 2) (packet 0 2 0 1 (-1))
      1 2 zeroPacket := by
    convert e3 using 1 <;>
      simp [upperSigma, zeroPacket, delta, Nat.cast_add] <;> congr 1 <;> ring
  simpa [baseTwoIndices] using
    OrderedPath.snoc (OrderedPath.snoc (OrderedPath.snoc
      (OrderedPath.nil (cyclePacket 1)) _ _ he1) _ _ he2) _ _ he3

def EightCases (J H : ℕ) : Prop :=
  (J,H) ∈ [(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1)]

/-- This table is specified only for EightCases. All n dependence remains
in the original RUN indices; there is no finite bound on n. -/
def eightIndices (n J H : ℕ) : List (ℕ × ℕ) :=
  if J=1 then
    if H=1 then baseOneIndices n 1
    else if H=2 then baseOneIndices n 2
    else if H=3 then decrementIndices 1 3 ++ baseOneIndices n 2
    else decrementIndices 1 4 ++ decrementIndices 1 3 ++ baseOneIndices n 2
  else if J=2 then
    if H=1 then baseTwoIndices n
    else decrementIndices 2 2 ++ baseTwoIndices n
  else decrementIndices J H

/-- All eight literal paths are proved for every n>=7. -/
theorem eight_ordered_paths (n J H : ℕ) (hn : 7 ≤ n) (hc : EightCases J H) :
    OrderedPath (upperSigma n J) (cyclePacket H) (eightIndices n J H) zeroPacket := by
  have b1 := base_one_path n 1 hn (by omega) (by omega)
  have b2 := base_one_path n 2 hn (by omega) (by omega)
  have b21 := base_two_path n hn
  have d13 := small_decrement n 1 3 hn (by omega) (by omega) (by omega) (by omega)
  have d14 := small_decrement n 1 4 hn (by omega) (by omega) (by omega) (by omega)
  have d22 := small_decrement n 2 2 hn (by omega) (by omega) (by omega) (by omega)
  have d31 := small_decrement n 3 1 hn (by omega) (by omega) (by omega) (by omega)
  have d41 := small_decrement n 4 1 hn (by omega) (by omega) (by omega) (by omega)
  simp only [EightCases, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
  rcases hc with h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl,rfl⟩
  · simpa [eightIndices] using b1
  · simpa [eightIndices] using b2
  · simpa [eightIndices] using d13.trans b2
  · simpa [eightIndices, List.append_assoc] using d14.trans (d13.trans b2)
  · simpa [eightIndices] using b21
  · simpa [eightIndices] using d22.trans b21
  · simpa [eightIndices, cyclePacket, zeroPacket] using d31
  · simpa [eightIndices, cyclePacket, zeroPacket] using d41

/-- Reversal swaps both actual occurrence ordinals. -/
theorem indexed_step_swap {s : Fin 3 → Word} {p q : Packet} {i j : ℕ}
    (h : IndexedDigitStep s p i j q) : IndexedDigitStep s p.swap j i q.swap := by
  obtain ⟨dt,db,hi,hj,rfl⟩ := h
  refine ⟨db,dt,hj,hi,?_⟩
  simp only [Packet.swap, Matrix.mulVec_neg]
  rw [residual_swap dt.before db.before]
  congr 1
  abel

theorem ordered_path_swap {s : Fin 3 → Word} {p q : Packet}
    {xs : List (ℕ × ℕ)} (hp : OrderedPath s p xs q) :
    OrderedPath s p.swap (xs.map Prod.swap) q.swap := by
  induction hp with
  | nil => exact .nil _
  | snoc _ i j he ih =>
    simpa only [List.map_append, List.map_cons, List.map_nil, Prod.swap_prod_mk] using
      OrderedPath.snoc ih j i (indexed_step_swap he)

def signedSource (reversed : Bool) (H : ℕ) : Packet :=
  if reversed then (cyclePacket H).swap else cyclePacket H

def signedIndices (reversed : Bool) (n J H : ℕ) : List (ℕ × ℕ) :=
  if reversed then (eightIndices n J H).map Prod.swap else eightIndices n J H

theorem signed_ordered_paths (n J H : ℕ) (hn : 7 ≤ n) (hc : EightCases J H)
    (reversed : Bool) :
    OrderedPath (upperSigma n J) (signedSource reversed H)
      (signedIndices reversed n J H) zeroPacket := by
  have hp := eight_ordered_paths n J H hn hc
  cases reversed
  · exact hp
  · have hz : zeroPacket.swap = zeroPacket := by
      simpa [zeroPacket] using ClassAMinusConstantRecurrence.packet_swap 2 2 0 0 0
    simpa only [signedSource, signedIndices, Bool.true_eq, ↓reduceIte, hz] using
      ordered_path_swap hp

/-- Strictness and full original-prefix assembly are attached to this
same ordered transcript. Positive scaling is explicit; no Perron root,
nearest-tail or supplied overlap/zero-hit premise is smuggled in. -/
theorem eight_traced_strict_prefixes (n J H : ℕ) (hn : 7 ≤ n)
    (hc : EightCases J H) (reversed : Bool)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (upperSigma n J a) = β*ℓ a) :
    OrderedInteriorPath (upperSigma n J) ℓ (signedSource reversed H)
      (signedIndices reversed n J H) zeroPacket ∧
    ∃ (top : Mark ((subst (upperSigma n J))^[(signedIndices reversed n J H).length]
        [(signedSource reversed H).top]))
      (bottom : Mark ((subst (upperSigma n J))^[(signedIndices reversed n J H).length]
        [(signedSource reversed H).bottom])),
      MarkTrace (upperSigma n J) (signedSource reversed H).top
        ((signedIndices reversed n J H).map Prod.fst) top.before top.letter top.after ∧
      MarkTrace (upperSigma n J) (signedSource reversed H).bottom
        ((signedIndices reversed n J H).map Prod.snd) bottom.before bottom.letter bottom.after ∧
      top.letter = 2 ∧ bottom.letter = 2 ∧
      incidenceZ (upperSigma n J) ^ (signedIndices reversed n J H).length *ᵥ
          (-(signedSource reversed H).delta) = parikhZ top.before-parikhZ bottom.before := by
  have hp := signed_ordered_paths n J H hn hc reversed
  have hz : zeroPacket.delta = 0 := by
    funext a
    fin_cases a <;> rfl
  exact ⟨ordered_path_indexed_interior (upperSigma n J) ℓ β hpos hβ hscale hp
      (zero_packet_interior ℓ hpos 2 2),
    ordered_path_traced_zero_original_prefixes hp hz⟩

/-- Every terminal state is the typed y/y zero, with no projected offset. -/
theorem zero_typed : zeroPacket.Diagonal := by
  constructor
  · rfl
  · funext a
    fin_cases a <;> rfl

/-- The disputed ordinal n+2 is precisely LAST c in the original y word. -/
theorem disputed_last_is_c (n d : ℕ) :
    (lastMark n d 2).index = n+2 ∧ (lastMark n d 2).letter = 1 ∧
      (lastMark n d 2).letter ≠ 2 := by
  simp [lastMark, Mark.index, plusRunLength, ClassAPlusConstantRecurrence.runLength,
    first, last, Nat.add_comm, Nat.add_left_comm]

end Psc.ClassAPlusUpperCycles
