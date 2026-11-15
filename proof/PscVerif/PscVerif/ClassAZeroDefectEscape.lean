/-
# Actual zero-return paths in a minus-Class-A slice

The substitution words and the selected proper-prefix occurrences are literal.
The arithmetic convention in the Class-A notes is bottom minus top; `packet`
negates it to use the existing top-minus-bottom occurrence transport.

Literature and scope: `docs/bh-class-a-entry-stop-go-2026-11-14.md`.
No complete source cover or universal BH statement is asserted.
-/
import PscVerif.OccurrenceSuccessor
import Mathlib.Tactic.FinCases

namespace Psc.ClassAZeroDefectEscape

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Psc.OccurrenceSuccessor Matrix
open scoped BigOperators

def first (a : Fin 3) : Fin 3 := if a = 1 then 1 else 0

def last (a : Fin 3) : Fin 3 := if a = 2 then 1 else 0

def runLength (n d : ℕ) (a : Fin 3) : ℕ :=
  if a = 0 then n + d else if a = 1 then n else n - 1

def sigma (n d : ℕ) (a : Fin 3) : Word :=
  [first a] ++ List.replicate (runLength n d a) 2 ++ [last a]

def packet (a b : Fin 3) (p q r : ℤ) : Packet :=
  ⟨a, b, ![-p, -q, -r]⟩

/-- Zero-based position inside the actual run of `y` letters. -/
def runMark (n d : ℕ) (a : Fin 3) (j : ℕ)
    (hj : j < runLength n d a) : Mark (sigma n d a) where
  before := [first a] ++ List.replicate j 2
  letter := 2
  after := List.replicate (runLength n d a - (j + 1)) 2 ++ [last a]
  split := by
    simp only [sigma, List.cons_append, List.nil_append]
    congr 1
    rw [← List.cons_append, ← List.replicate_succ, ← List.append_assoc,
      ← List.replicate_add]
    congr 2
    omega

def firstMark (n d : ℕ) (a : Fin 3) : Mark (sigma n d a) where
  before := []
  letter := first a
  after := List.replicate (runLength n d a) 2 ++ [last a]
  split := by simp [sigma]

def lastMark (n d : ℕ) (a : Fin 3) : Mark (sigma n d a) where
  before := [first a] ++ List.replicate (runLength n d a) 2
  letter := last a
  after := []
  split := by simp [sigma]

@[simp] theorem runMark_index (n d : ℕ) (a : Fin 3) (j : ℕ)
    (hj : j < runLength n d a) : (runMark n d a j hj).index = j + 1 := by
  simp [runMark, Mark.index]

@[simp] theorem lastMark_index (n d : ℕ) (a : Fin 3) :
    (lastMark n d a).index = runLength n d a + 1 := by
  simp [lastMark, Mark.index, Nat.add_comm]

/-- Positive occurrence ordinals include the final letter when `j = R_a`. -/
def positiveMark (n d : ℕ) (a : Fin 3) (j : ℕ)
    (_hj : j ≤ runLength n d a) : Mark (sigma n d a) :=
  if hrun : j < runLength n d a then runMark n d a j hrun
  else lastMark n d a

@[simp] theorem positiveMark_before (n d : ℕ) (a : Fin 3) (j : ℕ)
    (hj : j ≤ runLength n d a) :
    (positiveMark n d a j hj).before = [first a] ++ List.replicate j 2 := by
  unfold positiveMark
  split_ifs with hrun
  · rfl
  · have h : j = runLength n d a := by omega
    simp [lastMark, h]

@[simp] theorem positiveMark_index (n d : ℕ) (a : Fin 3) (j : ℕ)
    (hj : j ≤ runLength n d a) :
    (positiveMark n d a j hj).index = j + 1 := by
  simp [Mark.index]

theorem positiveMark_letter_of_lt (n d : ℕ) (a : Fin 3) (j : ℕ)
    (hj : j < runLength n d a) :
    (positiveMark n d a j hj.le).letter = 2 := by
  simp [positiveMark, hj, runMark]

/-- An affine edge with its original two literal occurrence ordinals. -/
def IndexedDigitStep (s : Fin 3 → Word) (p : Packet) (i j : ℕ)
    (q : Packet) : Prop :=
  ∃ (dt : Mark (s p.top)) (db : Mark (s p.bottom)),
    dt.index = i ∧ db.index = j ∧
    q = ⟨dt.letter, db.letter,
      incidenceZ s *ᵥ p.delta + residual dt.before db.before⟩

theorem IndexedDigitStep.digitStep {s : Fin 3 → Word}
    {p q : Packet} {i j : ℕ} (h : IndexedDigitStep s p i j q) :
    DigitStep s p q := by
  obtain ⟨dt, db, _, _, hq⟩ := h
  exact ⟨dt, db, hq⟩

def delta (a b : Fin 3) : ℤ :=
  (if a = 1 then 0 else 1) - (if b = 1 then 0 else 1)

/-- The full affine update from actual positive prefixes, including LAST.
The statement retains both chosen prefix occurrences and all coordinates. -/
theorem positive_step (n d : ℕ) (_hn : 1 ≤ n) (a b : Fin 3)
    (i j : ℕ) (hi : i ≤ runLength n d a) (hj : j ≤ runLength n d b)
    (p q r : ℤ) :
    IndexedDigitStep (sigma n d) (packet a b p q r) (i + 1) (j + 1)
      (packet (positiveMark n d a i hi).letter (positiveMark n d b j hj).letter
        (2*p+q+r-delta a b) (q+r+delta a b)
        (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+(j : ℤ)-i)) := by
  refine ⟨positiveMark n d a i hi, positiveMark n d b j hj,
    positiveMark_index n d a i hi, positiveMark_index n d b j hj, ?_⟩
  apply congrArg (fun v : Fin 3 → ℤ =>
    Packet.mk (positiveMark n d a i hi).letter (positiveMark n d b j hj).letter v)
  funext z
  fin_cases z <;> fin_cases a <;> fin_cases b <;>
    simp [packet, incidenceZ, inc, sigma, runLength, first, last, OccurrenceTransport.residual,
      parikhZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three, delta,
      List.count_replicate] <;> ring

/-- A strict target of an actual digit edge forces strict overlap of its
parent tiles.  This is the geometric containment argument, using the exact
substitution scaling rather than a separate assumption on the source. -/
theorem interior_source_of_digitStep
    (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {p q : Packet} (hedge : DigitStep s p q) (hq : q.Interior ℓ) :
    p.Interior ℓ := by
  obtain ⟨dt, db, rfl⟩ := hedge
  obtain ⟨x, hx, hxt, hxb, hxbe⟩ := hq
  have hnonneg : ∀ a, 0 ≤ ℓ a := fun a => (hpos a).le
  have htpre := physicalLength_nonneg ℓ hnonneg dt.before
  have hbpre := physicalLength_nonneg ℓ hnonneg db.before
  have htpost := physicalLength_nonneg ℓ hnonneg dt.after
  have hbpost := physicalLength_nonneg ℓ hnonneg db.after
  have htlen : physicalLength ℓ dt.before + ℓ dt.letter +
      physicalLength ℓ dt.after = β * ℓ p.top := by
    have h := congrArg (physicalLength ℓ) dt.split
    rw [hscale p.top] at h
    simpa only [physicalLength_append, physicalLength_cons, add_assoc] using h.symm
  have hblen : physicalLength ℓ db.before + ℓ db.letter +
      physicalLength ℓ db.after = β * ℓ p.bottom := by
    have h := congrArg (physicalLength ℓ) db.split
    rw [hscale p.bottom] at h
    simpa only [physicalLength_append, physicalLength_cons, add_assoc] using h.symm
  change 0 < x + offset ℓ (incidenceZ s *ᵥ p.delta +
    residual dt.before db.before) at hxb
  change x + offset ℓ (incidenceZ s *ᵥ p.delta +
    residual dt.before db.before) < ℓ db.letter at hxbe
  rw [offset_affine s ℓ β hscale] at hxb hxbe
  refine ⟨(physicalLength ℓ dt.before + x) / β, ?_, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) hβ
  · apply (div_lt_iff₀ hβ).2
    linarith
  · have h : -offset ℓ p.delta < (physicalLength ℓ dt.before + x) / β := by
      apply (lt_div_iff₀ hβ).2
      nlinarith
    linarith
  · have h : (physicalLength ℓ dt.before + x) / β <
        ℓ p.bottom - offset ℓ p.delta := by
      apply (div_lt_iff₀ hβ).2
      nlinarith
    linarith

def IndexedInteriorStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (p : Packet) (i j : ℕ) (q : Packet) : Prop :=
  IndexedDigitStep s p i j q ∧ q.Interior ℓ

theorem IndexedInteriorStep.interiorStep {s : Fin 3 → Word}
    {ℓ : Fin 3 → ℝ} {p q : Packet} {i j : ℕ}
    (h : IndexedInteriorStep s ℓ p i j q) : InteriorStep s ℓ p q :=
  ⟨h.1.digitStep, h.2⟩

theorem zero_packet_interior (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (a b : Fin 3) : (packet a b 0 0 0).Interior ℓ := by
  apply (Packet.interior_iff_bounds ℓ hpos _).2
  have hz : (packet a b 0 0 0).delta = 0 := by
    funext c; fin_cases c <;> rfl
  rw [hz]
  simpa [offset, dotProduct, packet] using And.intro (hpos a) (hpos b)

/-- The source outside the one-step predecessor segment at `m = n + 1`. -/
def overrunSource (n : ℕ) : Packet := packet 2 2 0 ((n : ℤ) + 1) (-(n : ℤ) - 1)

def endpointCx : Packet := packet 1 0 (-1) 0 2
def endpointXy : Packet := packet 0 2 1 1 (-2)
def endpointYx : Packet := packet 2 0 0 (-1) 1
def zeroYy : Packet := packet 2 2 0 0 0

/-- Four selected genuine occurrences, with LAST retained at the first edge. -/
theorem overrun_four_digit_steps (n d : ℕ) (hn : 2 ≤ n) :
    IndexedDigitStep (sigma n d) (overrunSource n) n 0 endpointCx ∧
    IndexedDigitStep (sigma n d) endpointCx (n + 1) (d + 1) endpointXy ∧
    IndexedDigitStep (sigma n d) endpointXy (d + 2) 0 endpointYx ∧
    IndexedDigitStep (sigma n d) endpointYx 1 2 zeroYy := by
  have hn1 : 1 ≤ n := by omega
  have hx1 : d < runLength n d 0 := by simp [runLength]; omega
  have hx2 : d + 1 < runLength n d 0 := by simp [runLength]; omega
  have hy0 : 0 < runLength n d 2 := by simp [runLength]; omega
  have hx01 : 1 < runLength n d 0 := by simp [runLength]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨lastMark n d 2, firstMark n d 2, ?_, rfl, ?_⟩
    · simp [lastMark, Mark.index, runLength]
      omega
    · change packet 1 0 (-1) 0 2 = _
      apply congrArg (fun v : Fin 3 → ℤ => Packet.mk 1 0 v)
      funext z
      fin_cases z <;>
        simp [packet, incidenceZ, inc, sigma, runLength, first, last,
          OccurrenceTransport.residual, parikhZ, lastMark, firstMark, overrunSource,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          List.count_replicate, Nat.cast_sub hn1] <;> ring
  · refine ⟨lastMark n d 1, runMark n d 0 d hx1, ?_, ?_, ?_⟩
    · simp [lastMark, Mark.index, runLength]
    · simp [runMark, Mark.index]
    · change packet 0 2 1 1 (-2) = _
      apply congrArg (fun v : Fin 3 → ℤ => Packet.mk 0 2 v)
      funext z
      fin_cases z <;>
        simp [packet, incidenceZ, inc, sigma, runLength, first, last,
          OccurrenceTransport.residual, parikhZ, lastMark, runMark, endpointCx,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          List.count_replicate, Nat.cast_sub hn1] <;> ring
  · refine ⟨runMark n d 0 (d + 1) hx2, firstMark n d 2, ?_, rfl, ?_⟩
    · simp [runMark, Mark.index] <;> omega
    · change packet 2 0 0 (-1) 1 = _
      apply congrArg (fun v : Fin 3 → ℤ => Packet.mk 2 0 v)
      funext z
      fin_cases z <;>
        simp [packet, incidenceZ, inc, sigma, runLength, first, last,
          OccurrenceTransport.residual, parikhZ, runMark, firstMark, endpointXy,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          List.count_replicate, Nat.cast_sub hn1] <;> ring
  · refine ⟨runMark n d 2 0 hy0, runMark n d 0 1 hx01, ?_, ?_, ?_⟩
    · simp [runMark, Mark.index]
    · simp [runMark, Mark.index]
    · change packet 2 2 0 0 0 = _
      apply congrArg (fun v : Fin 3 → ℤ => Packet.mk 2 2 v)
      funext z
      fin_cases z <;>
        simp [packet, incidenceZ, inc, sigma, runLength, first, last,
          OccurrenceTransport.residual, parikhZ, runMark, endpointYx,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          List.count_replicate, Nat.cast_sub hn1] <;> ring

/-- The selected four edges form a composable strict path to integral zero.
Strictness of every ancestor follows from the common final tile interval. -/
theorem overrun_four_steps (n d : ℕ) (hn : 2 ≤ n)
    (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (sigma n d a) = β * ℓ a) :
    IndexedInteriorStep (sigma n d) ℓ (overrunSource n) n 0 endpointCx ∧
    IndexedInteriorStep (sigma n d) ℓ endpointCx (n + 1) (d + 1) endpointXy ∧
    IndexedInteriorStep (sigma n d) ℓ endpointXy (d + 2) 0 endpointYx ∧
    IndexedInteriorStep (sigma n d) ℓ endpointYx 1 2 zeroYy ∧
    (overrunSource n).Interior ℓ ∧ zeroYy.delta = 0 := by
  obtain ⟨e1, e2, e3, e4⟩ := overrun_four_digit_steps n d hn
  have h4 : zeroYy.Interior ℓ := zero_packet_interior ℓ hpos 2 2
  have h3 := interior_source_of_digitStep (sigma n d) ℓ β hpos hβ hscale e4.digitStep h4
  have h2 := interior_source_of_digitStep (sigma n d) ℓ β hpos hβ hscale e3.digitStep h3
  have h1 := interior_source_of_digitStep (sigma n d) ℓ β hpos hβ hscale e2.digitStep h2
  have h0 := interior_source_of_digitStep (sigma n d) ℓ β hpos hβ hscale e1.digitStep h1
  exact ⟨⟨e1, h1⟩, ⟨e2, h2⟩, ⟨e3, h3⟩, ⟨e4, h4⟩, h0, by
    funext a; fin_cases a <;> rfl⟩

theorem overrun_composable_path (n d : ℕ) (hn : 2 ≤ n)
    (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (sigma n d a) = β * ℓ a) :
    Relation.ReflTransGen (InteriorStep (sigma n d) ℓ) (overrunSource n) zeroYy := by
  obtain ⟨e1, e2, e3, e4, _, _⟩ := overrun_four_steps n d hn ℓ β hpos hβ hscale
  exact ((Relation.ReflTransGen.single e1.interiorStep).trans
    (Relation.ReflTransGen.single e2.interiorStep)).trans
    ((Relation.ReflTransGen.single e3.interiorStep).trans
      (Relation.ReflTransGen.single e4.interiorStep))

/-- An explicit source slice whose first RUN/RUN child has zero first
coordinate and total sum zero.  Its total sum is `S`, and `h` is the
required difference of the first two occurrence ordinals. -/
def runSlice (n d : ℕ) (a b : Fin 3) (S h : ℤ) : Packet :=
  let q := h - ((d : ℤ) + 1) * delta a b + ((d : ℤ) - n) * S
  packet a b (delta a b - S) q (2*S-delta a b-q)

theorem runLength_pos (n d : ℕ) (hn : 2 ≤ n) (a : Fin 3) :
    0 < runLength n d a := by
  fin_cases a <;> simp [runLength] <;> omega

/-- The complete clipped two-step construction.  `h.toNat` and
`(-h).toNat` are zero-based positions inside the two first runs; the second
pair may select the actual LAST letter at the boundary `|2S| = n - 1`.
Only integral zero is claimed at that endpoint. -/
theorem run_slice_two_digit_steps (n d : ℕ) (hn : 2 ≤ n)
    (a b : Fin 3) (S h : ℤ)
    (hlo : 1 - (runLength n d b : ℤ) ≤ h)
    (hhi : h ≤ (runLength n d a : ℤ) - 1)
    (hSlo : -((n - 1 : ℕ) : ℤ) ≤ 2*S)
    (hShi : 2*S ≤ ((n - 1 : ℕ) : ℤ)) :
    ∃ goal : Packet,
      IndexedDigitStep (sigma n d) (runSlice n d a b S h)
        (h.toNat + 1) ((-h).toNat + 1) (packet 2 2 0 (2*S) (-2*S)) ∧
      IndexedDigitStep (sigma n d) (packet 2 2 0 (2*S) (-2*S))
        ((2*S).toNat + 1) ((-(2*S)).toNat + 1) goal ∧
      goal.delta = 0 := by
  have hn1 : 1 ≤ n := by omega
  have ha := runLength_pos n d hn a
  have hb := runLength_pos n d hn b
  have hi : h.toNat < runLength n d a := by omega
  have hj : (-h).toNat < runLength n d b := by omega
  have hu : (2*S).toNat ≤ runLength n d 2 := by simp [runLength]; omega
  have hv : (-(2*S)).toNat ≤ runLength n d 2 := by simp [runLength]; omega
  have hh : ((h.toNat : ℕ) : ℤ) - ((-h).toNat : ℤ) = h := by omega
  have hSS : (((2*S).toNat : ℕ) : ℤ) - ((-(2*S)).toNat : ℤ) = 2*S := by omega
  let q := h - ((d : ℤ) + 1) * delta a b + ((d : ℤ) - n) * S
  let u := positiveMark n d 2 (2*S).toNat hu
  let v := positiveMark n d 2 (-(2*S)).toNat hv
  let goal := packet u.letter v.letter 0 0 0
  have e1 := positive_step n d hn1 a b h.toNat (-h).toNat hi.le hj.le
    (delta a b - S) q (2*S-delta a b-q)
  have hP : 2*(delta a b-S)+q+(2*S-delta a b-q)-delta a b = 0 := by ring
  have hQ : q+(2*S-delta a b-q)+delta a b = 2*S := by ring
  have hR : ((n+d : ℕ) : ℤ)*(delta a b-S)+(n : ℤ)*q+
      ((n-1 : ℕ) : ℤ)*(2*S-delta a b-q)+((-h).toNat : ℤ)-h.toNat = -2*S := by
    dsimp [q]
    simp only [Nat.cast_sub hn1, Nat.cast_one]
    linear_combination -hh
  have e1' : IndexedDigitStep (sigma n d) (runSlice n d a b S h)
      (h.toNat+1) ((-h).toNat+1) (packet 2 2 0 (2*S) (-2*S)) := by
    simpa only [positiveMark_letter_of_lt n d a h.toNat hi,
      positiveMark_letter_of_lt n d b (-h).toNat hj, hP, hQ, hR,
      runSlice] using e1
  have e2 := positive_step n d hn1 2 2 (2*S).toNat (-(2*S)).toNat hu hv
    0 (2*S) (-2*S)
  have hR2 : ((n+d : ℕ) : ℤ)*0+(n : ℤ)*(2*S)+
      ((n-1 : ℕ) : ℤ)*(-2*S)+((-(2*S)).toNat : ℤ)-(2*S).toNat = 0 := by
    rw [Nat.cast_sub hn1]
    push_cast
    linear_combination -hSS
  have e2' : IndexedDigitStep (sigma n d) (packet 2 2 0 (2*S) (-2*S))
      ((2*S).toNat+1) ((-(2*S)).toNat+1) goal := by
    rw [hR2] at e2
    simpa [goal, u, v, delta] using e2
  refine ⟨goal, e1', e2', ?_⟩
  funext c
  fin_cases c <;> rfl

/-- The explicit two-step construction is strict at every stage under any
positive exact substitution length scaling.  The path is therefore directly
consumable by the occurrence-transport API. -/
theorem run_slice_two_steps (n d : ℕ) (hn : 2 ≤ n)
    (a b : Fin 3) (S h : ℤ)
    (hlo : 1 - (runLength n d b : ℤ) ≤ h)
    (hhi : h ≤ (runLength n d a : ℤ) - 1)
    (hSlo : -((n - 1 : ℕ) : ℤ) ≤ 2*S)
    (hShi : 2*S ≤ ((n - 1 : ℕ) : ℤ))
    (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ c, 0 < ℓ c) (hβ : 0 < β)
    (hscale : ∀ c, physicalLength ℓ (sigma n d c) = β * ℓ c) :
    ∃ goal : Packet,
      IndexedInteriorStep (sigma n d) ℓ (runSlice n d a b S h)
        (h.toNat + 1) ((-h).toNat + 1) (packet 2 2 0 (2*S) (-2*S)) ∧
      IndexedInteriorStep (sigma n d) ℓ (packet 2 2 0 (2*S) (-2*S))
        ((2*S).toNat + 1) ((-(2*S)).toNat + 1) goal ∧
      (runSlice n d a b S h).Interior ℓ ∧ goal.delta = 0 := by
  obtain ⟨goal, e1, e2, hzero⟩ := run_slice_two_digit_steps n d hn a b S h hlo hhi hSlo hShi
  have hg : goal.Interior ℓ := by
    apply (Packet.interior_iff_bounds ℓ hpos goal).2
    rw [hzero]
    simp [offset, dotProduct]
    constructor <;> linarith [hpos goal.top, hpos goal.bottom]
  have hm := interior_source_of_digitStep (sigma n d) ℓ β hpos hβ hscale e2.digitStep hg
  have hs := interior_source_of_digitStep (sigma n d) ℓ β hpos hβ hscale e1.digitStep hm
  exact ⟨goal, ⟨e1, hm⟩, ⟨e2, hg⟩, hs, hzero⟩

end Psc.ClassAZeroDefectEscape
