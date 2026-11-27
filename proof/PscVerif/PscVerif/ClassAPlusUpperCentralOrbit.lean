/-
# The literal upper plus-Class-A central RUN orbit

The nearest-integer selector is instantiated on complete integral packets.
Every iteration records its two actual RUN ordinals. Cubic half-tie exclusion
and literal length scaling prove strict centrality at every depth. The scalar
recurrence and full packet reconstruction are derived from that same orbit;
the reconstruction begins at depth one, not at the source.

This formalizes the central-source bridge already specified by
`docs/bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md`.
-/
import PscVerif.ClassAPlusUpperLiteralEntry

namespace Psc.ClassAPlusUpperCentralOrbit

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.OccurrenceSuccessor Psc.ClassAZeroDefectEscape
open Psc.ClassAMinusPrefixAssembly Psc.ClassAPlusUpperCycles
open Psc.ClassAPlusUpperRecurrence Psc.ClassAPlusUpperLiteralEntry Matrix

/-- Original bottom-minus-top coordinates, including all three entries. -/
def coordinates (p : Packet) : Fin 3 → ℤ := -p.delta

@[simp] theorem coordinates_packet (a b : Fin 3) (p q r : ℤ) :
    coordinates (packet a b p q r) = ![p,q,r] := by
  funext i
  fin_cases i <;> simp [coordinates, packet]

theorem central_packet {n : ℕ} {β : ℝ} {p : Packet} (hc : Central n β p) :
    p = packet 2 2 (coordinates p 0) (coordinates p 1) (coordinates p 2) := by
  obtain ⟨ht, hb, _⟩ := hc
  cases p with
  | mk top bottom delta =>
    simp only at ht hb
    subst top
    subst bottom
    apply congrArg (Packet.mk 2 2)
    funext i
    fin_cases i <;> simp [coordinates]

theorem shift_packet (n : ℕ) (β : ℝ) (a b : Fin 3) (p q r : ℤ) :
    shift n β (packet a b p q r) =
      xLength n β*(p : ℝ)+cLength β*(q : ℝ)+(r : ℝ) := by
  simp [shift, packet, offset, dotProduct, Fin.sum_univ_three]
  ring

/-- The complete incidence update followed by subtraction of the rounded
physical gap. Its stored residual has the opposite sign to the coordinates. -/
def advance (n J : ℕ) (e : ℤ) (p : Packet) : Packet :=
  ⟨2,2,incidenceZ (upperSigma n J) *ᵥ p.delta + ![0,0,e]⟩

theorem advance_packet (n J : ℕ) (e : ℤ) (p : Packet) :
    advance n J e p = packet 2 2
      (2*coordinates p 0+coordinates p 1+coordinates p 2)
      (coordinates p 1+coordinates p 2)
      (((n+(2*n+12-J) : ℕ) : ℤ)*coordinates p 0+
        (n : ℤ)*coordinates p 1+((n+1 : ℕ) : ℤ)*coordinates p 2-e) := by
  apply congrArg (Packet.mk 2 2)
  funext i
  fin_cases i <;>
    simp [coordinates, incidenceZ, inc, upperSigma,
      plusSigma, ClassAPlusConstantRecurrence.sigma,
      ClassAPlusConstantRecurrence.runLength, first, last,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, List.count_replicate] <;> ring

theorem advance_first (n J : ℕ) (e : ℤ) (p : Packet) :
    coordinates (advance n J e p) 0 =
      2*coordinates p 0+coordinates p 1+coordinates p 2 := by
  simp [advance_packet]

theorem advance_physical {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (e : ℤ) (p : Packet) :
    shift n β (advance n J e p) = β*shift n β p-(e : ℝ) := by
  dsimp [shift, advance]
  rw [offset_add, offset_incidence _ _ β (literal_scaling hp)]
  simp [offset, dotProduct, Fin.sum_univ_three]
  ring

/-- The inflated shift itself is a full integral displacement. This derives
its no-half-tie property through literal scaling and the proved cubic lemma. -/
theorem inflated_shift_no_half {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (p : Packet) (z : ℤ) : β*shift n β p ≠ (z : ℝ)+1/2 := by
  have hh := shift_no_half hp (advance n J 0 p) z
  simpa [advance_physical hp] using hh

noncomputable def nearestGap (n : ℕ) (β : ℝ) (p : Packet) : ℤ :=
  ⌊β*shift n β p+1/2⌋

theorem nearestGap_error {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (p : Packet) : |β*shift n β p-(nearestGap n β p : ℝ)| < 1/2 := by
  have hlo : (nearestGap n β p : ℝ) ≤ β*shift n β p+1/2 := Int.floor_le _
  have hhi : β*shift n β p+1/2 < (nearestGap n β p : ℝ)+1 := Int.lt_floor_add_one _
  have hlo' : (nearestGap n β p : ℝ) < β*shift n β p+1/2 := by
    apply lt_of_le_of_ne hlo
    intro he
    apply inflated_shift_no_half hp p (nearestGap n β p-1)
    push_cast
    linarith
  apply abs_lt.mpr
  constructor <;> linarith

theorem advance_central {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (p : Packet) : Central n β (advance n J (nearestGap n β p) p) := by
  refine ⟨rfl,rfl,?_⟩
  rw [advance_physical hp]
  exact nearestGap_error hp p

def gapIndices (e : ℤ) : ℕ × ℕ := (e.toNat+1,(-e).toNat+1)

/-- Every selected central update is an actual pair of original RUN positions.
The range proof comes from the established upper central-gap theorem. -/
theorem central_indexed_step {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (p : Packet) (hc : Central n β p) :
    IndexedDigitStep (upperSigma n J) p
      (gapIndices (nearestGap n β p)).1 (gapIndices (nearestGap n β p)).2
      (advance n J (nearestGap n β p) p) := by
  obtain ⟨helo, hehi⟩ := central_gap_in_run n hp.n_lower β (shift n β p)
    hp.beta_pos hp.root_upper hc.2.2 (nearestGap n β p) (nearestGap_error hp p)
  have he := run_gap_digit_step n (2*n+12-J)
    (coordinates p 0) (coordinates p 1) (coordinates p 2)
    (nearestGap n β p) helo hehi
  rw [← central_packet hc, ← advance_packet] at he
  exact he

noncomputable def orbit (n J : ℕ) (β : ℝ) (source : Packet) : ℕ → Packet
  | 0 => source
  | k+1 => advance n J (nearestGap n β (orbit n J β source k)) (orbit n J β source k)

theorem orbit_central {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hc : Central n β source) :
    ∀ k, Central n β (orbit n J β source k) := by
  intro k
  cases k with
  | zero => exact hc
  | succ k => exact advance_central hp _

theorem orbit_step {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hc : Central n β source) (k : ℕ) :
    IndexedDigitStep (upperSigma n J) (orbit n J β source k)
      (gapIndices (nearestGap n β (orbit n J β source k))).1
      (gapIndices (nearestGap n β (orbit n J β source k))).2
      (orbit n J β source (k+1)) :=
  central_indexed_step hp _ (orbit_central hp source hc k)

/-- The first coordinate is the actual first coordinate of the full packet. -/
noncomputable def scalarOrbit (n J : ℕ) (β : ℝ) (source : Packet) (k : ℕ) : ℤ :=
  coordinates (orbit n J β source k) 0

/-- Two successive full updates reconstruct the entire first child packet.
The formula is valid for all integral data and both selected gaps. -/
theorem advance_reconstruction (n J : ℕ) (e f : ℤ) (p : Packet) :
    advance n J e p = reconstructedPacket (coordinates p 0)
      (coordinates (advance n J e p) 0)
      (coordinates (advance n J f (advance n J e p)) 0) := by
  simp only [advance_packet, coordinates_packet, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, reconstructedPacket]
  apply congrArg (Packet.mk 2 2)
  funext i
  fin_cases i <;> simp <;> ring

/-- The source is not reconstructed at index zero. The identity begins at
the first actual child and holds at every later iteration. -/
theorem orbit_reconstruction (n J : ℕ) (β : ℝ) (source : Packet) (k : ℕ) :
    orbit n J β source (k+1) = reconstructedPacket
      (scalarOrbit n J β source k) (scalarOrbit n J β source (k+1))
      (scalarOrbit n J β source (k+2)) :=
  advance_reconstruction n J (nearestGap n β (orbit n J β source k))
    (nearestGap n β (orbit n J β source (k+1))) (orbit n J β source k)

/-- Centrality of the completely reconstructed packet supplies the existing
original scalar recurrence, with no independent projected sequence premise. -/
theorem reconstructed_recurrence (n : ℕ) (β : ℝ) (a b c : ℤ)
    (hc : |shift n β (reconstructedPacket a b c)| < 1/2) :
    OriginalNearest (A β) (C n β) a b c := by
  have hh : |(2+C n β+A β/2)*(b : ℝ)+
      (1-A β/2)*((b-2*a : ℤ) : ℝ)+((c-3*b+2*a : ℤ) : ℝ)| < 1/2 := by
    rw [reconstructedPacket, shift_packet] at hc
    have hx : 2+C n β+A β/2 = xLength n β := by dsimp [A,C,xLength]; ring
    have hk : 1-A β/2 = cLength β := by dsimp [A,cLength]; ring
    simpa only [hx,hk] using hc
  have hr := central_coordinate_recurrence (A β) (C n β) a b (c-3*b+2*a) hh
  have he : 3*b-2*a+(c-3*b+2*a) = c := by ring
  simpa only [he] using hr

theorem orbit_recurrence {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hc : Central n β source) (k : ℕ) :
    OriginalNearest (A β) (C n β)
      (scalarOrbit n J β source k) (scalarOrbit n J β source (k+1))
      (scalarOrbit n J β source (k+2)) := by
  apply reconstructed_recurrence
  rw [← orbit_reconstruction]
  exact (orbit_central hp source hc (k+1)).2.2

/-- One literal central orbit, with its original ordinal pair at every edge,
all complete packets, the actual first coordinates, and reconstruction delay. -/
structure CentralOrbit (n J : ℕ) (β : ℝ) (source : Packet) where
  u : ℕ → ℤ
  w : ℕ → Packet
  marks : ℕ → ℕ × ℕ
  initial : w 0 = source
  central : ∀ k, Central n β (w k)
  edge : ∀ k, IndexedDigitStep (upperSigma n J) (w k)
    (marks k).1 (marks k).2 (w (k+1))
  coordinate : ∀ k, u k = -(w k).delta 0
  next_coordinate : ∀ k, u (k+1) =
    2*(-(w k).delta 0)+(-(w k).delta 1)+(-(w k).delta 2)
  reconstruction : ∀ k, w (k+1) = reconstructedPacket (u k) (u (k+1)) (u (k+2))
  recurrence : ∀ k, OriginalNearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))

/-- No orbit, boundedness, recurrence or half-tie assumption is supplied. -/
noncomputable def central_orbit {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hc : Central n β source) : CentralOrbit n J β source where
  u := scalarOrbit n J β source
  w := orbit n J β source
  marks := fun k => gapIndices (nearestGap n β (orbit n J β source k))
  initial := rfl
  central := orbit_central hp source hc
  edge := orbit_step hp source hc
  coordinate := fun _ => rfl
  next_coordinate := fun k => advance_first n J
    (nearestGap n β (orbit n J β source k)) (orbit n J β source k)
  reconstruction := orbit_reconstruction n J β source
  recurrence := orbit_recurrence hp source hc

/-- Unbundled public endpoint: all arrays, every original ordinal pair and
every full packet update are existentially constructed from the source. -/
theorem exists_literal_central_orbit {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hc : Central n β source) :
    ∃ (u : ℕ → ℤ) (w : ℕ → Packet) (marks : ℕ → ℕ × ℕ),
      w 0 = source ∧
      (∀ k, Central n β (w k)) ∧
      (∀ k, IndexedDigitStep (upperSigma n J) (w k)
        (marks k).1 (marks k).2 (w (k+1))) ∧
      (∀ k, u k = -(w k).delta 0) ∧
      (∀ k, u (k+1) = 2*(-(w k).delta 0)+(-(w k).delta 1)+(-(w k).delta 2)) ∧
      (∀ k, w (k+1) = reconstructedPacket (u k) (u (k+1)) (u (k+2))) ∧
      (∀ k, OriginalNearest (A β) (C n β) (u k) (u (k+1)) (u (k+2))) := by
  let O := central_orbit hp source hc
  exact ⟨O.u,O.w,O.marks,O.initial,O.central,O.edge,O.coordinate,
    O.next_coordinate,O.reconstruction,O.recurrence⟩

def prefixIndices {n J : ℕ} {β : ℝ} {source : Packet}
    (O : CentralOrbit n J β source) (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).map O.marks

@[simp] theorem prefixIndices_length {n J : ℕ} {β : ℝ} {source : Packet}
    (O : CentralOrbit n J β source) (k : ℕ) : (prefixIndices O k).length = k := by
  simp [prefixIndices]

theorem orbit_prefix_path {n J : ℕ} {β : ℝ} {source : Packet}
    (O : CentralOrbit n J β source) (k : ℕ) :
    OrderedPath (upperSigma n J) source (prefixIndices O k) (O.w k) := by
  induction k with
  | zero => simpa [prefixIndices, O.initial] using OrderedPath.nil (s := upperSigma n J) source
  | succ k ih =>
    simpa [prefixIndices, List.range_succ] using
      OrderedPath.snoc ih (O.marks k).1 (O.marks k).2 (O.edge k)

theorem orbit_prefix_strict_path {n J : ℕ} {β : ℝ} {source : Packet}
    (hp : Family n J β) (O : CentralOrbit n J β source) (k : ℕ) :
    OrderedInteriorPath (upperSigma n J) (lengths n β) source (prefixIndices O k)
      (O.w k) := by
  induction k with
  | zero =>
    have hs : source.Interior (lengths n β) := by
      rw [← O.initial]
      exact central_interior hp (O.central 0)
    simpa [prefixIndices, O.initial] using OrderedInteriorPath.nil
      (s := upperSigma n J) source hs
  | succ k ih =>
    simpa [prefixIndices, List.range_succ] using OrderedInteriorPath.snoc ih
      (O.marks k).1 (O.marks k).2 (O.edge k) (central_interior hp (O.central (k+1)))

end Psc.ClassAPlusUpperCentralOrbit
