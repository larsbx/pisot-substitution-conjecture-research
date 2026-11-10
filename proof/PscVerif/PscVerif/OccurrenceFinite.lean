/-
# Finite support of actual marked word pairs

Every mark is determined by its actual letter index.  A supplied finite
carrier therefore has a finite set of actual marked members and a finite
packet image, bounded by the sum of the products of the two word lengths.
Filtering this image by strict physical interior overlap does not introduce
a guessed residual bound or a production graph identifier.

The pre-code review is `docs/c4-finite-carrier-dual-literature-2026-11-10.md`.
This module supplies finiteness, not productivity, a shared legal limit, or
an identification of packet-set membership with weighted edge multiplicity.
-/
import PscVerif.OccurrenceTransport
import Mathlib.Data.Fintype.Card

namespace Psc.OccurrenceFinite

open Psc.OccurrenceTransport
open scoped BigOperators

/-- Select the actual letter at a valid zero-based index. -/
def markAt (w : Word) (i : Fin w.length) : Mark w where
  before := w.take i
  letter := w[i.val]'i.isLt
  after := w.drop (i + 1)
  split := by rw [List.getElem_cons_drop i.isLt, List.take_append_drop]

theorem markAt_index (w : Word) (i : Fin w.length) :
    (markAt w i).index = i := by
  simp [markAt, Mark.index]

theorem markAt_before (w : Word) (i : Fin w.length) :
    (markAt w i).before = w.take i := rfl

theorem markAt_letter (w : Word) (i : Fin w.length) :
    (markAt w i).letter = w[i.val]'i.isLt := rfl

theorem mark_drop {w : Word} (m : Mark w) :
    w.drop (m.index + 1) = m.after := by
  simpa [Mark.index] using congrArg (List.drop (m.index + 1)) m.split

/-- Equal numeric addresses identify the entire actual mark, not merely
its selected letter. -/
theorem mark_index_injective (w : Word) :
    Function.Injective (fun m : Mark w => m.index) := by
  intro m n h
  change m.index = n.index at h
  have hb : m.before = n.before := by rw [← m.take_index, ← n.take_index, h]
  have hl : m.letter = n.letter := by
    apply Option.some.inj
    calc
      some m.letter = w[m.index]? := by
        rw [List.getElem?_eq_getElem m.index_lt, m.selected]
      _ = w[n.index]? := congrArg (fun k => w[k]?) h
      _ = some n.letter := by
        rw [List.getElem?_eq_getElem n.index_lt, n.selected]
  have ha : m.after = n.after := by rw [← mark_drop m, ← mark_drop n, h]
  cases m
  cases n
  cases hb
  cases hl
  cases ha
  rfl

def markIndex {w : Word} (m : Mark w) : Fin w.length := ⟨m.index, m.index_lt⟩

theorem markAt_markIndex {w : Word} (m : Mark w) :
    markAt w (markIndex m) = m :=
  mark_index_injective w (by simp [markAt_index, markIndex])

/-- The equivalence retains prefix, selected letter and suffix through the
index; occurrence multiplicity is not replaced by letter membership. -/
def markEquiv (w : Word) : Mark w ≃ Fin w.length where
  toFun := markIndex
  invFun := markAt w
  left_inv := markAt_markIndex
  right_inv i := Fin.ext (markAt_index w i)

/-- All actual index pairs in all members of the supplied finite carrier. -/
abbrev Indexed (C : Finset WordPair) :=
  Σ T : {T // T ∈ C}, Fin T.val.1.length × Fin T.val.2.length

def indexedPair (C : Finset WordPair) (x : Indexed C) : MarkedPair where
  words := x.1.val
  top := markAt _ x.2.1
  bottom := markAt _ x.2.2

theorem indexedPair_mem (C : Finset WordPair) (x : Indexed C) :
    (indexedPair C x).words ∈ C := x.1.property

theorem indexedPair_covers {C : Finset WordPair} (m : MarkedPair)
    (hm : m.words ∈ C) : ∃ x : Indexed C, indexedPair C x = m := by
  refine ⟨⟨⟨m.words, hm⟩, markIndex m.top, markIndex m.bottom⟩, ?_⟩
  cases m
  simp [indexedPair, markAt_markIndex]

/-- Actual marked members, before projecting to packet labels. -/
noncomputable def markedSupport (C : Finset WordPair) : Finset MarkedPair := by
  classical
  exact Finset.univ.image (indexedPair C)

theorem mem_markedSupport {C : Finset WordPair} {m : MarkedPair} :
    m ∈ markedSupport C ↔ m.words ∈ C := by
  classical
  constructor
  · intro hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
    exact indexedPair_mem C x
  · intro hm
    obtain ⟨x, rfl⟩ := indexedPair_covers m hm
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

/-- The exact packet image of all actual marks in the supplied carrier. -/
noncomputable def packetSupport (C : Finset WordPair) : Finset Packet := by
  classical
  exact (markedSupport C).image MarkedPair.packet

theorem mem_packetSupport {C : Finset WordPair} {p : Packet} :
    p ∈ packetSupport C ↔ ∃ m : MarkedPair, m.words ∈ C ∧ m.packet = p := by
  classical
  simp only [packetSupport, Finset.mem_image, mem_markedSupport]

theorem indexed_card (C : Finset WordPair) :
    Fintype.card (Indexed C) = ∑ T ∈ C, T.1.length * T.2.length := by
  classical
  simp only [Indexed, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  exact Finset.sum_coe_sort C (fun T : WordPair => T.1.length * T.2.length)

theorem markedSupport_card_le (C : Finset WordPair) :
    (markedSupport C).card ≤ ∑ T ∈ C, T.1.length * T.2.length := by
  classical
  calc
    (markedSupport C).card ≤ (Finset.univ : Finset (Indexed C)).card :=
      Finset.card_image_le
    _ = _ := by rw [Finset.card_univ, indexed_card]

theorem packetSupport_card_le (C : Finset WordPair) :
    (packetSupport C).card ≤ ∑ T ∈ C, T.1.length * T.2.length := by
  classical
  exact Finset.card_image_le.trans (markedSupport_card_le C)

/-- Geometric interiors are filtered using the actual positive-length
predicate; this is not the production packet's left-boundary flag. -/
noncomputable def interiorSupport (C : Finset WordPair) (ℓ : Fin 3 → ℝ) :
    Finset Packet := by
  classical
  exact (packetSupport C).filter (Packet.Interior ℓ)

theorem mem_interiorSupport {C : Finset WordPair} {ℓ : Fin 3 → ℝ} {p : Packet} :
    p ∈ interiorSupport C ℓ ↔
      (∃ m : MarkedPair, m.words ∈ C ∧ m.packet = p) ∧ p.Interior ℓ := by
  classical
  simp only [interiorSupport, Finset.mem_filter, mem_packetSupport]

theorem interiorSupport_card_le (C : Finset WordPair) (ℓ : Fin 3 → ℝ) :
    (interiorSupport C ℓ).card ≤ ∑ T ∈ C, T.1.length * T.2.length := by
  classical
  exact (Finset.card_filter_le _ _).trans (packetSupport_card_le C)

/-- The finite actual marked carrier used for recurrence.  It retains both
full words and both marks, before taking any packet-label quotient. -/
noncomputable def interiorMarkedSupport (C : Finset WordPair) (ℓ : Fin 3 → ℝ) :
    Finset MarkedPair := by
  classical
  exact (markedSupport C).filter (fun m => m.packet.Interior ℓ)

theorem mem_interiorMarkedSupport {C : Finset WordPair} {ℓ : Fin 3 → ℝ}
    {m : MarkedPair} : m ∈ interiorMarkedSupport C ℓ ↔
      m.words ∈ C ∧ m.packet.Interior ℓ := by
  classical
  simp only [interiorMarkedSupport, Finset.mem_filter, mem_markedSupport]

theorem interiorMarkedSupport_card_le (C : Finset WordPair) (ℓ : Fin 3 → ℝ) :
    (interiorMarkedSupport C ℓ).card ≤ ∑ T ∈ C, T.1.length * T.2.length := by
  classical
  exact (Finset.card_filter_le _ _).trans (markedSupport_card_le C)

/-- The two first letters of nonempty words have a common interior because
both literal prefix addresses are zero. -/
theorem first_marks_interior (T : WordPair) (ht : T.1 ≠ []) (hb : T.2 ≠ [])
    (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a) :
    ∃ m : MarkedPair, m.words = T ∧ m.packet.Interior ℓ := by
  let i : Fin T.1.length :=
    ⟨0, Nat.pos_of_ne_zero (fun h => ht (List.length_eq_zero_iff.mp h))⟩
  let j : Fin T.2.length :=
    ⟨0, Nat.pos_of_ne_zero (fun h => hb (List.length_eq_zero_iff.mp h))⟩
  let m : MarkedPair := ⟨T, markAt T.1 i, markAt T.2 j⟩
  refine ⟨m, rfl, (Packet.interior_iff_bounds ℓ hpos m.packet).mpr ?_⟩
  have hz : offset ℓ m.packet.delta = 0 := by
    simp [m, i, j, markAt, MarkedPair.packet, OccurrenceTransport.residual,
      offset, dotProduct]
  rw [hz]
  exact ⟨neg_neg_of_pos (hpos _), hpos _⟩

theorem interiorMarkedSupport_nonempty {C : Finset WordPair}
    (hC : ∃ T ∈ C, T.1 ≠ [] ∧ T.2 ≠ []) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) : (interiorMarkedSupport C ℓ).Nonempty := by
  obtain ⟨T, hT, ht, hb⟩ := hC
  obtain ⟨m, hm, hi⟩ := first_marks_interior T ht hb ℓ hpos
  exact ⟨m, mem_interiorMarkedSupport.mpr ⟨by simpa only [hm] using hT, hi⟩⟩

theorem interiorSupport_nonempty {C : Finset WordPair}
    (hC : ∃ T ∈ C, T.1 ≠ [] ∧ T.2 ≠ []) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) : (interiorSupport C ℓ).Nonempty := by
  obtain ⟨m, hm⟩ := interiorMarkedSupport_nonempty hC ℓ hpos
  obtain ⟨hmem, hi⟩ := mem_interiorMarkedSupport.mp hm
  exact ⟨m.packet, mem_interiorSupport.mpr ⟨⟨m, hmem, rfl⟩, hi⟩⟩

end Psc.OccurrenceFinite
