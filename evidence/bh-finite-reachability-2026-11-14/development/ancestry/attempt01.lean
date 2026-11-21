/-
# Actual parent occurrences for strict interior packets

Literal mark decomposition and exact physical scaling pull a child overlap
back to its parent. Seed coverage and complete InteriorStep closure therefore
cover every actual iterate. No abstract realization premise is inserted.

Stop/go: docs/bh-finite-reachability-stop-go-2026-11-14.md.
-/
import PscVerif.OccurrenceSuccessor

namespace Psc.OccurrenceAncestry

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport

private theorem mark_drop {w : Word} (m : Mark w) :
    w.drop (m.index + 1) = m.after := by
  simpa [Mark.index, List.drop_append] using congrArg (List.drop (m.index + 1)) m.split

theorem mark_eq_of_index {w : Word} (m n : Mark w) (h : m.index = n.index) : m = n := by
  have hb : m.before = n.before := by rw [← m.take_index, ← n.take_index, h]
  have hl : m.letter = n.letter := by rw [← m.selected, ← n.selected, h]
  have ha : m.after = n.after := by rw [← mark_drop m, ← mark_drop n, h]
  cases m
  cases n
  cases hb
  cases hl
  cases ha
  rfl

private def markAt (w : Word) (i : ℕ) (hi : i < w.length) : Mark w where
  before := w.take i
  letter := w[i]
  after := w.drop (i + 1)
  split := by
    rw [← List.drop_eq_getElem_cons hi]
    exact (List.take_append_drop i w).symm

private theorem markAt_index (w : Word) (i : ℕ) (hi : i < w.length) :
    (markAt w i hi).index = i := by
  simp [markAt, Mark.index, Nat.min_eq_left (Nat.le_of_lt hi)]

/-- Every selected letter in an actual substituted word belongs to an actual
source letter and an actual digit in its image, including for erasing maps. -/
theorem mark_uninflate (s : Fin 3 → Word) (w : Word) (child : Mark (subst s w)) :
    ∃ (parent : Mark w) (digit : Mark (s parent.letter)), parent.inflate s digit = child := by
  induction w with
  | nil =>
    have h := child.index_lt
    simp [subst] at h
  | cons a w ih =>
    by_cases hfirst : child.index < (s a).length
    · let parent : Mark (a :: w) := ⟨[], a, w, rfl⟩
      let digit : Mark (s a) := markAt (s a) child.index hfirst
      refine ⟨parent, digit, mark_eq_of_index _ _ ?_⟩
      simp [parent, digit, Mark.inflate, Mark.index, markAt,
        Nat.min_eq_left (Nat.le_of_lt hfirst), subst]
    · have hrest : child.index - (s a).length < (subst s w).length := by
        have h := child.index_lt
        rw [subst_cons, List.length_append] at h
        omega
      let rest : Mark (subst s w) := markAt (subst s w) (child.index - (s a).length) hrest
      obtain ⟨parent, digit, hpd⟩ := ih rest
      let lifted : Mark (a :: w) :=
        ⟨a :: parent.before, parent.letter, parent.after,
          by simpa using congrArg (List.cons a) parent.split⟩
      refine ⟨lifted, digit, mark_eq_of_index _ _ ?_⟩
      have hind : (parent.inflate s digit).index = child.index - (s a).length := by
        rw [hpd]
        exact markAt_index _ _ _
      change (subst s (a :: parent.before) ++ digit.before).length = child.index
      simp only [subst_cons, List.length_append]
      change (s a).length + (subst s parent.before).length + digit.before.length = child.index
      change (subst s parent.before ++ digit.before).length = child.index - (s a).length at hind
      simp only [List.length_append] at hind
      omega

private theorem physicalLength_subst (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (w : Word) :
    physicalLength ℓ (subst s w) = β * physicalLength ℓ w := by
  induction w with
  | nil => simp [subst]
  | cons a w ih => simp only [subst_cons, physicalLength_append, physicalLength_cons, hscale, ih]; ring

private theorem inflate_interval_bounds (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    {w : Word} (m : Mark w) (d : Mark (s m.letter)) :
    β * physicalLength ℓ m.before ≤ physicalLength ℓ (m.inflate s d).before ∧
    physicalLength ℓ (m.inflate s d).before + ℓ (m.inflate s d).letter ≤
      β * (physicalLength ℓ m.before + ℓ m.letter) := by
  have hbefore := physicalLength_nonneg ℓ (fun a => (hpos a).le) d.before
  have hafter := physicalLength_nonneg ℓ (fun a => (hpos a).le) d.after
  have hd : physicalLength ℓ d.before + ℓ d.letter + physicalLength ℓ d.after = β * ℓ m.letter := by
    have h := congrArg (physicalLength ℓ) d.split
    rw [hscale, physicalLength_append, physicalLength_cons] at h
    linarith
  simp only [Mark.inflate, physicalLength_append, physicalLength_subst s ℓ β hscale]
  constructor <;> nlinarith

/-- A strict overlap of actual child occurrences has a strict actual parent
overlap and the literal affine digit edge between their packets. -/
theorem overlapping_parent (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (u v : Word) (top : Mark (subst s u)) (bottom : Mark (subst s v))
    (hov : (MarkedPair.mk (subst s u, subst s v) top bottom).Overlaps ℓ) :
    ∃ (pt : Mark u) (pb : Mark v),
      (MarkedPair.mk (u, v) pt pb).Overlaps ℓ ∧
      InteriorStep s ℓ (MarkedPair.mk (u, v) pt pb).packet
        (MarkedPair.mk (subst s u, subst s v) top bottom).packet := by
  obtain ⟨pt, dt, rfl⟩ := mark_uninflate s u top
  obtain ⟨pb, db, rfl⟩ := mark_uninflate s v bottom
  have ht := inflate_interval_bounds s ℓ β hpos hscale pt dt
  have hb := inflate_interval_bounds s ℓ β hpos hscale pb db
  refine ⟨pt, pb, ?_, ?_⟩
  · obtain ⟨x, hxt, htx, hxb, hbx⟩ := hov
    refine ⟨x / β, ?_, ?_, ?_, ?_⟩
    · apply (lt_div_iff₀ hβ).2
      nlinarith [ht.1]
    · apply (div_lt_iff₀ hβ).2
      nlinarith [ht.2]
    · apply (lt_div_iff₀ hβ).2
      nlinarith [hb.1]
    · apply (div_lt_iff₀ hβ).2
      nlinarith [hb.2]
  · exact ⟨(MarkedPair.mk (u, v) pt pb).inflate_digitStep s dt db,
      (MarkedPair.overlaps_iff ℓ _).1 hov⟩

/-- Coverage of actual strict overlaps in a specified pair of words. -/
def CoversWords (ℓ : Fin 3 → ℝ) (T : WordPair) (C : Set Packet) : Prop :=
  ∀ (top : Mark T.1) (bottom : Mark T.2),
    (MarkedPair.mk T top bottom).Overlaps ℓ → (MarkedPair.mk T top bottom).packet ∈ C

/-- Seed occurrence coverage plus closure under every literal interior edge
implies occurrence coverage at every substitution generation. -/
theorem covers_iterates_of_closed (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (T : WordPair) (C : Set Packet) (hseed : CoversWords ℓ T C)
    (hclosed : ∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) :
    ∀ n, CoversWords ℓ (((subst s)^[n] T.1), ((subst s)^[n] T.2)) C := by
  intro n
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    intro top bottom hov
    obtain ⟨pt, pb, hp, hedge⟩ :=
      overlapping_parent s ℓ β hpos hβ hscale _ _ top bottom hov
    exact hclosed _ (ih pt pb hp) _ hedge

end Psc.OccurrenceAncestry
