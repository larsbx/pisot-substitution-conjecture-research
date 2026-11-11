/-
# Ordered overlap subdivision

The length of a physical packet overlap is conserved by its complete ordered
family of actual digit pairs, with the exact inflation scale.  Position indices
retain repeated packet labels.  Boundary touching contributes zero length.

The proof is elementary finite interval subdivision; no tiling realization,
balanced carrier, Pisot hypothesis, or strict loss is assumed or concluded.
Pre-code review: `docs/c4-overlap-mass-literature-2026-11-10.md`.
-/
import PscVerif.OccurrenceFinite
import PscVerif.OccurrenceSuccessor
import Mathlib.Algebra.BigOperators.Fin

namespace Psc.OccurrenceMass

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceSuccessor Matrix
open scoped BigOperators

/-- Length of the intersection of two ordered real intervals.  Degenerate
or disjoint intervals have zero length. -/
noncomputable def intervalMass (a b c d : ℝ) : ℝ :=
  max 0 (min b d - max a c)

theorem intervalMass_nonneg (a b c d : ℝ) : 0 ≤ intervalMass a b c d :=
  le_max_left _ _

theorem intervalMass_swap (a b c d : ℝ) :
    intervalMass a b c d = intervalMass c d a b := by
  simp only [intervalMass, min_comm, max_comm]

theorem intervalMass_same_endpoint (a b c : ℝ) : intervalMass a b c c = 0 := by
  apply max_eq_left
  exact sub_nonpos.mpr ((min_le_right b c).trans (le_max_right a c))

/-- Clipping the endpoints of the first interval to the second gives its
intersection length.  This identity makes subdivision telescope. -/
theorem intervalMass_eq_clip (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    intervalMass a b c d = min (max b c) d - min (max a c) d := by
  by_cases hbc : b ≤ c
  · simp [intervalMass, max_eq_right (hab.trans hbc), max_eq_right hbc,
      min_eq_left (hbc.trans hcd), min_eq_left hcd,
      max_eq_left (sub_nonpos.mpr hbc)]
  · have hcb : c ≤ b := (lt_of_not_ge hbc).le
    by_cases hda : d ≤ a
    · simp [intervalMass, min_eq_right (hda.trans hab),
        max_eq_left (hcd.trans hda), max_eq_left hcb,
        min_eq_right hda, max_eq_left (sub_nonpos.mpr hda)]
    · have had : a ≤ d := (lt_of_not_ge hda).le
      by_cases hac : a ≤ c
      · by_cases hbd : b ≤ d
        · simp [intervalMass, min_eq_left hbd, max_eq_right hac,
            max_eq_left hcb, min_eq_left hcd,
            max_eq_right (sub_nonneg.mpr hcb)]
        · have hdb : d ≤ b := (lt_of_not_ge hbd).le
          simp [intervalMass, min_eq_right hdb, max_eq_right hac,
            max_eq_left hcb, min_eq_left hcd,
            max_eq_right (sub_nonneg.mpr hcd)]
      · have hca : c ≤ a := (lt_of_not_ge hac).le
        by_cases hbd : b ≤ d
        · simp [intervalMass, min_eq_left hbd, max_eq_left hca,
            max_eq_left hcb, min_eq_left had,
            max_eq_right (sub_nonneg.mpr hab)]
        · have hdb : d ≤ b := (lt_of_not_ge hbd).le
          simp [intervalMass, min_eq_right hdb, max_eq_left hca,
            max_eq_left hcb, min_eq_left had,
            max_eq_right (sub_nonneg.mpr had)]

/-- Split the first interval at a genuine intermediate endpoint.  The
common endpoint itself contributes no extra mass. -/
theorem intervalMass_split (a b c d e : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hde : d ≤ e) :
    intervalMass a b d e + intervalMass b c d e = intervalMass a c d e := by
  rw [intervalMass_eq_clip a b d e hab hde,
    intervalMass_eq_clip b c d e hbc hde,
    intervalMass_eq_clip a c d e (hab.trans hbc) hde]
  ring

theorem intervalMass_split_right (a b c d e : ℝ) (hab : a ≤ b)
    (hcd : c ≤ d) (hde : d ≤ e) :
    intervalMass a b c d + intervalMass a b d e = intervalMass a b c e := by
  simpa only [intervalMass_swap a b] using intervalMass_split c d e a b hcd hde hab

theorem intervalMass_translate (a b c d t : ℝ) :
    intervalMass (a + t) (b + t) (c + t) (d + t) = intervalMass a b c d := by
  simp [intervalMass, min_add_add_right, max_add_add_right]

theorem intervalMass_scale (a b c d β : ℝ) (hβ : 0 ≤ β) :
    intervalMass (β * a) (β * b) (β * c) (β * d) = β * intervalMass a b c d := by
  simp only [intervalMass, ← mul_min_of_nonneg b d hβ,
    ← mul_max_of_nonneg a c hβ, ← mul_sub]
  simpa only [mul_zero] using (mul_max_of_nonneg 0 (min b d - max a c) hβ).symm

/-- Sum over every actual position in a word, using its literal prefix
length.  Zero letter lengths and the empty word are allowed. -/
theorem sum_intervalMass_word (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 ≤ ℓ a)
    (w : Word) (a b c : ℝ) (hab : a ≤ b) :
    (∑ i : Fin w.length,
      intervalMass a b (c + physicalLength ℓ (w.take i))
        (c + physicalLength ℓ (w.take i) + ℓ w[i.val])) =
      intervalMass a b c (c + physicalLength ℓ w) := by
  induction w generalizing c with
  | nil => simp [intervalMass_same_endpoint]
  | cons x w ih =>
    calc
      _ = intervalMass a b c (c + ℓ x) +
          ∑ i : Fin w.length,
            intervalMass a b (c + ℓ x + physicalLength ℓ (w.take i))
              (c + ℓ x + physicalLength ℓ (w.take i) + ℓ w[i.val]) := by
        simp [Fin.sum_univ_succ, List.take_succ_cons, add_assoc]
      _ = intervalMass a b c (c + ℓ x) +
          intervalMass a b (c + ℓ x) (c + ℓ x + physicalLength ℓ w) := by
        rw [ih]
      _ = _ := by
        rw [physicalLength_cons, ← add_assoc]
        exact intervalMass_split_right a b c (c + ℓ x)
          (c + ℓ x + physicalLength ℓ w) hab
          (le_add_of_nonneg_right (hℓ x))
          (le_add_of_nonneg_right (physicalLength_nonneg ℓ hℓ w))

/-- Refine both intervals using their complete ordered words. -/
theorem sum_intervalMass_words (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 ≤ ℓ a)
    (u v : Word) (a b : ℝ) :
    (∑ i : Fin u.length, ∑ j : Fin v.length,
      intervalMass (a + physicalLength ℓ (u.take i))
        (a + physicalLength ℓ (u.take i) + ℓ u[i.val])
        (b + physicalLength ℓ (v.take j))
        (b + physicalLength ℓ (v.take j) + ℓ v[j.val])) =
      intervalMass a (a + physicalLength ℓ u) b (b + physicalLength ℓ v) := by
  calc
    _ = ∑ i : Fin u.length,
        intervalMass (a + physicalLength ℓ (u.take i))
          (a + physicalLength ℓ (u.take i) + ℓ u[i.val])
          b (b + physicalLength ℓ v) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_intervalMass_word ℓ hℓ v _ _ b (le_add_of_nonneg_right (hℓ _))
    _ = _ := by
      simp_rw [intervalMass_swap _ _ b]
      exact sum_intervalMass_word ℓ hℓ u _ _ a
        (le_add_of_nonneg_right (physicalLength_nonneg ℓ hℓ v))

/-- The physical overlap length in the existing top-minus-bottom convention. -/
noncomputable def packetMass (ℓ : Fin 3 → ℝ) (p : Packet) : ℝ :=
  intervalMass 0 (ℓ p.top) (-offset ℓ p.delta) (ℓ p.bottom - offset ℓ p.delta)

theorem packetMass_nonneg (ℓ : Fin 3 → ℝ) (p : Packet) : 0 ≤ packetMass ℓ p :=
  intervalMass_nonneg _ _ _ _

theorem packetMass_pos_iff_interior (ℓ : Fin 3 → ℝ) (p : Packet) :
    0 < packetMass ℓ p ↔ p.Interior ℓ := by
  change 0 < max 0 (min (ℓ p.top) (ℓ p.bottom - offset ℓ p.delta) -
    max 0 (-offset ℓ p.delta)) ↔ _
  rw [lt_max_iff]
  simp only [lt_self_iff_false, false_or, sub_pos]
  constructor
  · intro h
    obtain ⟨x, hxlo, hxhi⟩ := exists_between h
    refine ⟨x, (max_lt_iff.mp hxlo).1, (lt_min_iff.mp hxhi).1, ?_, ?_⟩
    · have := (max_lt_iff.mp hxlo).2
      linarith
    · have := (lt_min_iff.mp hxhi).2
      linarith
  · rintro ⟨x, hx0, hxt, hxb0, hxb⟩
    have hlo : max 0 (-offset ℓ p.delta) < x := by
      rw [max_lt_iff]
      constructor <;> linarith
    have hhi : x < min (ℓ p.top) (ℓ p.bottom - offset ℓ p.delta) := by
      rw [lt_min_iff]
      constructor <;> linarith
    exact hlo.trans hhi

theorem packetMass_eq_zero_iff_not_interior (ℓ : Fin 3 → ℝ) (p : Packet) :
    packetMass ℓ p = 0 ↔ ¬ p.Interior ℓ := by
  constructor
  · intro hz hi
    have hp := (packetMass_pos_iff_interior ℓ p).mpr hi
    linarith
  · intro hn
    apply le_antisymm _ (packetMass_nonneg ℓ p)
    exact le_of_not_gt (fun h => hn ((packetMass_pos_iff_interior ℓ p).mp h))

/-- Swapping both physical tracks preserves overlap length, including the
zero-mass boundary cases. -/
theorem packetMass_swap (ℓ : Fin 3 → ℝ) (p : Packet) :
    packetMass ℓ p.swap = packetMass ℓ p := by
  simp only [packetMass, Packet.swap, offset_neg, neg_neg]
  convert (intervalMass_translate (-offset ℓ p.delta)
    (ℓ p.bottom - offset ℓ p.delta) 0 (ℓ p.top) (offset ℓ p.delta)).trans
      (intervalMass_swap (-offset ℓ p.delta)
        (ℓ p.bottom - offset ℓ p.delta) 0 (ℓ p.top)) using 1
  congr 1 <;> ring

/-- The actual digit pair selected by its two independent position indices. -/
def digitPacket (s : Fin 3 → Word) (p : Packet)
    (i : Fin (s p.top).length) (j : Fin (s p.bottom).length) : Packet :=
  let dt := markAt (s p.top) i
  let db := markAt (s p.bottom) j
  ⟨dt.letter, db.letter, incidenceZ s *ᵥ p.delta + residual dt.before db.before⟩

theorem digitPacket_digitStep (s : Fin 3 → Word) (p : Packet)
    (i : Fin (s p.top).length) (j : Fin (s p.bottom).length) :
    DigitStep s p (digitPacket s p i j) :=
  ⟨markAt (s p.top) i, markAt (s p.bottom) j, rfl⟩

theorem digitPacket_mass (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (p : Packet) (i : Fin (s p.top).length) (j : Fin (s p.bottom).length) :
    packetMass ℓ (digitPacket s p i j) =
      intervalMass (physicalLength ℓ ((s p.top).take i))
        (physicalLength ℓ ((s p.top).take i) + ℓ (s p.top)[i.val])
        (-β * offset ℓ p.delta + physicalLength ℓ ((s p.bottom).take j))
        (-β * offset ℓ p.delta + physicalLength ℓ ((s p.bottom).take j) +
          ℓ (s p.bottom)[j.val]) := by
  simp only [packetMass, digitPacket, markAt, offset_affine s ℓ β hscale]
  convert (intervalMass_translate 0 (ℓ (s p.top)[i.val])
    (-(β * offset ℓ p.delta + physicalLength ℓ ((s p.top).take i) -
      physicalLength ℓ ((s p.bottom).take j)))
    (ℓ (s p.bottom)[j.val] -
      (β * offset ℓ p.delta + physicalLength ℓ ((s p.top).take i) -
        physicalLength ℓ ((s p.bottom).take j)))
    (physicalLength ℓ ((s p.top).take i))).symm using 1
  congr 1 <;> ring

/-- Exact conservation over all ordered image digit pairs.  Repeated packet
labels contribute once for each actual pair of digit positions. -/
theorem sum_digitPacket_mass (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hℓ : ∀ a, 0 ≤ ℓ a) (hβ : 0 ≤ β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) (p : Packet) :
    (∑ i : Fin (s p.top).length, ∑ j : Fin (s p.bottom).length,
      packetMass ℓ (digitPacket s p i j)) = β * packetMass ℓ p := by
  simp_rw [digitPacket_mass s ℓ β hscale]
  have h := sum_intervalMass_words ℓ hℓ (s p.top) (s p.bottom)
    0 (-β * offset ℓ p.delta)
  simp only [zero_add] at h
  rw [h, hscale, hscale]
  unfold packetMass
  convert intervalMass_scale 0 (ℓ p.top) (-offset ℓ p.delta)
    (ℓ p.bottom - offset ℓ p.delta) β hβ using 1
  congr 1 <;> ring

end Psc.OccurrenceMass
