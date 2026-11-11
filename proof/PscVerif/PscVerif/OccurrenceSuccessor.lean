/-
# Interior successors from exact length scaling

A positive length row with exact substitution scaling makes every strictly
interior packet admit an actual digit successor.  The proof avoids the finite
set of image-prefix boundaries before selecting the two digit occurrences.

This is a seriality statement for the literal packet relation.  It does not
assert a route to a diagonal packet, uniqueness of the selected route, or a
shared legal limit for two occurrence histories.

Literature stop/go: `docs/c4-finite-carrier-dual-literature-2026-11-10.md`.
Derivation and scope: `docs/c4-interior-successors-2026-11-10.md`.
-/
import PscVerif.OccurrenceTransport

namespace Psc.OccurrenceSuccessor

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn
open Psc.OccurrenceTransport Matrix
open scoped BigOperators

/-- Exact image-length scaling acts on every integral packet displacement,
including displacements that are not assumed to have a word realization. -/
theorem offset_incidence (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (r : Fin 3 → ℤ) :
    offset ℓ (incidenceZ s *ᵥ r) = β * offset ℓ r := by
  calc
    offset ℓ (incidenceZ s *ᵥ r) =
        ∑ b, (∑ a, ℓ a * (incidenceZ s a b : ℝ)) * (r b : ℝ) := by
      simp only [offset, Matrix.mulVec, dotProduct, Int.cast_sum,
        Int.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = ∑ b, (β * ℓ b) * (r b : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hrow : (∑ a, ℓ a * (incidenceZ s a b : ℝ)) = β * ℓ b := by
        simpa [physicalLength, dotProduct, incidenceZ, inc] using hscale b
      rw [hrow]
    _ = β * offset ℓ r := by
      simp [offset, dotProduct, Finset.mul_sum, mul_assoc]

theorem offset_add (ℓ : Fin 3 → ℝ) (r t : Fin 3 → ℤ) :
    offset ℓ (r + t) = offset ℓ r + offset ℓ t := by
  simp [offset, dotProduct, mul_add, Finset.sum_add_distrib]

/-- The physical displacement of an actual digit pair is the scaled parent
displacement plus the difference of the two literal image-prefix lengths. -/
theorem offset_affine (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (r : Fin 3 → ℤ) (u v : Word) :
    offset ℓ (incidenceZ s *ᵥ r + residual u v) =
      β * offset ℓ r + physicalLength ℓ u - physicalLength ℓ v := by
  rw [offset_add, offset_incidence s ℓ β hscale, offset_residual]
  ring

/-- Every point strictly between the word endpoints and away from all
prefix boundaries lies in the strict interior of an actual selected letter.
The selected prefix and suffix retain its literal occurrence address. -/
theorem exists_mark_containing (ℓ : Fin 3 → ℝ) (w : Word) (x : ℝ)
    (hx0 : 0 < x) (hxend : x < physicalLength ℓ w)
    (hcut : ∀ i ≤ w.length, x ≠ physicalLength ℓ (w.take i)) :
    ∃ m : Mark w, physicalLength ℓ m.before < x ∧
      x < physicalLength ℓ m.before + ℓ m.letter := by
  induction w generalizing x with
  | nil =>
    simp only [physicalLength_nil] at hxend
    linarith
  | cons a w ih =>
    by_cases hxa : x < ℓ a
    · exact ⟨⟨[], a, w, rfl⟩, by simpa using hx0, by simpa using hxa⟩
    · have hxne : x ≠ ℓ a := by
        simpa using hcut 1 (by simp)
      have hax : ℓ a < x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm hxne)
      have hxsub0 : 0 < x - ℓ a := sub_pos.mpr hax
      have hxsubend : x - ℓ a < physicalLength ℓ w := by
        rw [physicalLength_cons] at hxend
        linarith
      have hsubcut : ∀ i ≤ w.length,
          x - ℓ a ≠ physicalLength ℓ (w.take i) := by
        intro i hi heq
        have hn := hcut (i + 1) (by simpa using Nat.succ_le_succ hi)
        apply hn
        simp only [List.take_succ_cons, physicalLength_cons]
        linarith
      obtain ⟨m, hmlo, hmhi⟩ := ih (x - ℓ a) hxsub0 hxsubend hsubcut
      let lifted : Mark (a :: w) :=
        ⟨a :: m.before, m.letter, m.after, by simpa using congrArg (List.cons a) m.split⟩
      refine ⟨lifted, ?_, ?_⟩ <;>
        dsimp [lifted] <;> rw [physicalLength_cons] <;> linarith

/-- A finite collection of boundary points cannot exhaust a nonempty real
open interval.  No interval endpoint is admitted by this choice. -/
theorem exists_between_avoiding (F : Finset ℝ) (a b : ℝ) (hab : a < b) :
    ∃ x, a < x ∧ x < b ∧ x ∉ F := by
  classical
  induction F using Finset.induction_on generalizing a b with
  | empty =>
    obtain ⟨x, hax, hxb⟩ := exists_between hab
    exact ⟨x, hax, hxb, by simp⟩
  | @insert c F hc ih =>
    obtain ⟨x, hax, hxb, hxF⟩ := ih a b hab
    by_cases hxc : x = c
    · obtain ⟨y, hay, hyx, hyF⟩ := ih a x hax
      have hyc : y ≠ c := by intro heq; linarith
      exact ⟨y, hay, hyx.trans hxb, by simp [hyc, hyF]⟩
    · exact ⟨x, hax, hxb, by simp [hxc, hxF]⟩

/-- All physical prefix boundaries, including both endpoints, of a finite
word.  Repeated boundary values are harmless for the avoidance argument. -/
noncomputable def prefixCuts (ℓ : Fin 3 → ℝ) (w : Word) : Finset ℝ := by
  classical
  exact (Finset.range (w.length + 1)).image (fun i => physicalLength ℓ (w.take i))

theorem mem_prefixCuts (ℓ : Fin 3 → ℝ) (w : Word) (i : ℕ) (hi : i ≤ w.length) :
    physicalLength ℓ (w.take i) ∈ prefixCuts ℓ w := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

/-- Every strict interior packet has a strict interior successor selected
from actual positions of the two substitution images.  Exact length scaling
is essential; positivity of lengths alone does not imply this statement. -/
theorem interiorStep_exists (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (p : Packet) (hp : p.Interior ℓ) :
    ∃ q, InteriorStep s ℓ p q := by
  classical
  have hbounds := (Packet.interior_iff_bounds ℓ hpos p).mp hp
  have hleft := mul_lt_mul_of_pos_left hbounds.1 hβ
  have hright := mul_lt_mul_of_pos_left hbounds.2 hβ
  have htpos := mul_pos hβ (hpos p.top)
  have hbpos := mul_pos hβ (hpos p.bottom)
  have hopen : max 0 (-(β * offset ℓ p.delta)) <
      min (β * ℓ p.top) (β * ℓ p.bottom - β * offset ℓ p.delta) := by
    rw [max_lt_iff]
    constructor <;> rw [lt_min_iff] <;> constructor <;> linarith
  let bottomCuts := (prefixCuts ℓ (s p.bottom)).image
    (fun z => z - β * offset ℓ p.delta)
  obtain ⟨x, hxlo, hxhi, hxavoid⟩ :=
    exists_between_avoiding (prefixCuts ℓ (s p.top) ∪ bottomCuts)
      _ _ hopen
  have hx0 : 0 < x := lt_of_le_of_lt (le_max_left _ _) hxlo
  have hxtop : x < physicalLength ℓ (s p.top) := by
    rw [hscale]
    exact lt_of_lt_of_le hxhi (min_le_left _ _)
  have hxb0 : 0 < x + β * offset ℓ p.delta := by
    have := lt_of_le_of_lt (le_max_right _ _) hxlo
    linarith
  have hxbend : x + β * offset ℓ p.delta < physicalLength ℓ (s p.bottom) := by
    rw [hscale]
    have := lt_of_lt_of_le hxhi (min_le_right _ _)
    linarith
  have htopcut : ∀ i ≤ (s p.top).length,
      x ≠ physicalLength ℓ ((s p.top).take i) := by
    intro i hi heq
    apply hxavoid
    apply Finset.mem_union.mpr
    left
    rw [heq]
    exact mem_prefixCuts ℓ (s p.top) i hi
  have hbottomcut : ∀ i ≤ (s p.bottom).length,
      x + β * offset ℓ p.delta ≠ physicalLength ℓ ((s p.bottom).take i) := by
    intro i hi heq
    apply hxavoid
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr
      ⟨physicalLength ℓ ((s p.bottom).take i),
        mem_prefixCuts ℓ (s p.bottom) i hi, by linarith⟩
  obtain ⟨dt, htlo, hthi⟩ := exists_mark_containing ℓ (s p.top) x hx0 hxtop htopcut
  obtain ⟨db, hblo, hbhi⟩ := exists_mark_containing ℓ (s p.bottom)
    (x + β * offset ℓ p.delta) hxb0 hxbend hbottomcut
  let q : Packet := ⟨dt.letter, db.letter,
    incidenceZ s *ᵥ p.delta + residual dt.before db.before⟩
  refine ⟨q, ⟨⟨dt, db, rfl⟩, ?_⟩⟩
  change ∃ y, 0 < y ∧ y < ℓ dt.letter ∧
    0 < y + offset ℓ (incidenceZ s *ᵥ p.delta + residual dt.before db.before) ∧
    y + offset ℓ (incidenceZ s *ᵥ p.delta + residual dt.before db.before) < ℓ db.letter
  refine ⟨x - physicalLength ℓ dt.before, by linarith, by linarith, ?_, ?_⟩ <;>
    rw [offset_affine s ℓ β hscale] <;> linarith

end Psc.OccurrenceSuccessor
