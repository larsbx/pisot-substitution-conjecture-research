import PscVerif.ClassAMinusPrefixAssembly
import PscVerif.OccurrenceAncestry
import PscVerif.BHNearDiagonalLiteral
import PscVerif.OccurrenceMass

/-!
# From original iterated-image marks to strict indexed packet paths

Every pair of original depth-n marks decomposes into n genuine local digit
pairs. The terminal packet keeps the entire integral affine displacement.
Strictness of that terminal packet then pulls back along the same ordered
transcript. The run-window specialization consumes the actual positioned
marks furnished by the third-level geometry.
-/

namespace Psc.BHThirdLevelTransport

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.OccurrenceSuccessor Psc.OccurrenceAncestry
open Psc.ClassAMinusPrefixAssembly Psc.BHNearDiagonalLiteral Matrix
open Psc.OccurrenceMass

/-- Uninflation preserves the exact original mark, including its complete
prefix and suffix, at each depth. -/
theorem image_mark_uninflate (s : Fin 3 → Word) (n : ℕ) (a : Fin 3)
    (child : Mark (image s (n+1) a)) :
    ∃ (parent : Mark (image s n a)) (digit : Mark (s parent.letter)),
      inflateImageMark s parent digit = child := by
  let child' : Mark (subst s (image s n a)) :=
    ⟨child.before, child.letter, child.after, by rw [← image_succ]; exact child.split⟩
  obtain ⟨parent, digit, he⟩ := mark_uninflate s (image s n a) child'
  refine ⟨parent, digit, mark_eq_of_index _ _ ?_⟩
  have hi := congrArg Mark.index he
  exact hi

/-- Reverse assembly: any pair of original depth-n marks gives an actual
n-edge ordinal transcript with the full prescribed affine endpoint. -/
theorem assembled_has_ordered_path (s : Fin 3 → Word) (p : Packet) (n : ℕ)
    (top : Mark (image s n p.top)) (bottom : Mark (image s n p.bottom)) :
    ∃ xs : List (ℕ × ℕ), xs.length = n ∧
      OrderedPath s p xs (assembledPacket s p n top bottom) := by
  induction n with
  | zero =>
    obtain ⟨ht, htl, _⟩ := singleton_mark p.top top
    obtain ⟨hb, hbl, _⟩ := singleton_mark p.bottom bottom
    refine ⟨[], rfl, ?_⟩
    simpa [assembledPacket, ht, hb, htl, hbl, OccurrenceTransport.residual]
      using OrderedPath.nil (s := s) p
  | succ n ih =>
    obtain ⟨pt, dt, htop⟩ := image_mark_uninflate s n p.top top
    obtain ⟨pb, db, hbottom⟩ := image_mark_uninflate s n p.bottom bottom
    rw [← htop, ← hbottom]
    obtain ⟨xs, hlen, hpath⟩ := ih pt pb
    refine ⟨xs ++ [(dt.index, db.index)], by simp [hlen],
      .snoc hpath dt.index db.index ?_⟩
    refine ⟨dt, db, rfl, rfl, ?_⟩
    apply congrArg (Packet.mk dt.letter db.letter)
    change incidenceZ s ^ (n+1) *ᵥ p.delta +
        residual (subst s pt.before ++ dt.before) (subst s pb.before ++ db.before) =
      incidenceZ s *ᵥ (incidenceZ s ^ n *ᵥ p.delta + residual pt.before pb.before) +
        residual dt.before db.before
    rw [residual_inflate, Matrix.mulVec_add, pow_succ', Matrix.mulVec_mulVec]
    abel

/-- Strict terminal overlap upgrades that exact ordinal transcript to a
strict path, including every ancestor and the original source. -/
theorem assembled_has_ordered_interior_path (s : Fin 3 → Word)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a)
    (p : Packet) (n : ℕ) (top : Mark (image s n p.top))
    (bottom : Mark (image s n p.bottom))
    (hi : (assembledPacket s p n top bottom).Interior ℓ) :
    ∃ xs : List (ℕ × ℕ), xs.length = n ∧
      OrderedInteriorPath s ℓ p xs (assembledPacket s p n top bottom) := by
  obtain ⟨xs, hlen, hpath⟩ := assembled_has_ordered_path s p n top bottom
  exact ⟨xs, hlen, ordered_path_indexed_interior s ℓ β hpos hβ hscale hpath hi⟩

theorem offset_incidence_pow (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a) (n : ℕ) (v : Fin 3 → ℤ) :
    offset ℓ (incidenceZ s ^ n *ᵥ v) = β^n*offset ℓ v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, offset_incidence s ℓ β hscale, ih]
    ring

/-- The physical displacement of the exact integral assembled packet. -/
theorem assembled_offset (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a)
    (p : Packet) (n : ℕ) (top : Mark (image s n p.top))
    (bottom : Mark (image s n p.bottom)) :
    offset ℓ (assembledPacket s p n top bottom).delta =
      β^n*offset ℓ p.delta + physicalLength ℓ top.before - physicalLength ℓ bottom.before := by
  change offset ℓ (incidenceZ s ^ n *ᵥ p.delta + residual top.before bottom.before) = _
  rw [offset_add, offset_incidence_pow s ℓ β hscale, offset_residual]
  ring

/-- Positioned type-1 marks produce a strict ordered run-window entry.
The signed bound is bottom-position minus top-position, with the scaled
source displacement retained; it is the negative of the packet offset. -/
theorem positioned_run_marks {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hscale : ∀ a, physicalLength (lengths r β) (sigma r k a) = β*lengths r β a)
    (p : Packet) (n : ℕ) (top : Mark (image (sigma r k) n p.top))
    (bottom : Mark (image (sigma r k) n p.bottom))
    (htop : top.letter = 1) (hbottom : bottom.letter = 1)
    (hbound : |(-β^n*offset (lengths r β) p.delta +
      physicalLength (lengths r β) bottom.before)-
      physicalLength (lengths r β) top.before| ≤ (k : ℝ)-1) :
    ∃ xs : List (ℕ × ℕ), xs.length = n ∧
      OrderedInteriorPath (sigma r k) (lengths r β) p xs
        (assembledPacket (sigma r k) p n top bottom) ∧
      Central r k β (assembledPacket (sigma r k) p n top bottom) := by
  have hpos : ∀ a, 0 < lengths r β a :=
    fun a => zero_lt_one.trans_le (h.lengths_ge_one a)
  have habs : |offset (lengths r β)
      (assembledPacket (sigma r k) p n top bottom).delta| ≤ (k : ℝ)-1 := by
    rw [assembled_offset _ _ β hscale]
    calc
      |β^n*offset (lengths r β) p.delta +
        physicalLength (lengths r β) top.before - physicalLength (lengths r β) bottom.before| =
        |-((-β^n*offset (lengths r β) p.delta+
          physicalLength (lengths r β) bottom.before)-physicalLength (lengths r β) top.before)| := by
          congr 1
          ring
      _ = _ := abs_neg _
      _ ≤ _ := hbound
  have hc : Central r k β (assembledPacket (sigma r k) p n top bottom) :=
    ⟨htop, hbottom, habs⟩
  have hi : (assembledPacket (sigma r k) p n top bottom).Interior (lengths r β) := by
    apply (Packet.interior_iff_bounds _ hpos _).mpr
    change -lengths r β top.letter < _ ∧ _ < lengths r β bottom.letter
    rw [htop, hbottom]
    change -β < _ ∧ _ < β
    constructor <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2, h.lower]
  obtain ⟨xs, hlen, hpath⟩ := assembled_has_ordered_interior_path (sigma r k)
    (lengths r β) β hpos h.beta_pos hscale p n top bottom hi
  exact ⟨xs, hlen, hpath, hc⟩

private theorem physical_subst_scale (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a) (w : Word) :
    physicalLength ℓ (subst s w) = β*physicalLength ℓ w := by
  induction w with
  | nil => simp [subst]
  | cons a w ih =>
    simp only [subst_cons, physicalLength_append, physicalLength_cons, hscale, ih]
    ring

theorem physical_image_scale (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β*ℓ a) (n : ℕ) (a : Fin 3) :
    physicalLength ℓ (image s n a) = β^n*ℓ a := by
  induction n with
  | zero => simp [image]
  | succ n ih =>
    rw [image_succ, physical_subst_scale s ℓ β hscale, ih]
    ring

/-- Three inflations of a half-unit overlap contain the entire common
length-`18β` interval used by the clean-window selection. Both physical
track origins, and the sign of the scaled displacement, are explicit. -/
theorem half_mass_common_interval {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hscale : ∀ a, physicalLength (lengths r β) (sigma r k a) = β*lengths r β a)
    (hβ : 12 < β) (p : Packet) (hmass : (1/2 : ℝ) ≤ packetMass (lengths r β) p) :
    let S : ℝ := -β^3*offset (lengths r β) p.delta
    let L : ℝ := max 0 S
    0 ≤ L ∧ S ≤ L ∧
      L+18*β ≤ physicalLength (lengths r β) (image (sigma r k) 3 p.top) ∧
      L+18*β ≤ S+physicalLength (lengths r β) (image (sigma r k) 3 p.bottom) := by
  let S : ℝ := -β^3*offset (lengths r β) p.delta
  let L : ℝ := max 0 S
  let T := physicalLength (lengths r β) (image (sigma r k) 3 p.top)
  let U := physicalLength (lengths r β) (image (sigma r k) 3 p.bottom)
  have hβ0 := h.beta_pos
  have hβcube : 0 ≤ β^3 := by positivity
  have hscaled : intervalMass 0 T S (S+U) = β^3*packetMass (lengths r β) p := by
    have hs := intervalMass_scale 0 (lengths r β p.top)
      (-offset (lengths r β) p.delta)
      (lengths r β p.bottom-offset (lengths r β) p.delta) (β^3) hβcube
    dsimp [T, U, S]
    rw [physical_image_scale _ _ β hscale, physical_image_scale _ _ β hscale]
    simpa only [packetMass, mul_zero, mul_neg, mul_sub, mul_add, neg_mul, sub_eq_add_neg,
      add_comm] using hs
  have hlen : 18*β ≤ intervalMass 0 T S (S+U) := by
    rw [hscaled]
    have hm := mul_le_mul_of_nonneg_left hmass hβcube
    have hs : (36 : ℝ) ≤ β^2 := by nlinarith only [hβ, sq_nonneg (β-12)]
    have hc := mul_le_mul_of_nonneg_left hs hβ0.le
    nlinarith only [hm, hc]
  have hw : 18*β ≤ min T (S+U)-L := by
    change 18*β ≤ max 0 (min T (S+U)-L) at hlen
    rcases le_max_iff.mp hlen with hz | hw
    · linarith only [hz, hβ0]
    · exact hw
  refine ⟨le_max_left _ _, le_max_right _ _, ?_, ?_⟩
  · have ht := min_le_left T (S+U)
    change L+18*β ≤ T
    linarith only [hw, ht]
  · have hu := min_le_right T (S+U)
    change L+18*β ≤ S+U
    linarith only [hw, hu]

end Psc.BHThirdLevelTransport
