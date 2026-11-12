import PscVerif.NamedGeometricEnclosure

/-!
# Sharp closed box for the original named geometric tiles

The complete block-twelve digit premise is kept visible in the general
lemma. Actual prefix addressing, including self-parent addresses, proves
the anisotropic bound without assuming boundedness first. Strict rational
interval rejection then implies empty overlap; boundary contact is kept.

Pre-code gate: `docs/c4-archived-graph-refinement-literature-2026-11-11.md`.
-/

namespace Psc.NamedSharpBox

open Psc.Binomial Psc.OccurrenceTransport Psc.OccurrenceInverse
open Psc.OccurrenceResidue Psc.OccurrencePiece Psc.OccurrenceCover Psc.PrefixAddress Psc.PrefixClosure
open Psc.StablePrefixWindow Psc.NamedStableChart Psc.NamedStableContraction Psc.NamedPrefixCompact
open Psc.NamedGeometricEnclosure Psc.GeometricPacketCarrier Matrix

/-- Every actual block digit, not an extrema sample or a radius metadata field. -/
def DigitsBound (fixture : Fin 2) : Prop :=
  ∀ (letter : Fin 3) (d : Mark (iterateImages (substitution fixture) 12 letter)),
    |piZ (parikhZ d.before) 0| ≤ (23 : ℝ) / 5 ∧
    |piZ (parikhZ d.before) 1| ≤ (14 : ℝ) / 5

/-- The existing authenticated entry bounds suffice for this sharp box. -/
theorem block_coordinate_bounds (x : Stable) :
    |((B ^ 12) x) 0| ≤ (19 : ℝ) / 40 * |x 0| + (2 : ℝ) / 5 * |x 1| ∧
    |((B ^ 12) x) 1| ≤ (3 : ℝ) / 20 * |x 0| + (7 : ℝ) / 20 * |x 1| := by
  obtain ⟨h00, h01, h10, h11⟩ := twelfth_entry_bounds
  rw [B_pow_apply_eq_matrix, Bmat_pow_twelve]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · change |(3941 - 4755 * a) * x 0 + (7415 - 8945 * a) * x 1| ≤ _
    exact (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right h00 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right h01 (abs_nonneg _)))
  · change |(2095 - 4755 * b) * x 0 + (3941 - 8945 * b) * x 1| ≤ _
    exact (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right h10 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right h11 (abs_nonneg _)))

/-- Self-parent addresses cannot escape the box: solve both coordinate
inequalities together, preserving their distinct coefficients and digits. -/
theorem self_parent_box {x y : ℝ}
    (hx : x ≤ (19 : ℝ) / 40 * x + (2 : ℝ) / 5 * y + 23 / 5)
    (hy : y ≤ (3 : ℝ) / 20 * x + (7 : ℝ) / 20 * y + 14 / 5) :
    x ≤ 16 ∧ y ≤ 8 := by constructor <;> linarith

/-- The two invariant inequalities are checked in the original coordinates. -/
theorem box_invariant :
    (19 : ℝ) / 40 * 16 + (2 : ℝ) / 5 * 8 + 23 / 5 ≤ 16 ∧
    (3 : ℝ) / 20 * 16 + (7 : ℝ) / 20 * 8 + 14 / 5 ≤ 8 := by norm_num

/-- Every prefix ordinal is covered by its full parent and local mark.
This is universal in the actual infinite word, not a finite word check. -/
theorem prefix_box_of_digits (fixture : Fin 2) (digits : DigitsBound fixture) (n : ℕ) :
    |piZ (parikhZ (wordPrefix (word fixture) n)) 0| ≤ 16 ∧
    |piZ (parikhZ (wordPrefix (word fixture) n)) 1| ≤ 8 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let τ := iterateImages (substitution fixture) 12
    have hn : ∀ c, τ c ≠ [] := nonerasing_iterateImages _ (nonerasing fixture) 12
    obtain ⟨e, he⟩ := childIndex_surjective τ (word fixture)
      (cofinalImages_of_nonerasing τ (word fixture) hn) n
    have hparent := childIndex_parent_le τ (word fixture) hn e
    rw [he] at hparent
    have hprefix := parikhZ_prefix_childIndex τ (word fixture) (word_fixed_twelve fixture) e
    rw [he] at hprefix
    have hstar := congrArg piZ hprefix
    rw [map_add, ← action_pow_commute (substitution fixture) B piZ
      (pi_commute fixture) 12] at hstar
    have hb := block_coordinate_bounds (piZ (parikhZ (wordPrefix (word fixture) e.1)))
    have hd := digits _ e.2
    have h0 : |piZ (parikhZ (wordPrefix (word fixture) n)) 0| ≤
        (19 : ℝ) / 40 * |piZ (parikhZ (wordPrefix (word fixture) e.1)) 0| +
        (2 : ℝ) / 5 * |piZ (parikhZ (wordPrefix (word fixture) e.1)) 1| + 23 / 5 := by
      rw [hstar]
      exact (abs_add_le _ _).trans (add_le_add hb.1 hd.1)
    have h1 : |piZ (parikhZ (wordPrefix (word fixture) n)) 1| ≤
        (3 : ℝ) / 20 * |piZ (parikhZ (wordPrefix (word fixture) e.1)) 0| +
        (7 : ℝ) / 20 * |piZ (parikhZ (wordPrefix (word fixture) e.1)) 1| + 14 / 5 := by
      rw [hstar]
      exact (abs_add_le _ _).trans (add_le_add hb.2 hd.2)
    rcases lt_or_eq_of_le hparent with hlt | heq
    · obtain ⟨hp0, hp1⟩ := ih e.1 hlt
      constructor <;> linarith
    · rw [heq] at h0 h1
      exact self_parent_box h0 h1

/-- Passing closed coordinate inequalities to the actual prefix closure
retains all completion coordinates and every boundary point. -/
theorem tile_box_of_digits (fixture : Fin 2) (digits : DigitsBound fixture)
    (letter : Fin 3) (x : Ambient (substitution fixture) Stable)
    (hx : x ∈ tiles fixture letter) : |x.1 0| ≤ 16 ∧ |x.1 1| ≤ 8 := by
  have hclosed : IsClosed {y : Ambient (substitution fixture) Stable |
      |y.1 0| ≤ 16 ∧ |y.1 1| ≤ 8} :=
    (isClosed_le ((continuous_apply 0).comp continuous_fst).abs continuous_const).inter
      (isClosed_le ((continuous_apply 1).comp continuous_fst).abs continuous_const)
  have hraw : raw (word fixture) (ambientStar (substitution fixture) piZ) letter ⊆
      {y : Ambient (substitution fixture) Stable | |y.1 0| ≤ 16 ∧ |y.1 1| ≤ 8} := by
    rintro y ⟨n, hn, rfl⟩
    exact prefix_box_of_digits fixture digits n
  change x ∈ closure (raw (word fixture)
    (ambientStar (substitution fixture) piZ) letter) at hx
  exact closure_minimal hraw hclosed hx

/-- A chart instance whose radii are the original archived `(16,8)`.
The unrelated physical bound is inherited from its exact named chart. -/
noncomputable def sharpChart (fixture : Fin 2) (digits : DigitsBound fixture) :
    ChartEnclosure (ambientStar (substitution fixture) piZ) (tiles fixture) physicalRow :=
  { chart fixture with
    radius := ![16, 8]
    enclosed := by
      intro letter x hx i
      have h := tile_box_of_digits fixture digits letter x hx
      fin_cases i
      · exact h.1
      · exact h.2 }

/-- This is exactly one strict integer interval test in the historical code. -/
def RejectCoordinate (lo hi bound x y : ℤ) : Prop :=
  (bound < 1000000 * x - lo * y ∧ bound < 1000000 * x - hi * y) ∨
  (1000000 * x - lo * y < -bound ∧ 1000000 * x - hi * y < -bound)

instance (lo hi bound x y : ℤ) : Decidable (RejectCoordinate lo hi bound x y) := by
  unfold RejectCoordinate
  infer_instance

/-- Integer arithmetic with both endpoints, never floating-point separation. -/
def Reject (z : Fin 3 → ℤ) : Prop :=
  RejectCoordinate 828911 828912 32000000 (z 0) (z 1) ∨
  RejectCoordinate 440619 440620 16000000 (z 2) (z 1)

instance (z : Fin 3 → ℤ) : Decidable (Reject z) := by
  unfold Reject
  infer_instance

def admitted (p : Packet) : Prop := ¬ Reject p.delta

instance (p : Packet) : Decidable (admitted p) := by
  unfold admitted
  infer_instance

/-- A coordinate enclosed by the real chart cannot fail both rational
endpoint tests, for either sign of the integer middle coordinate. -/
theorem not_rejectCoordinate {lo hi bound x y : ℤ} {c : ℝ}
    (hl : (lo : ℝ) / 1000000 ≤ c) (hu : c ≤ (hi : ℝ) / 1000000)
    (hb : |(x : ℝ) - c * y| ≤ (bound : ℝ) / 1000000) :
    ¬ RejectCoordinate lo hi bound x y := by
  obtain ⟨hbl, hbu⟩ := abs_le.mp hb
  intro reject
  rcases reject with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have h0R : (bound : ℝ) < 1000000 * x - lo * y := by exact_mod_cast h0
    have h1R : (bound : ℝ) < 1000000 * x - hi * y := by exact_mod_cast h1
    rcases le_total (0 : ℝ) y with hy | hy
    · have hmulU := mul_le_mul_of_nonneg_right hu hy
      nlinarith
    · have hmulL := mul_le_mul_of_nonpos_right hl hy
      nlinarith
  · have h0R : 1000000 * x - lo * y < -(bound : ℝ) := by exact_mod_cast h0
    have h1R : 1000000 * x - hi * y < -(bound : ℝ) := by exact_mod_cast h1
    rcases le_total (0 : ℝ) y with hy | hy
    · have hmulL := mul_le_mul_of_nonneg_right hl hy
      nlinarith
    · have hmulU := mul_le_mul_of_nonpos_right hu hy
      nlinarith

/-- The original rational exclusion is sound for every actual overlap,
provided the complete digit bound. The completion factor is retained. -/
theorem nonempty_admitted_of_digits (fixture : Fin 2) (digits : DigitsBound fixture)
    (p : Packet) (h : (overlap (ambientStar (substitution fixture) piZ)
      (tiles fixture) p).Nonempty) : admitted p := by
  have h0 := stable_difference_bound (sharpChart fixture digits) p h 0
  have h1 := stable_difference_bound (sharpChart fixture digits) p h 1
  norm_num [sharpChart, chart, stableCoordinate, ambientStar] at h0 h1
  rw [piZ_apply, W_mulVec] at h0 h1
  change |(p.delta 0 : ℝ) - a * p.delta 1| ≤ 32 at h0
  change |(p.delta 2 : ℝ) - b * p.delta 1| ≤ 16 at h1
  obtain ⟨⟨hal, hau⟩, ⟨hbl, hbu⟩⟩ := chart_coarse_bounds
  have haL : (828911 : ℝ) / 1000000 ≤ a := by linarith
  have haU : a ≤ (828912 : ℝ) / 1000000 := by linarith
  have hbL : (440619 : ℝ) / 1000000 ≤ b := by linarith
  have hbU : b ≤ (440620 : ℝ) / 1000000 := by linarith
  have hn0 := not_rejectCoordinate haL haU
    (show |(p.delta 0 : ℝ) - a * p.delta 1| ≤ (32000000 : ℝ) / 1000000 by norm_num; exact h0)
  have hn1 := not_rejectCoordinate hbL hbU
    (show |(p.delta 2 : ℝ) - b * p.delta 1| ≤ (16000000 : ℝ) / 1000000 by norm_num; exact h1)
  exact fun hr => hr.elim hn0 hn1

/-- A strict outer-box rejection proves actual emptiness, not just a
failed finite-graph lookup or an exhausted coordinate cap. -/
theorem overlap_empty_of_reject (fixture : Fin 2) (digits : DigitsBound fixture)
    (p : Packet) (reject : Reject p.delta) :
    overlap (ambientStar (substitution fixture) piZ) (tiles fixture) p = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact nonempty_admitted_of_digits fixture digits p ⟨x, hx⟩ reject

/-- Endpoint contact is retained by the exact strict interval test. -/
theorem boundary_contact_retained :
    ¬ Reject (![32, 0, 16] : Fin 3 → ℤ) := by decide +kernel

/-- One integer step strictly beyond either original difference radius is rejected. -/
theorem strict_separation_rejected :
    Reject (![33, 0, 0] : Fin 3 → ℤ) ∧ Reject (![0, 0, 17] : Fin 3 → ℤ) := by decide +kernel

end Psc.NamedSharpBox
