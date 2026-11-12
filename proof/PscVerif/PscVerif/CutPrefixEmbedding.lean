import PscVerif.StablePrefixWindow

/-!
# Re-embedding actual inflated marks in the same fixed-word prefix closure

Every selected position of an inflated finite word has a complete parent
and local mark. Replacing its finite parent prefix by an actual occurrence
of the same parent letter in the declared fixed word preserves the selected
letter. The difference of the two prefix points is exactly the powered
incidence image of the finite source-prefix correction.

The theorem retains the original matrix-adic carrier. At every shallower
residue depth the correction vanishes exactly. No proximity, tile
positivity, density, or obstruction-to-measure premise is assumed.

Pre-code gate: `docs/c4-cut-prefix-embedding-literature-2026-11-12.md`.
-/

namespace Psc.CutPrefixEmbedding

open Psc.Binomial Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceAddress Psc.OccurrenceInverse Psc.OccurrenceResidue
open Psc.PrefixAddress Psc.PrefixClosure Psc.StablePrefixWindow Matrix
open scoped BigOperators

/-- Splitting an actual inflated mark recovers the whole parent/local
occurrence, including repeated letters and both suffixes. Erasing image
blocks do not invalidate the statement for a supplied actual mark. -/
theorem mark_decomposition (τ : Fin 3 → Word) (u : Word)
    (m : Mark (subst τ u)) :
    ∃ (parent : Mark u) (digit : Mark (τ parent.letter)),
      parent.inflate τ digit = m := by
  let o := locateSubst τ u m.index m.index_lt
  obtain ⟨ho, hf⟩ := List.getElem?_eq_some_iff.mp o.atOrdinal
  let parent : Mark u := markAt u ⟨o.ordinal, ho⟩
  have hparent : parent.letter = o.factor := hf
  let digit : Mark (τ parent.letter) :=
    ⟨o.before, o.letter, o.after, by rw [hparent]; exact o.split⟩
  refine ⟨parent, digit, mark_index_injective _ ?_⟩
  simp only [Mark.inflate, Mark.index, List.length_append]
  change (subst τ (u.take o.ordinal)).length + o.before.length = m.index
  rw [o.local_length]
  exact (locateSubst_index τ u m.index m.index_lt).symm

/-- A complete digit mark copied to an authenticated occurrence of its
parent letter in the actual infinite word. Its literal fields are unchanged. -/
def anchoredDigit (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (a : Fin 3) (d : Mark (τ a)) : Mark (τ (w (anchor a))) where
  before := d.before
  letter := d.letter
  after := d.after
  split := by rw [occurs]; exact d.split

/-- The witness is an actual ordinal of the same word defining the tiles. -/
def embeddedIndex (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (a : Fin 3) (d : Mark (τ a)) : ℕ :=
  childIndex τ w ⟨anchor a, anchoredDigit τ w anchor occurs a d⟩

theorem embedded_letter (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (fixed : FixedPrefix τ w) (a : Fin 3) (d : Mark (τ a)) :
    w (embeddedIndex τ w anchor occurs a d) = d.letter :=
  letter_childIndex τ w fixed ⟨anchor a, anchoredDigit τ w anchor occurs a d⟩

theorem embedded_prefix (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (fixed : FixedPrefix τ w) (a : Fin 3) (d : Mark (τ a)) :
    wordPrefix w (embeddedIndex τ w anchor occurs a d) =
      subst τ (wordPrefix w (anchor a)) ++ d.before :=
  prefix_childIndex τ w fixed ⟨anchor a, anchoredDigit τ w anchor occurs a d⟩

/-- The correction depends only on a mark of the original finite word and
the fixed reference occurrence, not on the inflation exponent or local digit. -/
def correction (w : ℕ → Fin 3) (anchor : Fin 3 → ℕ)
    {u : Word} (m : Mark u) : Fin 3 → ℤ :=
  parikhZ m.before - parikhZ (wordPrefix w (anchor m.letter))

/-- The exact integer identity precedes projection or any norm estimate. -/
theorem prefix_error (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (fixed : FixedPrefix τ w) {u : Word} (m : Mark u) (d : Mark (τ m.letter)) :
    parikhZ (m.inflate τ d).before -
        parikhZ (wordPrefix w (embeddedIndex τ w anchor occurs m.letter d)) =
      incidenceZ τ *ᵥ correction w anchor m := by
  rw [embedded_prefix τ w anchor occurs fixed]
  change parikhZ (subst τ m.before ++ d.before) -
      parikhZ (subst τ (wordPrefix w (anchor m.letter)) ++ d.before) = _
  simp only [parikhZ_append, parikhZ_subst, correction, Matrix.mulVec_sub]
  abel

section AdditiveProjection

variable {G : Type*} [AddCommGroup G]

theorem projected_prefix_error (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (fixed : FixedPrefix τ w) (A : G →+ G) (star : (Fin 3 → ℤ) →+ G)
    (commute : ∀ z, A (star z) = star (incidenceZ τ *ᵥ z))
    {u : Word} (m : Mark u) (d : Mark (τ m.letter)) :
    star (parikhZ (m.inflate τ d).before) -
        star (parikhZ (wordPrefix w (embeddedIndex τ w anchor occurs m.letter d))) =
      A (star (correction w anchor m)) := by
  rw [← map_sub, prefix_error τ w anchor occurs fixed, commute]

variable [TopologicalSpace G]

/-- The embedded point lies in the actual raw prefix set, hence in its
defined closure, with the same selected letter. -/
theorem embedded_mem_prefixTiles (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (fixed : FixedPrefix τ w) (star : (Fin 3 → ℤ) →+ G)
    (a : Fin 3) (d : Mark (τ a)) :
    star (parikhZ (wordPrefix w (embeddedIndex τ w anchor occurs a d))) ∈
      prefixTiles w star d.letter :=
  subset_closure ⟨embeddedIndex τ w anchor occurs a d,
    embedded_letter τ w anchor occurs fixed a d, rfl⟩

end AdditiveProjection

section NormedProjection

variable {E : Type*} [NormedAddCommGroup E]

/-- A finite source-only bound over all original positions and reference
letters. The sum is finite before any inflation exponent is chosen. -/
noncomputable def correctionBound (w : ℕ → Fin 3) (anchor : Fin 3 → ℕ)
    (pi : (Fin 3 → ℤ) →+ E) (u : Word) : ℝ :=
  ∑ i ∈ Finset.range u.length, ∑ a : Fin 3,
    ‖pi (parikhZ (u.take i) - parikhZ (wordPrefix w (anchor a)))‖

theorem correctionBound_nonneg (w : ℕ → Fin 3) (anchor : Fin 3 → ℕ)
    (pi : (Fin 3 → ℤ) →+ E) (u : Word) : 0 ≤ correctionBound w anchor pi u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem correction_norm_le (w : ℕ → Fin 3) (anchor : Fin 3 → ℕ)
    (pi : (Fin 3 → ℤ) →+ E) {u : Word} (m : Mark u) :
    ‖pi (correction w anchor m)‖ ≤ correctionBound w anchor pi u := by
  classical
  calc
    _ = ‖pi (parikhZ (u.take m.index) - parikhZ (wordPrefix w (anchor m.letter)))‖ := by
      rw [m.take_index]
      rfl
    _ ≤ ∑ a : Fin 3, ‖pi (parikhZ (u.take m.index) - parikhZ (wordPrefix w (anchor a)))‖ :=
      Finset.single_le_sum
        (f := fun a : Fin 3 =>
          ‖pi (parikhZ (u.take m.index) - parikhZ (wordPrefix w (anchor a)))‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ m.letter)
    _ ≤ correctionBound w anchor pi u := by
      unfold correctionBound
      exact Finset.single_le_sum
        (f := fun i => ∑ a : Fin 3,
          ‖pi (parikhZ (u.take i) - parikhZ (wordPrefix w (anchor a)))‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr m.index_lt)

/-- The pointwise contraction estimate iterates without a matrix-norm or
continuity assumption; the norm used in the premise is retained. -/
theorem norm_pow_le (A : AddMonoid.End E) (q : ℝ) (hq : 0 ≤ q)
    (contract : ∀ x, ‖A x‖ ≤ q * ‖x‖) (n : ℕ) (x : E) :
    ‖(A ^ n) x‖ ≤ q ^ n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ' A n]
      change ‖A ((A ^ n) x)‖ ≤ _
      calc
        _ ≤ q * ‖(A ^ n) x‖ := contract _
        _ ≤ q * (q ^ n * ‖x‖) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * ‖x‖ := by rw [pow_succ]; ring

end NormedProjection

section OriginalMatrixAdicCarrier

variable {E : Type*} [AddCommGroup E]

/-- Literal powers act in the original carrier; no replacement by a
completion for the powered matrix is made. -/
theorem ambient_prefix_error (s : Fin 3 → Word) (k : ℕ) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (fixed : FixedPrefix (iterateImages s k) w)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    {u : Word} (m : Mark u) (d : Mark (iterateImages s k m.letter)) :
    ambientStar s pi (parikhZ (m.inflate (iterateImages s k) d).before) -
        ambientStar s pi (parikhZ (wordPrefix w
          (embeddedIndex (iterateImages s k) w anchor occurs m.letter d))) =
      (ambientAction s B ^ k) (ambientStar s pi (correction w anchor m)) :=
  projected_prefix_error _ w anchor occurs fixed _ _
    (ambient_block_commute s B pi commute k) m d

/-- Equality at the whole inflation depth is an exact integral statement. -/
theorem prefix_residue_eq (s : Fin 3 → Word) (k : ℕ) (w : ℕ → Fin 3)
    (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (fixed : FixedPrefix (iterateImages s k) w)
    {u : Word} (m : Mark u) (d : Mark (iterateImages s k m.letter)) :
    MadicResidue.quotient (incidenceLinear s) k
        (parikhZ (m.inflate (iterateImages s k) d).before) =
      MadicResidue.quotient (incidenceLinear s) k
        (parikhZ (wordPrefix w
          (embeddedIndex (iterateImages s k) w anchor occurs m.letter d))) := by
  apply (MadicResidue.quotient_eq_iff _ _ _ _).mpr
  refine ⟨correction w anchor m, ?_⟩
  rw [prefix_error _ w anchor occurs fixed]
  change (incidenceLinear s ^ k) _ = incidenceLinear (iterateImages s k) _
  rw [incidenceLinear_iterateImages]

/-- Every shallower cylinder agrees as well; there is no floating residue
test and no restriction to a sampled finite depth. -/
theorem prefix_residue_eq_of_le (s : Fin 3 → Word) (k q : ℕ) (hq : q ≤ k)
    (w : ℕ → Fin 3) (anchor : Fin 3 → ℕ) (occurs : ∀ a, w (anchor a) = a)
    (fixed : FixedPrefix (iterateImages s k) w)
    {u : Word} (m : Mark u) (d : Mark (iterateImages s k m.letter)) :
    MadicResidue.quotient (incidenceLinear s) q
        (parikhZ (m.inflate (iterateImages s k) d).before) =
      MadicResidue.quotient (incidenceLinear s) q
        (parikhZ (wordPrefix w
          (embeddedIndex (iterateImages s k) w anchor occurs m.letter d))) :=
  congrArg (MadicResidue.reduction (incidenceLinear s) hq)
    (prefix_residue_eq s k w anchor occurs fixed m d)

end OriginalMatrixAdicCarrier

end Psc.CutPrefixEmbedding
