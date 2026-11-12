import PscVerif.CutPrefixEmbedding
import PscVerif.NamedPrefixCompact
import PscVerif.StrictSystem
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform approximation of literal balanced cuts by the named prefix tiles

The source is either original named substitution and the tile is its actual
period-two prefix closure in the same matrix-adic product. Every selected
mark at power `12*n` is re-embedded at a literal position of that word. The
stable error is at most `(7/8)^n` times a finite source-only bound, while
every residue through depth `12*n` is exactly equal.

A genuine balanced cut supplies two such tile witnesses around the same
integer prefix point. Strict-system membership supplies their distinct
letters. These are proximity statements, not membership in the tile
intersection, a positive measure theorem, or a regular-cylinder count.

Pre-code gate: `docs/c4-cut-prefix-embedding-literature-2026-11-12.md`.
-/

namespace Psc.NamedCutProximity

open Set Filter
open Psc.Binomial Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceInverse Psc.OccurrenceResidue Psc.PrefixAddress
open Psc.PrefixClosure Psc.StablePrefixWindow Psc.CutPrefixEmbedding
open Psc.NamedStableChart Psc.NamedStableContraction Psc.NamedPrefixCompact
open scoped BigOperators Topology

/-- These are authenticated ordinals of the named infinite words, not
sampled positions of an independent word. -/
def anchor (fixture : Fin 2) (a : Fin 3) : ℕ :=
  ((![![0, 2, 1], ![0, 1, 2]] : Fin 2 → Fin 3 → Fin 3) fixture a).val

theorem anchor_occurs (fixture : Fin 2) (a : Fin 3) :
    word fixture (anchor fixture a) = a := by
  fin_cases fixture <;> fin_cases a <;>
    exact word_initial _ _

/-- A finite sum over all original parent positions and all three reference
letters bounds every correction. It is independent of the inflation depth. -/
noncomputable def sourceBound (fixture : Fin 2) (u : Word) : ℝ :=
  correctionBound (word fixture) (anchor fixture) piZ u

theorem sourceBound_nonneg (fixture : Fin 2) (u : Word) :
    0 ≤ sourceBound fixture u :=
  correctionBound_nonneg _ _ _ u

theorem correction_le_sourceBound (fixture : Fin 2) {u : Word} (m : Mark u) :
    ‖piZ (correction (word fixture) (anchor fixture) m)‖ ≤ sourceBound fixture u :=
  correction_norm_le _ _ _ m

/-- The proved block-twelve contraction iterates at every finite exponent. -/
theorem block_contract (n : ℕ) (x : Stable) :
    ‖(B ^ (12 * n)) x‖ ≤ (7 / 8 : ℝ) ^ n * ‖x‖ := by
  rw [pow_mul]
  exact norm_pow_le (B ^ 12) (7 / 8) (by norm_num) B_pow_twelve_contract n x

theorem word_fixed_block (fixture : Fin 2) (n : ℕ) :
    FixedPrefix (iterateImages (substitution fixture) (12 * n)) (word fixture) :=
  fixedPrefix_period_lift _ _ 12 n (word_fixed_twelve fixture)

/-- Every actual marked position of every compatible inflation has an
authentic same-letter prefix witness, a vanishing stable error and exact
agreement at all eligible depths of the original matrix-adic carrier. -/
theorem prefix_approximation (fixture : Fin 2) (u : Word) (n : ℕ)
    (m : Mark (subst (iterateImages (substitution fixture) (12 * n)) u)) :
    ∃ j : ℕ,
      word fixture j = m.letter ∧
      ambientStar (substitution fixture) piZ
          (parikhZ (wordPrefix (word fixture) j)) ∈ tiles fixture m.letter ∧
      ‖piZ (parikhZ m.before) - piZ (parikhZ (wordPrefix (word fixture) j))‖ ≤
        (7 / 8 : ℝ) ^ n * sourceBound fixture u ∧
      ∀ q : ℕ, q ≤ 12 * n →
        MadicResidue.quotient (incidenceLinear (substitution fixture)) q
            (parikhZ m.before) =
          MadicResidue.quotient (incidenceLinear (substitution fixture)) q
            (parikhZ (wordPrefix (word fixture) j)) := by
  obtain ⟨parent, digit, rfl⟩ := mark_decomposition _ u m
  let j := embeddedIndex _ (word fixture) (anchor fixture) (anchor_occurs fixture)
    parent.letter digit
  refine ⟨j, embedded_letter _ _ _ _ (word_fixed_block fixture n) _ _,
    embedded_mem_prefixTiles _ _ _ _ (word_fixed_block fixture n) _ _ _, ?_, ?_⟩
  · have he := projected_prefix_error _ (word fixture) (anchor fixture)
      (anchor_occurs fixture) (word_fixed_block fixture n) (B ^ (12 * n)) piZ
      (action_pow_commute _ B piZ (pi_commute fixture) (12 * n)) parent digit
    change ‖piZ (parikhZ (parent.inflate _ digit).before) -
      piZ (parikhZ (wordPrefix (word fixture) j))‖ ≤ _
    rw [he]
    exact (block_contract n _).trans
      (mul_le_mul_of_nonneg_left (correction_le_sourceBound fixture parent)
        (pow_nonneg (by norm_num) n))
  · intro q hq
    exact prefix_residue_eq_of_le _ (12 * n) q hq _ _ _
      (word_fixed_block fixture n) parent digit

/-- The numerical envelope tends to zero for each fixed finite source word. -/
theorem source_error_tendsto_zero (fixture : Fin 2) (u : Word) :
    Tendsto (fun n : ℕ => (7 / 8 : ℝ) ^ n * sourceBound fixture u) atTop (𝓝 0) := by
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (7 / 8 : ℝ) < 1)).mul_const
      (sourceBound fixture u)

/-- Epsilon control is uniform over every actual mark at a large enough
generation. The same threshold also guarantees any fixed residue depth. -/
theorem eventually_all_prefixes_close (fixture : Fin 2) (u : Word)
    (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : Mark (subst (iterateImages (substitution fixture) (12 * n)) u),
        ∃ j : ℕ, word fixture j = m.letter ∧
          ambientStar (substitution fixture) piZ
              (parikhZ (wordPrefix (word fixture) j)) ∈ tiles fixture m.letter ∧
          ‖piZ (parikhZ m.before) - piZ (parikhZ (wordPrefix (word fixture) j))‖ < ε ∧
          MadicResidue.quotient (incidenceLinear (substitution fixture)) q
              (parikhZ m.before) =
            MadicResidue.quotient (incidenceLinear (substitution fixture)) q
              (parikhZ (wordPrefix (word fixture) j)) := by
  have he : ∀ᶠ n : ℕ in atTop, (7 / 8 : ℝ) ^ n * sourceBound fixture u < ε :=
    (source_error_tendsto_zero fixture u).eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N q, ?_⟩
  intro n hn m
  obtain ⟨j, hj, ht, hb, hr⟩ := prefix_approximation fixture u n m
  refine ⟨j, hj, ht, hb.trans_lt (hN n ((le_max_left N q).trans hn)), hr q ?_⟩
  have hq : q ≤ n := (le_max_right N q).trans hn
  omega

/-- The two witnesses refer to a single exact balanced-cut vector. Their
closeness does not assert that the cut already lies in the intersection. -/
theorem balanced_cut_approximation (fixture : Fin 2) (u v : Word) (n : ℕ)
    (top : Mark (subst (iterateImages (substitution fixture) (12 * n)) u))
    (bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) v))
    (balanced : parikhZ top.before = parikhZ bottom.before) :
    ∃ jt jb : ℕ,
      word fixture jt = top.letter ∧ word fixture jb = bottom.letter ∧
      ambientStar (substitution fixture) piZ (parikhZ (wordPrefix (word fixture) jt)) ∈
        tiles fixture top.letter ∧
      ambientStar (substitution fixture) piZ (parikhZ (wordPrefix (word fixture) jb)) ∈
        tiles fixture bottom.letter ∧
      ‖piZ (parikhZ top.before) - piZ (parikhZ (wordPrefix (word fixture) jt))‖ ≤
        (7 / 8 : ℝ) ^ n * (sourceBound fixture u + sourceBound fixture v) ∧
      ‖piZ (parikhZ top.before) - piZ (parikhZ (wordPrefix (word fixture) jb))‖ ≤
        (7 / 8 : ℝ) ^ n * (sourceBound fixture u + sourceBound fixture v) ∧
      ∀ q : ℕ, q ≤ 12 * n →
        MadicResidue.quotient (incidenceLinear (substitution fixture)) q (parikhZ top.before) =
          MadicResidue.quotient (incidenceLinear (substitution fixture)) q
            (parikhZ (wordPrefix (word fixture) jt)) ∧
        MadicResidue.quotient (incidenceLinear (substitution fixture)) q (parikhZ top.before) =
          MadicResidue.quotient (incidenceLinear (substitution fixture)) q
            (parikhZ (wordPrefix (word fixture) jb)) := by
  obtain ⟨jt, hjt, hkt, hbt, hrt⟩ := prefix_approximation fixture u n top
  obtain ⟨jb, hjb, hkb, hbb, hrb⟩ := prefix_approximation fixture v n bottom
  refine ⟨jt, jb, hjt, hjb, hkt, hkb, ?_, ?_, ?_⟩
  · exact hbt.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (sourceBound_nonneg fixture v))
      (pow_nonneg (by norm_num) n))
  · rw [balanced]
    exact hbb.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (sourceBound_nonneg fixture u))
      (pow_nonneg (by norm_num) n))
  · intro q hq
    exact ⟨hrt q hq, by rw [balanced]; exact hrb q hq⟩

/-- On a supplied actual strict carrier, the two letters of every such
proper balanced cut are a represented cut pair and are distinct. -/
theorem strict_cut_labels (fixture : Fin 2) {C : Finset WordPair}
    (strict : Psc.StrictSystem.StrictSystem (substitution fixture) C)
    (T : WordPair) (hT : T ∈ C) (n : ℕ)
    (top : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.1))
    (bottom : Mark (subst (iterateImages (substitution fixture) (12 * n)) T.2))
    (balanced : parikhZ top.before = parikhZ bottom.before) :
    Psc.StrictSystem.CutPair C top.letter bottom.letter ∧ top.letter ≠ bottom.letter := by
  have hu : (subst (substitution fixture))^[12 * n] T.1 =
      top.before ++ top.letter :: top.after := by
    simpa only [subst_iterateImages] using top.split
  have hv : (subst (substitution fixture))^[12 * n] T.2 =
      bottom.before ++ bottom.letter :: bottom.after := by
    simpa only [subst_iterateImages] using bottom.split
  have hp := strict.cut_follow hT (12 * n) hu hv (equiv1_of_parikhZ_eq balanced)
  exact ⟨hp, strict.cutPair_ne hp⟩

end Psc.NamedCutProximity
