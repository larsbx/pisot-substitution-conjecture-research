import PscVerif.NamedStableContraction
import PscVerif.StablePrefixWindow
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Closed compactness instances for the two named actual prefix words

The two literal substitutions have the same incidence, but their words
are constructed separately from their own period-two images of `[0]`.
Their complete prefix closures live in the original matrix-adic product.
The enclosure uses every block-twelve literal digit through the canonical
finite norm sum; no numerical digit bound of five is assumed.

All chart, contraction, injectivity, properness, and fixed-word premises
are discharged for the named instances. The tile equations retain their
stated period. No one-step equation, radius forty, Haar scaling, positive
overlap measure, or general Pisot constructor is asserted.

Pre-code gate: `docs/c4-named-stable-chart-literature-2026-11-11.md`.
-/

namespace Psc.NamedPrefixCompact

open Psc.Binomial Psc.OccurrenceTransport Psc.OccurrenceInverse
open Psc.OccurrenceCover Psc.OccurrenceResidue Psc.PrefixAddress Psc.PrefixClosure
open Psc.StablePrefixWindow Psc.NamedStableChart Psc.NamedStableContraction Matrix

def sigma0 : Fin 3 → Word := ![[1], [0, 2, 1], [0, 0, 1]]
def sigma1 : Fin 3 → Word := ![[1], [0, 1, 2], [0, 0, 1]]

/-- The finite index has precisely the two declared literal controls. -/
def substitution (fixture : Fin 2) : Fin 3 → Word := ![sigma0, sigma1] fixture

theorem incidence_eq (fixture : Fin 2) : incidenceZ (substitution fixture) = MZ := by
  fin_cases fixture <;> ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem nonerasing (fixture : Fin 2) (a : Fin 3) : substitution fixture a ≠ [] := by
  fin_cases fixture <;> fin_cases a <;> decide

theorem square_nonerasing (fixture : Fin 2) (a : Fin 3) :
    iterateImages (substitution fixture) 2 a ≠ [] :=
  nonerasing_iterateImages (substitution fixture) (nonerasing fixture) 2 a

theorem seed_prolongable (fixture : Fin 2) :
    ([0] : Word) <+: subst (iterateImages (substitution fixture) 2) [0] := by
  fin_cases fixture <;> decide

theorem seed_grows (fixture : Fin 2) :
    ([0] : Word).length < (subst (iterateImages (substitution fixture) 2) [0]).length := by
  fin_cases fixture <;> decide

/-- The authentic infinite word, not a finite prefix sample or an
unspecified solution of the fixed-prefix predicate. -/
noncomputable def word (fixture : Fin 2) : ℕ → Fin 3 :=
  seedWord (iterateImages (substitution fixture) 2) [0]
    (square_nonerasing fixture) (seed_prolongable fixture) (seed_grows fixture)

theorem word_fixed_two (fixture : Fin 2) :
    FixedPrefix (iterateImages (substitution fixture) 2) (word fixture) :=
  seedWord_fixedPrefix _ _ (square_nonerasing fixture)
    (seed_prolongable fixture) (seed_grows fixture)

/-- The contraction scale uses the same constructed word. -/
theorem word_fixed_twelve (fixture : Fin 2) :
    FixedPrefix (iterateImages (substitution fixture) 12) (word fixture) :=
  period_two_to_twelve _ _ (word_fixed_two fixture)

/-- These finite witnesses are proved positions of the actual infinite
words by the seed-limit specification. -/
theorem word_initial (fixture : Fin 2) (i : Fin 3) :
    word fixture i = (![![0, 2, 1], ![0, 1, 2]] : Fin 2 → Fin 3 → Fin 3) fixture i := by
  fin_cases fixture
  · fin_cases i
    · exact seedWord_spec _ _ (square_nonerasing 0) (seed_prolongable 0) (seed_grows 0)
        1 0 (by decide)
    · exact seedWord_spec _ _ (square_nonerasing 0) (seed_prolongable 0) (seed_grows 0)
        1 1 (by decide)
    · exact seedWord_spec _ _ (square_nonerasing 0) (seed_prolongable 0) (seed_grows 0)
        1 2 (by decide)
  · fin_cases i
    · exact seedWord_spec _ _ (square_nonerasing 1) (seed_prolongable 1) (seed_grows 1)
        1 0 (by decide)
    · exact seedWord_spec _ _ (square_nonerasing 1) (seed_prolongable 1) (seed_grows 1)
        1 1 (by decide)
    · exact seedWord_spec _ _ (square_nonerasing 1) (seed_prolongable 1) (seed_grows 1)
        1 2 (by decide)

theorem word_zero (fixture : Fin 2) : word fixture 0 = 0 := by
  fin_cases fixture <;> exact word_initial _ 0

/-- Equal incidence does not identify the two actual words. -/
theorem words_distinct : word 0 ≠ word 1 := by
  intro h
  have h0 : word 0 1 = 2 := word_initial 0 1
  have h1 : word 1 1 = 1 := word_initial 1 1
  have hc : (2 : Fin 3) = 1 := h0.symm.trans ((congrFun h 1).trans h1)
  norm_num at hc

/-- Both words start in `0`, whereas a one-step image starts in `1`.
The proved period-two equation cannot be relabelled as a one-step one. -/
theorem word_not_fixed_one (fixture : Fin 2) :
    ¬ FixedPrefix (substitution fixture) (word fixture) := by
  intro fixed
  have hp : wordPrefix (word fixture) 1 = [0] := by
    simpa [word_zero] using prefix_succ (word fixture) 0
  have hi : subst (substitution fixture) [0] = [1] := by
    fin_cases fixture <;> rfl
  have h := fixed 1
  rw [hp, hi] at h
  norm_num [hp] at h

theorem integralInjective (fixture : Fin 2) :
    Function.Injective (fun z => incidenceZ (substitution fixture) *ᵥ z) := by
  simpa only [incidence_eq fixture] using MZ_mulVec_injective

theorem pi_commute (fixture : Fin 2) (z : Fin 3 → ℤ) :
    B (piZ z) = piZ (incidenceZ (substitution fixture) *ᵥ z) := by
  simpa only [incidence_eq fixture] using piZ_commute z

/-- Every literal block-twelve mark participates in this finite sum,
including repeated occurrences. No external numerical bound is supplied. -/
noncomputable def digitBound (fixture : Fin 2) : ℝ :=
  digitNormSum (iterateImages (substitution fixture) 12) piZ

noncomputable def radius (fixture : Fin 2) : ℝ := 8 * digitBound fixture

theorem radius_nonneg (fixture : Fin 2) : 0 ≤ radius fixture :=
  mul_nonneg (by norm_num) (digitNormSum_nonneg _ _)

/-- The bound holds at every actual prefix position of either named word. -/
theorem prefix_norm_bound (fixture : Fin 2) (n : ℕ) :
    ‖piZ (parikhZ (wordPrefix (word fixture) n))‖ ≤ radius fixture := by
  have h := prefix_norm_le_canonical (iterateImages (substitution fixture) 12)
    (word fixture) (B ^ 12) piZ (7 / 8)
    (nonerasing_iterateImages _ (nonerasing fixture) 12) (word_fixed_twelve fixture)
    (action_pow_commute _ B piZ (pi_commute fixture) 12)
    (by norm_num) (by norm_num) B_pow_twelve_contract n
  change ‖piZ (parikhZ (wordPrefix (word fixture) n))‖ ≤
    digitBound fixture / (1 - (7 / 8 : ℝ)) at h
  have hr : digitBound fixture / (1 - (7 / 8 : ℝ)) = radius fixture := by
    norm_num [radius, div_eq_mul_inv] <;> ring
  rw [hr] at h
  exact h

theorem prefix_mem_ball (fixture : Fin 2) (n : ℕ) :
    piZ (parikhZ (wordPrefix (word fixture) n)) ∈
      Metric.closedBall (0 : Stable) (radius fixture) := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using prefix_norm_bound fixture n

/-- Closures of the named actual prefixes in the original `E × H_M`. -/
noncomputable def tiles (fixture : Fin 2) :
    Fin 3 → Set (Ambient (substitution fixture) Stable) :=
  prefixTiles (word fixture) (ambientStar (substitution fixture) piZ)

/-- The formal compactness instance has no unproved chart, contraction,
word, injectivity, or enclosing-window hypothesis. -/
theorem tiles_compact (fixture : Fin 2) (c : Fin 3) : IsCompact (tiles fixture c) :=
  prefixTiles_compact_of_window (substitution fixture) (word fixture) piZ
    (integralInjective fixture) (Metric.closedBall 0 (radius fixture))
    (isCompact_closedBall 0 (radius fixture)) (prefix_mem_ball fixture) c

theorem tiles_nonempty (fixture : Fin 2) (c : Fin 3) : (tiles fixture c).Nonempty := by
  fin_cases fixture <;> fin_cases c
  · exact prefixTiles_nonempty _ _ 0 0 (word_initial 0 0)
  · exact prefixTiles_nonempty _ _ 1 2 (word_initial 0 2)
  · exact prefixTiles_nonempty _ _ 2 1 (word_initial 0 1)
  · exact prefixTiles_nonempty _ _ 0 0 (word_initial 1 0)
  · exact prefixTiles_nonempty _ _ 1 1 (word_initial 1 1)
  · exact prefixTiles_nonempty _ _ 2 2 (word_initial 1 2)

theorem ambientAction_closedEmbedding (fixture : Fin 2) :
    Topology.IsClosedEmbedding (ambientAction (substitution fixture) B) :=
  ambientAction_isClosedEmbedding _ B B_isClosedEmbedding (integralInjective fixture)

/-- The actual prefix equation is at the authentic word period two. -/
theorem tileEquation_two (fixture : Fin 2) :
    OccurrencePiece.TileEquation (iterateImages (substitution fixture) 2)
      (ambientAction (substitution fixture) B ^ 2)
      (ambientStar (substitution fixture) piZ) (tiles fixture) :=
  ambient_prefixTiles_tileEquation _ 2 _ B piZ B_isClosedEmbedding
    (integralInjective fixture) (pi_commute fixture) (word_fixed_two fixture)
    (cofinalImages_of_nonerasing _ _ (square_nonerasing fixture))

/-- Block twelve gives the same actual tiles their complete block equation. -/
theorem tileEquation_twelve (fixture : Fin 2) :
    OccurrencePiece.TileEquation (iterateImages (substitution fixture) 12)
      (ambientAction (substitution fixture) B ^ 12)
      (ambientStar (substitution fixture) piZ) (tiles fixture) :=
  ambient_prefixTiles_tileEquation _ 12 _ B piZ B_isClosedEmbedding
    (integralInjective fixture) (pi_commute fixture) (word_fixed_twelve fixture)
    (cofinalImages_of_nonerasing _ _
      (nonerasing_iterateImages _ (nonerasing fixture) 12))

/-- The `1/021/001` instance. -/
theorem sigma0_prefixTiles_compact (c : Fin 3) :
    IsCompact (prefixTiles (word 0) (ambientStar sigma0 piZ) c) := tiles_compact 0 c

/-- The `1/012/001` instance, using its own actual word. -/
theorem sigma1_prefixTiles_compact (c : Fin 3) :
    IsCompact (prefixTiles (word 1) (ambientStar sigma1 piZ) c) := tiles_compact 1 c

end Psc.NamedPrefixCompact
