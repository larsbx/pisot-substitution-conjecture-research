import PscVerif.PrefixClosure
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Compact windows for all actual stable prefix points

The literal parent of an output position need not have smaller ordinal.
Strong induction handles a smaller parent; the self-parent case is solved
using the strict contraction inequality itself. No already bounded prefix
set, compact tile, or finite prefix sample is used in this argument.

The coordinate map, its incidence commutation, the contraction bound, and
the complete local digit bound remain explicit. Properness turns the proved
closed-ball enclosure into a compact window in the original matrix-adic
product. A closed embedding is retained separately for history pieces.

Pre-code gate: `docs/c4-stable-prefix-window-literature-2026-11-11.md`.
-/

namespace Psc.StablePrefixWindow

open Psc.Binomial Psc.OccurrenceTransport Psc.OccurrenceFinite
open Psc.OccurrenceInverse Psc.OccurrenceCover Psc.OccurrenceResidue
open Psc.PrefixAddress Psc.PrefixClosure Matrix

/-- The self-parent inequality gives a bound without assuming that the
parent ordinal strictly decreases. -/
theorem self_bound {q D R x : ℝ} (hq : q < 1)
    (invariant : q * R + D ≤ R) (step : x ≤ q * x + D) : x ≤ R := by
  by_contra h
  have hpos : 0 < (1 - q) * (x - R) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- The geometric-series radius satisfies the exact invariant inequality. -/
theorem geometric_radius {q D : ℝ} (hq : q < 1) :
    q * (D / (1 - q)) + D = D / (1 - q) := by
  have hn : 1 - q ≠ 0 := by linarith
  field_simp
  <;> ring

section NormBound

variable {E : Type*} [NormedAddCommGroup E]

/-- A canonical bound obtained from every literal digit. Repeated marks
remain in this sum; choosing a sharper separately proved bound is optional. -/
noncomputable def digitNormSum (τ : Fin 3 → Word) (pi : (Fin 3 → ℤ) →+ E) : ℝ :=
  letI := digitFintype τ
  ∑ d : Digit τ, ‖pi (parikhZ d.2.before)‖

theorem digitNormSum_nonneg (τ : Fin 3 → Word) (pi : (Fin 3 → ℤ) →+ E) :
    0 ≤ digitNormSum τ pi := by
  unfold digitNormSum
  exact Finset.sum_nonneg (fun d _ => norm_nonneg _)

/-- The finite complete inventory supplies the local digit-bound premise. -/
theorem digit_norm_le_sum (τ : Fin 3 → Word) (pi : (Fin 3 → ℤ) →+ E)
    (a : Fin 3) (d : Mark (τ a)) : ‖pi (parikhZ d.before)‖ ≤ digitNormSum τ pi := by
  classical
  letI := digitFintype τ
  exact Finset.single_le_sum (fun e _ => norm_nonneg (pi (parikhZ e.2.before)))
    (Finset.mem_univ (⟨a, d⟩ : Digit τ))

/-- The norm estimate is derived from the entire literal prefix identity. -/
theorem addressed_step (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (q D : ℝ)
    (fixed : FixedPrefix τ w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (contract : ∀ x, ‖B x‖ ≤ q * ‖x‖)
    (digits : ∀ a (d : Mark (τ a)), ‖pi (parikhZ d.before)‖ ≤ D)
    (e : Address τ w) :
    ‖pi (parikhZ (wordPrefix w (childIndex τ w e)))‖ ≤
      q * ‖pi (parikhZ (wordPrefix w e.1))‖ + D := by
  rw [parikhZ_prefix_childIndex τ w fixed, map_add, ← commute]
  exact (norm_add_le _ _).trans (add_le_add (contract _) (digits _ _))

/-- Every actual prefix is bounded. Nonerasure gives complete addresses and
`parent ≤ output`; strict contraction handles the possible equality case.
The invariant inequality and actual digit bounds already force a usable
nonnegative radius, so separate nonnegativity assumptions on `D,R` are not
needed. -/
theorem prefix_norm_le (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (q D R : ℝ)
    (nonerasing : ∀ a, τ a ≠ []) (fixed : FixedPrefix τ w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖B x‖ ≤ q * ‖x‖)
    (digits : ∀ a (d : Mark (τ a)), ‖pi (parikhZ d.before)‖ ≤ D)
    (invariant : q * R + D ≤ R) (n : ℕ) :
    ‖pi (parikhZ (wordPrefix w n))‖ ≤ R := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨e, he⟩ := childIndex_surjective τ w
        (cofinalImages_of_nonerasing τ w nonerasing) n
      have hparent := childIndex_parent_le τ w nonerasing e
      rw [he] at hparent
      have hstep := addressed_step τ w B pi q D fixed commute contract digits e
      rw [he] at hstep
      rcases lt_or_eq_of_le hparent with hlt | heq
      · exact hstep.trans ((add_le_add_right (mul_le_mul_of_nonneg_left
          (ih e.1 hlt) hq0) D).trans invariant)
      · rw [heq] at hstep
        exact self_bound hq1 invariant hstep

/-- The standard radius follows from the same all-prefix argument. -/
theorem prefix_norm_le_geometric (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (q D : ℝ)
    (nonerasing : ∀ a, τ a ≠ []) (fixed : FixedPrefix τ w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖B x‖ ≤ q * ‖x‖)
    (digits : ∀ a (d : Mark (τ a)), ‖pi (parikhZ d.before)‖ ≤ D)
    (n : ℕ) : ‖pi (parikhZ (wordPrefix w n))‖ ≤ D / (1 - q) :=
  prefix_norm_le τ w B pi q D _ nonerasing fixed commute hq0 hq1 contract digits
    (geometric_radius hq1).le n

/-- A universal bound with no externally supplied digit bound or prefix
window: both are derived from the actual finite literal digit family. -/
theorem prefix_norm_le_canonical (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (q : ℝ)
    (nonerasing : ∀ a, τ a ≠ []) (fixed : FixedPrefix τ w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖B x‖ ≤ q * ‖x‖) (n : ℕ) :
    ‖pi (parikhZ (wordPrefix w n))‖ ≤ digitNormSum τ pi / (1 - q) :=
  prefix_norm_le_geometric τ w B pi q (digitNormSum τ pi) nonerasing fixed
    commute hq0 hq1 contract (digit_norm_le_sum τ pi) n

/-- This is the exact universal enclosure consumed by the earlier
prefix-closure compactness theorem. -/
theorem prefix_mem_closedBall (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (q D R : ℝ)
    (nonerasing : ∀ a, τ a ≠ []) (fixed : FixedPrefix τ w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖B x‖ ≤ q * ‖x‖)
    (digits : ∀ a (d : Mark (τ a)), ‖pi (parikhZ d.before)‖ ≤ D)
    (invariant : q * R + D ≤ R) (n : ℕ) :
    pi (parikhZ (wordPrefix w n)) ∈ Metric.closedBall (0 : E) R := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    prefix_norm_le τ w B pi q D R nonerasing fixed commute hq0 hq1 contract digits
      invariant n

/-- A productive prolonging seed supplies the actual infinite fixed word;
no finite sample substitutes for the limit-word theorem. -/
theorem seed_prefix_norm_le (τ : Fin 3 → Word) (u : Word)
    (nonerasing : ∀ a, τ a ≠ []) (prolongable : u <+: subst τ u)
    (grows : u.length < (subst τ u).length)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (q D R : ℝ)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖B x‖ ≤ q * ‖x‖)
    (digits : ∀ a (d : Mark (τ a)), ‖pi (parikhZ d.before)‖ ≤ D)
    (invariant : q * R + D ≤ R) (n : ℕ) :
    ‖pi (parikhZ (wordPrefix (seedWord τ u nonerasing prolongable grows) n))‖ ≤ R :=
  prefix_norm_le τ _ B pi q D R nonerasing
    (seedWord_fixedPrefix τ u nonerasing prolongable grows) commute hq0 hq1
    contract digits invariant n

end NormBound

/-! ## Literal powers and period compatibility -/

/-- Powers of the letter substitution act as powers on complete words. -/
theorem subst_iterateImages (s : Fin 3 → Word) (k : ℕ) :
    subst (iterateImages s k) = (subst s)^[k] :=
  subst_power s k

/-- Fixedness propagates through every actual finite iteration. -/
theorem fixedPrefix_subst_iterate (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (fixed : FixedPrefix τ w) (r n : ℕ) :
    wordPrefix w (((subst τ)^[r] (wordPrefix w n)).length) =
      (subst τ)^[r] (wordPrefix w n) := by
  induction r with
  | zero => simp only [Function.iterate_zero, id_eq, prefix_length]
  | succ r ih =>
      simpa only [Function.iterate_succ_apply', ih] using
        fixed (((subst τ)^[r] (wordPrefix w n)).length)

/-- A fixed word for `s^k` is fixed at every compatible exponent `k*r`.
This is an identity of literal words, not merely incidence matrices. -/
theorem fixedPrefix_period_lift (s : Fin 3 → Word) (w : ℕ → Fin 3)
    (k r : ℕ) (fixed : FixedPrefix (iterateImages s k) w) :
    FixedPrefix (iterateImages s (k * r)) w := by
  intro n
  have h := fixedPrefix_subst_iterate (iterateImages s k) w fixed r n
  rw [subst_iterateImages, ← Function.iterate_mul] at h
  simpa only [subst_iterateImages] using h

/-- Nonerasure is preserved by every power, including the identity power. -/
theorem nonerasing_iterateImages (s : Fin 3 → Word)
    (nonerasing : ∀ a, s a ≠ []) (k : ℕ) (a : Fin 3) :
    iterateImages s k a ≠ [] :=
  Psc.FixedPointLimit.iterate_subst_ne_nil s nonerasing k (by simp)

section ActionPowers

variable {E : Type*} [AddCommGroup E]

/-- The stable-coordinate action commutes at the same literal block scale. -/
theorem action_pow_commute (s : Fin 3 → Word) (B : E →+ E)
    (pi : (Fin 3 → ℤ) →+ E)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z)) (k : ℕ) (z : Fin 3 → ℤ) :
    (B ^ k) (pi z) = pi (incidenceZ (iterateImages s k) *ᵥ z) := by
  simp only [incidenceZ_iterateImages]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ' B k, pow_succ' (incidenceZ s) k]
      change B ((B ^ k) (pi z)) = _
      rw [ih, commute, Matrix.mulVec_mulVec]

end ActionPowers

section Compactness

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- The compact window is derived for the same actual prefix sets. The
matrix-adic factor uses the original incidence `s`, even when the norm
estimate uses another explicitly fixed substitution `τ`. -/
theorem compact_prefixTiles (s τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (q D R : ℝ)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (nonerasing : ∀ a, τ a ≠ []) (fixed : FixedPrefix τ w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖B x‖ ≤ q * ‖x‖)
    (digits : ∀ a (d : Mark (τ a)), ‖pi (parikhZ d.before)‖ ≤ D)
    (invariant : q * R + D ≤ R) (c : Fin 3) :
    IsCompact (prefixTiles w (ambientStar s pi) c) :=
  prefixTiles_compact_of_window s w pi integralInjective
    (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
    (prefix_mem_closedBall τ w B pi q D R nonerasing fixed commute hq0 hq1
      contract digits invariant) c

/-- Compactness from actual fixedness, commutation and strict contraction,
with the complete finite digit bound constructed internally. -/
theorem compact_prefixTiles_canonical (s τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (q : ℝ)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (nonerasing : ∀ a, τ a ≠ []) (fixed : FixedPrefix τ w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖B x‖ ≤ q * ‖x‖) (c : Fin 3) :
    IsCompact (prefixTiles w (ambientStar s pi) c) :=
  compact_prefixTiles s τ w B pi q (digitNormSum τ pi) _ integralInjective
    nonerasing fixed commute hq0 hq1 contract (digit_norm_le_sum τ pi)
    (geometric_radius hq1).le c

/-- Compactness at a compatible block exponent retains the original
matrix-adic carrier and binds the actual action and all block digits. -/
theorem compact_prefixTiles_at_multiple (s : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (k r : ℕ) (q D R : ℝ)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (nonerasing : ∀ a, s a ≠ []) (fixed : FixedPrefix (iterateImages s k) w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖(B ^ (k * r)) x‖ ≤ q * ‖x‖)
    (digits : ∀ a (d : Mark (iterateImages s (k * r) a)), ‖pi (parikhZ d.before)‖ ≤ D)
    (invariant : q * R + D ≤ R) (c : Fin 3) :
    IsCompact (prefixTiles w (ambientStar s pi) c) :=
  compact_prefixTiles s (iterateImages s (k * r)) w (B ^ (k * r)) pi q D R
    integralInjective (nonerasing_iterateImages s nonerasing (k * r))
    (fixedPrefix_period_lift s w k r fixed) (action_pow_commute s B pi commute (k * r))
    hq0 hq1 contract digits invariant c

/-- Every actual finite-history piece is compact. Its map still requires
the separately supplied closed embedding; contraction does not supply one. -/
theorem compact_historyPiece_at_multiple (s : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E) (k r : ℕ) (q D R : ℝ)
    (closedB : Topology.IsClosedEmbedding B)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (nonerasing : ∀ a, s a ≠ []) (fixed : FixedPrefix (iterateImages s k) w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (contract : ∀ x, ‖(B ^ (k * r)) x‖ ≤ q * ‖x‖)
    (digits : ∀ a (d : Mark (iterateImages s (k * r) a)), ‖pi (parikhZ d.before)‖ ≤ D)
    (invariant : q * R + D ≤ R) (n : ℕ) (p : Packet)
    (h : History (iterateImages s (k * r)) n p) :
    IsCompact (historyPiece (iterateImages s (k * r))
      (ambientAction s B ^ (k * r)) (ambientStar s pi)
      (prefixTiles w (ambientStar s pi)) n p h) :=
  compact_prefix_historyPiece s (k * r) w B pi closedB integralInjective
    (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
    (prefix_mem_closedBall (iterateImages s (k * r)) w (B ^ (k * r)) pi q D R
      (nonerasing_iterateImages s nonerasing (k * r))
      (fixedPrefix_period_lift s w k r fixed)
      (action_pow_commute s B pi commute (k * r)) hq0 hq1 contract digits invariant) n p h

end Compactness

/-! ## Exact scalar calibration and weakened-premise controls -/

/-- This scalar identity justifies radius 40 once the actual block
contraction and complete digit premises `q=7/8,D=5` are authenticated. -/
theorem radius_forty_calibration :
    (0 : ℝ) ≤ 7 / 8 ∧ (7 / 8 : ℝ) < 1 ∧
      (7 / 8 : ℝ) * 40 + 5 = 40 ∧ (5 : ℝ) / (1 - 7 / 8) = 40 := by
  norm_num

/-- This binds the scalar calibration to every actual prefix, while
retaining the genuine action and complete digit estimates as hypotheses. -/
theorem prefix_norm_le_forty {E : Type*} [NormedAddCommGroup E]
    (τ : Fin 3 → Word) (w : ℕ → Fin 3)
    (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E)
    (nonerasing : ∀ a, τ a ≠ []) (fixed : FixedPrefix τ w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ τ *ᵥ z))
    (contract : ∀ x, ‖B x‖ ≤ (7 / 8 : ℝ) * ‖x‖)
    (digits : ∀ a (d : Mark (τ a)), ‖pi (parikhZ d.before)‖ ≤ 5)
    (n : ℕ) : ‖pi (parikhZ (wordPrefix w n))‖ ≤ 40 :=
  prefix_norm_le τ w B pi (7 / 8) 5 40 nonerasing fixed commute
    radius_forty_calibration.1 radius_forty_calibration.2.1 contract digits
    radius_forty_calibration.2.2.1.le n

theorem period_two_to_twelve (s : Fin 3 → Word) (w : ℕ → Fin 3)
    (fixed : FixedPrefix (iterateImages s 2) w) :
    FixedPrefix (iterateImages s 12) w :=
  fixedPrefix_period_lift s w 2 6 fixed

/-- The existing period-two fixture may use the length-twelve calibration
only with the full literal length-twelve digit bounds and action estimate. -/
theorem compact_prefixTiles_two_twelve {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (s : Fin 3 → Word) (w : ℕ → Fin 3) (B : E →+ E) (pi : (Fin 3 → ℤ) →+ E)
    (integralInjective : Function.Injective (fun z => incidenceZ s *ᵥ z))
    (nonerasing : ∀ a, s a ≠ []) (fixed : FixedPrefix (iterateImages s 2) w)
    (commute : ∀ z, B (pi z) = pi (incidenceZ s *ᵥ z))
    (contract : ∀ x, ‖(B ^ 12) x‖ ≤ (7 / 8 : ℝ) * ‖x‖)
    (digits : ∀ a (d : Mark (iterateImages s 12 a)), ‖pi (parikhZ d.before)‖ ≤ 5)
    (c : Fin 3) : IsCompact (prefixTiles w (ambientStar s pi) c) :=
  compact_prefixTiles_at_multiple s w B pi 2 6 (7 / 8) 5 40 integralInjective
    nonerasing fixed commute radius_forty_calibration.1 radius_forty_calibration.2.1
    contract digits radius_forty_calibration.2.2.1.le c

/-- A non-strict contraction cannot solve a self-parent inequality. -/
theorem unit_contraction_control :
    (1 : ℝ) * 0 + 0 ≤ 0 ∧ 1 ≤ (1 : ℝ) * 1 + 0 ∧ ¬ (1 : ℝ) ≤ 0 := by
  norm_num

/-- A radius below the invariant threshold is rejected. -/
theorem radius_thirty_nine_control : ¬ ((7 / 8 : ℝ) * 39 + 5 ≤ 39) := by
  norm_num

/-- Strict contraction alone does not imply injectivity or a closed embedding. -/
theorem zero_action_not_injective :
    (∀ x : ℝ, ‖(0 : ℝ →+ ℝ) x‖ ≤ (1 / 2 : ℝ) * ‖x‖) ∧
      ¬ Function.Injective (0 : ℝ →+ ℝ) := by
  constructor
  · intro x
    simp only [AddMonoidHom.zero_apply, norm_zero]
    positivity
  · intro h
    have h01 : (0 : ℝ) = 1 := h rfl
    norm_num at h01

end Psc.StablePrefixWindow
