import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Boundaries of compact-neighborhood transfer

These are abstract topological controls, not Pisot counterexamples. The
real points can be paired with the zero matrix-adic coordinate, so their
residue coordinates agree at every depth. Closedness without compactness,
mere containment without a neighborhood, and pointwise convergence over
an infinite source family do not supply the hypotheses of the positive
compact-transfer theorem.

Pre-code gate: `docs/c4-compact-neighborhood-literature-2026-11-12.md`.
-/

namespace Psc.CompactNeighborhoodControls

open Set Filter
open scoped Topology

def axis : Set (ℝ × ℝ) := {p | p.2 = 0}

def hyperbola : Set (ℝ × ℝ) := {p | p.1 * p.2 = 1}

/-- Both sets are closed and noncompact, with empty intersection. They
nevertheless have simultaneous approximants at every positive tolerance.
Thus even the open target `∅` has no uniform transfer threshold when the
compactness premises are replaced by closedness. -/
theorem closed_noncompact_control :
    IsClosed axis ∧ IsClosed hyperbola ∧ Disjoint axis hyperbola ∧
      ¬ IsCompact axis ∧ ¬ IsCompact hyperbola ∧
      ¬ ∃ ε : ℝ, 0 < ε ∧
        ∀ x y z : ℝ × ℝ, y ∈ axis → z ∈ hyperbola →
          ‖x - y‖ < ε → ‖x - z‖ < ε → x ∈ (∅ : Set (ℝ × ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_eq continuous_snd continuous_const
  · exact isClosed_eq (continuous_fst.mul continuous_snd) continuous_const
  · apply Set.disjoint_left.mpr
    intro p hp hk
    change p.2 = 0 at hp
    change p.1 * p.2 = 1 at hk
    rw [hp, mul_zero] at hk
    exact zero_ne_one hk
  · intro hc
    obtain ⟨r, hr⟩ := (hc.image continuous_fst).bddAbove
    have hbound : r + 1 ≤ r := hr ⟨(r + 1, 0), rfl, rfl⟩
    linarith
  · intro hc
    obtain ⟨r, hr⟩ := (hc.image continuous_fst).bddAbove
    have hpos : 0 < |r| + 1 := by linarith [abs_nonneg r]
    have hmem : (|r| + 1, (|r| + 1)⁻¹) ∈ hyperbola :=
      mul_inv_cancel₀ (ne_of_gt hpos)
    have hbound : |r| + 1 ≤ r := hr ⟨_, hmem, rfl⟩
    linarith [le_abs_self r]
  · rintro ⟨ε, hε, htransfer⟩
    have hhalf : 0 < ε / 2 := half_pos hε
    let x : ℝ × ℝ := ((ε / 2)⁻¹, 0)
    let z : ℝ × ℝ := ((ε / 2)⁻¹, ε / 2)
    have hx : x ∈ axis := rfl
    have hz : z ∈ hyperbola := inv_mul_cancel₀ (ne_of_gt hhalf)
    have hxx : ‖x - x‖ < ε := by simpa using hε
    have hxz : ‖x - z‖ < ε := by
      change max ‖(ε / 2)⁻¹ - (ε / 2)⁻¹‖ ‖(0 : ℝ) - ε / 2‖ < ε
      simpa only [sub_self, norm_zero, zero_sub, norm_neg, Real.norm_eq_abs,
        abs_of_pos hhalf, max_eq_right (le_of_lt hhalf)] using half_lt_self hε
    exact htransfer x x z hx hz hxx hxz

/-- A compact singleton is contained in itself, but it is not a neighborhood
of itself. Arbitrarily small nonzero perturbations rule out replacing an
open target by an arbitrary containing set, or by the intersection itself. -/
theorem compact_singleton_without_open_target :
    IsCompact ({0} : Set ℝ) ∧ ¬ IsOpen ({0} : Set ℝ) ∧
      ¬ ∃ ε : ℝ, 0 < ε ∧
        ∀ x : ℝ, ‖x - 0‖ < ε → ‖x - 0‖ < ε → x ∈ ({0} : Set ℝ) := by
  refine ⟨isCompact_singleton, not_isOpen_singleton 0, ?_⟩
  rintro ⟨ε, hε, htransfer⟩
  have hhalf : 0 < ε / 2 := half_pos hε
  have hclose : ‖ε / 2 - 0‖ < ε := by
    simpa only [sub_zero, Real.norm_eq_abs, abs_of_pos hhalf] using half_lt_self hε
  have hzero : ε / 2 = 0 := htransfer (ε / 2) hclose hclose
  exact (ne_of_gt hhalf) hzero

/-- A moving unit spike, indexed by the source and the generation. -/
def movingSpike (n i : ℕ) : ℝ := if i = n then 1 else 0

/-- Every fixed source converges to zero, but no generation threshold
works for all sources at tolerance one half. The positive named theorem
takes a finite fixed carrier before combining eventual statements. -/
theorem infinite_family_not_uniform :
    (∀ i : ℕ, Tendsto (fun n : ℕ => movingSpike n i) atTop (𝓝 0)) ∧
      ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : ℕ, ‖movingSpike n i‖ < (1 / 2 : ℝ) := by
  constructor
  · intro i
    have he : (fun n : ℕ => movingSpike n i) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
      apply eventually_atTop.mpr
      refine ⟨i + 1, ?_⟩
      intro n hn
      have hne : i ≠ n := ne_of_lt ((Nat.lt_succ_self i).trans_le hn)
      simp [movingSpike, hne]
    exact tendsto_const_nhds.congr' he.symm
  · rintro ⟨N, hN⟩
    have hbad := hN N le_rfl N
    norm_num [movingSpike] at hbad

end Psc.CompactNeighborhoodControls
