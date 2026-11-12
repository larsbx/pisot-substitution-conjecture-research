import PscVerif.NamedFullChart
import PscVerif.MadicFundamentalCell
import PscVerif.NamedCutProximity
import PscVerif.CompactNeighborhood

/-!
# Physical and internal widths of the named fundamental cells

The real part is the actual full named chart of the named incidence power.
The compact coordinate remains the original carrier for `M`, with the same
cell depth. Positive physical weights bound its real interval. One fixed
closed-cube bound, `beta`, and the existing block-twelve contraction bound
every stable coordinate uniformly. The residue kernels supply the other
part of the original product neighborhoods.

These width facts do not need an incidence compatibility assumption. The
separate fundamental-domain theorem retains that assumption when the real
and integer maps are bound together. No overlap or measure conclusion is
asserted here. Pre-code gate: the following-increment section of
`docs/c4-finite-cut-count.md`.
-/

namespace Psc.NamedCellBounds

open Set Filter Matrix
open Psc.NamedStableChart Psc.NamedFullChart Psc.MadicFundamentalCell
open scoped BigOperators Topology

/-- A finite physical width at each fixed cell depth. -/
noncomputable def physicalWidth (q : ℕ) : ℝ :=
  beta ^ q * ∑ i : Fin 3, physicalRow i

theorem physicalWidth_nonneg (q : ℕ) : 0 ≤ physicalWidth q := by
  exact mul_nonneg (pow_nonneg beta_pos.le q)
    (Finset.sum_nonneg fun i _ => (physical_row_pos i).le)

/-- Positive physical weights bound the whole closed coordinate cube. -/
theorem physical_on_closedCube {u : AmbientReal} (hu : u ∈ Icc 0 1) :
    0 ≤ physical u ∧ physical u ≤ ∑ i : Fin 3, physicalRow i := by
  change 0 ≤ ∑ i : Fin 3, physicalRow i * u i ∧
    (∑ i : Fin 3, physicalRow i * u i) ≤ ∑ i : Fin 3, physicalRow i
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (physical_row_pos i).le (hu.1 i)
  · exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_left (hu.2 i) (physical_row_pos i).le).trans_eq (mul_one _)

/-- One fixed bound for the stable image of the closed cube. This bound is
independent of the cell depth and of the original integer map. -/
theorem stable_on_closedCube {u : AmbientReal} (hu : u ∈ Icc 0 1) :
    ‖W *ᵥ u‖ ≤ beta := by
  have hcoord (i : Fin 3) : ‖u i‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    exact hu.2 i
  have ha : ‖a * u 1‖ ≤ a := by
    calc
      ‖a * u 1‖ = a * ‖u 1‖ := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos a_pos]
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left (hcoord 1) a_pos.le
      _ = a := mul_one a
  have hb : ‖b * u 1‖ ≤ b := by
    calc
      ‖b * u 1‖ = b * ‖u 1‖ := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos b_pos]
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left (hcoord 1) b_pos.le
      _ = b := mul_one b
  rw [W_mulVec]
  apply (pi_norm_le_iff_of_nonneg beta_pos.le).mpr
  intro i
  fin_cases i
  · change ‖u 0 - a * u 1‖ ≤ beta
    calc
      ‖u 0 - a * u 1‖ ≤ ‖u 0‖ + ‖a * u 1‖ := norm_sub_le _ _
      _ ≤ 1 + a := add_le_add (hcoord 0) ha
      _ ≤ beta := by linarith [a_add_b_add_one, b_pos]
  · change ‖u 2 - b * u 1‖ ≤ beta
    calc
      ‖u 2 - b * u 1‖ ≤ ‖u 2‖ + ‖b * u 1‖ := norm_sub_le _ _
      _ ≤ 1 + b := add_le_add (hcoord 2) hb
      _ ≤ beta := by linarith [a_add_b_add_one, a_pos]

theorem physical_realIncidence_pow (q : ℕ) (u : AmbientReal) :
    physical ((realIncidence ^ q) u) = beta ^ q * physical u := by
  induction q with
  | zero =>
      change physical u = 1 * physical u
      rw [one_mul]
  | succ q ih =>
      rw [pow_succ' realIncidence q, pow_succ' beta q]
      change physical (realIncidence ((realIncidence ^ q) u)) =
        (beta * beta ^ q) * physical u
      rw [realIncidence_apply, physical_eigen, ih, mul_assoc]

theorem stable_realIncidence_pow (q : ℕ) (u : AmbientReal) :
    W *ᵥ ((realIncidence ^ q) u) = (B ^ q) (W *ᵥ u) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [pow_succ' realIncidence q, pow_succ' B q]
      change W *ᵥ (realIncidence ((realIncidence ^ q) u)) =
        B ((B ^ q) (W *ᵥ u))
      rw [realIncidence_apply, B_apply, Matrix.mulVec_mulVec, WM_eq_BW,
        ← Matrix.mulVec_mulVec, ih]

variable (M : Int3 →ₗ[ℤ] Int3)

/-- Every actual cell point has a nonnegative physical coordinate in the
stated finite interval. -/
theorem cell_physical_bounds (q : ℕ)
    {x : (ℝ × Stable) × MadicResidue.Carrier M}
    (hx : x ∈ cell M realIncidence fullChart q) :
    0 ≤ x.1.1 ∧ x.1.1 ≤ physicalWidth q := by
  rcases hx.1 with ⟨_, ⟨u, hu, rfl⟩, he⟩
  have hp : physical ((realIncidence ^ q) u) = x.1.1 := congrArg Prod.fst he
  rw [← hp, physical_realIncidence_pow]
  obtain ⟨hu0, hub⟩ := physical_on_closedCube (coordinateCube_subset_Icc hu)
  exact ⟨mul_nonneg (pow_nonneg beta_pos.le q) hu0,
    mul_le_mul_of_nonneg_left hub (pow_nonneg beta_pos.le q)⟩

/-- The same closed-cube bound controls every point of every block cell. -/
theorem cell_block_stable_bound (n : ℕ)
    {x : (ℝ × Stable) × MadicResidue.Carrier M}
    (hx : x ∈ cell M realIncidence fullChart (12 * n)) :
    ‖x.1.2‖ ≤ (7 / 8 : ℝ) ^ n * beta := by
  rcases hx.1 with ⟨_, ⟨u, hu, rfl⟩, he⟩
  have hs : W *ᵥ ((realIncidence ^ (12 * n)) u) = x.1.2 := congrArg Prod.snd he
  rw [← hs, stable_realIncidence_pow]
  exact (NamedCutProximity.block_contract n _).trans
    (mul_le_mul_of_nonneg_left (stable_on_closedCube (coordinateCube_subset_Icc hu))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 8) n))

/-- A cell's actual depth kernel vanishes at every shallower residue depth. -/
theorem cell_eval_eq_zero_of_le {q m : ℕ} (hmq : m ≤ q)
    {x : (ℝ × Stable) × MadicResidue.Carrier M}
    (hx : x ∈ cell M realIncidence fullChart q) :
    MadicResidue.eval M m x.2 = 0 := by
  have hq : MadicResidue.eval M q x.2 = 0 := hx.2
  rw [← MadicResidue.reduction_eval M hmq x.2, hq, map_zero]

/-- The uniform stable envelope tends to zero; the physical width need not. -/
theorem block_error_tendsto_zero :
    Tendsto (fun n : ℕ => (7 / 8 : ℝ) ^ n * beta) atTop (𝓝 0) := by
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (7 / 8 : ℝ) < 1)).mul_const beta

/-- A single threshold places every later block cell's internal projection
in a prescribed stable ball and original-carrier residue kernel. -/
theorem eventually_cell_internal_zeroSlice (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x ∈ cell M realIncidence fullChart (12 * n),
        (x.1.2, x.2) ∈ CompactNeighborhood.zeroSlice M ε q := by
  have he : ∀ᶠ n : ℕ in atTop, (7 / 8 : ℝ) ^ n * beta < ε :=
    block_error_tendsto_zero.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N q, ?_⟩
  intro n hn x hx
  refine ⟨(cell_block_stable_bound M n hx).trans_lt
    (hN n ((le_max_left N q).trans hn)), cell_eval_eq_zero_of_le M ?_ hx⟩
  have hq : q ≤ n := (le_max_right N q).trans hn
  omega

/-- The whole internal cell projection shrinks in the original product
topology. The neighborhood is fixed before the cell-depth threshold. -/
theorem eventually_cell_internal_mem
    {V : Set (Stable × MadicResidue.Carrier M)} (hV : V ∈ 𝓝 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x ∈ cell M realIncidence fullChart (12 * n), (x.1.2, x.2) ∈ V := by
  obtain ⟨ε, hε, q, hslice⟩ := CompactNeighborhood.exists_zeroSlice_subset M hV
  obtain ⟨N, hN⟩ := eventually_cell_internal_zeroSlice M q ε hε
  exact ⟨N, fun n hn x hx => hslice (hN n hn x hx)⟩

end Psc.NamedCellBounds
