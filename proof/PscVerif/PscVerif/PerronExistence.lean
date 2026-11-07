/-
# Perron–Frobenius for primitive matrices

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`: hypothesis `H1` (`M_σ ^ k > 0`
entrywise for some `k ≥ 1`) and the Perron–Frobenius eigenvalue `β` of `H3`; the
paragraph before `lem:Zindep` ("Let `ℓ ∈ ℝ^d_{>0}` be a left Perron eigenvector,
`ℓᵀ M_σ = β ℓᵀ`"); the last sentence of the proof of `thm:parikh` (`λᵀ N_C = β λᵀ`
with `λ > 0`, hence `ρ(N_C) = β`); the clause `ρ(S) ≤ β` of `prop:cocycle`; and
the step of `lem:aperiodic` ("since `M^q` is primitive, a nonnegative eigenvector
belongs to the Perron eigenvalue").  The manuscript takes Perron–Frobenius from
`BermanPlemmons` and `HornJohnson`; the argument here is Collatz–Wielandt's (as in
Seneta, *Non-negative matrices and Markov chains*, Thm 1.1, an external source not
cited by the manuscript).  `docs/c4-concentration-attack-2026-11-06.md` §8.

Mathlib has `Matrix.IsPrimitive` but no Perron–Frobenius theorem.  The modules
`PscVerif.PerronCore`, `PscVerif.ParikhIntertwiner`, `PscVerif.PerronSimple`,
`PscVerif.Wielandt` and `PscVerif.SignedCocycle` take the positive left eigenvector
as a hypothesis; this module supplies it for a primitive matrix.  Primitivity is used
in the form of `H1` and `PscVerif.PrimitiveExpansion`: `∃ k ≥ 1, ∀ i j, 0 < (A ^ k) i j`.
The incidence matrix is `Psc.Incidence.inc s a c = (s c).count a`, the manuscript's
`M_ij = |σ(j)|_i`, so `ℓ ᵥ* M = β • ℓ` is `ℓᵀ M = β ℓᵀ`.

Proof of existence (Collatz–Wielandt, row-vector form).  With `B = A ^ k > 0` and the
standard simplex `Δ` (`simplex`, compact), every `y = x B`, `x ∈ Δ`, is strictly
positive (`vecMul_pos`), so `F x = min_j ((x B) A)_j / (x B)_j` is continuous on `Δ`;
let `x` maximize it, `y = x B`, `r = F x`.  Then `r y ≤ y A`.  If `z = y A - r y ≠ 0`
then `z ≥ 0` gives `z B > 0`, and the normalised `x' = y / ∑ y ∈ Δ` has
`(x' B) A - r (x' B) = (z B) / ∑ y > 0` (`A` and `B` commute), i.e. `F x' > r`: a
contradiction.  So `y A = r y`, `y > 0`; `r ≥ 0` from `A ≥ 0`
(`Psc.PerronCore.beta_nonneg`), and `r ≠ 0` since otherwise `y A ^ k = 0`.

Proved here, in full:

* `simplex`, `isCompact_simplex`, `single_mem_simplex`, `ne_zero_of_mem_simplex`: the
  standard simplex of `ι → ℝ` (a local copy: Mathlib's `stdSimplex` is deprecated);
  `dotProduct_pos_of_nonneg`, `vecMul_pos`, `ne_zero_of_pos`, `transpose_pow_pos`;
* `exists_pos_left_eigen_of_nonempty` (the argument above) and
  **`exists_pos_left_eigen`**: for `A ≥ 0` with `A ^ k > 0`, `k ≥ 1`, there are `r > 0`
  and `v > 0` with `v ᵥ* A = r • v`; `exists_pos_right_eigen`: `A *ᵥ u = r • u`, via
  `Aᵀ`; `exists_pos_left_eigen_of_isPrimitive`: the same from `Matrix.IsPrimitive`;
* without primitivity, for a strictly positive left eigenvector `v ᵥ* A = r • v`:
  `isRoot_ofReal_of_left_eigen` (`r` is a root of the complexified `χ_A`);
  **`norm_le_of_pos_left_eigen`** (`A ≥ 0`: every complex root `μ` of `χ_A` has
  `‖μ‖ ≤ r`, via `Psc.ParikhIntertwiner.spectral_bound`);
  **`eigenvalue_eq_of_pos_left_eigen`** (`A ≥ 0`: two positive left eigenvectors have
  the same eigenvalue); `colSum_bounds` (`A ≥ 0`: `r` lies between the least and the
  greatest column sum); `eigenvalue_eq_of_dotProduct_ne_zero` (a left and a right
  eigenvector with `x ⬝ y ≠ 0` share their eigenvalue) and
  **`eigenvalue_pow_eq_of_nonneg_right_eigen`** (`lem:aperiodic`'s step: a nonzero
  nonnegative right eigenvector of `A ^ n` has eigenvalue `r ^ n`; no `A ≥ 0`);
* with `A ^ k > 0` (neither `A ≥ 0` nor `k ≥ 1` used): `vecMul_pow_of_left_eigen`;
  **`eq_smul_of_left_eigen`** (the real left eigenspace of the eigenvalue of a positive
  left eigenvector `w` is the line `ℝ w`); `pos_of_eq_smul`;
  `eq_smul_of_pos_left_eigen` (positive multiples);
* `PerronData A r v u` and **`perron_frobenius`**: for `A ≥ 0` primitive on a nonempty
  `ι` there are `r > 0`, `v > 0`, `u > 0` with `v ᵥ* A = r • v`, `A *ᵥ u = r • u`,
  `χ_A(r) = 0`, every complex root of `χ_A` of modulus `≤ r` (so `r = ρ(A)`), the real
  left and right `r`-eigenspaces equal to `ℝ v` and `ℝ u`, and every nonzero
  nonnegative left (right) eigenvector of `A` with eigenvalue `r` and a positive
  multiple of `v` (`u`); `perron_frobenius_of_isPrimitive`;
* `inc_cast_primitive`, **`exists_pos_left_eigen_inc`** (`ℓ > 0` with
  `ℓ ᵥ* (inc s).map Nat.cast = β • ℓ`: the hypotheses `hℓ`, `hℓN` of
  `Psc.ParikhIntertwiner.spectral_bound_childSystem`, `perron_root_childSystem` and
  `Psc.SignedCocycle.Normalisation.cocycle_spectral_bound`), and **`perron_inc`**
  (`PerronData` of the incidence matrix, the root bound for its `ℕ → ℂ` cast, and
  `lem:aperiodic`'s step for its powers);
* consumers, each with `β` the Perron root of `M` (`PerronData` of `inc S.s`):
  **`perron_root_childSystem_of_primitive`** (`ρ(Nc) = β` for the raw ordered state
  matrix `Psc.ParikhIntertwiner.Nc`, which for a swap-closed system is the oriented
  double cover); **`perron_root_rep_of_primitive`** (`ρ(N_C) = β` for the manuscript's
  `N_C = A + B` on normalised representatives, `Psc.SignedCocycle.Normalisation.Nrep`,
  for balanced states: the last clause of `thm:parikh`, together with the positive left
  `β`-eigenvector `L` of `N_C` that `Psc.CocycleSpectrum` assumes as `hL`, `hLN`);
  **`cocycle_spectral_bound_of_primitive`** (`ρ(S) ≤ β` of `prop:cocycle`, no balance);
* controls: `A0_pos`, `m0_hyp`, `A0_isPrimitive`, `m0_perron`, `m0_hyps` (the matrix
  `[[5,21,1],[6,26,1],[6,24,1]]` of `PscVerif.ConcentrationControls`, `k = 1`; its
  `PerronData` meets the hypotheses of every theorem of the third and fourth items);
  `sigma_primitive`, `sigma_perron` (the substitution `0 ↦ 011`, `1 ↦ 2`, `2 ↦ 120` of
  `PscVerif.ConcentrationControls`: primitive with `k = 2`, not with `k = 1`);
  `thueMorse_perron_root` (the Thue–Morse child system meets every hypothesis of the
  three consumers, with `Psc.SignedCocycle.thueMorseNorm`), `thueMorse_beta` (there the
  Perron root is `2`), `thueMorse_perron_rep`;
* negative controls: `neg_nonneg_needed` (`A = (-1)`, `A ^ 2 > 0`) and
  `neg_exponent_needed` (`A = (0)`, `A ^ 0 > 0`) have no positive left eigenvector with
  positive eigenvalue, so neither `A ≥ 0` nor `k ≥ 1` can be dropped from
  `exists_pos_left_eigen`; `neg_primitive_needed` (`A = 1 ≥ 0` on two letters, no power
  positive) has non-proportional positive left eigenvectors for `1`, so `A ^ k > 0`
  cannot be dropped from `eq_smul_of_left_eigen` or `eq_smul_of_pos_left_eigen`;
  `neg_nonneg_eigenvector_needed` (`A = [[1,1],[1,1]]`, the right eigenvector `(1, -1)`
  for `0`) shows that `w ≥ 0` cannot be dropped from
  `eigenvalue_pow_eq_of_nonneg_right_eigen`.

Not proved here:

* strict dominance `‖μ‖ < r` for the roots `μ ≠ r` of a primitive `A` (only `‖μ‖ ≤ r`),
  and algebraic simplicity of `r` as a root of `χ_A` (geometric simplicity is
  `PerronData.left_line`, `PerronData.right_line`);
* the equality case of the comparison (Seneta Thm 1.1(e): `|B| ≤ A` entrywise with an
  eigenvalue of modulus `r` forces `|B| = A`).  `Psc.PerronCore.norm_eigen_pos` proves
  it for strongly connected `A`, and `Psc.CocycleSpectrum.stronglyConnected_of_pow_pos`
  derives strong connectivity from primitivity; the two are not combined here;
* the irreducible non-primitive case of Perron–Frobenius.  The manuscript's `N_C` is
  only irreducible; `perron_root_rep_of_primitive` needs no irreducibility of `N_C`
  (its positive eigenvector `L` is pulled back from `ℓ`), but it assumes balance
  (`hbal`; the nonempty top tracks follow, `Psc.SignedCocycle.Normalisation.top_ne_nil`)
  and `C ≠ ∅`, and gives no uniqueness of `L`;
* that a child system is the manuscript's zero-return system
  (`Psc.Reduction.redNormalisation`, not used here), and anything about `r > 1` or the
  Pisot property.
-/
import PscVerif.PerronCore
import PscVerif.ParikhIntertwiner
import PscVerif.SignedCocycle
import PscVerif.M0Pisot
import PscVerif.ConcentrationControls
import PscVerif.PrimitiveExpansion
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Order.Field

namespace Psc.PerronExistence

open Matrix Finset

variable {ι : Type*} [Fintype ι]

/-! ### The standard simplex and positivity -/

/-- The standard simplex of `ι → ℝ`. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem isCompact_simplex : IsCompact (simplex ι) := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := 0) (b := 1)) ?_ fun x hx => ?_
  · exact (isClosed_Ici (a := (0 : ι → ℝ))).inter (isClosed_eq (by fun_prop) continuous_const)
  · exact ⟨hx.1, fun i => (single_le_sum (fun j _ => hx.1 j) (mem_univ i)).trans_eq hx.2⟩

theorem single_mem_simplex [DecidableEq ι] (i : ι) : Pi.single i 1 ∈ simplex ι :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩

theorem ne_zero_of_mem_simplex {x : ι → ℝ} (hx : x ∈ simplex ι) : x ≠ 0 := by
  rintro rfl; simp [simplex] at hx

/-- A strictly positive row paired with a nonzero nonnegative one is positive. -/
theorem dotProduct_pos_of_nonneg {v w : ι → ℝ} (hv : ∀ i, 0 < v i) (hw0 : ∀ i, 0 ≤ w i)
    (hw : w ≠ 0) : 0 < v ⬝ᵥ w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  exact sum_pos' (fun i _ => mul_nonneg (hv i).le (hw0 i))
    ⟨i, mem_univ i, mul_pos (hv i) ((hw0 i).lt_of_ne' hi)⟩

/-- A nonzero nonnegative row times an entrywise positive matrix is positive. -/
theorem vecMul_pos {B : Matrix ι ι ℝ} (hB : ∀ i j, 0 < B i j) {x : ι → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx : x ≠ 0) (j : ι) : 0 < (x ᵥ* B) j := by
  have h := dotProduct_pos_of_nonneg (fun i => hB i j) hx0 hx
  rwa [dotProduct_comm] at h

omit [Fintype ι] in
theorem ne_zero_of_pos [Nonempty ι] {v : ι → ℝ} (hv : ∀ i, 0 < v i) : v ≠ 0 :=
  Function.ne_iff.2 ⟨Classical.arbitrary ι, (hv _).ne'⟩

variable [DecidableEq ι]

theorem transpose_pow_pos {A : Matrix ι ι ℝ} {k : ℕ} (hk : ∀ i j, 0 < (A ^ k) i j)
    (i j : ι) : 0 < (Aᵀ ^ k) i j := by
  rw [← transpose_pow]; exact hk j i

/-! ### Existence -/

/-- The Collatz–Wielandt argument on a nonempty index type. -/
theorem exists_pos_left_eigen_of_nonempty [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : ∀ i j, 0 ≤ A i j) {k : ℕ} (hk1 : 1 ≤ k) (hk : ∀ i j, 0 < (A ^ k) i j) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ v ᵥ* A = r • v := by
  have hne : (univ : Finset ι).Nonempty := univ_nonempty
  have hcomm : ∀ w : ι → ℝ, w ᵥ* A ^ k ᵥ* A = w ᵥ* A ᵥ* A ^ k := fun w => by
    rw [vecMul_vecMul, vecMul_vecMul, ← pow_succ, pow_succ']
  have hpos : ∀ x ∈ simplex ι, ∀ j, 0 < (x ᵥ* A ^ k) j := fun x hx =>
    vecMul_pos hk hx.1 (ne_zero_of_mem_simplex hx)
  let F : (ι → ℝ) → ℝ := fun x =>
    univ.inf' hne fun j => (x ᵥ* A ^ k ᵥ* A) j / (x ᵥ* A ^ k) j
  have hF : ContinuousOn F (simplex ι) :=
    ContinuousOn.finset_inf'_apply hne fun j _ =>
      ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (hpos x hx j).ne'
  obtain ⟨x, hx, hmax⟩ := isCompact_simplex.exists_isMaxOn
    ⟨_, single_mem_simplex (Classical.arbitrary ι)⟩ hF
  set y := x ᵥ* A ^ k
  set r := F x
  have hy0 : ∀ j, 0 < y j := hpos x hx
  have hle : ∀ j, r * y j ≤ (y ᵥ* A) j := fun j =>
    (le_div_iff₀ (hy0 j)).1 (inf'_le _ (mem_univ j))
  -- the gap `z = y A - r y` vanishes
  have hz : y ᵥ* A - r • y = 0 := by
    by_contra hz
    have hz0 : ∀ j, 0 ≤ (y ᵥ* A - r • y) j := fun j => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linarith [hle j]
    have hgap : ∀ j, r * (y ᵥ* A ^ k) j < (y ᵥ* A ᵥ* A ^ k) j := fun j => by
      have := vecMul_pos hk hz0 hz j
      rw [sub_vecMul, smul_vecMul] at this
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    set c := ∑ i, y i
    have hc : 0 < c := sum_pos (fun i _ => hy0 i) hne
    have hx' : c⁻¹ • y ∈ simplex ι :=
      ⟨fun i => mul_nonneg (inv_nonneg.2 hc.le) (hy0 i).le, by
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]; exact inv_mul_cancel₀ hc.ne'⟩
    refine not_lt.2 (show F (c⁻¹ • y) ≤ r from hmax hx') ((lt_inf'_iff _).2 fun j _ => ?_)
    rw [lt_div_iff₀ (hpos _ hx' j), smul_vecMul, smul_vecMul, hcomm]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc r * (c⁻¹ * (y ᵥ* A ^ k) j) = c⁻¹ * (r * (y ᵥ* A ^ k) j) := by ring
      _ < c⁻¹ * (y ᵥ* A ᵥ* A ^ k) j := mul_lt_mul_of_pos_left (hgap j) (inv_pos.2 hc)
  have hyA : y ᵥ* A = r • y := sub_eq_zero.1 hz
  obtain ⟨j⟩ := ‹Nonempty ι›
  refine ⟨r, (Psc.PerronCore.beta_nonneg A hA y hy0 r hyA j).lt_of_ne fun h => ?_, y, hy0, hyA⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk1
  have h0 : y ᵥ* A ^ (m + 1) = 0 := by
    rw [pow_succ', ← vecMul_vecMul, hyA, ← h, zero_smul, zero_vecMul]
  exact (vecMul_pos hk (fun i => (hy0 i).le) (ne_zero_of_pos hy0) j).ne' (congrFun h0 j)

/-- **Perron–Frobenius existence, row form.**  A nonnegative matrix with a
strictly positive power `A ^ k`, `k ≥ 1`, has a strictly positive left
eigenvector `v ᵥ* A = r • v` with `r > 0`. -/
theorem exists_pos_left_eigen (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hprim : ∃ k ≥ 1, ∀ i j, 0 < (A ^ k) i j) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ v ᵥ* A = r • v := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, 0, isEmptyElim, funext isEmptyElim⟩
  · obtain ⟨k, hk1, hk⟩ := hprim
    exact exists_pos_left_eigen_of_nonempty A hA hk1 hk

/-- **Perron–Frobenius existence, column form**, via `Aᵀ`. -/
theorem exists_pos_right_eigen (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hprim : ∃ k ≥ 1, ∀ i j, 0 < (A ^ k) i j) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : ι → ℝ, (∀ i, 0 < u i) ∧ A *ᵥ u = r • u := by
  obtain ⟨k, hk1, hk⟩ := hprim
  obtain ⟨r, hr, u, hu, huA⟩ :=
    exists_pos_left_eigen Aᵀ (fun i j => hA j i) ⟨k, hk1, transpose_pow_pos hk⟩
  exact ⟨r, hr, u, hu, by rwa [vecMul_transpose] at huA⟩

/-- `exists_pos_left_eigen` for Mathlib's `Matrix.IsPrimitive`. -/
theorem exists_pos_left_eigen_of_isPrimitive (A : Matrix ι ι ℝ) (h : A.IsPrimitive) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ v ᵥ* A = r • v :=
  exists_pos_left_eigen A h.nonneg h.exists_pos_pow

/-! ### Consequences of one positive left eigenvector -/

/-- A nonzero real left eigenvector makes its eigenvalue a root of the
complexified characteristic polynomial. -/
theorem isRoot_ofReal_of_left_eigen (A : Matrix ι ι ℝ) (v : ι → ℝ) (hv0 : v ≠ 0) (r : ℝ)
    (hv : v ᵥ* A = r • v) : (A.map ((↑) : ℝ → ℂ)).charpoly.eval (r : ℂ) = 0 := by
  have h := Psc.ConcentrationAlgebra.isRoot_of_left_eigen A r v hv0 hv
  rw [show A.map ((↑) : ℝ → ℂ) = A.map Complex.ofRealHom from rfl, charpoly_map,
    Polynomial.eval_map, show (r : ℂ) = Complex.ofRealHom r from rfl,
    Polynomial.eval₂_at_apply, h, map_zero]

/-- **Spectral bound** (no primitivity): if `A ≥ 0` has a strictly positive left
eigenvector `w ᵥ* A = s • w`, every complex root `μ` of `χ_A` has `‖μ‖ ≤ s`. -/
theorem norm_le_of_pos_left_eigen (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (s : ℝ) (hwA : w ᵥ* A = s • w) (μ : ℂ)
    (hμ : (A.map ((↑) : ℝ → ℂ)).charpoly.eval μ = 0) : ‖μ‖ ≤ s := by
  obtain ⟨x, hx0, hx⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot _ μ hμ
  exact Psc.ParikhIntertwiner.spectral_bound A w hw s hwA _
    (fun i j => by simp [abs_of_nonneg (hA i j)]) x hx0 μ hx

/-- **Uniqueness of the positive eigenvalue** (no primitivity): two strictly
positive left eigenvectors of `A ≥ 0` have the same eigenvalue. -/
theorem eigenvalue_eq_of_pos_left_eigen [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (v w : ι → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (r s : ℝ) (hvA : v ᵥ* A = r • v) (hwA : w ᵥ* A = s • w) : r = s := by
  have h1 := norm_le_of_pos_left_eigen A hA w hw s hwA _
    (isRoot_ofReal_of_left_eigen A v (ne_zero_of_pos hv) r hvA)
  have h2 := norm_le_of_pos_left_eigen A hA v hv r hvA _
    (isRoot_ofReal_of_left_eigen A w (ne_zero_of_pos hw) s hwA)
  rw [Complex.norm_real, Real.norm_eq_abs] at h1 h2
  linarith [le_abs_self r, le_abs_self s]

omit [DecidableEq ι] in
/-- **Column-sum bounds** (no primitivity): if `A ≥ 0` has a strictly positive
left eigenvector for `r`, some column sum of `A` is `≤ r` and some is `≥ r`
(look at a least and a greatest entry of the eigenvector). -/
theorem colSum_bounds [Nonempty ι] (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {r : ℝ} (hvA : v ᵥ* A = r • v) :
    (∃ j, ∑ i, A i j ≤ r) ∧ ∃ j, r ≤ ∑ i, A i j := by
  have hr : ∀ j, r * v j = ∑ i, v i * A i j := fun j => (congrFun hvA j).symm
  obtain ⟨j₀, -, h₀⟩ := exists_min_image univ v univ_nonempty
  obtain ⟨j₁, -, h₁⟩ := exists_max_image univ v univ_nonempty
  refine ⟨⟨j₀, le_of_mul_le_mul_right ?_ (hv j₀)⟩, ⟨j₁, le_of_mul_le_mul_right ?_ (hv j₁)⟩⟩
  · rw [hr, sum_mul]
    exact sum_le_sum fun i _ => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (h₀ i (mem_univ i)) (hA i j₀)
  · rw [hr, sum_mul]
    exact sum_le_sum fun i _ => by
      rw [mul_comm (A i j₁)]; exact mul_le_mul_of_nonneg_right (h₁ i (mem_univ i)) (hA i j₁)

omit [DecidableEq ι] in
/-- A left and a right eigenvector with nonzero pairing share their eigenvalue:
`s (x ⬝ y) = x ⬝ (A y) = (x A) ⬝ y = r (x ⬝ y)`. -/
theorem eigenvalue_eq_of_dotProduct_ne_zero (A : Matrix ι ι ℝ) {x y : ι → ℝ} {r s : ℝ}
    (hx : x ᵥ* A = r • x) (hy : A *ᵥ y = s • y) (hxy : x ⬝ᵥ y ≠ 0) : s = r := by
  have h := dotProduct_mulVec x A y
  rw [hy, hx, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h
  exact mul_right_cancel₀ hxy h

/-- Powers of a left eigen-row: `x ᵥ* A ^ n = r ^ n • x`. -/
theorem vecMul_pow_of_left_eigen (A : Matrix ι ι ℝ) (x : ι → ℝ) (r : ℝ)
    (hx : x ᵥ* A = r • x) (n : ℕ) : x ᵥ* A ^ n = r ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← vecMul_vecMul, hx, smul_vecMul, ih, smul_smul, pow_succ']

/-- **A nonnegative eigenvector belongs to the Perron root** (`lem:aperiodic`; no
primitivity, no `A ≥ 0`): if `v > 0` and `v ᵥ* A = r • v`, every nonzero
nonnegative right eigenvector of `A ^ n` has eigenvalue `r ^ n`. -/
theorem eigenvalue_pow_eq_of_nonneg_right_eigen (A : Matrix ι ι ℝ) {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) {r : ℝ} (hvA : v ᵥ* A = r • v) (n : ℕ) {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw : w ≠ 0) {s : ℝ} (hwA : A ^ n *ᵥ w = s • w) : s = r ^ n :=
  eigenvalue_eq_of_dotProduct_ne_zero _ (vecMul_pow_of_left_eigen A v r hvA n) hwA
    (dotProduct_pos_of_nonneg hv hw0 hw).ne'

/-! ### Uniqueness under primitivity -/

/-- **The eigenspace is a line** (needs neither `A ≥ 0` nor `k ≥ 1`): if
`A ^ k > 0` and `w > 0` is a left eigenvector for `r`, every real left
eigenvector `x` for `r` is a multiple of `w`.  With `t = min_i x i / w i`, the
row `x - t w ≥ 0` is a left eigenvector with a zero entry, so it cannot be
nonzero (`(x - t w) A ^ k = r ^ k (x - t w)` would be strictly positive). -/
theorem eq_smul_of_left_eigen (A : Matrix ι ι ℝ) {k : ℕ} (hk : ∀ i j, 0 < (A ^ k) i j)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) {r : ℝ} (hwA : w ᵥ* A = r • w) (x : ι → ℝ)
    (hxA : x ᵥ* A = r • x) : ∃ t : ℝ, x = t • w := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, funext isEmptyElim⟩
  set t := univ.inf' univ_nonempty fun i => x i / w i
  obtain ⟨i₀, -, hi₀⟩ := exists_mem_eq_inf' univ_nonempty fun i => x i / w i
  have hd0 : ∀ i, 0 ≤ (x - t • w) i := fun i => by
    have := (le_div_iff₀ (hw i)).1 (inf'_le (fun i => x i / w i) (mem_univ i))
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linarith
  have hdi : (x - t • w) i₀ = 0 := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, show t = x i₀ / w i₀ from hi₀,
      div_mul_cancel₀ _ (hw i₀).ne', sub_self]
  have hdA : (x - t • w) ᵥ* A = r • (x - t • w) := by
    rw [sub_vecMul, smul_vecMul, hxA, hwA, smul_sub, smul_comm]
  refine ⟨t, sub_eq_zero.1 (by_contra fun hd => ?_)⟩
  have := vecMul_pos hk hd0 hd i₀
  rw [vecMul_pow_of_left_eigen A _ r hdA, Pi.smul_apply, hdi, smul_zero] at this
  exact lt_irrefl _ this

omit [Fintype ι] [DecidableEq ι] in
/-- A nonzero nonnegative multiple `w = t • v` of a strictly positive `v` has
`t > 0`. -/
theorem pos_of_eq_smul {v w : ι → ℝ} (hv : ∀ i, 0 < v i) (hw0 : ∀ i, 0 ≤ w i)
    (hw : w ≠ 0) {t : ℝ} (ht : w = t • v) : 0 < t := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have h : 0 < t * v i := by simpa [ht] using (hw0 i).lt_of_ne' hi
  exact (pos_iff_pos_of_mul_pos h).2 (hv i)

/-- **Uniqueness of the positive eigenvector up to scaling** (needs neither
`A ≥ 0` nor `k ≥ 1`): if `A ^ k > 0`, two strictly positive left eigenvectors of
`A` for the same eigenvalue are positive multiples of each other. -/
theorem eq_smul_of_pos_left_eigen (A : Matrix ι ι ℝ) {k : ℕ} (hk : ∀ i j, 0 < (A ^ k) i j)
    (v w : ι → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i) (r : ℝ)
    (hvA : v ᵥ* A = r • v) (hwA : w ᵥ* A = r • w) : ∃ t : ℝ, 0 < t ∧ v = t • w := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, funext isEmptyElim⟩
  obtain ⟨t, ht⟩ := eq_smul_of_left_eigen A hk hw hwA v hvA
  exact ⟨t, pos_of_eq_smul hw (fun i => (hv i).le) (ne_zero_of_pos hv) ht, ht⟩

/-! ### Perron–Frobenius for a primitive matrix -/

/-- **Perron data** of `A`: the Perron root `r`, a positive left eigenvector `v`
and a positive right eigenvector `u`, with the spectral and uniqueness clauses
of the Perron–Frobenius theorem for a primitive matrix. -/
structure PerronData (A : Matrix ι ι ℝ) (r : ℝ) (v u : ι → ℝ) : Prop where
  pos : 0 < r
  left_pos : ∀ i, 0 < v i
  left : v ᵥ* A = r • v
  right_pos : ∀ i, 0 < u i
  right : A *ᵥ u = r • u
  /-- `r` is a root of `χ_A`. -/
  isRoot : A.charpoly.eval r = 0
  /-- `r = ρ(A)`: every complex root of `χ_A` has modulus at most `r`. -/
  norm_le : ∀ μ : ℂ, (A.map ((↑) : ℝ → ℂ)).charpoly.eval μ = 0 → ‖μ‖ ≤ r
  /-- The real left `r`-eigenspace is `ℝ v`. -/
  left_line : ∀ x : ι → ℝ, x ᵥ* A = r • x → ∃ t : ℝ, x = t • v
  /-- The real right `r`-eigenspace is `ℝ u`. -/
  right_line : ∀ x : ι → ℝ, A *ᵥ x = r • x → ∃ t : ℝ, x = t • u
  /-- A nonzero nonnegative left eigenvector belongs to `r` and lies on `ℝ_{>0} v`. -/
  left_nonneg : ∀ (s : ℝ) (w : ι → ℝ), (∀ i, 0 ≤ w i) → w ≠ 0 → w ᵥ* A = s • w →
    s = r ∧ ∃ t : ℝ, 0 < t ∧ w = t • v
  /-- A nonzero nonnegative right eigenvector belongs to `r` and lies on `ℝ_{>0} u`. -/
  right_nonneg : ∀ (s : ℝ) (w : ι → ℝ), (∀ i, 0 ≤ w i) → w ≠ 0 → A *ᵥ w = s • w →
    s = r ∧ ∃ t : ℝ, 0 < t ∧ w = t • u

/-- **Perron–Frobenius for a primitive matrix.**  A nonnegative matrix `A` with
`A ^ k > 0` for some `k ≥ 1`, on a nonempty index type, has Perron data. -/
theorem perron_frobenius [Nonempty ι] (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hprim : ∃ k ≥ 1, ∀ i j, 0 < (A ^ k) i j) : ∃ r v u, PerronData A r v u := by
  obtain ⟨r, hr, v, hv, hvA⟩ := exists_pos_left_eigen A hA hprim
  obtain ⟨r', -, u, hu, huA⟩ := exists_pos_right_eigen A hA hprim
  rw [eigenvalue_eq_of_dotProduct_ne_zero A hvA huA
    (dotProduct_pos_of_nonneg hv (fun i => (hu i).le) (ne_zero_of_pos hu)).ne'] at huA
  obtain ⟨k, -, hk⟩ := hprim
  have hline := eq_smul_of_left_eigen A hk hv hvA
  have hlineT : ∀ x : ι → ℝ, A *ᵥ x = r • x → ∃ t : ℝ, x = t • u := fun x hx =>
    eq_smul_of_left_eigen Aᵀ (transpose_pow_pos hk) hu (by rw [vecMul_transpose, huA]) x
      (by rw [vecMul_transpose, hx])
  refine ⟨r, v, u, hr, hv, hvA, hu, huA,
    Psc.ConcentrationAlgebra.isRoot_of_left_eigen A r v (ne_zero_of_pos hv) hvA,
    norm_le_of_pos_left_eigen A hA v hv r hvA, hline, hlineT,
    fun s w hw0 hw hwA => ?_, fun s w hw0 hw hwA => ?_⟩
  · have hs : s = r := (eigenvalue_eq_of_dotProduct_ne_zero A hwA huA
      (by rw [dotProduct_comm]; exact (dotProduct_pos_of_nonneg hu hw0 hw).ne')).symm
    obtain ⟨t, ht⟩ := hline w (hs ▸ hwA)
    exact ⟨hs, t, pos_of_eq_smul hv hw0 hw ht, ht⟩
  · have hs : s = r := eigenvalue_eq_of_dotProduct_ne_zero A hvA hwA
      (dotProduct_pos_of_nonneg hv hw0 hw).ne'
    obtain ⟨t, ht⟩ := hlineT w (hs ▸ hwA)
    exact ⟨hs, t, pos_of_eq_smul hu hw0 hw ht, ht⟩

/-- `perron_frobenius` for Mathlib's `Matrix.IsPrimitive`. -/
theorem perron_frobenius_of_isPrimitive [Nonempty ι] (A : Matrix ι ι ℝ) (h : A.IsPrimitive) :
    ∃ r v u, PerronData A r v u :=
  perron_frobenius A h.nonneg h.exists_pos_pow

/-! ### The incidence matrix of a primitive substitution -/

section Incidence

open Psc.Incidence Psc.Binomial Psc.ParikhIntertwiner Psc.SignedCocycle

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The real incidence matrix of a substitution with primitive incidence matrix
is nonnegative and primitive. -/
theorem inc_cast_primitive (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) :
    (∀ a c, 0 ≤ (inc s).map (Nat.cast : ℕ → ℝ) a c) ∧
      ∃ k ≥ 1, ∀ a c, 0 < ((inc s).map (Nat.cast : ℕ → ℝ) ^ k) a c := by
  obtain ⟨k, hk1, hk⟩ := hprim
  refine ⟨fun a c => Nat.cast_nonneg _, k, hk1, fun a c => ?_⟩
  rw [show (inc s).map (Nat.cast : ℕ → ℝ) = (inc s).map (Nat.castRingHom ℝ) from rfl,
    ← Matrix.map_pow, Matrix.map_apply]
  exact Nat.cast_pos.2 (hk a c)

/-- **The positive left Perron eigenvector of a primitive incidence matrix**, in
the hypothesis shape (`hℓ`, `hℓN`) of
`Psc.ParikhIntertwiner.spectral_bound_childSystem`,
`Psc.ParikhIntertwiner.perron_root_childSystem` and
`Psc.SignedCocycle.Normalisation.cocycle_spectral_bound`. -/
theorem exists_pos_left_eigen_inc (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) :
    ∃ β : ℝ, 0 < β ∧ ∃ ℓ : α → ℝ, (∀ a, 0 < ℓ a) ∧
      ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ :=
  exists_pos_left_eigen _ (inc_cast_primitive s hprim).1 (inc_cast_primitive s hprim).2

/-- **Perron–Frobenius for a primitive incidence matrix** `N` on a nonempty
alphabet: `PerronData` of `N` (so `β = ρ(N)`, and `ℓ > 0` is unique up to positive
scaling), the root bound for the `ℕ → ℂ` cast of `N`, and the step of
`lem:aperiodic`: a nonzero nonnegative right eigenvector of `N ^ q` has
eigenvalue `β ^ q`. -/
theorem perron_inc [Nonempty α] (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) :
    ∃ (β : ℝ) (ℓ u : α → ℝ), PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) β ℓ u ∧
      (∀ μ : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval μ = 0 → ‖μ‖ ≤ β) ∧
      ∀ (q : ℕ) (κ : ℝ) (w : α → ℝ), (∀ a, 0 ≤ w a) → w ≠ 0 →
        (inc s).map (Nat.cast : ℕ → ℝ) ^ q *ᵥ w = κ • w → κ = β ^ q := by
  obtain ⟨β, ℓ, u, h⟩ :=
    perron_frobenius _ (inc_cast_primitive s hprim).1 (inc_cast_primitive s hprim).2
  have hc : ((inc s).map (Nat.cast : ℕ → ℝ)).map ((↑) : ℝ → ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by
    ext; simp
  exact ⟨β, ℓ, u, h, fun μ hμ => h.norm_le μ (hc ▸ hμ), fun q κ w hw0 hw hwA =>
    eigenvalue_pow_eq_of_nonneg_right_eigen _ h.left_pos h.left q hw0 hw hwA⟩

omit [Fintype α] in
/-- A nonempty top track of a state gives a letter. -/
theorem nonempty_of_tracks {S : ChildSystem α} (hne : ∀ T ∈ S.C, T.1 ≠ [])
    (hC : S.C.Nonempty) : Nonempty α := by
  obtain ⟨T, hT⟩ := hC
  obtain ⟨a, -⟩ := List.exists_mem_of_ne_nil _ (hne T hT)
  exact ⟨a⟩

/-- **`ρ(Nc) = β` for a child system of a primitive substitution**, with `β` the
Perron root of the incidence matrix `M`: `PerronData` of `M`, `β` is an eigenvalue
of the raw ordered state matrix `Nc`, and every complex eigenvalue of `Nc` has
modulus at most `β`.  `Nc` counts raw ordered children; for a swap-closed system
it is the oriented double cover, not the manuscript's `N_C = A + B`
(`perron_root_rep_of_primitive`). -/
theorem perron_root_childSystem_of_primitive (S : ChildSystem α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c) (hne : ∀ T ∈ S.C, T.1 ≠ [])
    (hC : S.C.Nonempty) :
    ∃ (β : ℝ) (ℓ u : α → ℝ), PerronData ((inc S.s).map (Nat.cast : ℕ → ℝ)) β ℓ u ∧
      (∃ v : State S → ℝ, v ≠ 0 ∧ (Nc S).map (Nat.cast : ℕ → ℝ) *ᵥ v = β • v) ∧
      ∀ x : State S → ℂ, x ≠ 0 → ∀ μ : ℂ,
        (Nc S).map (Nat.cast : ℕ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ β := by
  have := nonempty_of_tracks hne hC
  obtain ⟨β, ℓ, u, h, -, -⟩ := perron_inc S.s hprim
  exact ⟨β, ℓ, u, h, perron_root_childSystem S ℓ h.left_pos hne β h.left hC⟩

/-- **`ρ(N_C) = β` on normalised representatives** (`thm:parikh`, last clause, for
the manuscript's `N_C = A + B`, `Psc.SignedCocycle.Normalisation.Nrep`), for
balanced states of a primitive substitution: with `β` the Perron root of `M`
(`PerronData`), `N_C` has the positive left eigenvector `L = Lrep ℓ` for `β`
(the hypotheses `hL`, `hLN` of `PscVerif.CocycleSpectrum`), `β` is an eigenvalue
of `N_C`, and every complex eigenvalue of `N_C` has modulus at most `β`. -/
theorem perron_root_rep_of_primitive {S : ChildSystem α} (P : Normalisation S)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c)
    (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) (hC : S.C.Nonempty) :
    ∃ (β : ℝ) (ℓ u : α → ℝ), PerronData ((inc S.s).map (Nat.cast : ℕ → ℝ)) β ℓ u ∧
      (∃ L : P.Rep → ℝ, (∀ i, 0 < L i) ∧ L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L) ∧
      (∃ x : P.Rep → ℝ, x ≠ 0 ∧ P.Nrep.map (Nat.cast : ℕ → ℝ) *ᵥ x = β • x) ∧
      ∀ x : P.Rep → ℂ, x ≠ 0 → ∀ μ : ℂ,
        P.Nrep.map (Nat.cast : ℕ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ β := by
  have hne := P.top_ne_nil hbal
  have := nonempty_of_tracks hne hC
  obtain ⟨T, hT⟩ := hC
  have : Nonempty P.Rep := (P.cover T hT).elim (fun h => ⟨⟨T, h⟩⟩) fun h => ⟨⟨T.swap, h⟩⟩
  obtain ⟨β, ℓ, u, h, -, -⟩ := perron_inc S.s hprim
  have hL := P.lrep_pos ℓ h.left_pos hne
  have hLN := P.rep_eigen ℓ β h.left hbal
  obtain ⟨x, hx0, hx⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot _ β
    (Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ β _ (ne_zero_of_pos hL) hLN)
  exact ⟨β, ℓ, u, h, ⟨_, hL, hLN⟩, ⟨x, hx0, hx⟩, fun y hy0 μ hy =>
    spectral_bound _ _ hL β hLN _ (fun i j => by simp) y hy0 μ hy⟩

/-- **`prop:cocycle`, `ρ(S) ≤ β`, for a primitive substitution**, with `β` the
Perron root of `M` (`PerronData`); no balance is needed (the bound goes through
the double cover, `Psc.SignedCocycle.Normalisation.cocycle_spectral_bound`). -/
theorem cocycle_spectral_bound_of_primitive [Nonempty α] {S : ChildSystem α}
    (P : Normalisation S) (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c)
    (hne : ∀ T ∈ S.C, T.1 ≠ []) :
    ∃ (β : ℝ) (ℓ u : α → ℝ), PerronData ((inc S.s).map (Nat.cast : ℕ → ℝ)) β ℓ u ∧
      ∀ x : P.Rep → ℂ, x ≠ 0 → ∀ μ : ℂ,
        P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ β := by
  obtain ⟨β, ℓ, u, h, -, -⟩ := perron_inc S.s hprim
  exact ⟨β, ℓ, u, h, P.cocycle_spectral_bound ℓ h.left_pos hne β h.left⟩

end Incidence

/-! ### Controls -/

section Controls

open Psc.Incidence Psc.Binomial

/-- The control matrix `m0 = [[5,21,1],[6,26,1],[6,24,1]]`
(`Psc.ConcentrationControls.m0`, as `Psc.M0Pisot.M0`) over `ℝ`. -/
noncomputable abbrev A0 : Matrix (Fin 3) (Fin 3) ℝ := Psc.M0Pisot.M0.map ((↑) : ℚ → ℝ)

theorem A0_pos (i j : Fin 3) : 0 < A0 i j := by
  show 0 < ((Psc.M0Pisot.M0 i j : ℚ) : ℝ)
  rw [Psc.M0Pisot.M0_eq_m0]
  exact_mod_cast Psc.ConcentrationControls.m0_positive i j

/-- **Control** (`k = 1`): `m0` meets the hypotheses of `exists_pos_left_eigen`
and `perron_frobenius`. -/
theorem m0_hyp : (∀ i j, 0 ≤ A0 i j) ∧ ∃ k ≥ 1, ∀ i j, 0 < (A0 ^ k) i j :=
  ⟨fun i j => (A0_pos i j).le, 1, le_rfl, by simpa using A0_pos⟩

/-- **Control**: `m0` is primitive in Mathlib's sense. -/
theorem A0_isPrimitive : A0.IsPrimitive :=
  ⟨m0_hyp.1, m0_hyp.2⟩

/-- **Control**: `perron_frobenius_of_isPrimitive` applies to `m0`. -/
theorem m0_perron : ∃ r v u, PerronData A0 r v u :=
  perron_frobenius_of_isPrimitive A0 A0_isPrimitive

/-- **Control**: the Perron data of `m0` meet the hypotheses (with `k = 1`, `n = 1`,
`w = u`, `x = v`, `y = u`) of `norm_le_of_pos_left_eigen`,
`eigenvalue_eq_of_pos_left_eigen`, `colSum_bounds`,
`eigenvalue_eq_of_dotProduct_ne_zero`, `eigenvalue_pow_eq_of_nonneg_right_eigen`,
`eq_smul_of_left_eigen` and `eq_smul_of_pos_left_eigen`. -/
theorem m0_hyps : ∃ (r : ℝ) (v u : Fin 3 → ℝ), (∀ i j, 0 ≤ A0 i j) ∧
    (∀ i j, 0 < (A0 ^ 1) i j) ∧ (∀ i, 0 < v i) ∧ v ᵥ* A0 = r • v ∧ (∀ i, 0 ≤ u i) ∧
    u ≠ 0 ∧ A0 *ᵥ u = r • u ∧ A0 ^ 1 *ᵥ u = r • u ∧ v ⬝ᵥ u ≠ 0 := by
  obtain ⟨r, v, u, h⟩ := m0_perron
  have hu0 : ∀ i, 0 ≤ u i := fun i => (h.right_pos i).le
  exact ⟨r, v, u, m0_hyp.1, by simpa using A0_pos, h.left_pos, h.left, hu0,
    ne_zero_of_pos h.right_pos, h.right, by rw [pow_one]; exact h.right,
    (dotProduct_pos_of_nonneg h.left_pos hu0 (ne_zero_of_pos h.right_pos)).ne'⟩

/-- **Control** (`k = 2`, not `k = 1`): the substitution
`Psc.ConcentrationControls.sigma` (`0 ↦ 011`, `1 ↦ 2`, `2 ↦ 120`) has a
primitive incidence matrix whose first power has a zero entry. -/
theorem sigma_primitive : (∀ a c, 0 < (inc Psc.ConcentrationControls.sigma ^ 2) a c) ∧
    ¬ ∀ a c, 0 < (inc Psc.ConcentrationControls.sigma ^ 1) a c := by
  have h : ∀ a c, 0 < (inc Psc.ConcentrationControls.sigma *
      inc Psc.ConcentrationControls.sigma) a c := by
    decide +kernel
  exact ⟨fun a c => sq (inc Psc.ConcentrationControls.sigma) ▸ h a c,
    fun h1 => absurd (h1 0 1) (by rw [pow_one]; decide)⟩

/-- **Control**: `perron_inc` applies to `sigma`. -/
theorem sigma_perron : ∃ (β : ℝ) (ℓ u : Fin 3 → ℝ),
    PerronData ((inc Psc.ConcentrationControls.sigma).map (Nat.cast : ℕ → ℝ)) β ℓ u := by
  obtain ⟨β, ℓ, u, h, -⟩ := perron_inc _ ⟨2, by norm_num, sigma_primitive.1⟩
  exact ⟨β, ℓ, u, h⟩

/-- **Control**: the Thue–Morse child system `Psc.Binomial.thueMorse` (with the
normalisation `Psc.SignedCocycle.thueMorseNorm`) meets every hypothesis of
`perron_root_childSystem_of_primitive`, `perron_root_rep_of_primitive` and
`cocycle_spectral_bound_of_primitive`. -/
theorem thueMorse_perron_root :
    (∃ k ≥ 1, ∀ a c, 0 < (inc thueMorse.s ^ k) a c) ∧ (∀ T ∈ thueMorse.C, T.1 ≠ []) ∧
      (∀ T ∈ thueMorse.C, Equiv1 T.1 T.2) ∧ thueMorse.C.Nonempty :=
  ⟨Psc.PrimitiveExpansion.thueMorse_control.1, by decide, by decide,
    ⟨_, Psc.PrimitiveExpansion.thueMorse_control.2.2.1⟩⟩

/-- **Control**: the uniqueness clause has teeth: the Perron root of the
Thue–Morse incidence matrix is `2` (its left eigenvector `(1, 1)`,
`Psc.SignedCocycle.thueMorse_left_eigen`, is positive). -/
theorem thueMorse_beta {β : ℝ} {ℓ u : Fin 2 → ℝ}
    (h : PerronData ((inc thueMorse.s).map (Nat.cast : ℕ → ℝ)) β ℓ u) : β = 2 :=
  (h.left_nonneg 2 _ (fun _ => zero_le_one) (ne_zero_of_pos fun _ => one_pos)
    Psc.SignedCocycle.thueMorse_left_eigen).1.symm

/-- **Control**: `perron_root_rep_of_primitive` on Thue–Morse. -/
theorem thueMorse_perron_rep : ∃ (β : ℝ) (ℓ u : Fin 2 → ℝ),
    PerronData ((inc thueMorse.s).map (Nat.cast : ℕ → ℝ)) β ℓ u ∧
      (∃ L : Psc.SignedCocycle.thueMorseNorm.Rep → ℝ, (∀ i, 0 < L i) ∧
        L ᵥ* Psc.SignedCocycle.thueMorseNorm.Nrep.map (Nat.cast : ℕ → ℝ) = β • L) ∧
      (∃ x : Psc.SignedCocycle.thueMorseNorm.Rep → ℝ, x ≠ 0 ∧
        Psc.SignedCocycle.thueMorseNorm.Nrep.map (Nat.cast : ℕ → ℝ) *ᵥ x = β • x) ∧
      ∀ x : Psc.SignedCocycle.thueMorseNorm.Rep → ℂ, x ≠ 0 → ∀ μ : ℂ,
        Psc.SignedCocycle.thueMorseNorm.Nrep.map (Nat.cast : ℕ → ℂ) *ᵥ x = μ • x →
          ‖μ‖ ≤ β :=
  perron_root_rep_of_primitive _ thueMorse_perron_root.1 thueMorse_perron_root.2.2.1
    thueMorse_perron_root.2.2.2

/-- **Negative control: `A ≥ 0` cannot be dropped.**  `A = (-1)` has
`A ^ 2 = (1) > 0` but no positive left eigenvector with positive eigenvalue. -/
theorem neg_nonneg_needed :
    (∀ i j, 0 < ((-1 : Matrix (Fin 1) (Fin 1) ℝ) ^ 2) i j) ∧
      ¬ ∃ r : ℝ, 0 < r ∧ ∃ v : Fin 1 → ℝ, (∀ i, 0 < v i) ∧
        v ᵥ* (-1 : Matrix (Fin 1) (Fin 1) ℝ) = r • v := by
  refine ⟨fun i j => by simp [Subsingleton.elim i j], ?_⟩
  rintro ⟨r, hr, v, hv, h⟩
  have := congrFun h 0
  simp [vecMul, dotProduct] at this
  nlinarith [hv 0]

/-- **Negative control: `k ≥ 1` cannot be dropped.**  `A = (0)` has
`A ^ 0 = (1) > 0` but no positive left eigenvector with positive eigenvalue. -/
theorem neg_exponent_needed :
    (∀ i j, 0 < ((0 : Matrix (Fin 1) (Fin 1) ℝ) ^ 0) i j) ∧
      ¬ ∃ r : ℝ, 0 < r ∧ ∃ v : Fin 1 → ℝ, (∀ i, 0 < v i) ∧
        v ᵥ* (0 : Matrix (Fin 1) (Fin 1) ℝ) = r • v := by
  refine ⟨fun i j => by simp [Subsingleton.elim i j], ?_⟩
  rintro ⟨r, hr, v, hv, h⟩
  have := congrFun h 0
  simp at this
  rcases this with h | h
  · exact hr.ne' h
  · exact (hv 0).ne' h

/-- **Negative control: `A ^ k > 0` is needed for `eq_smul_of_left_eigen` and
`eq_smul_of_pos_left_eigen`.**  The identity `1 ≥ 0` on two letters has no
entrywise positive power, and the strictly positive rows `(1, 1)` and `(1, 2)` are
left eigenvectors for the same eigenvalue `1` that are not proportional.
(`eigenvalue_eq_of_pos_left_eigen` still applies.) -/
theorem neg_primitive_needed :
    (∀ k, ¬ ∀ i j, 0 < ((1 : Matrix (Fin 2) (Fin 2) ℝ) ^ k) i j) ∧
      (∀ i, 0 < ![(1 : ℝ), 1] i) ∧ (∀ i, 0 < ![(1 : ℝ), 2] i) ∧
      ![1, 1] ᵥ* (1 : Matrix (Fin 2) (Fin 2) ℝ) = (1 : ℝ) • ![1, 1] ∧
      ![1, 2] ᵥ* (1 : Matrix (Fin 2) (Fin 2) ℝ) = (1 : ℝ) • ![1, 2] ∧
      ¬ ∃ t : ℝ, ![(1 : ℝ), 2] = t • ![1, 1] := by
  refine ⟨fun k h => by simpa using h 0 1, fun i => by fin_cases i <;> simp,
    fun i => by fin_cases i <;> simp, by simp, by simp, ?_⟩
  rintro ⟨t, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  linarith

/-- **Negative control: `w ≥ 0` is needed for
`eigenvalue_pow_eq_of_nonneg_right_eigen`.**  For `A = [[1,1],[1,1]]` the row
`(1, 1) > 0` is a left eigenvector for `2`, but the sign-changing right
eigenvector `(1, -1)` has eigenvalue `0 ≠ 2 ^ 1`. -/
theorem neg_nonneg_eigenvector_needed :
    ![(1 : ℝ), 1] ᵥ* !![1, 1; 1, 1] = (2 : ℝ) • ![1, 1] ∧
      !![(1 : ℝ), 1; 1, 1] ^ 1 *ᵥ ![1, -1] = (0 : ℝ) • ![1, -1] ∧ (0 : ℝ) ≠ 2 ^ 1 := by
  refine ⟨?_, ?_, by norm_num⟩ <;> ext i <;> fin_cases i <;>
    simp [vecMul, mulVec, dotProduct] <;> norm_num

end Controls

end Psc.PerronExistence
