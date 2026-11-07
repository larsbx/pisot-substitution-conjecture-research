/-
# Diagonalization of `M`, the weights of the rational `Φ_r`, and the sector `im Q_r`

`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`: the shared steps of the
proofs of `thm:deg23` (iii) and `thm:sieve` (lines ~720–750), namely

* "`Φ₃` is semisimple since `χ_M` is" (`thm:deg23` (iii)) and "its weights
  under a semisimple `M` with eigenvalues `βᵢ` are the monomials `∏ βᵢ^{aᵢ}`"
  (`thm:sieve`): for a rational `M` with irreducible `χ_M`, a complex
  diagonalization `M = Q (diag x) Q⁻¹` exists, so the weight theorems of
  `Psc.LieWeights` apply to it;
* "`im Q_r` is a nonzero rational `Φ_r`-invariant subspace on which the induced
  action is a quotient of `S`" (`thm:defect-intertwiner`): the characteristic
  polynomial `q_r` of `Φ_r` on `im Q_r` divides both `χ_S` and `χ(Φ_r)`, so its
  roots are roots of `χ_S` and weights of `Φ_r`.

`docs/c4-concentration-attack-2026-11-06.md` §8, rows `KernelCofactor`,
`LieWeights` (whose weights are proved for `M = Q (diag x) Q⁻¹`) and `GaloisOrbit`.
The shape theorems of `Psc.GaloisOrbit` (`orbit_310_excluded`, `orbit_211_forces_unit`,
`orbit_220_forces_complex_unit`) take, among other hypotheses, a rational `q`
vanishing at a weight `β^a α^b γ^c` of a listed degree-four shape (`habc`, `hq`);
this module supplies exactly those two for `q = q₄` (`galoisOrbit_input_q4`), and
not the others (see "Not proved here").  Those shape theorems are degree-four only:
for `q₃` only `Psc.GaloisOrbit.orbit_exponent_on_beta` (arbitrary exponents) applies
directly.  `Psc.WeightModulus` takes modulus inequalities on given weights (with a
real `β`), not a polynomial, and is not addressed here.

Notation.  `L` is a field of characteristic zero (algebraically closed where
roots are produced; `ℂ` in the representative section).  `mono x κ =
x₀^{κ₀} x₁^{κ₁} x₂^{κ₂}` (`Psc.LieWeights.mono`, `mono_fin_three`).  `Shape4 κ`:
`κ` is a permutation of `(3,1,0)`, `(2,2,0)` or `(2,1,1)`; `Shape3 κ`: of
`(2,1,0)` or `(1,1,1)`.  On representatives, `S` is the child system, `P` a
`Psc.SignedCocycle.Normalisation S`, `M = incQ S` (`Psc.ParikhRank.incQ`), the
manuscript's cocycle matrix is `SsignQ P` (`Psc.Degree2Sector.SsignQ`), `Lie₃`,
`Lie₄` are the `ℚ`-spans `Lie3Q`, `Lie4Q` of the Lyndon brackets, and
`Φ₃ = Psc.LieWeights.phi3Lie M`, `Φ₄ = Psc.LieWeights.phi4Lie M` (the
restrictions of `M^{⊗3}`, `M^{⊗4}`).

## Proved here, in full

* **(a) Diagonalization.**  `exists_conj_diagonal`: if `x : Fin 3 → L` are
  pairwise distinct roots of `χ_M` (no irreducibility needed), then
  `M.map (algebraMap ℚ L) = Q (diag x) Q⁻¹` with `IsUnit Q.det`, in exactly the
  form consumed by `Psc.LieWeights.charpoly_phi3Lie_rat`, `charpoly_phi4Lie_rat`
  (eigenvectors from `Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot`, their
  independence `Module.End.eigenvectors_linearIndependent'`, `Q` their column
  matrix).  `exists_distinct_roots` (`L` algebraically closed): an irreducible
  `χ_M` is separable (characteristic zero), so it has three pairwise distinct roots
  `x 0, x 1, x 2`, and every root is one of them.  `exists_diagonalization`: both.
* **(b) Roots of the rational `Φ_r`.**  `root_phi4Lie_rat`, `root_phi3Lie_rat`:
  for `M.map (algebraMap ℚ L) = Q (diag x) Q⁻¹`, every root `z ∈ L` of `χ(Φ₄)`
  (resp. `χ(Φ₃)`) is `mono x κ` for an exponent vector `κ` with `Σ κ = 4` (resp.
  `3`), `dim_ℚ comp κ > 0` and `Shape4 κ` (resp. `Shape3 κ`): the multiplicity of
  `(4,0,0)` (resp. `(3,0,0)`) is zero (`Psc.LieWeights.comp4_eq_bot`,
  `comp3_eq_bot`), so the exponent vector of a weight is never a permutation of
  `(4,0,0)` (resp. `(3,0,0)`): `Shape4.le_three`, `Shape3.le_two` (no letter carries
  the whole degree; a statement about `κ`, not about the value `mono x κ`, see
  `mono_eq_pow_of_cube_eq` below); `Shape4.triple`, `Shape3.triple` list the exponent
  triples, the former in the form of the hypotheses `habc` of `Psc.GaloisOrbit`.
  `mono_eq_pow_of_cube_eq`: for three distinct `x` with equal cubes (the roots of
  any `X³ − c`, `c ≠ 0`), `x₀ x₁ x₂ = x₀³` and `x₀² x₁ x₂ = x₀⁴`, so a weight of
  shape `(1,1,1)` or `(2,1,1)` can be numerically a pure power.
  `root_phi4Lie_of_roots`, `root_phi3Lie_of_roots`: the same for any
  three distinct roots `x` of `χ_M`; `roots_phi4Lie_of_irreducible`,
  `roots_phi3Lie_of_irreducible`: combined with (a).
* **(c) Quotient and restriction**, over any field `K`.  For `φ : End V`
  (`V` finite-dimensional), `S : Matrix R R K` with `R` finite, and
  `Qm : (R → K) →ₗ V` with `Qm ∘ S = φ ∘ Qm`: `range_invariant` (`W = im Qm` is
  `φ`-invariant), `imRestrict` (`φ|_W`) and `imCharpoly` (its characteristic
  polynomial); `imCharpoly_dvd_left`: `χ(φ|_W) ∣ χ_S` (the cofactor
  `Psc.KernelCofactor.charpoly_eq_mul_restrict` for the onto intertwiner
  `Qm : R → K ↠ W`); `imCharpoly_dvd_right`: `χ(φ|_W) ∣ χ_φ`, from the general
  `charpoly_restrict_dvd` (the restriction to an invariant subspace: the same
  cofactor for the quotient map `V ↠ V/W`, whose kernel is `W`);
  `natDegree_imCharpoly`: `deg χ(φ|_W) = dim W`; `imCharpoly_monic`;
  `aeval_of_imCharpoly`: every root in any extension is a root of `χ_S` and of
  `χ_φ`; `natDegree_imCharpoly_pos`, `exists_root_imCharpoly`: if `W ≠ 0`, positive
  degree, hence a root in every algebraically closed extension;
  `imCharpoly_eq_of_card_eq_one`: if `|R| = 1` and `W ≠ 0`, `χ(φ|_W) = χ_S`.  For
  `Qm = Fintype.linearCombination K k` (columns `k : R → V`):
  `linearCombination_intertwine` (the column identities `φ (k j) = Σᵢ S i j • k i`
  give `Qm ∘ S = φ ∘ Qm`) and `range_linearCombination_ne_bot` (a nonzero column
  gives `W ≠ 0`).
* **(d) The sectors `im Q₃`, `im Q₄` on representatives.**
  - degree three (every state `Equiv2`): `k3Lie` (the column `K₃(j) ∈ Lie₃`, via
    `Psc.SignedIntertwiner.q3_col_mem_lie3`), `phi3_k3Vec_rep`, `phi3Lie_k3Lie`
    (`Φ₃ K₃(j) = Σᵢ S i j K₃(i)`, from `Psc.SignedIntertwiner.k3_rep`; the
    degree-three twin of `Psc.Defect4Lie.phi4Lie_k4Lie`), `Q3m` (the `ℚ`-linear map
    `u ↦ Σⱼ uⱼ K₃(j)` into `Lie₃`), `q3m_intertwine` (`Q₃ S = Φ₃ Q₃`, by
    `linearCombination_intertwine`), and
    `q3 = χ(Φ₃|_{im Q₃})` with `q3_dvd_ssign`, `q3_dvd_phi3`, `natDegree_q3`
    (`= rank Q₃`), `range_q3m_ne_bot`, `natDegree_q3_pos`, `exists_root_q3` (some
    column `K₃(j) ≠ 0`);
  - degree four (every state `Psc.Defect4.Equiv3`): `Q4m` (on the columns
    `Psc.Defect4Lie.k4Lie`), `q4m_intertwine` (`Psc.Defect4Lie.phi4Lie_k4Lie` and
    `linearCombination_intertwine`),
    `q4 = χ(Φ₄|_{im Q₄})`, `q4_dvd_ssign`, `q4_dvd_phi4`, `natDegree_q4`,
    `range_q4m_ne_bot`, `natDegree_q4_pos`, `exists_root_q4`;
  - **the bridge** `root_q3`, `root_q4`: for any three pairwise distinct roots `x`
    of `χ_M` in `L`, every root `z ∈ L` of `q_r` is a root of `χ_S` and
    `z = mono x κ` with `Shape3 κ` (resp. `Shape4 κ`); and
    `exists_weight_root_q3`, `exists_weight_root_q4`: if `χ_M` is irreducible and
    some column is nonzero, there are such `x` in `ℂ` and a common root `z ∈ ℂ` of
    `q_r` and `χ_S` that is a weight of a listed shape.  With
    `(β, α, γ) = (x 0, x 1, x 2)` (`mono_fin_three`) and `(a, b, c) =
    (κ 0, κ 1, κ 2)` (`Shape4.triple`), this is the pair of hypotheses `habc`, `hq`
    of `Psc.GaloisOrbit.orbit_310_excluded`, `orbit_211_forces_unit`,
    `orbit_220_forces_complex_unit`, for the rational `q = q₄`;
    `galoisOrbit_input_q4` states it verbatim for prescribed distinct roots
    `β, α, γ` (no irreducibility needed once the roots are given).
* **Controls.**
  - (a), (b): `m0_diagonalization` and `m0_roots_phi4Lie`, `m0_roots_phi3Lie`
    (`Psc.M0Pisot.M0`, `χ = x³ − 32x² + 5x + 2` irreducible,
    `Psc.KernelCofactor.ctrl_irreducible`), and `plastic_diagonalization`
    (`Psc.Degree2Sector.plasticSubst`, `χ = X³ − X − 1`) meet the hypothesis
    `Irreducible χ_M`.
  - (c), (d): `wT_q3_pos`, `wT_q3_eq`, `wT_exists_root_q3`
    (`Psc.SignedIntertwiner.wTNorm`: `Equiv2` states, `K₃ ≠ 0`, `S = (1)`;
    `q₃ = χ_S` has degree one) and `w4_q4_pos`, `w4_q4_eq`, `w4_exists_root_q4`
    (`Psc.Defect4.w4Norm`: `Equiv3` states, `K₄ ≠ 0`, `S = (1)`) meet the state
    hypotheses of the degree-three and degree-four sector theorems, with
    `im Q_r ≠ 0`.
  - **The bridge, every hypothesis**: `cyc3_root_q3`, `cyc4_root_q4`,
    `cyc4_galoisOrbit_input` apply `root_q3`, `root_q4`, `galoisOrbit_input_q4` on
    `cycSubst`, the 3-cycle relabelling `0 ↦ 1 ↦ 2 ↦ 0` (`χ_M = X³ − 1`,
    `cycM_charpoly`; distinct roots `cycX = (1, ζ, ζ²)`, `ζ` a primitive cube root
    of unity), with `C` the three relabellings of `wTPair` (resp.
    `Psc.Defect4.w4Pair`) and their swaps (`cyc3_states`, `cyc4_states`):
    `Equiv2` (resp. `Equiv3`) states, a nonzero column, three distinct roots of
    `χ_M`.  `cycSubst` is a permutation substitution (not primitive, `χ_M`
    reducible, no Pisot root), so these controls show only that the hypotheses of
    the three bridge theorems are jointly satisfiable; they do not meet the
    hypotheses of `Psc.GaloisOrbit` itself.  `cycX_mono_pure`:
    `mono_eq_pow_of_cube_eq` on `cycX`.

## Not proved here

* **No control meets the full hypothesis set of `exists_weight_root_q3`,
  `exists_weight_root_q4`** (a normalisation over `Fin 3` with `Equiv2`, resp.
  `Equiv3`, states, a nonzero column, and `χ_M` irreducible).  The controls with a
  child system (`wT`, `w4` on the identity substitution, `χ_M = (X − 1)³`; the cycle
  controls, `χ_M = X³ − 1`) have reducible `χ_M`; the matrix-level controls `M0`,
  `plastic` carry no child system.  These two theorems are reductio lemmas:
  necessary conditions on a hypothetical component (as the `Psc.Degree2Sector` and
  `Psc.KernelCofactor` representative theorems are), not facts about a known one.
  (`root_q3`, `root_q4`, `galoisOrbit_input_q4` need only three distinct roots of
  `χ_M` and have the full cycle controls above.)
* The composition with `Psc.GaloisOrbit`.  Besides `habc`, `hq` (supplied for
  `q = q₄`), its shape theorems take `Irreducible f` with `f = χ_M` (its
  `natDegree f = 3` is `Matrix.charpoly_natDegree_eq_dim`), `β, α, γ` the roots of
  `f`, the bound `1 ≤ ‖βαγ‖`, and: `orbit_310_excluded` the Pisot moduli
  `1 < ‖β‖`, `‖α‖ < 1`, `‖γ‖ < 1` (its conclusion, a root of `q₄` of modulus
  `> ‖β‖²`, contradicts nothing without a bound on the roots of `q₄`);
  `orbit_211_forces_unit` the bound `hbound` (every root of `q` has modulus
  `≤ ‖β‖`); `orbit_220_forces_complex_unit` `1 < ‖β‖` and `hbound`.  For `q₄`
  that bound is `ρ(S) ≤ β` as a statement about the roots of `χ_S` (`prop:cocycle`;
  `Psc.CocycleSpectrum`, `Psc.SignedCocycle` state it for eigenvectors over `ℂ`).
* The case analysis itself.  `thm:sieve` at `r = 4` (`|det M| = 1`) and
  `thm:deg23` (iii) (`im Q₃ ⊆ ker (Φ₃ − det M)`, `rank Q₃ ≤ 2`) need, beyond this
  module, that bound, the Pisot moduli of `x`, the composition above, and for the
  inclusion into the `det M`-eigenspace the semisimplicity of `Φ₃|_{im Q₃}`, which
  is not proved (only that `Φ₃` has the eigenbasis of
  `Psc.LieWeights.exists_eigenbasis_phi3Lie` over `L`).
* The first-defect selection (the hypotheses are `Equiv2` / `Equiv3` on every
  state, not that `3` / `4` is the least degree with a nonzero defect); other
  alphabets and degrees `r ≥ 5`.
* That a weight of a listed shape is not *numerically* a pure power.  Without the
  Pisot moduli this is **false**: for the irreducible `χ_M = X³ − 2` (Eisenstein at
  `2`; its irreducibility is not formalized here) any three distinct roots satisfy
  `x₀ x₁ x₂ = x₀³` (shape `(1,1,1)`) and `x₀² x₁ x₂ = x₀⁴` (shape `(2,1,1)`)
  (`mono_eq_pow_of_cube_eq`).  Under the Pisot moduli and `1 ≤ |det M|` the
  `(1,1,1)` case does hold (`xᵢ³ = det M = x₀ x₁ x₂` forces `|xᵢ|² = |xⱼ xₖ| < 1`
  when `xᵢ` is the Perron root, and `|xᵢ|³ < 1 ≤ |det M|` otherwise); that is not
  proved here either.
-/
import PscVerif.KernelCofactor
import PscVerif.Degree2Sector
import PscVerif.Defect4Lie
import PscVerif.M0Pisot

namespace Psc.SectorBridge

open Matrix Polynomial

/-! ### (a) Diagonalization of a rational `3 × 3` matrix with irreducible `χ_M` -/

section Diagonal

variable {L : Type*} [Field L] [CharZero L]

/-- **Three distinct eigenvalues diagonalize.**  If `x 0, x 1, x 2` are pairwise
distinct roots of `χ_M` in `L`, then `M = Q (diag x) Q⁻¹` over `L` with `Q`
invertible: `Q` is the matrix of eigenvectors, which are independent because
their eigenvalues are distinct. -/
theorem exists_conj_diagonal (M : Matrix (Fin 3) (Fin 3) ℚ) (x : Fin 3 → L)
    (hx : Function.Injective x) (hroot : ∀ i, aeval (x i) M.charpoly = 0) :
    ∃ Q : Matrix (Fin 3) (Fin 3) L, IsUnit Q.det ∧
      M.map (algebraMap ℚ L) = Q * Matrix.diagonal x * Q⁻¹ := by
  classical
  set A := M.map (algebraMap ℚ L) with hA
  have hev : ∀ i, A.charpoly.eval (x i) = 0 := fun i => by
    rw [hA, Matrix.charpoly_map, eval_map_algebraMap]; exact hroot i
  choose v hv0 hv using fun i =>
    Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot A (x i) (hev i)
  have hli : LinearIndependent L v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) x hx v fun i =>
      Module.End.hasEigenvector_iff.2
        ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact hv i), hv0 i⟩
  set Q : Matrix (Fin 3) (Fin 3) L := Matrix.of fun r i => v i r with hQdef
  have hQd : IsUnit Q.det :=
    (Matrix.isUnit_iff_isUnit_det Q).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)
  have hAQ : A * Q = Q * Matrix.diagonal x := by
    ext r i
    rw [Matrix.mul_diagonal]
    have := congrFun (hv i) r
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, hQdef, Matrix.of_apply]
    rw [this, mul_comm]
  refine ⟨Q, hQd, ?_⟩
  rw [← hAQ]
  exact (Matrix.mul_nonsing_inv_cancel_right Q A hQd).symm

/-- **An irreducible `χ_M` has three distinct roots**, and they are all its roots:
in characteristic zero it is separable, and it splits in an algebraically closed
`L`. -/
theorem exists_distinct_roots [IsAlgClosed L] (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : Irreducible M.charpoly) :
    ∃ x : Fin 3 → L, Function.Injective x ∧ (∀ i, aeval (x i) M.charpoly = 0) ∧
      ∀ z : L, aeval z M.charpoly = 0 → ∃ i, z = x i := by
  classical
  set p := M.charpoly.map (algebraMap ℚ L) with hp
  have hsep : p.Separable := hM.separable.map
  have hp0 : p ≠ 0 := Polynomial.map_ne_zero hM.ne_zero
  have hcard : p.roots.toFinset.card = 3 := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      hp, natDegree_map, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmem : ∀ y : L, y ∈ p.roots.toFinset ↔ aeval y M.charpoly = 0 := fun y => by
    rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def, hp, eval_map_algebraMap]
  set e := p.roots.toFinset.equivFinOfCardEq hcard
  exact ⟨fun i => (e.symm i : L), Subtype.val_injective.comp e.symm.injective,
    fun i => (hmem _).1 (e.symm i).2, fun z hz => ⟨e ⟨z, (hmem z).2 hz⟩, by simp⟩⟩

/-- **(a) Diagonalization from irreducibility.**  For a rational `M` with
irreducible `χ_M` there are pairwise distinct roots `x 0, x 1, x 2` of `χ_M` in
`L`, every root of `χ_M` is one of them, and `M = Q (diag x) Q⁻¹` over `L` with
`IsUnit Q.det` (the hypotheses of `Psc.LieWeights.charpoly_phi3Lie_rat`,
`charpoly_phi4Lie_rat`). -/
theorem exists_diagonalization [IsAlgClosed L] (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : Irreducible M.charpoly) :
    ∃ x : Fin 3 → L, Function.Injective x ∧ (∀ i, aeval (x i) M.charpoly = 0) ∧
      (∀ z : L, aeval z M.charpoly = 0 → z = x 0 ∨ z = x 1 ∨ z = x 2) ∧
      ∃ Q : Matrix (Fin 3) (Fin 3) L, IsUnit Q.det ∧
        M.map (algebraMap ℚ L) = Q * Matrix.diagonal x * Q⁻¹ := by
  obtain ⟨x, hx, hroot, hall⟩ := exists_distinct_roots (L := L) M hM
  refine ⟨x, hx, hroot, fun z hz => ?_, exists_conj_diagonal M x hx hroot⟩
  obtain ⟨i, rfl⟩ := hall z hz
  fin_cases i <;> simp

end Diagonal

/-! ### (b) The roots of the rational `Φ₃`, `Φ₄` are weights of the listed shapes -/

section Weights

open Psc.LieWeights

/-- `mono x κ = x₀^{κ₀} x₁^{κ₁} x₂^{κ₂}`, the form of `Psc.GaloisOrbit`. -/
theorem mono_fin_three {N : Type*} [CommMonoid N] (x : Fin 3 → N) (κ : Fin 3 → ℕ) :
    mono x κ = x 0 ^ κ 0 * x 1 ^ κ 1 * x 2 ^ κ 2 :=
  Fin.prod_univ_three _

/-- The degree-four weight shapes of `Lie₄(ℚ³)` with nonzero multiplicity: a
permutation of `(3,1,0)`, `(2,2,0)` or `(2,1,1)`. -/
def Shape4 (κ : Fin 3 → ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), κ = ![3, 1, 0] ∘ σ ∨ κ = ![2, 2, 0] ∘ σ ∨ κ = ![2, 1, 1] ∘ σ

/-- The degree-three weight shapes of `Lie₃(ℚ³)` with nonzero multiplicity: a
permutation of `(2,1,0)` or `(1,1,1)`. -/
def Shape3 (κ : Fin 3 → ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), κ = ![2, 1, 0] ∘ σ ∨ κ = ![1, 1, 1] ∘ σ

/-- A degree-four shape puts at most `3` on any letter: the exponent vector is never a
permutation of `(4,0,0)`.  This constrains `κ`, not the value `mono x κ`
(`mono_eq_pow_of_cube_eq`). -/
theorem Shape4.le_three {κ : Fin 3 → ℕ} (h : Shape4 κ) (i : Fin 3) : κ i ≤ 3 := by
  obtain ⟨σ, rfl | rfl | rfl⟩ := h <;> revert i <;> revert σ <;> decide

/-- A degree-three shape puts at most `2` on any letter: the exponent vector is never a
permutation of `(3,0,0)`.  This constrains `κ`, not the value `mono x κ`
(`mono_eq_pow_of_cube_eq`). -/
theorem Shape3.le_two {κ : Fin 3 → ℕ} (h : Shape3 κ) (i : Fin 3) : κ i ≤ 2 := by
  obtain ⟨σ, rfl | rfl⟩ := h <;> revert i <;> revert σ <;> decide

/-- `Shape4` as the explicit exponent triples, in the form of the hypotheses
`habc` of `Psc.GaloisOrbit.orbit_310_excluded`, `orbit_220_forces_complex_unit`
and `orbit_211_forces_unit` (in that order). -/
theorem Shape4.triple {κ : Fin 3 → ℕ} (h : Shape4 κ) :
    ((κ 0, κ 1, κ 2) = (3, 1, 0) ∨ (κ 0, κ 1, κ 2) = (3, 0, 1) ∨ (κ 0, κ 1, κ 2) = (1, 3, 0) ∨
      (κ 0, κ 1, κ 2) = (0, 3, 1) ∨ (κ 0, κ 1, κ 2) = (1, 0, 3) ∨ (κ 0, κ 1, κ 2) = (0, 1, 3)) ∨
    ((κ 0, κ 1, κ 2) = (2, 2, 0) ∨ (κ 0, κ 1, κ 2) = (2, 0, 2) ∨ (κ 0, κ 1, κ 2) = (0, 2, 2)) ∨
    ((κ 0, κ 1, κ 2) = (2, 1, 1) ∨ (κ 0, κ 1, κ 2) = (1, 2, 1) ∨ (κ 0, κ 1, κ 2) = (1, 1, 2)) := by
  obtain ⟨σ, rfl | rfl | rfl⟩ := h <;> revert σ <;> decide

/-- `Shape3` as the explicit exponent triples. -/
theorem Shape3.triple {κ : Fin 3 → ℕ} (h : Shape3 κ) :
    ((κ 0, κ 1, κ 2) = (2, 1, 0) ∨ (κ 0, κ 1, κ 2) = (2, 0, 1) ∨ (κ 0, κ 1, κ 2) = (1, 2, 0) ∨
      (κ 0, κ 1, κ 2) = (0, 2, 1) ∨ (κ 0, κ 1, κ 2) = (1, 0, 2) ∨ (κ 0, κ 1, κ 2) = (0, 1, 2)) ∨
    (κ 0, κ 1, κ 2) = (1, 1, 1) := by
  obtain ⟨σ, rfl | rfl⟩ := h <;> revert σ <;> decide

/-- **A listed shape can be numerically a pure power.**  If `x 0, x 1, x 2` are
pairwise distinct with equal cubes (e.g. the three roots of `X³ − c`, `c ≠ 0`; for
`c = 2` that cubic is irreducible over `ℚ`, by Eisenstein at `2`, which is not
formalized here), then the shape-`(1,1,1)` weight is
`x₀³` and the shape-`(2,1,1)` weight is `x₀⁴`.  From `x₀³ = x₁³ = x₂³` and
distinctness: `x₀² + x₀x₁ + x₁² = 0`, `x₀² + x₀x₂ + x₂² = 0`, hence
`x₀ + x₁ + x₂ = 0` and `x₀x₁x₂ − x₀³ = x₀x₁ (x₀ + x₁ + x₂) − x₀ (x₀² + x₀x₁ + x₁²)`. -/
theorem mono_eq_pow_of_cube_eq {F : Type*} [Field F] {x : Fin 3 → F}
    (hx : Function.Injective x) (hc : ∀ i, x i ^ 3 = x 0 ^ 3) :
    mono x ![1, 1, 1] = x 0 ^ 3 ∧ mono x ![2, 1, 1] = x 0 ^ 4 := by
  have h01 : x 0 - x 1 ≠ 0 := sub_ne_zero.2 (hx.ne (by decide))
  have h02 : x 0 - x 2 ≠ 0 := sub_ne_zero.2 (hx.ne (by decide))
  have h12 : x 1 - x 2 ≠ 0 := sub_ne_zero.2 (hx.ne (by decide))
  have h1 : x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 = 0 :=
    (mul_eq_zero.1 (by linear_combination (-1 : F) * hc 1 :
      (x 0 - x 1) * (x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2) = 0)).resolve_left h01
  have h2 : x 0 ^ 2 + x 0 * x 2 + x 2 ^ 2 = 0 :=
    (mul_eq_zero.1 (by linear_combination (-1 : F) * hc 2 :
      (x 0 - x 2) * (x 0 ^ 2 + x 0 * x 2 + x 2 ^ 2) = 0)).resolve_left h02
  have h3 : x 0 + x 1 + x 2 = 0 :=
    (mul_eq_zero.1 (by linear_combination h1 - h2 :
      (x 1 - x 2) * (x 0 + x 1 + x 2) = 0)).resolve_left h12
  rw [mono_fin_three, mono_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, pow_one]
  constructor
  · linear_combination (x 0 * x 1) * h3 - x 0 * h1
  · linear_combination x 0 * ((x 0 * x 1) * h3 - x 0 * h1)

/-- A root of `∏_{κ ∈ s} (X - a κ)^{m κ}` is some `a κ` with `m κ ≠ 0`. -/
theorem eq_of_eval_prod_pow {F ι : Type*} [Field F] (s : Finset ι) (a : ι → F) (m : ι → ℕ)
    {z : F} (hz : eval z (∏ κ ∈ s, (X - C (a κ)) ^ m κ) = 0) :
    ∃ κ ∈ s, m κ ≠ 0 ∧ z = a κ := by
  rw [eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨κ, hκ, h⟩ := hz
  refine ⟨κ, hκ, ?_⟩
  rw [eval_pow, eval_sub, eval_X, eval_C] at h
  by_cases hm : m κ = 0
  · rw [hm, pow_zero] at h; exact absurd h one_ne_zero
  · exact ⟨hm, sub_eq_zero.1 ((pow_eq_zero_iff hm).1 h)⟩

variable {L : Type*} [Field L] [CharZero L]

/-- **(b) Roots of the rational `Φ₄`.**  If `M = Q (diag x) Q⁻¹` over `L`, every
root `z ∈ L` of `χ(Φ₄)` is a weight `x^κ` with `Σ κ = 4`, `dim_ℚ comp4 κ > 0`,
and `κ` a permutation of `(3,1,0)`, `(2,2,0)` or `(2,1,1)` (never of `(4,0,0)`,
`comp4_eq_bot`). -/
theorem root_phi4Lie_rat (M : Matrix (Fin 3) (Fin 3) ℚ) (Q : Matrix (Fin 3) (Fin 3) L)
    (x : Fin 3 → L) (hQ : IsUnit Q.det)
    (hMQ : M.map (algebraMap ℚ L) = Q * Matrix.diagonal x * Q⁻¹) {z : L}
    (hz : aeval z (phi4Lie M).charpoly = 0) :
    ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 4 ∧ 0 < Module.finrank ℚ (comp4 (R := ℚ) κ) ∧ Shape4 κ ∧
      z = mono x κ := by
  rw [← eval_map_algebraMap, charpoly_phi4Lie_rat M Q x hQ hMQ] at hz
  obtain ⟨κ, hκ, hm, rfl⟩ := eq_of_eval_prod_pow _ _ _ hz
  refine ⟨κ, Finset.Nat.mem_antidiagonalTuple.1 hκ, Nat.pos_of_ne_zero hm, ?_, rfl⟩
  obtain ⟨σ, h | h | h | h⟩ := shapes4 κ hκ
  · exact absurd (by rw [h]; exact (finrank_comp4_shapes (F := ℚ) σ).1) hm
  · exact ⟨σ, Or.inl h⟩
  · exact ⟨σ, Or.inr (Or.inl h)⟩
  · exact ⟨σ, Or.inr (Or.inr h)⟩

/-- **(b) Roots of the rational `Φ₃`.**  If `M = Q (diag x) Q⁻¹` over `L`, every
root `z ∈ L` of `χ(Φ₃)` is a weight `x^κ` with `Σ κ = 3`, `dim_ℚ comp3 κ > 0`,
and `κ` a permutation of `(2,1,0)` or `(1,1,1)` (never of `(3,0,0)`,
`comp3_eq_bot`). -/
theorem root_phi3Lie_rat (M : Matrix (Fin 3) (Fin 3) ℚ) (Q : Matrix (Fin 3) (Fin 3) L)
    (x : Fin 3 → L) (hQ : IsUnit Q.det)
    (hMQ : M.map (algebraMap ℚ L) = Q * Matrix.diagonal x * Q⁻¹) {z : L}
    (hz : aeval z (phi3Lie M).charpoly = 0) :
    ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 3 ∧ 0 < Module.finrank ℚ (comp3 (R := ℚ) κ) ∧ Shape3 κ ∧
      z = mono x κ := by
  rw [← eval_map_algebraMap, charpoly_phi3Lie_rat M Q x hQ hMQ] at hz
  obtain ⟨κ, hκ, hm, rfl⟩ := eq_of_eval_prod_pow _ _ _ hz
  refine ⟨κ, Finset.Nat.mem_antidiagonalTuple.1 hκ, Nat.pos_of_ne_zero hm, ?_, rfl⟩
  obtain ⟨σ, h | h | h⟩ := shapes3 κ hκ
  · exact absurd (by rw [h]; exact (finrank_comp3_shapes (F := ℚ) σ).1) hm
  · exact ⟨σ, Or.inl h⟩
  · exact ⟨σ, Or.inr h⟩

/-- `root_phi4Lie_rat` for any three pairwise distinct roots `x` of `χ_M`. -/
theorem root_phi4Lie_of_roots (M : Matrix (Fin 3) (Fin 3) ℚ) (x : Fin 3 → L)
    (hx : Function.Injective x) (hroot : ∀ i, aeval (x i) M.charpoly = 0) {z : L}
    (hz : aeval z (phi4Lie M).charpoly = 0) :
    ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 4 ∧ Shape4 κ ∧ z = mono x κ := by
  obtain ⟨Q, hQ, hMQ⟩ := exists_conj_diagonal M x hx hroot
  obtain ⟨κ, hκ, -, hsh, rfl⟩ := root_phi4Lie_rat M Q x hQ hMQ hz
  exact ⟨κ, hκ, hsh, rfl⟩

/-- `root_phi3Lie_rat` for any three pairwise distinct roots `x` of `χ_M`. -/
theorem root_phi3Lie_of_roots (M : Matrix (Fin 3) (Fin 3) ℚ) (x : Fin 3 → L)
    (hx : Function.Injective x) (hroot : ∀ i, aeval (x i) M.charpoly = 0) {z : L}
    (hz : aeval z (phi3Lie M).charpoly = 0) :
    ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 3 ∧ Shape3 κ ∧ z = mono x κ := by
  obtain ⟨Q, hQ, hMQ⟩ := exists_conj_diagonal M x hx hroot
  obtain ⟨κ, hκ, -, hsh, rfl⟩ := root_phi3Lie_rat M Q x hQ hMQ hz
  exact ⟨κ, hκ, hsh, rfl⟩

/-- **(a) + (b) at degree four**: for irreducible `χ_M`, with its three distinct
roots `x`, every root of `χ(Φ₄)` is a weight `x^κ` of shape `(3,1,0)`, `(2,2,0)`
or `(2,1,1)`. -/
theorem roots_phi4Lie_of_irreducible [IsAlgClosed L] (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : Irreducible M.charpoly) :
    ∃ x : Fin 3 → L, Function.Injective x ∧ (∀ i, aeval (x i) M.charpoly = 0) ∧
      (∀ z : L, aeval z M.charpoly = 0 → ∃ i, z = x i) ∧
      ∀ z : L, aeval z (phi4Lie M).charpoly = 0 →
        ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 4 ∧ Shape4 κ ∧ z = mono x κ := by
  obtain ⟨x, hx, hroot, hall⟩ := exists_distinct_roots (L := L) M hM
  exact ⟨x, hx, hroot, hall, fun _ hz => root_phi4Lie_of_roots M x hx hroot hz⟩

/-- **(a) + (b) at degree three**: for irreducible `χ_M`, with its three distinct
roots `x`, every root of `χ(Φ₃)` is a weight `x^κ` of shape `(2,1,0)` or
`(1,1,1)`. -/
theorem roots_phi3Lie_of_irreducible [IsAlgClosed L] (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : Irreducible M.charpoly) :
    ∃ x : Fin 3 → L, Function.Injective x ∧ (∀ i, aeval (x i) M.charpoly = 0) ∧
      (∀ z : L, aeval z M.charpoly = 0 → ∃ i, z = x i) ∧
      ∀ z : L, aeval z (phi3Lie M).charpoly = 0 →
        ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 3 ∧ Shape3 κ ∧ z = mono x κ := by
  obtain ⟨x, hx, hroot, hall⟩ := exists_distinct_roots (L := L) M hM
  exact ⟨x, hx, hroot, hall, fun _ hz => root_phi3Lie_of_roots M x hx hroot hz⟩

end Weights

/-! ### (c) The image of an intertwiner: quotient of `S`, invariant subspace of `φ` -/

section Abstract

variable {K V R : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype R] [DecidableEq R]
  {φ : V →ₗ[K] V} {S : Matrix R R K} {Qm : (R → K) →ₗ[K] V}

/-- **Restriction to an invariant subspace**: `χ(φ|_W) ∣ χ_φ`.  The quotient map
`V ↠ V/W` intertwines `φ` with the induced map and has kernel `W`, so
`Psc.KernelCofactor.charpoly_eq_mul_restrict` gives `χ_φ = χ(φ_{V/W}) χ(φ|_W)`. -/
theorem charpoly_restrict_dvd [FiniteDimensional K V] (φ : V →ₗ[K] V) (W : Submodule K V)
    (hW : ∀ v ∈ W, φ v ∈ W) : (φ.restrict hW).charpoly ∣ φ.charpoly := by
  have hq : W.mkQ ∘ₗ φ = W.mapQ W φ hW ∘ₗ W.mkQ := (Submodule.mapQ_mkQ W W φ).symm
  have h := Psc.KernelCofactor.charpoly_eq_mul_restrict W.mkQ W.mkQ_surjective φ _ hq
  have hcongr : ∀ {W₁ W₂ : Submodule K V} (_ : W₁ = W₂) (h₁ : ∀ v ∈ W₁, φ v ∈ W₁)
      (h₂ : ∀ v ∈ W₂, φ v ∈ W₂), (φ.restrict h₁).charpoly = (φ.restrict h₂).charpoly := by
    rintro _ _ rfl _ _; rfl
  rw [h, hcongr (Submodule.ker_mkQ W) _ hW]
  exact dvd_mul_left _ _

/-- `im Qm` is `φ`-invariant when `Qm ∘ S = φ ∘ Qm`. -/
theorem range_invariant (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm) :
    ∀ v ∈ LinearMap.range Qm, φ v ∈ LinearMap.range Qm := by
  rintro _ ⟨u, rfl⟩
  exact ⟨Matrix.toLin' S u, by rw [← LinearMap.comp_apply, h, LinearMap.comp_apply]⟩

/-- `φ` restricted to `im Qm`. -/
abbrev imRestrict (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm) :
    LinearMap.range Qm →ₗ[K] LinearMap.range Qm :=
  φ.restrict (range_invariant h)

/-- The characteristic polynomial of `φ` on `im Qm` (`q_r` in the application). -/
noncomputable def imCharpoly (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm) : K[X] :=
  (imRestrict h).charpoly

/-- **`χ(φ|_{im Qm}) ∣ χ_S`**: `Qm : R → K ↠ im Qm` is an onto intertwiner, so
`χ_S = χ(φ|_{im Qm}) · χ(S|_{ker Qm})` (`Psc.KernelCofactor.charpoly_eq_mul_restrict`). -/
theorem imCharpoly_dvd_left (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm) :
    imCharpoly h ∣ S.charpoly := by
  have hint : Qm.rangeRestrict ∘ₗ Matrix.toLin' S = imRestrict h ∘ₗ Qm.rangeRestrict :=
    LinearMap.ext fun u => Subtype.ext (LinearMap.congr_fun h u)
  have h' := Psc.KernelCofactor.charpoly_eq_mul_restrict _
    (LinearMap.surjective_rangeRestrict Qm) _ _ hint
  rw [Matrix.charpoly_toLin'] at h'
  rw [h', imCharpoly]
  exact dvd_mul_right _ _

/-- **`χ(φ|_{im Qm}) ∣ χ_φ`** (`charpoly_restrict_dvd`). -/
theorem imCharpoly_dvd_right [FiniteDimensional K V] (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm) :
    imCharpoly h ∣ φ.charpoly :=
  charpoly_restrict_dvd φ _ (range_invariant h)

/-- `deg χ(φ|_{im Qm}) = dim im Qm`. -/
theorem natDegree_imCharpoly (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm) :
    (imCharpoly h).natDegree = Module.finrank K (LinearMap.range Qm) :=
  LinearMap.charpoly_natDegree _

theorem imCharpoly_monic (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm) : (imCharpoly h).Monic :=
  LinearMap.charpoly_monic _

/-- Every root of `χ(φ|_{im Qm})`, in any extension, is a root of `χ_S` and of
`χ_φ`. -/
theorem aeval_of_imCharpoly [FiniteDimensional K V] (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm)
    {L : Type*} [Field L] [Algebra K L] {z : L} (hz : aeval z (imCharpoly h) = 0) :
    aeval z S.charpoly = 0 ∧ aeval z φ.charpoly = 0 :=
  ⟨aeval_eq_zero_of_dvd_aeval_eq_zero (imCharpoly_dvd_left h) hz,
    aeval_eq_zero_of_dvd_aeval_eq_zero (imCharpoly_dvd_right h) hz⟩

/-- A nonzero image gives a characteristic polynomial of positive degree. -/
theorem natDegree_imCharpoly_pos (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm)
    (hne : LinearMap.range Qm ≠ ⊥) : 0 < (imCharpoly h).natDegree := by
  rw [natDegree_imCharpoly]
  exact Nat.pos_of_ne_zero fun h0 => hne (Submodule.finrank_eq_zero.1 h0)

/-- A nonzero image gives a root of `χ(φ|_{im Qm})` in every algebraically closed
extension. -/
theorem exists_root_imCharpoly (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm)
    (hne : LinearMap.range Qm ≠ ⊥) (L : Type*) [Field L] [IsAlgClosed L] [Algebra K L] :
    ∃ z : L, aeval z (imCharpoly h) = 0 :=
  IsAlgClosed.exists_aeval_eq_zero_of_injective L (algebraMap K L).injective _
    (natDegree_pos_iff_degree_pos.1 (natDegree_imCharpoly_pos h hne)).ne'

/-- **One representative**: if `|R| = 1` and `im Qm ≠ 0`, the divisibility
`imCharpoly_dvd_left` is an equality, `χ(φ|_{im Qm}) = χ_S` (both monic of degree
one). -/
theorem imCharpoly_eq_of_card_eq_one (h : Qm ∘ₗ Matrix.toLin' S = φ ∘ₗ Qm)
    (hR : Fintype.card R = 1) (hne : LinearMap.range Qm ≠ ⊥) : imCharpoly h = S.charpoly :=
  (eq_of_monic_of_dvd_of_natDegree_le (imCharpoly_monic h) (charpoly_monic _)
    (imCharpoly_dvd_left h)
    (by rw [charpoly_natDegree_eq_dim, hR]; exact natDegree_imCharpoly_pos h hne)).symm

/-- **Column identities give the intertwining.**  If `φ (k j) = Σᵢ S i j • k i` for
every `j`, then `Qm = Fintype.linearCombination K k` (`u ↦ Σⱼ uⱼ k j`) satisfies
`Qm ∘ S = φ ∘ Qm`. -/
theorem linearCombination_intertwine (k : R → V) (hk : ∀ j, φ (k j) = ∑ i, S i j • k i) :
    Fintype.linearCombination K k ∘ₗ Matrix.toLin' S = φ ∘ₗ Fintype.linearCombination K k := by
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply, Matrix.toLin'_apply,
    map_sum, map_smul, hk, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- A nonzero column `k j` gives `im (Fintype.linearCombination K k) ≠ 0`. -/
theorem range_linearCombination_ne_bot {k : R → V} {j : R} (hj : k j ≠ 0) :
    LinearMap.range (Fintype.linearCombination K k) ≠ ⊥ := by
  intro h
  have hmem : k j ∈ LinearMap.range (Fintype.linearCombination K k) :=
    ⟨Pi.single j 1, by simp⟩
  rw [h, Submodule.mem_bot] at hmem
  exact hj hmem

end Abstract

/-! ### (d) The sectors `im Q₃ ⊆ Lie₃` and `im Q₄ ⊆ Lie₄` on representatives -/

section Rep

open Psc.Binomial Psc.SignedCocycle Psc.LieWeights Psc.ParikhRank Psc.Degree2Sector

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)

/-- `Lie₃(ℚ³)`, the `ℚ`-span of the eight Lyndon brackets. -/
abbrev Lie3Q : Submodule ℚ (Lie3.Vec3 ℚ) := Submodule.span ℚ (Set.range (Lie3.lyndon (R := ℚ)))

/-- `Lie₄(ℚ³)`, the `ℚ`-span of the eighteen Lyndon brackets. -/
abbrev Lie4Q : Submodule ℚ (Vec4 ℚ) := Submodule.span ℚ (Set.range (lyndon4 (R := ℚ)))

section Deg3

variable (hbal : ∀ T ∈ S.C, Equiv2 T.1 T.2)

/-- The column `j` of `Q₃` as an element of `Lie₃`. -/
def k3Lie (j : P.Rep) : Lie3Q :=
  ⟨Lie3.k3Vec j.1.1 j.1.2, SignedIntertwiner.q3_col_mem_lie3 P hbal j⟩

include hbal in
/-- **`Q₃ S = M^{⊗3} Q₃` over `ℚ`**, column `j`, in the coordinates of
`Psc.Lie3.phi3` (`Psc.SignedIntertwiner.k3_rep`). -/
theorem phi3_k3Vec_rep (j : P.Rep) :
    Lie3.phi3 (incQ S) (Lie3.k3Vec j.1.1 j.1.2) =
      ∑ i : P.Rep, (P.Ssign i j : ℚ) • Lie3.k3Vec i.1.1 i.1.2 := by
  funext a b c
  simp only [Lie3.phi3, incQ, Matrix.map_apply, Lie3.k3Vec, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact_mod_cast SignedIntertwiner.k3_rep P hbal j a b c

/-- **`Q₃ S = Φ₃ Q₃` with `Φ₃ = M^{⊗3}|_{Lie₃}`**, column `j` (the degree-three
twin of `Psc.Defect4Lie.phi4Lie_k4Lie`). -/
theorem phi3Lie_k3Lie (j : P.Rep) :
    phi3Lie (incQ S) (k3Lie P hbal j) = ∑ i : P.Rep, (P.Ssign i j : ℚ) • k3Lie P hbal i := by
  apply Subtype.ext
  simp only [phi3Lie, Submodule.coe_sum, Submodule.coe_smul, k3Lie]
  exact phi3_k3Vec_rep P hbal j

/-- `Q₃ : ℚ^R → Lie₃`, `u ↦ Σⱼ uⱼ K₃(j)`. -/
noncomputable def Q3m : (P.Rep → ℚ) →ₗ[ℚ] Lie3Q := Fintype.linearCombination ℚ (k3Lie P hbal)

/-- `Q₃ ∘ S = Φ₃ ∘ Q₃` as linear maps. -/
theorem q3m_intertwine :
    Q3m P hbal ∘ₗ Matrix.toLin' (SsignQ P) = phi3Lie (incQ S) ∘ₗ Q3m P hbal :=
  linearCombination_intertwine (V := Lie3Q) _ (phi3Lie_k3Lie P hbal)

/-- `q₃ = χ(Φ₃|_{im Q₃})`, a monic rational polynomial. -/
noncomputable def q3 : ℚ[X] := imCharpoly (q3m_intertwine P hbal)

/-- **`q₃ ∣ χ_S`.** -/
theorem q3_dvd_ssign : q3 P hbal ∣ (SsignQ P).charpoly := imCharpoly_dvd_left _

/-- **`q₃ ∣ χ(Φ₃)`.** -/
theorem q3_dvd_phi3 : q3 P hbal ∣ (phi3Lie (incQ S)).charpoly := imCharpoly_dvd_right _

/-- `deg q₃ = rank Q₃`. -/
theorem natDegree_q3 :
    (q3 P hbal).natDegree = Module.finrank ℚ (LinearMap.range (Q3m P hbal)) :=
  natDegree_imCharpoly _

/-- A nonzero column gives `im Q₃ ≠ 0`. -/
theorem range_q3m_ne_bot (hK : ∃ j : P.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0) :
    LinearMap.range (Q3m P hbal) ≠ ⊥ := by
  obtain ⟨j, hj⟩ := hK
  exact range_linearCombination_ne_bot (V := Lie3Q) (j := j) fun h =>
    hj (by simpa [k3Lie] using congrArg Subtype.val h)

theorem natDegree_q3_pos (hK : ∃ j : P.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0) :
    0 < (q3 P hbal).natDegree :=
  natDegree_imCharpoly_pos _ (range_q3m_ne_bot P hbal hK)

/-- A nonzero column gives a complex root of `q₃`. -/
theorem exists_root_q3 (hK : ∃ j : P.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0) :
    ∃ z : ℂ, aeval z (q3 P hbal) = 0 :=
  exists_root_imCharpoly _ (range_q3m_ne_bot P hbal hK) ℂ

/-- **The degree-three bridge.**  For three pairwise distinct roots `x` of `χ_M`,
every root of `q₃` is a root of `χ_S` and a weight `x^κ` of shape `(2,1,0)` or
`(1,1,1)`. -/
theorem root_q3 {L : Type*} [Field L] [CharZero L] (x : Fin 3 → L) (hx : Function.Injective x)
    (hroot : ∀ i, aeval (x i) (incQ S).charpoly = 0) {z : L} (hz : aeval z (q3 P hbal) = 0) :
    aeval z (SsignQ P).charpoly = 0 ∧
      ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 3 ∧ Shape3 κ ∧ z = mono x κ := by
  obtain ⟨hS, hΦ⟩ := aeval_of_imCharpoly (q3m_intertwine P hbal) hz
  exact ⟨hS, root_phi3Lie_of_roots (incQ S) x hx hroot hΦ⟩

/-- **The degree-three bridge, existence**: for irreducible `χ_M` and a nonzero
column, some common complex root of `q₃` and `χ_S` is a weight of shape `(2,1,0)`
or `(1,1,1)` in the three distinct roots of `χ_M`. -/
theorem exists_weight_root_q3 (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0) :
    ∃ x : Fin 3 → ℂ, Function.Injective x ∧ (∀ i, aeval (x i) (incQ S).charpoly = 0) ∧
      ∃ z : ℂ, aeval z (q3 P hbal) = 0 ∧ aeval z (SsignQ P).charpoly = 0 ∧
        ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 3 ∧ Shape3 κ ∧ z = mono x κ := by
  obtain ⟨x, hx, hroot, -⟩ := exists_distinct_roots (L := ℂ) _ hM
  obtain ⟨z, hz⟩ := exists_root_q3 P hbal hK
  exact ⟨x, hx, hroot, z, hz, root_q3 P hbal x hx hroot hz⟩

end Deg3

section Deg4

variable (hbal : ∀ T ∈ S.C, Defect4.Equiv3 T.1 T.2)

/-- `Q₄ : ℚ^R → Lie₄`, `u ↦ Σⱼ uⱼ K₄(j)`. -/
noncomputable def Q4m : (P.Rep → ℚ) →ₗ[ℚ] Lie4Q :=
  Fintype.linearCombination ℚ (Defect4Lie.k4Lie P hbal)

/-- `Q₄ ∘ S = Φ₄ ∘ Q₄` as linear maps (`Psc.Defect4Lie.phi4Lie_k4Lie`). -/
theorem q4m_intertwine :
    Q4m P hbal ∘ₗ Matrix.toLin' (SsignQ P) = phi4Lie (incQ S) ∘ₗ Q4m P hbal :=
  linearCombination_intertwine (V := Lie4Q) _ (Defect4Lie.phi4Lie_k4Lie P hbal)

/-- `q₄ = χ(Φ₄|_{im Q₄})`, a monic rational polynomial. -/
noncomputable def q4 : ℚ[X] := imCharpoly (q4m_intertwine P hbal)

/-- **`q₄ ∣ χ_S`.** -/
theorem q4_dvd_ssign : q4 P hbal ∣ (SsignQ P).charpoly := imCharpoly_dvd_left _

/-- **`q₄ ∣ χ(Φ₄)`.** -/
theorem q4_dvd_phi4 : q4 P hbal ∣ (phi4Lie (incQ S)).charpoly := imCharpoly_dvd_right _

/-- `deg q₄ = rank Q₄`. -/
theorem natDegree_q4 :
    (q4 P hbal).natDegree = Module.finrank ℚ (LinearMap.range (Q4m P hbal)) :=
  natDegree_imCharpoly _

/-- A nonzero column gives `im Q₄ ≠ 0`. -/
theorem range_q4m_ne_bot (hK : ∃ j : P.Rep, Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) :
    LinearMap.range (Q4m P hbal) ≠ ⊥ := by
  obtain ⟨j, hj⟩ := hK
  exact range_linearCombination_ne_bot (V := Lie4Q) (j := j) fun h =>
    hj (by simpa [Defect4Lie.k4Lie] using congrArg Subtype.val h)

theorem natDegree_q4_pos (hK : ∃ j : P.Rep, Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) :
    0 < (q4 P hbal).natDegree :=
  natDegree_imCharpoly_pos _ (range_q4m_ne_bot P hbal hK)

/-- A nonzero column gives a complex root of `q₄`. -/
theorem exists_root_q4 (hK : ∃ j : P.Rep, Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) :
    ∃ z : ℂ, aeval z (q4 P hbal) = 0 :=
  exists_root_imCharpoly _ (range_q4m_ne_bot P hbal hK) ℂ

/-- **The degree-four bridge.**  For three pairwise distinct roots `x` of `χ_M`,
every root of `q₄` is a root of `χ_S` and a weight `x^κ` of shape `(3,1,0)`,
`(2,2,0)` or `(2,1,1)`. -/
theorem root_q4 {L : Type*} [Field L] [CharZero L] (x : Fin 3 → L) (hx : Function.Injective x)
    (hroot : ∀ i, aeval (x i) (incQ S).charpoly = 0) {z : L} (hz : aeval z (q4 P hbal) = 0) :
    aeval z (SsignQ P).charpoly = 0 ∧
      ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 4 ∧ Shape4 κ ∧ z = mono x κ := by
  obtain ⟨hS, hΦ⟩ := aeval_of_imCharpoly (q4m_intertwine P hbal) hz
  exact ⟨hS, root_phi4Lie_of_roots (incQ S) x hx hroot hΦ⟩

/-- **The degree-four bridge, existence**: for irreducible `χ_M` and a nonzero
column, some common complex root of `q₄` and `χ_S` is a weight of shape
`(3,1,0)`, `(2,2,0)` or `(2,1,1)` in the three distinct roots of `χ_M`. -/
theorem exists_weight_root_q4 (hM : Irreducible (incQ S).charpoly)
    (hK : ∃ j : P.Rep, Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) :
    ∃ x : Fin 3 → ℂ, Function.Injective x ∧ (∀ i, aeval (x i) (incQ S).charpoly = 0) ∧
      ∃ z : ℂ, aeval z (q4 P hbal) = 0 ∧ aeval z (SsignQ P).charpoly = 0 ∧
        ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 4 ∧ Shape4 κ ∧ z = mono x κ := by
  obtain ⟨x, hx, hroot, -⟩ := exists_distinct_roots (L := ℂ) _ hM
  obtain ⟨z, hz⟩ := exists_root_q4 P hbal hK
  exact ⟨x, hx, hroot, z, hz, root_q4 P hbal x hx hroot hz⟩

/-- **The input of `Psc.GaloisOrbit` for `q = q₄`.**  For pairwise distinct roots
`β, α, γ` of `χ_M` (in any order, e.g. the Perron root first) and a nonzero
column, `q₄` vanishes at some `β^a α^b γ^c` with `(a, b, c)` a permutation of
`(3,1,0)`, `(2,2,0)` or `(2,1,1)`, listed as in the hypotheses `habc` of
`orbit_310_excluded`, `orbit_220_forces_complex_unit`, `orbit_211_forces_unit`.
Only `habc` and `hq` are supplied.  To compose, those theorems also need, none of it
supplied here: `Irreducible f` with `f = (incQ S).charpoly` (`natDegree f = 3` is
`Matrix.charpoly_natDegree_eq_dim`); `1 ≤ ‖β * α * γ‖`; for `orbit_310_excluded`
the Pisot moduli `1 < ‖β‖`, `‖α‖ < 1`, `‖γ‖ < 1`, and then a bound on the roots of
`q₄` to contradict its conclusion; for `orbit_211_forces_unit` and
`orbit_220_forces_complex_unit` (the latter also `1 < ‖β‖`) the bound `hbound`:
every root of `q₄` has modulus `≤ ‖β‖`.  The roots of `q₄` are roots of `χ_S`
(`q4_dvd_ssign`), so that bound is `ρ(S) ≤ β` stated for the roots of `χ_S`. -/
theorem galoisOrbit_input_q4 {β α γ : ℂ} (hβ : aeval β (incQ S).charpoly = 0)
    (hα : aeval α (incQ S).charpoly = 0) (hγ : aeval γ (incQ S).charpoly = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    (hK : ∃ j : P.Rep, Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0) :
    ∃ a b c : ℕ,
      (((a, b, c) = (3, 1, 0) ∨ (a, b, c) = (3, 0, 1) ∨ (a, b, c) = (1, 3, 0) ∨
          (a, b, c) = (0, 3, 1) ∨ (a, b, c) = (1, 0, 3) ∨ (a, b, c) = (0, 1, 3)) ∨
        ((a, b, c) = (2, 2, 0) ∨ (a, b, c) = (2, 0, 2) ∨ (a, b, c) = (0, 2, 2)) ∨
        ((a, b, c) = (2, 1, 1) ∨ (a, b, c) = (1, 2, 1) ∨ (a, b, c) = (1, 1, 2))) ∧
      aeval (β ^ a * α ^ b * γ ^ c) (q4 P hbal) = 0 := by
  have hx : Function.Injective ![β, α, γ] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hroot : ∀ i, aeval (![β, α, γ] i) (incQ S).charpoly = 0 := by
    intro i; fin_cases i <;> simpa
  obtain ⟨z, hz⟩ := exists_root_q4 P hbal hK
  obtain ⟨-, κ, -, hsh, rfl⟩ := root_q4 P hbal ![β, α, γ] hx hroot hz
  refine ⟨κ 0, κ 1, κ 2, hsh.triple, ?_⟩
  rw [mono_fin_three] at hz
  simpa using hz

end Deg4

end Rep

/-! ### Controls -/

section Controls

open Psc.Binomial Psc.SignedCocycle Psc.LieWeights Psc.SignedIntertwiner Psc.ParikhRank
  Psc.Degree2Sector

/-- Non-vacuity of (a): `M0` (`χ = x³ − 32x² + 5x + 2`, irreducible) is
diagonalized over `ℂ`. -/
theorem m0_diagonalization :
    ∃ x : Fin 3 → ℂ, Function.Injective x ∧ (∀ i, aeval (x i) Psc.M0Pisot.M0.charpoly = 0) ∧
      (∀ z : ℂ, aeval z Psc.M0Pisot.M0.charpoly = 0 → z = x 0 ∨ z = x 1 ∨ z = x 2) ∧
      ∃ Q : Matrix (Fin 3) (Fin 3) ℂ, IsUnit Q.det ∧
        Psc.M0Pisot.M0.map (algebraMap ℚ ℂ) = Q * Matrix.diagonal x * Q⁻¹ :=
  exists_diagonalization _ Psc.KernelCofactor.ctrl_irreducible

/-- Non-vacuity of (a) on an actual substitution: `plasticSubst`
(`χ = X³ − X − 1`). -/
theorem plastic_diagonalization :
    ∃ x : Fin 3 → ℂ, Function.Injective x ∧
      (∀ i, aeval (x i) ((Psc.Incidence.inc plasticSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0) ∧
      (∀ z : ℂ, aeval z ((Psc.Incidence.inc plasticSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
        z = x 0 ∨ z = x 1 ∨ z = x 2) ∧
      ∃ Q : Matrix (Fin 3) (Fin 3) ℂ, IsUnit Q.det ∧
        ((Psc.Incidence.inc plasticSubst).map (Nat.cast : ℕ → ℚ)).map (algebraMap ℚ ℂ) =
          Q * Matrix.diagonal x * Q⁻¹ :=
  exists_diagonalization _ plastic_irreducible

/-- Non-vacuity of (b) at degree four: the weights of the rational `Φ₄` of `M0`. -/
theorem m0_roots_phi4Lie :
    ∃ x : Fin 3 → ℂ, Function.Injective x ∧ (∀ i, aeval (x i) Psc.M0Pisot.M0.charpoly = 0) ∧
      (∀ z : ℂ, aeval z Psc.M0Pisot.M0.charpoly = 0 → ∃ i, z = x i) ∧
      ∀ z : ℂ, aeval z (phi4Lie Psc.M0Pisot.M0).charpoly = 0 →
        ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 4 ∧ Shape4 κ ∧ z = mono x κ :=
  roots_phi4Lie_of_irreducible _ Psc.KernelCofactor.ctrl_irreducible

/-- Non-vacuity of (b) at degree three: the weights of the rational `Φ₃` of `M0`. -/
theorem m0_roots_phi3Lie :
    ∃ x : Fin 3 → ℂ, Function.Injective x ∧ (∀ i, aeval (x i) Psc.M0Pisot.M0.charpoly = 0) ∧
      (∀ z : ℂ, aeval z Psc.M0Pisot.M0.charpoly = 0 → ∃ i, z = x i) ∧
      ∀ z : ℂ, aeval z (phi3Lie Psc.M0Pisot.M0).charpoly = 0 →
        ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 3 ∧ Shape3 κ ∧ z = mono x κ :=
  roots_phi3Lie_of_irreducible _ Psc.KernelCofactor.ctrl_irreducible

theorem wT_k3_col_ne : ∃ j : wTNorm.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0 :=
  ⟨wTRep, fun h => by
    have := congrFun (congrFun (congrFun h 0) 1) 0
    simp [Lie3.k3Vec, wTRep, wT_k3_ne] at this⟩

/-- Non-vacuity of (c), (d) at degree three: on `wT` (`Equiv2` states, `K₃ ≠ 0`),
`im Q₃ ≠ 0`, so `q₃` has positive degree. -/
theorem wT_q3_pos : 0 < (q3 wTNorm wT_equiv2).natDegree :=
  natDegree_q3_pos _ _ wT_k3_col_ne

/-- On `wT` (one representative, `S = (1)`), `q₃ = χ_S`: the divisibility
`q3_dvd_ssign` is an equality. -/
theorem wT_q3_eq : q3 wTNorm wT_equiv2 = (SsignQ wTNorm).charpoly :=
  imCharpoly_eq_of_card_eq_one _ (Fintype.card_eq_one_iff.2 ⟨wTRep, wTNorm_rep⟩)
    (range_q3m_ne_bot _ _ wT_k3_col_ne)

theorem wT_exists_root_q3 : ∃ z : ℂ, aeval z (q3 wTNorm wT_equiv2) = 0 :=
  exists_root_q3 _ _ wT_k3_col_ne

/-- Non-vacuity of (c), (d) at degree four: on `w4` (`Equiv3` states, `K₄ ≠ 0`),
`im Q₄ ≠ 0`, so `q₄` has positive degree. -/
theorem w4_q4_pos : 0 < (q4 Defect4.w4Norm Defect4.w4_equiv3).natDegree :=
  natDegree_q4_pos _ _ ⟨Defect4.w4Rep, Defect4Lie.w4_k4Vec_ne⟩

/-- On `w4` (one representative, `S = (1)`), `q₄ = χ_S`. -/
theorem w4_q4_eq : q4 Defect4.w4Norm Defect4.w4_equiv3 = (SsignQ Defect4.w4Norm).charpoly :=
  imCharpoly_eq_of_card_eq_one _ (Fintype.card_eq_one_iff.2 ⟨Defect4.w4Rep, Defect4.w4Norm_rep⟩)
    (range_q4m_ne_bot _ _ ⟨Defect4.w4Rep, Defect4Lie.w4_k4Vec_ne⟩)

theorem w4_exists_root_q4 : ∃ z : ℂ, aeval z (q4 Defect4.w4Norm Defect4.w4_equiv3) = 0 :=
  exists_root_q4 _ _ ⟨Defect4.w4Rep, Defect4Lie.w4_k4Vec_ne⟩

/-! #### The bridge with every hypothesis: the 3-cycle relabelling

A permutation substitution, not primitive and not Pisot (`χ_M = X³ − 1`): it shows
only that the hypotheses of `root_q3`, `root_q4`, `galoisOrbit_input_q4` (states,
a nonzero column, three distinct roots of `χ_M`) are jointly satisfiable. -/

/-- The 3-cycle relabelling `0 ↦ 1 ↦ 2 ↦ 0`. -/
def cycSubst : Fin 3 → List (Fin 3) := ![[1], [2], [0]]

/-- Its rational incidence matrix (`incQ` of every child system over `cycSubst`). -/
abbrev cycM : Matrix (Fin 3) (Fin 3) ℚ := (Psc.Incidence.inc cycSubst).map (Nat.cast : ℕ → ℚ)

/-- `χ_M = X³ − 1` (trace `0`, trace of `Λ²M` `0`, `det M = 1`). -/
theorem cycM_charpoly : cycM.charpoly = X ^ 3 - 1 := by
  rw [Psc.Cyclicity.charpoly_fin_three]
  have htr : cycM.trace = 0 := by simp [Matrix.trace_fin_three, cycSubst]
  have hw : (Psc.Cyclicity.wedge2 cycM).trace = 0 := by
    simp [Matrix.trace_fin_three, Psc.Cyclicity.wedge2, Psc.Cyclicity.pairFst,
      Psc.Cyclicity.pairSnd, cycSubst]
  have hd : cycM.det = 1 := by simp [Matrix.det_fin_three, cycSubst]
  rw [htr, hw, hd]
  simp

/-- A primitive cube root of unity `ζ`. -/
noncomputable def cycRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem cycRoot_prim : IsPrimitiveRoot cycRoot 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- The roots `(1, ζ, ζ²)` of `χ_M = X³ − 1`. -/
noncomputable def cycX : Fin 3 → ℂ := fun i => cycRoot ^ (i : ℕ)

theorem cycX_injective : Function.Injective cycX := fun i j h =>
  Fin.ext (cycRoot_prim.pow_inj i.isLt j.isLt h)

theorem cycX_cube (i : Fin 3) : cycX i ^ 3 = 1 := by
  rw [cycX, ← pow_mul, mul_comm, pow_mul, cycRoot_prim.pow_eq_one, one_pow]

theorem cycX_root (i : Fin 3) : aeval (cycX i) cycM.charpoly = 0 := by
  rw [cycM_charpoly]
  simp [cycX_cube]

/-- `mono_eq_pow_of_cube_eq` on `cycX`: the weights `x₀x₁x₂`, `x₀²x₁x₂` of shape
`(1,1,1)`, `(2,1,1)` equal the pure powers `x₀³`, `x₀⁴`. -/
theorem cycX_mono_pure : mono cycX ![1, 1, 1] = cycX 0 ^ 3 ∧ mono cycX ![2, 1, 1] = cycX 0 ^ 4 :=
  mono_eq_pow_of_cube_eq cycX_injective fun i => by rw [cycX_cube, cycX_cube]

/-! Degree three: the three relabellings of `wTPair`. -/

def cycT1 : List (Fin 3) × List (Fin 3) := ([1, 2, 2, 0, 0, 1, 2], [2, 0, 1, 1, 2, 2, 0])

def cycT2 : List (Fin 3) × List (Fin 3) := ([2, 0, 0, 1, 1, 2, 0], [0, 1, 2, 2, 0, 0, 1])

/-- `cycT1`, `cycT2` are the images of `wTPair` under `cycSubst` and its square. -/
theorem cyc3_states : cycT1 = (subst cycSubst wTPair.1, subst cycSubst wTPair.2) ∧
    cycT2 = (subst cycSubst cycT1.1, subst cycSubst cycT1.2) := by decide

/-- The zero-return system: each relabelling's only child is the next one. -/
def cyc3Sys : ChildSystem (Fin 3) :=
  Psc.Reduction.redSystem cycSubst (by decide)
    {wTPair, cycT1, cycT2, wTPair.swap, cycT1.swap, cycT2.swap} (by decide) (by decide)

def cyc3Norm : Normalisation cyc3Sys :=
  Psc.Reduction.redNormalisation cycSubst (by decide)
    {wTPair, cycT1, cycT2, wTPair.swap, cycT1.swap, cycT2.swap} (by decide) (by decide)
    (by decide) {wTPair, cycT1, cycT2} (by decide) (by decide) (by decide)

theorem cyc3_equiv2 : ∀ T ∈ cyc3Sys.C, Equiv2 T.1 T.2 := by
  unfold Equiv2 Equiv1; decide

theorem cyc3_k3_col_ne : ∃ j : cyc3Norm.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0 :=
  ⟨⟨wTPair, by decide⟩, fun h => by
    have := congrFun (congrFun (congrFun h 0) 1) 0
    simp [Lie3.k3Vec, wT_k3_ne] at this⟩

/-- **Full control of `root_q3`**: on `cyc3Norm` every hypothesis holds, and `q₃` has a
complex root, which is a root of `χ_S` and a weight `cycX^κ` of shape `(2,1,0)` or
`(1,1,1)`. -/
theorem cyc3_root_q3 : ∃ z : ℂ, aeval z (q3 cyc3Norm cyc3_equiv2) = 0 ∧
    aeval z (SsignQ cyc3Norm).charpoly = 0 ∧
      ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 3 ∧ Shape3 κ ∧ z = mono cycX κ := by
  obtain ⟨z, hz⟩ := exists_root_q3 cyc3Norm cyc3_equiv2 cyc3_k3_col_ne
  exact ⟨z, hz, root_q3 cyc3Norm cyc3_equiv2 cycX cycX_injective cycX_root hz⟩

/-! Degree four: the three relabellings of `w4Pair`. -/

def cyc4T1 : List (Fin 3) × List (Fin 3) :=
  ([1, 2, 2, 0, 0, 1, 2, 1, 1, 2, 2, 0], [2, 0, 1, 1, 2, 1, 2, 2, 0, 0, 1, 2])

def cyc4T2 : List (Fin 3) × List (Fin 3) :=
  ([2, 0, 0, 1, 1, 2, 0, 2, 2, 0, 0, 1], [0, 1, 2, 2, 0, 2, 0, 0, 1, 1, 2, 0])

/-- `cyc4T1`, `cyc4T2` are the images of `w4Pair` under `cycSubst` and its square. -/
theorem cyc4_states :
    cyc4T1 = (subst cycSubst Defect4.w4Pair.1, subst cycSubst Defect4.w4Pair.2) ∧
      cyc4T2 = (subst cycSubst cyc4T1.1, subst cycSubst cyc4T1.2) := by decide

def cyc4Sys : ChildSystem (Fin 3) :=
  Psc.Reduction.redSystem cycSubst (by decide)
    {Defect4.w4Pair, cyc4T1, cyc4T2, Defect4.w4Pair.swap, cyc4T1.swap, cyc4T2.swap}
    (by decide) (by decide)

def cyc4Norm : Normalisation cyc4Sys :=
  Psc.Reduction.redNormalisation cycSubst (by decide)
    {Defect4.w4Pair, cyc4T1, cyc4T2, Defect4.w4Pair.swap, cyc4T1.swap, cyc4T2.swap}
    (by decide) (by decide) (by decide) {Defect4.w4Pair, cyc4T1, cyc4T2} (by decide)
    (by decide) (by decide)

theorem cyc4_equiv3 : ∀ T ∈ cyc4Sys.C, Defect4.Equiv3 T.1 T.2 := by decide

theorem cyc4_k4_col_ne : ∃ j : cyc4Norm.Rep, Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0 :=
  ⟨⟨Defect4.w4Pair, by decide⟩, Defect4Lie.w4_k4Vec_ne⟩

/-- **Full control of `root_q4`.** -/
theorem cyc4_root_q4 : ∃ z : ℂ, aeval z (q4 cyc4Norm cyc4_equiv3) = 0 ∧
    aeval z (SsignQ cyc4Norm).charpoly = 0 ∧
      ∃ κ : Fin 3 → ℕ, ∑ i, κ i = 4 ∧ Shape4 κ ∧ z = mono cycX κ := by
  obtain ⟨z, hz⟩ := exists_root_q4 cyc4Norm cyc4_equiv3 cyc4_k4_col_ne
  exact ⟨z, hz, root_q4 cyc4Norm cyc4_equiv3 cycX cycX_injective cycX_root hz⟩

/-- **Full control of `galoisOrbit_input_q4`**, at `(β, α, γ) = (1, ζ, ζ²)`. -/
theorem cyc4_galoisOrbit_input : ∃ a b c : ℕ,
      (((a, b, c) = (3, 1, 0) ∨ (a, b, c) = (3, 0, 1) ∨ (a, b, c) = (1, 3, 0) ∨
          (a, b, c) = (0, 3, 1) ∨ (a, b, c) = (1, 0, 3) ∨ (a, b, c) = (0, 1, 3)) ∨
        ((a, b, c) = (2, 2, 0) ∨ (a, b, c) = (2, 0, 2) ∨ (a, b, c) = (0, 2, 2)) ∨
        ((a, b, c) = (2, 1, 1) ∨ (a, b, c) = (1, 2, 1) ∨ (a, b, c) = (1, 1, 2))) ∧
      aeval (cycX 0 ^ a * cycX 1 ^ b * cycX 2 ^ c) (q4 cyc4Norm cyc4_equiv3) = 0 :=
  galoisOrbit_input_q4 cyc4Norm cyc4_equiv3 (cycX_root 0) (cycX_root 1) (cycX_root 2)
    (cycX_injective.ne (by decide)) (cycX_injective.ne (by decide))
    (cycX_injective.ne (by decide)) cyc4_k4_col_ne

end Controls

/-! ### Shared helpers of `Psc.Degree3Sector` and `Psc.Degree4Floor` -/

section Shared

theorem vec3_injective {L : Type*} {β α γ : L} (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) :
    Function.Injective ![β, α, γ] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem vec3_roots {L : Type*} [Field L] [Algebra ℚ L] {p : ℚ[X]} {β α γ : L}
    (hβ : aeval β p = 0) (hα : aeval α p = 0) (hγ : aeval γ p = 0) :
    ∀ i, aeval (![β, α, γ] i) p = 0 := by
  intro i; fin_cases i <;> simpa

/-- **`det M = βαγ`** for pairwise distinct roots `β, α, γ` of `χ_M` (from the
diagonalization `Psc.SectorBridge.exists_conj_diagonal`). -/
theorem det_eq_mul_roots (M : Matrix (Fin 3) (Fin 3) ℚ) {β α γ : ℂ}
    (hβ : aeval β M.charpoly = 0) (hα : aeval α M.charpoly = 0) (hγ : aeval γ M.charpoly = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) : (M.det : ℂ) = β * α * γ := by
  obtain ⟨Q, hQ, hMQ⟩ :=
    exists_conj_diagonal M ![β, α, γ] (vec3_injective hβα hβγ hαγ) (vec3_roots hβ hα hγ)
  have h := RingHom.map_det (algebraMap ℚ ℂ) M
  rw [RingHom.mapMatrix_apply, hMQ, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det Q).mpr hQ),
    Matrix.det_diagonal, Fin.prod_univ_three] at h
  rw [← eq_ratCast (algebraMap ℚ ℂ), h]
  simp [mul_assoc]

/-- **Three pairwise distinct complex roots of `χ_M` are all of its roots**: they form a
sub-multiset of the roots of `χ_M` over `ℂ`, which has cardinality three
(`IsAlgClosed.card_roots_eq_natDegree`). -/
theorem root_cases (M : Matrix (Fin 3) (Fin 3) ℚ) {β α γ : ℂ}
    (hβ : aeval β M.charpoly = 0) (hα : aeval α M.charpoly = 0) (hγ : aeval γ M.charpoly = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) {z : ℂ} (hz : aeval z M.charpoly = 0) :
    z = β ∨ z = α ∨ z = γ := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℂ := M.map (algebraMap ℚ ℂ)
  have hcp : A.charpoly = M.charpoly.map (algebraMap ℚ ℂ) := Matrix.charpoly_map M _
  have hp0 : A.charpoly ≠ 0 := (charpoly_monic A).ne_zero
  have hmem : ∀ w : ℂ, aeval w M.charpoly = 0 → w ∈ A.charpoly.roots := fun w hw => by
    rw [mem_roots hp0, IsRoot.def, hcp, eval_map_algebraMap]; exact hw
  have hnd : ({β, α, γ} : Multiset ℂ).Nodup := by simp [hβα, hβγ, hαγ]
  have hle : ({β, α, γ} : Multiset ℂ) ≤ A.charpoly.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro w hw
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hmem _ hβ
    · exact hmem _ hα
    · exact hmem _ hγ
  have hcard : A.charpoly.roots.card ≤ ({β, α, γ} : Multiset ℂ).card := by
    rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim, Fintype.card_fin]
    simp
  have hz' := hmem z hz
  rw [← Multiset.eq_of_le_of_card_le hle hcard] at hz'
  simpa using hz'

/-- `1 ≤ ‖βαγ‖` from `1 ≤ |det M|` (`det_eq_mul_roots`). -/
theorem one_le_norm_mul_roots {M : Matrix (Fin 3) (Fin 3) ℚ} {β α γ : ℂ}
    (hβ : aeval β M.charpoly = 0) (hα : aeval α M.charpoly = 0) (hγ : aeval γ M.charpoly = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) (hdet : 1 ≤ |M.det|) : 1 ≤ ‖β * α * γ‖ := by
  rw [← det_eq_mul_roots M hβ hα hγ hβα hβγ hαγ, Complex.norm_ratCast]
  exact_mod_cast hdet

/-- `det M0 = -2`. -/
theorem M0_det : Psc.M0Pisot.M0.det = -2 := by
  rw [Matrix.det_fin_three]; simp [Psc.M0Pisot.M0]; norm_num

open Psc.Binomial Psc.SignedCocycle Psc.Degree2Sector in
/-- A complex root of `χ_S` is an eigenvalue of `S` over `ℂ`, in the form
`P.Ssign.map Int.cast` used by `Psc.SignedCocycle` and `Psc.CocycleSpectrum`. -/
theorem exists_eigen_of_root_ssign {S : ChildSystem (Fin 3)} (P : Normalisation S) {μ : ℂ}
    (hμ : aeval μ (SsignQ P).charpoly = 0) :
    ∃ x : P.Rep → ℂ, x ≠ 0 ∧ P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x := by
  have hm : (SsignQ P).map (algebraMap ℚ ℂ) = P.Ssign.map (Int.cast : ℤ → ℂ) := by ext; simp
  obtain ⟨x, hx0, hx⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot
    ((SsignQ P).map (algebraMap ℚ ℂ)) μ (by rw [Matrix.charpoly_map, eval_map_algebraMap]; exact hμ)
  exact ⟨x, hx0, hm ▸ hx⟩

open Psc.Binomial Psc.SignedCocycle Psc.Degree2Sector in
/-- **`prop:cocycle`'s `ρ(S) ≤ β` as a bound on the roots of `χ_S`, from Perron data for
`N_C`.**  If `L` is a positive left `β`-eigenvector of `N_C`, every complex root of `χ_S`
has modulus at most `β`: it is an eigenvalue of `S` (`exists_eigen_of_root_ssign`), and
`|S| ≤ N_C` entrywise (`Psc.SignedCocycle.Normalisation.ssign_abs_le`) with
`Psc.ParikhIntertwiner.spectral_bound`.  Neither strong connectivity nor primitivity is
used. -/
theorem ssign_root_bound_of_perron {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) {β : ℝ}
    (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L) :
    ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ β := by
  intro μ hμ
  obtain ⟨x, hx0, hx⟩ := exists_eigen_of_root_ssign P hμ
  exact Psc.ParikhIntertwiner.spectral_bound _ L hL β hLN _
    (fun i j => by
      have h := P.ssign_abs_le i j
      simp only [Matrix.map_apply, Complex.norm_intCast]
      exact_mod_cast h) x hx0 μ hx

end Shared

end Psc.SectorBridge
