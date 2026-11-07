/-
# Cyclicity of an irreducible `3 × 3` matrix and of its exterior square

`docs/c4-concentration-attack-2026-11-06.md` §§2, 3, 8.

This module discharges the hypothesis `hcyc` of
`Psc.ConcentrationAlgebra.eigenrow_eq_zero` for `W = Λ²M`, when `M` is a rational
`3 × 3` matrix with irreducible characteristic polynomial.

## What is proved

* `cyclic_of_irreducible`: over a field `F`, if `W : Matrix (Fin 3) (Fin 3) F`
  has irreducible characteristic polynomial, then every nonzero `w` is a cyclic
  vector: `w, W w, W² w` are linearly independent.
  (A dependency gives a nonzero `p` of degree `≤ 2` with `p(W) w = 0`;
  Cayley–Hamilton gives `χ_W(W) w = 0`; `p` and `χ_W` are coprime since `χ_W`
  is irreducible of degree `3`; Bézout gives `w = 0`.)
* `invariant_eq_bot_or_top`: for the same `W`, every `W`-invariant subspace of
  `F³` is `⊥` or `⊤`.
* `wedge2`: the exterior square `Λ²M` written in the basis
  `(e₀∧e₁, e₀∧e₂, e₁∧e₂)`; its entries are the `2 × 2` minors
  `Λ²M (a,b) (c,e) = M a c * M b e - M a e * M b c`.
* `wedge2_transpose_mul_mul`: the identity `(Λ²M)ᵀ · P · M = det M • P` for the
  fixed signed permutation matrix `wedgePairing` (`P`) encoding the pairing
  `Λ² × Λ¹ → Λ³`, valid over any commutative ring.
* `irreducible_wedge2`: for `M` rational with `χ_M` irreducible, `χ_{Λ²M}` is
  irreducible.  (A rational root `r` of the cubic `χ_{Λ²M}` gives a rational
  eigenvector `v`; `det M ≠ 0` because `0` is not a root of `χ_M`; the pairing
  identity turns `v` into a left eigen-row `v P` of `M` with eigenvalue
  `det M / r`, contradicting that the irreducible cubic `χ_M` has no root.)
* `eigenrow_wedge2`: the Galois lemma `eigenrow_eq_zero` specialised to
  `W = Λ²M`: a left eigen-row of `Λ²M` over any field extension of `ℚ` that
  vanishes on a nonzero rational vector is zero.

## Hypotheses

* `Irreducible W.charpoly` (resp. `Irreducible M.charpoly`): the only standing
  hypothesis; in the PSC setting it is irreducibility of the incidence cubic.
* In `eigenrow_wedge2`: `y` is a left eigen-row of `Λ²M` mapped to `K`
  (`hy`), `w` is a nonzero rational vector (`hw0`) and `y` vanishes on it (`hw`).

## What is NOT formalized

* The identification of `wedge2 M` with the action of `M` on `Λ²ℚ³` (Mathlib's
  exterior algebra) is not formalized; `wedge2` is the explicit minor matrix.
* The application to the Concentration attack (that the relevant rows are the
  eigen-rows of `Λ²M` attached to Galois conjugate products of eigenvalues, and
  that `K₂` is rational) is not formalized here.
* That `K₂(σT) = wedge2 M · K₂(T)` in these coordinates (the intertwining of
  `prop:midarea`) is not formalized here.  `irreducible_wedge2_of_field`
  proves irreducibility of `χ_{Λ²M}` over any field; `irreducible_wedge2` is
  its `ℚ` instance.
-/
import Mathlib
import PscVerif.ConcentrationAlgebra

set_option linter.unusedSectionVars false

namespace Psc.Cyclicity

open Matrix Polynomial

/-! ### Cyclic vectors of a matrix with irreducible characteristic polynomial -/

section Cyclic

variable {F : Type*} [Field F]

theorem cyclic_of_irreducible (W : Matrix (Fin 3) (Fin 3) F)
    (hW : Irreducible W.charpoly) (w : Fin 3 → F) (hw : w ≠ 0) :
    LinearIndependent F ![w, W *ᵥ w, W *ᵥ (W *ᵥ w)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  rw [not_forall] at hne
  obtain ⟨i, hi⟩ := hne
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  set p : F[X] := C (g 0) + C (g 1) * X + C (g 2) * X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h
    have h0 := congrArg (fun q => q.coeff 0) h
    have h1 := congrArg (fun q => q.coeff 1) h
    have h2 := congrArg (fun q => q.coeff 2) h
    simp [hp, coeff_X, coeff_C, coeff_X_pow] at h0 h1 h2
    fin_cases i <;> simp_all
  have hpdeg : p.natDegree ≤ 2 := by
    rw [hp]; compute_degree
  have hpw : aeval W p *ᵥ w = 0 := by
    simp only [hp, map_add, map_mul, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one, add_mulVec, smul_mul_assoc, one_mul, smul_mulVec,
      one_mulVec, pow_two, ← mulVec_mulVec]
    exact hg
  have hndvd : ¬ W.charpoly ∣ p := by
    intro hd
    have := natDegree_le_of_dvd hd hp0
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    omega
  obtain ⟨a, b, hab⟩ := (hW.coprime_iff_not_dvd).mpr hndvd
  have h1 := congrArg (fun q => aeval W q *ᵥ w) hab
  simp only [map_add, map_mul, aeval_self_charpoly, mul_zero, zero_add, map_one,
    one_mulVec] at h1
  rw [← mulVec_mulVec, hpw, mulVec_zero] at h1
  exact hw h1.symm

theorem invariant_eq_bot_or_top (W : Matrix (Fin 3) (Fin 3) F)
    (hW : Irreducible W.charpoly) (p : Submodule F (Fin 3 → F))
    (hp : ∀ x ∈ p, W *ᵥ x ∈ p) : p = ⊥ ∨ p = ⊤ := by
  by_cases hbot : p = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwp, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hli := cyclic_of_irreducible W hW w hw0
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · exact hwp
  · exact hp _ hwp
  · exact hp _ (hp _ hwp)

end Cyclic

/-! ### The exterior square -/

section Wedge

variable {R : Type*} [CommRing R]

/-- First index of the basis pair: `0 ↦ (0,1)`, `1 ↦ (0,2)`, `2 ↦ (1,2)`. -/
def pairFst : Fin 3 → Fin 3 := ![0, 0, 1]

/-- Second index of the basis pair: `0 ↦ (0,1)`, `1 ↦ (0,2)`, `2 ↦ (1,2)`. -/
def pairSnd : Fin 3 → Fin 3 := ![1, 2, 2]

/-- The exterior square `Λ²M` in the basis `(e₀∧e₁, e₀∧e₂, e₁∧e₂)`: entry
`(I, J)` with `I ↔ (a,b)`, `J ↔ (c,e)` is the minor `M a c * M b e - M a e * M b c`. -/
def wedge2 (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun I J =>
    M (pairFst I) (pairFst J) * M (pairSnd I) (pairSnd J) -
      M (pairFst I) (pairSnd J) * M (pairSnd I) (pairFst J)

/-- The pairing `Λ² × Λ¹ → Λ³`: `(e₀∧e₁)∧e₂ = 1`, `(e₀∧e₂)∧e₁ = -1`,
`(e₁∧e₂)∧e₀ = 1`. -/
def wedgePairing : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem wedge2_transpose_mul_mul (M : Matrix (Fin 3) (Fin 3) R) :
    (wedge2 M)ᵀ * wedgePairing * M = M.det • wedgePairing := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wedge2, wedgePairing, pairFst, pairSnd, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.det_fin_three] <;> ring

end Wedge

/-! ### Irreducibility of `χ_{Λ²M}` -/

section Irreducible

variable {F : Type*} [Field F]

/-- A root of the characteristic polynomial gives an eigenvector. -/
theorem not_isRoot_of_irreducible (A : Matrix (Fin 3) (Fin 3) F)
    (hA : Irreducible A.charpoly) (r : F) : A.charpoly.eval r ≠ 0 := by
  intro hr
  have := degree_eq_one_of_irreducible_of_root hA hr
  rw [degree_eq_natDegree (charpoly_monic A).ne_zero, charpoly_natDegree_eq_dim,
    Fintype.card_fin] at this
  norm_num at this

theorem det_ne_zero_of_irreducible (A : Matrix (Fin 3) (Fin 3) F)
    (hA : Irreducible A.charpoly) : A.det ≠ 0 := by
  intro hd
  apply not_isRoot_of_irreducible A hA 0
  rw [eval_charpoly, scalar_apply, diagonal_zero, zero_sub, det_neg, hd, mul_zero]

theorem vecMul_wedgePairing_ne_zero (v : Fin 3 → F) (hv : v ≠ 0) :
    v ᵥ* (wedgePairing : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
  intro h
  apply hv
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [wedgePairing, vecMul, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  ext k
  fin_cases k <;> simp [h0, h1, h2]

theorem irreducible_wedge2_of_field (M : Matrix (Fin 3) (Fin 3) F)
    (hM : Irreducible M.charpoly) : Irreducible (wedge2 M).charpoly := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp
  intro r hr
  obtain ⟨v, hv0, hv⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot (wedge2 M) r hr
  set u := v ᵥ* (wedgePairing : Matrix (Fin 3) (Fin 3) F) with hu
  have hu0 : u ≠ 0 := vecMul_wedgePairing_ne_zero v hv0
  have hdet := det_ne_zero_of_irreducible M hM
  -- `r • (u ᵥ* M) = det M • u`
  have key : r • (u ᵥ* M) = M.det • u := by
    have hvt : v ᵥ* (wedge2 M)ᵀ = r • v := by rw [vecMul_transpose, hv]
    calc r • (u ᵥ* M) = ((r • v) ᵥ* wedgePairing) ᵥ* M := by
          rw [hu, smul_vecMul, smul_vecMul]
      _ = v ᵥ* ((wedge2 M)ᵀ * wedgePairing * M) := by
          rw [← hvt, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc]
      _ = M.det • u := by
          rw [wedge2_transpose_mul_mul, vecMul_smul, hu]
  by_cases hr0 : r = 0
  · rw [hr0, zero_smul] at key
    exact hdet (smul_eq_zero.mp key.symm |>.resolve_right hu0)
  · apply not_isRoot_of_irreducible M hM (M.det / r)
    apply Psc.ConcentrationAlgebra.isRoot_of_left_eigen M _ u hu0
    rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ hr0, one_smul]

theorem irreducible_wedge2 (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : Irreducible M.charpoly) : Irreducible (wedge2 M).charpoly :=
  irreducible_wedge2_of_field M hM

end Irreducible

/-! ### The Galois lemma for `Λ²M` -/

theorem eigenrow_wedge2 {K : Type*} [Field K] [Algebra ℚ K]
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : Irreducible M.charpoly)
    (y : Fin 3 → K) (μ : K) (hy : y ᵥ* (wedge2 M).map (algebraMap ℚ K) = μ • y)
    (w : Fin 3 → ℚ) (hw0 : w ≠ 0) (hw : y ⬝ᵥ (algebraMap ℚ K ∘ w) = 0) : y = 0 :=
  Psc.ConcentrationAlgebra.eigenrow_eq_zero (wedge2 M)
    (cyclic_of_irreducible (wedge2 M) (irreducible_wedge2 M hM)) y μ hy w hw0 hw

end Psc.Cyclicity
