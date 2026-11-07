/-
# Perron simplicity discharges the kernel-splitting hypothesis

`docs/c4-concentration-attack-2026-11-06.md` §§2, 3, 8.  The factorization step
`Psc.ConcentrationAlgebra.exists_factor_through` (Theorem A(iv)) assumes

  `hsplit : ∀ x ∈ ker P, ∃ z ∈ ker P, x = f(N) z`,   `f = χ_M`,

i.e. that `f(N)` maps `ker P` onto itself.  This module derives `hsplit` from
Perron data, without Galois theory and without the Perron–Frobenius existence
theorem (only the elementary equality cases of `Psc.PerronCore` are used).

Standing data (hypotheses of the three main theorems):

* `ι` a finite index type (`Fintype`, `DecidableEq`);
* `N : Matrix ι ι ℚ` with `hN : ∀ i j, 0 ≤ N i j` (the incidence matrix of the
  balanced-pair / state system is non-negative);
* `hSC : PerronCore.StronglyConnected (N.map (↑) : Matrix ι ι ℝ)` (the positive
  entries of `N` form a strongly connected digraph);
* `M : Matrix (Fin 3) (Fin 3) ℚ` with `hM : Irreducible M.charpoly` (the
  incidence cubic `f := χ_M` is irreducible over `ℚ`);
* `P : Matrix (Fin 3) ι ℚ` with `hPN : P * N = M * P` (the Parikh map
  intertwines `N` with `M`);
* `ℓ : Fin 3 → ℝ`, `β : ℝ` with `hℓ : ℓ ᵥ* M.map (↑) = β • ℓ` (a real left
  eigenvector of `M`);
* `hL : ∀ i, 0 < (ℓ ᵥ* P.map (↑)) i` (the pulled-back functional
  `L := ℓ ᵥ* P` is strictly positive; this holds when `ℓ > 0` and the Parikh
  columns of `P` are non-negative and non-zero).

Proved:

1. `charpoly_kerP_injective`: for `x : ι → ℚ`, `P x = 0` and `f(N) x = 0`
   imply `x = 0`.  Proof: (a) the irreducible cubic `f` annihilates `x`, so by
   Bezout no non-zero rational polynomial of degree `< 3` does; (b) over `ℝ`,
   `f = (X − β) h` with `h` monic quadratic; if `u := h(N) x = 0` then a
   `ℚ`-linear functional `θ : ℝ → ℚ` with `θ 1 = 1` (basis extension) applied
   to the coefficients of `h` gives a rational monic quadratic annihilator,
   contradicting (a); (c) so `u ≠ 0`, `N u = β u` and `P u = h(M) P x = 0`,
   whence `L ⬝ u = ℓ ⬝ P u = 0`; (d) by `PerronCore`, `|u|` is a `β`-eigenvector
   and every non-zero real `β`-eigenvector of `N` has full support, so
   `|u i₀| u − u i₀ |u| = 0` and `L ⬝ u` is a non-zero multiple of
   `L ⬝ |u| > 0`, a contradiction.
2. `hsplit_of_perron`: the hypothesis `hsplit` of `exists_factor_through`, in
   exactly that form, for `V = ι → ℚ`, `P = mulVecLin P`, `N = toLin' N`,
   `f = χ_M`: the restriction of `f(N)` to the finite-dimensional `N`-invariant
   subspace `ker P` is injective by (1), hence surjective.
3. `factor_through_parikh`: combined with `exists_factor_through`: every
   `Q : (ι → ℚ) →ₗ[ℚ] Y` intertwining `N` with an `R` annihilated by `χ_M`
   factors as `Q = L' ∘ P` when `P` is onto.

Auxiliary results: `isRoot_of_real_left_eigen` (a non-zero real left eigenvector of
`M` for `β` makes `β` a root of `χ_M`, so this is *not* assumed), `PerronCore.beta_nonneg`
(a strictly positive left eigenvector of a non-negative matrix has eigenvalue
`β ≥ 0`, so `0 < β` is *not* assumed), `PerronCore.abs_eigen`, `PerronCore.full_support`,
`mul_aeval_of_intertwine`.

Not formalized here: the Perron–Frobenius theorem (existence of `ℓ`, `β` as
the dominant root, positivity of `ℓ`), the derivation of `hL` from positivity
of `ℓ` and the shape of the Parikh matrix, the identification of `N`, `P`, `Q`,
`R` with the concrete objects of the attack document, and the characteristic
polynomial identity `χ_{N | ker P} = χ_N / χ_M`; the argument above avoids it.

Deviations from the original task statement, both of which only weaken
hypotheses: the main theorems do not assume `0 < β` (derived as `0 ≤ β` by
`PerronCore.beta_nonneg`, which is all the argument needs) and do not assume
`aeval β χ_M = 0` (derived by `isRoot_of_real_left_eigen` from `hℓ`, since `hL`
forces `ℓ ≠ 0` whenever `ι` is non-empty, and the statement is trivial for
empty `ι`).
-/
import PscVerif.PerronCore
import PscVerif.ConcentrationAlgebra
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision

set_option linter.unusedSectionVars false

namespace Psc.PerronSimple

open Matrix Polynomial Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Generic algebra -/

/-- A rectangular intertwining `A B = C A` passes to polynomials. -/
theorem mul_aeval_of_intertwine {R m n : Type*} [CommRing R] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n R) (B : Matrix n n R) (C : Matrix m m R)
    (h : A * B = C * A) (p : R[X]) : A * aeval B p = aeval C p * A := by
  have hpow : ∀ k : ℕ, A * B ^ k = C ^ k * A := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial k a => simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, hpow]

/-- Casting a rational matrix-vector product to `ℝ`. -/
theorem cast_mulVec {m n : Type*} [Fintype n] (A : Matrix m n ℚ) (v : n → ℚ) :
    A.map ((↑) : ℚ → ℝ) *ᵥ (fun j => (v j : ℝ)) = fun i => ((A *ᵥ v) i : ℝ) := by
  funext i
  simp [mulVec, dotProduct, Matrix.map_apply]

/-- Casting commutes with polynomial evaluation at a matrix. -/
theorem cast_aeval (N : Matrix ι ι ℚ) (p : ℚ[X]) :
    aeval (N.map ((↑) : ℚ → ℝ)) p = (aeval N p).map ((↑) : ℚ → ℝ) := by
  have := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId ℚ ℝ) : Matrix ι ι ℚ →ₐ[ℚ] _) N p
  have hc : (⇑(Algebra.ofId ℚ ℝ) : ℚ → ℝ) = ((↑) : ℚ → ℝ) := by
    funext q; simp
  simpa [AlgHom.mapMatrix_apply, hc] using this

/-- **(a)** If the irreducible `f` annihilates `x` under `N`, no non-zero
polynomial of smaller degree does, unless `x = 0` (Bezout). -/
theorem eq_zero_of_aeval_of_degree_lt {F n : Type*} [Field F] [Fintype n] [DecidableEq n]
    (N : Matrix n n F) (f : F[X]) (hf : Irreducible f) (x : n → F)
    (hfx : aeval N f *ᵥ x = 0) (g : F[X]) (hg : g ≠ 0) (hdeg : g.degree < f.degree)
    (hgx : aeval N g *ᵥ x = 0) : x = 0 := by
  have hnd : ¬ f ∣ g := fun hd => hg (eq_zero_of_dvd_of_degree_lt hd hdeg)
  obtain ⟨a, b, hab⟩ := (hf.coprime_iff_not_dvd).2 hnd
  have : aeval N (a * f + b * g) *ᵥ x = x := by rw [hab]; simp
  rw [← this, map_add, map_mul, map_mul, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hfx, hgx,
    mulVec_zero, mulVec_zero, add_zero]

/-- A non-zero real left eigenvector of `M` for `β` makes `β` a root of `χ_M`
(`Psc.ConcentrationAlgebra.isRoot_of_left_eigen` for `M` mapped to `ℝ`). -/
theorem isRoot_of_real_left_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℚ) (ℓ : n → ℝ) (β : ℝ) (hℓ0 : ℓ ≠ 0)
    (hℓ : ℓ ᵥ* M.map ((↑) : ℚ → ℝ) = β • ℓ) : aeval β M.charpoly = 0 := by
  rw [← eval_map_algebraMap, ← charpoly_map]
  exact Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ β ℓ hℓ0 hℓ

/-! ### The main theorems -/

/-- **(1)** Under the Perron data, `ker P ∩ ker χ_M(N) = 0`. -/
theorem charpoly_kerP_injective (N : Matrix ι ι ℚ) (hN : ∀ i j, 0 ≤ N i j)
    (hSC : PerronCore.StronglyConnected (N.map ((↑) : ℚ → ℝ)))
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : Irreducible M.charpoly)
    (P : Matrix (Fin 3) ι ℚ) (hPN : P * N = M * P)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hℓ : ℓ ᵥ* M.map ((↑) : ℚ → ℝ) = β • ℓ)
    (hL : ∀ i, 0 < (ℓ ᵥ* P.map ((↑) : ℚ → ℝ)) i) :
    ∀ x : ι → ℚ, P *ᵥ x = 0 → (aeval N M.charpoly) *ᵥ x = 0 → x = 0 := by
  intro x hPx hfx
  by_contra hx0
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hx0
  set f := M.charpoly with hf_def
  set N' : Matrix ι ι ℝ := N.map ((↑) : ℚ → ℝ) with hN'
  set P' : Matrix (Fin 3) ι ℝ := P.map ((↑) : ℚ → ℝ) with hP'
  set M' : Matrix (Fin 3) (Fin 3) ℝ := M.map ((↑) : ℚ → ℝ) with hM'
  set x' : ι → ℝ := fun i => (x i : ℝ) with hx'
  set L : ι → ℝ := ℓ ᵥ* P' with hLdef
  -- intertwining over `ℝ`
  have hPN' : P' * N' = M' * P' := by
    ext i j
    have := congrArg ((↑) : ℚ → ℝ) (congrFun (congrFun hPN i) j)
    simpa [Matrix.mul_apply, Matrix.map_apply, hP', hN', hM'] using this
  have hA : ∀ i j, 0 ≤ N' i j := fun i j => by simpa [hN'] using hN i j
  have hLA : L ᵥ* N' = β • L := by
    rw [hLdef, vecMul_vecMul, hPN', ← vecMul_vecMul, hℓ, smul_vecMul]
  have hβ : 0 ≤ β := PerronCore.beta_nonneg N' hA L hL β hLA i0
  -- `ℓ ≠ 0`, so `β` is a root of `f`
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    have := hL i0
    simp [hLdef, h] at this
  have hroot : IsRoot (f.map (algebraMap ℚ ℝ)) β := by
    rw [IsRoot, eval_map_algebraMap]
    exact isRoot_of_real_left_eigen M ℓ β hℓ0 hℓ
  -- (a) degree of `f`
  have hfdeg : f.degree = 3 := by
    rw [hf_def, charpoly_degree_eq_dim]; simp
  -- (b) the real factorization `f = (X - β) h`
  set f' := f.map (algebraMap ℚ ℝ) with hf'
  set h := f' /ₘ (X - C β) with hh
  have hfac : (X - C β) * h = f' := mul_divByMonic_eq_iff_isRoot.2 hroot
  have hf'monic : f'.Monic := (charpoly_monic M).map _
  have hf'deg : f'.natDegree = 3 := by
    rw [hf', natDegree_map, hf_def, charpoly_natDegree_eq_dim]; simp
  have hhdeg : h.natDegree = 2 := by
    rw [hh, natDegree_divByMonic _ (monic_X_sub_C β), hf'deg, natDegree_X_sub_C]
  have hhmonic : h.Monic := by
    have := congrArg leadingCoeff hfac
    rw [leadingCoeff_mul, (monic_X_sub_C β).leadingCoeff, one_mul, hf'monic.leadingCoeff] at this
    exact this
  set a1 := h.coeff 1 with ha1
  set a0 := h.coeff 0 with ha0
  have hquad : h = X ^ 2 + C a1 * X + C a0 := by
    conv_lhs => rw [as_sum_range_C_mul_X_pow h]
    have h2 : h.coeff 2 = 1 := by
      have := hhmonic.leadingCoeff
      rwa [leadingCoeff, hhdeg] at this
    rw [hhdeg]
    simp [Finset.sum_range_succ, h2, ha1, ha0]
    ring
  set u : ι → ℝ := aeval N' h *ᵥ x' with hu
  -- explicit coordinates of `u`
  have hcoord : ∀ i, u i = ((N *ᵥ (N *ᵥ x)) i : ℝ) + a1 * ((N *ᵥ x) i : ℝ) + a0 * (x i : ℝ) := by
    intro i
    have e1 : N' *ᵥ x' = fun i => ((N *ᵥ x) i : ℝ) := cast_mulVec N x
    have e2 : N' *ᵥ (N' *ᵥ x') = fun i => ((N *ᵥ (N *ᵥ x)) i : ℝ) := by
      rw [e1]; exact cast_mulVec N (N *ᵥ x)
    have hexp : aeval N' h *ᵥ x' = N' *ᵥ (N' *ᵥ x') + a1 • (N' *ᵥ x') + a0 • x' := by
      rw [hquad]
      simp only [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
        add_mulVec, smul_mul_assoc, one_mul, smul_mulVec, one_mulVec, pow_two]
      rw [mulVec_mulVec]
    rw [hu, hexp, e2, e1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx']
  -- (b) `u ≠ 0`
  have hu0 : u ≠ 0 := by
    intro hu0
    obtain ⟨θ, hθ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℝ)
      (LinearMap.ker_eq_bot.2 (fun a b hab => by simpa using hab))
    have hθq : ∀ q : ℚ, θ (q : ℝ) = q := fun q => by
      simpa using LinearMap.congr_fun hθ q
    have hθmul : ∀ (r : ℝ) (q : ℚ), θ (r * q) = θ r * q := by
      intro r q
      have : r * (q : ℝ) = q • r := by rw [Rat.smul_def]; ring
      rw [this, map_smul, smul_eq_mul, mul_comm]
    set g : ℚ[X] := C 1 * X ^ 2 + C (θ a1) * X + C (θ a0) with hg
    have hgdeg : g.degree = 2 := degree_quadratic one_ne_zero
    have hg0 : g ≠ 0 := by
      intro h0; rw [h0, degree_zero] at hgdeg; exact absurd hgdeg (by decide)
    have hgx : aeval N g *ᵥ x = 0 := by
      funext i
      have hi := congrArg θ (hcoord i)
      rw [show u i = 0 from congrFun hu0 i, map_zero, map_add, map_add, hθmul, hθmul,
        hθq] at hi
      rw [hg]
      simp only [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
        add_mulVec, smul_mulVec, one_mulVec, pow_two, ← mulVec_mulVec, map_one]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have : θ ((N *ᵥ x) i : ℝ) = (N *ᵥ x) i := hθq _
      linarith
    exact hx0 (eq_zero_of_aeval_of_degree_lt N f hM x hfx g hg0 (by rw [hgdeg, hfdeg]; decide) hgx)
  -- (c) `u` is a `β`-eigenvector with `L ⬝ u = 0`
  have hfx' : aeval N' f' *ᵥ x' = 0 := by
    rw [hf', aeval_map_algebraMap, cast_aeval, cast_mulVec, hfx]
    funext i; simp
  have hNu : N' *ᵥ u = β • u := by
    rw [← hfac] at hfx'
    simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      ← mulVec_mulVec, sub_mulVec] at hfx'
    rw [← hu, smul_mulVec, one_mulVec] at hfx'
    exact sub_eq_zero.1 hfx'
  have hPu : P' *ᵥ u = 0 := by
    rw [hu, mulVec_mulVec, mul_aeval_of_intertwine P' N' M' hPN', ← mulVec_mulVec,
      cast_mulVec, hPx]
    have : (fun i => ((0 : Fin 3 → ℚ) i : ℝ)) = 0 := by funext i; simp
    rw [this, mulVec_zero]
  have hLu : L ⬝ᵥ u = 0 := by
    rw [hLdef, ← dotProduct_mulVec, hPu, dotProduct_zero]
  -- (d) Perron step
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 hu0
  have habs := PerronCore.abs_eigen N' hA L hL β hLA hβ u hNu
  set v : ι → ℝ := |u j0| • u - u j0 • (fun i => |u i|) with hv
  have hNv : N' *ᵥ v = β • v := by
    rw [hv, mulVec_sub, mulVec_smul, mulVec_smul, hNu, habs, smul_sub, smul_comm β (|u j0|),
      smul_comm β (u j0)]
  have hv0 : v = 0 := by
    by_contra hne
    have := PerronCore.full_support N' hA L hL β hLA hSC hβ v hNv hne j0
    simp [hv, mul_comm] at this
  have hpos := PerronCore.full_support N' hA L hL β hLA hSC hβ u hNu hu0
  have hLabs : 0 < L ⬝ᵥ (fun i => |u i|) :=
    Finset.sum_pos (fun i _ => mul_pos (hL i) (hpos i)) ⟨j0, Finset.mem_univ _⟩
  have hdot := congrArg (fun w => L ⬝ᵥ w) hv0
  simp only [hv, dotProduct_sub, dotProduct_smul, hLu, smul_eq_mul, mul_zero, zero_sub,
    dotProduct_zero, neg_eq_zero] at hdot
  rcases mul_eq_zero.1 hdot with h0 | h0
  · exact hj0 h0
  · exact hLabs.ne' h0

/-- **(2)** The hypothesis `hsplit` of
`Psc.ConcentrationAlgebra.exists_factor_through`, for `V = ι → ℚ`,
`P = mulVecLin P`, `N = toLin' N` and `f = χ_M`. -/
theorem hsplit_of_perron (N : Matrix ι ι ℚ) (hN : ∀ i j, 0 ≤ N i j)
    (hSC : PerronCore.StronglyConnected (N.map ((↑) : ℚ → ℝ)))
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : Irreducible M.charpoly)
    (P : Matrix (Fin 3) ι ℚ) (hPN : P * N = M * P)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hℓ : ℓ ᵥ* M.map ((↑) : ℚ → ℝ) = β • ℓ)
    (hL : ∀ i, 0 < (ℓ ᵥ* P.map ((↑) : ℚ → ℝ)) i) :
    ∀ x ∈ LinearMap.ker (Matrix.mulVecLin P), ∃ z ∈ LinearMap.ker (Matrix.mulVecLin P),
      x = aeval (Matrix.toLin' N) M.charpoly z := by
  set K := LinearMap.ker (Matrix.mulVecLin P) with hK
  have haeval : ∀ z, aeval (Matrix.toLin' N) M.charpoly z = aeval N M.charpoly *ᵥ z := by
    intro z
    have := aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix ι ι ℚ ≃ₐ[ℚ] _) N M.charpoly
    have h2 : (Matrix.toLinAlgEquiv' N : (ι → ℚ) →ₗ[ℚ] (ι → ℚ)) = Matrix.toLin' N := rfl
    rw [h2] at this
    rw [this]
    rfl
  have hmaps : ∀ z ∈ K, Matrix.toLin' (aeval N M.charpoly) z ∈ K := by
    intro z hz
    rw [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz ⊢
    rw [Matrix.toLin'_apply, mulVec_mulVec, mul_aeval_of_intertwine P N M hPN, ← mulVec_mulVec,
      hz, mulVec_zero]
  let φ : K →ₗ[ℚ] K := (Matrix.toLin' (aeval N M.charpoly)).restrict hmaps
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    apply Subtype.ext
    have hz' : aeval N M.charpoly *ᵥ (z : ι → ℚ) = 0 := by
      have := congrArg Subtype.val hz
      simpa [φ, LinearMap.restrict_apply, Matrix.toLin'_apply] using this
    have hPz : P *ᵥ (z : ι → ℚ) = 0 := LinearMap.mem_ker.1 z.2
    exact charpoly_kerP_injective N hN hSC M hM P hPN ℓ β hℓ hL z hPz hz'
  have hsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.1 hinj
  intro x hx
  obtain ⟨z, hz⟩ := hsurj ⟨x, hx⟩
  refine ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simp only [φ, LinearMap.restrict_apply, Matrix.toLin'_apply] at this
  rw [haeval, this]

/-- **(3)** Factorization through the Parikh map: under the Perron data, every
`Q` intertwining `N` with an `R` annihilated by `χ_M` factors through `P`. -/
theorem factor_through_parikh (N : Matrix ι ι ℚ) (hN : ∀ i j, 0 ≤ N i j)
    (hSC : PerronCore.StronglyConnected (N.map ((↑) : ℚ → ℝ)))
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : Irreducible M.charpoly)
    (P : Matrix (Fin 3) ι ℚ) (hPN : P * N = M * P)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hℓ : ℓ ᵥ* M.map ((↑) : ℚ → ℝ) = β • ℓ)
    (hL : ∀ i, 0 < (ℓ ᵥ* P.map ((↑) : ℚ → ℝ)) i)
    {Y : Type*} [AddCommGroup Y] [Module ℚ Y] (Q : (ι → ℚ) →ₗ[ℚ] Y) (R : Y →ₗ[ℚ] Y)
    (hQ : Q ∘ₗ Matrix.toLin' N = R ∘ₗ Q) (hR : aeval R M.charpoly = 0)
    (hP : Function.Surjective (Matrix.mulVecLin P)) :
    ∃ L' : (Fin 3 → ℚ) →ₗ[ℚ] Y, Q = L' ∘ₗ Matrix.mulVecLin P :=
  ConcentrationAlgebra.exists_factor_through (Matrix.mulVecLin P) Q (Matrix.toLin' N) R hP hQ
    M.charpoly hR (hsplit_of_perron N hN hSC M hM P hPN ℓ β hℓ hL)

end Psc.PerronSimple
