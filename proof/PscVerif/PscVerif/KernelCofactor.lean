/-
# The cofactor of `χ_M` in `χ_{N_C}`, and `β` the simple Perron root of `N_C`

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `thm:parikh` (the clause
`χ_{N_C} = χ_{N_C | ker P_C} · χ_M` by block triangularization, and `ρ(N_C) = β`
with `β` a simple root); `docs/c4-concentration-attack-2026-11-06.md` §2
(Theorem A(iv): "since `β` is a simple root of `χ_N`, `χ_N = χ_M · g` with
`gcd(χ_M, g) = 1`", and the factorization through `P` by an injective
intertwiner), §3 and §8.

Proved here, in full:

* `charpoly_eq_mul_restrict` (**the cofactor**, any field `F`): if `p : V → Y` is
  onto and `p ∘ n = m ∘ p`, then `ker p` is `n`-invariant (`ker_invariant`) and
  `χ_n = χ_m · χ_{n | ker p}`.  Proof: a section `s` of `p` gives
  `K × Y ≃ V`, `(k, y) ↦ k + s y`, conjugating `n` to the block-triangular
  `(k, y) ↦ (n k + (n s − s m) y, m y)`, whose characteristic polynomial is the
  product (`charpoly_triangular`, via `Matrix.charpoly_fromBlocks_zero₂₁`);
* its matrix form `charpoly_eq_mul_kerRestrict`: for `P : Matrix κ ι F` onto with
  `P N = M P`, `χ_N = χ_M · χ_{N | ker P}`, where `kerRestrict` is the restriction
  of `toLin' N` to `ker (mulVecLin P)`; the converse
  `charpoly_eq_mul_kerRestrict_iff`: given `P N = M P`, the identity holds **iff**
  `P` is onto (degrees and rank–nullity); `coe_aeval_kerRestrict`:
  `f(N | ker P) = f(N) | ker P`;
* `isCoprime_charpoly_of_injective` (any field): if `f(A)` is injective then
  `IsCoprime f χ_A`.  A common root `z` in an algebraic closure is an eigenvalue of
  the matrix of `A` (`aeval_charpoly_ne_zero`), and an eigenvector for `z` is
  killed by `f(A)` (`aeval_mulVec_of_eigen`, `aeval_matrix_map`), against
  `det f(A) ≠ 0`;
* **Perron simplicity** under the hypotheses of
  `Psc.PerronSimple.charpoly_kerP_injective` (`N ≥ 0` strongly connected over
  `ℝ`, `χ_M` irreducible, `P N = M P`, `ℓ M = β ℓ`, `ℓ P > 0`):
  `isCoprime_charpoly_kerRestrict`, `IsCoprime χ_M χ_{N | ker P}` over `ℚ` (no
  surjectivity needed: `χ_M(N)` is injective on `ker P` by `charpoly_kerP_injective`);
  and, with `P` onto, `rootMultiplicity_charpoly_eq_one`: `β` is a simple root
  of `χ_N` over `ℝ`.  That `β` is a simple root of `χ_M` is derived
  (`rootMultiplicity_eq_one_of_irreducible`: irreducible ⇒ separable in
  characteristic `0`), as is `χ_M(β) = 0` (`PerronSimple.isRoot_of_real_left_eigen`);
* **`ρ(N) = β`**, `perron_root_of_intertwine` (`N ≥ 0`, `P N = M P`, `ℓ M = β ℓ`,
  `ℓ P > 0`, any finite `κ`; no irreducibility, no strong connectivity): `β` is a
  real eigenvalue of `N` and `‖μ‖ ≤ β` for every complex eigenvalue `μ`, since
  `λ = ℓ P` is a positive left `β`-eigenvector (`Psc.ParikhIntertwiner.spectral_bound`);
* **Theorem A(iv) in full**, `factor_through_parikh_full`: under the Perron
  hypotheses with `P` onto, every `Q` with `Q N = R Q` and `χ_M(R) = 0` is
  `Q = L' P` with `L' M = R L'`, and `L'` is injective unless `Q = 0`
  (`Psc.PerronSimple.factor_through_parikh`,
  `Psc.ConcentrationAlgebra.injective_of_irreducible`,
  `Psc.Cyclicity.invariant_eq_bot_or_top`);
* **representatives** (a `Psc.SignedCocycle.Normalisation P0` of a balanced child
  system on `Fin 3`, `N_C = NrepQ P0`, `P_R = PrepQ P0`, `M = incQ S`):
  `vecMul_prepQ` (`ℓ P_R = Lrep ℓ`) and `vecMul_prepQ_pos` (`ℓ P_R > 0`, from
  `lrep_pos`); `charpoly_nrep_eq_mul`; `cofactor_int` (the cofactor is the image of
  an integer polynomial: cancel `χ_M` in `Psc.ParikhRank.charpoly_dvd_rep_int`);
  `isCoprime_rep`, `rootMultiplicity_rep`; `perron_root_rep` (`ρ(N_C) = β`, without
  irreducibility or strong connectivity); `simple_perron_root_rep`: **`β` is the
  simple Perron root of `N_C`**; and `factor_through_rep`, Theorem A(iv) in full
  on representatives, surjectivity discharged by `Psc.ParikhRank.prep_surjective`;
* controls (abstract matrices): `ctrlN`, `ctrlP`, a four-state splitting of the
  letter `2` of `Psc.M0Pisot.M0` with `P N = M0 P` (`decide +kernel`), `P` onto and
  `ker P ∋ e_{2a} − e_{2b}`, so `ker P ≠ 0` (`ctrl_ker_ne_bot`); `ctrl_charpoly`
  instantiates the cofactor and `ctrl_cofactor` pins it: `N` acts on `ker P` as
  `-1` (`ctrl_kerRestrict`), so `χ_{N | ker P} = X + 1`; `ctrl_nonneg`,
  `ctrl_stronglyConnected`, `ctrl_perron` (root `b ∈ (31, 32)` of `χ_{M0}` by the
  intermediate value theorem, `ℓ = (6b, b² − 6b − 1, b + 1) > 0`) meet every
  Perron hypothesis; `ctrl_isCoprime_and_simple` instantiates both forms of Perron
  simplicity and `ρ(N) = b`; `ctrl_factor` instantiates `factor_through_parikh_full`
  with `Q = P ≠ 0`, `R = M0`;
* control (representatives): `wT_rep_hyps`, `Psc.SignedIntertwiner.wTNorm` (the
  zero-return system of the irreducible pair `(0112201, 1200112)` under the identity
  substitution, `N_C = (1)` by `wT_nrep`) meets every hypothesis of the
  representative theorems except irreducibility of `χ_M`; `wT_perron_root`
  instantiates `perron_root_rep`, which does not use it;
* negative controls: `neg_surjective_needed` (`P = 0`: `P` onto cannot be dropped
  from `charpoly_eq_mul_kerRestrict`); `neg_sc_needed` and
  `blk_not_stronglyConnected` (`blkN = diag(M0, M0)` with `blkP = [I | I]`,
  `blk_intertwine` by `decide +kernel`, meets every hypothesis of
  `rootMultiplicity_charpoly_eq_one` but strong connectivity, and `b` is a double
  root); `wT_no_cofactor` and `wT_not_irreducible` (on `wTNorm`,
  `deg χ_{N_C} = 1 < 3 = deg χ_M`, so irreducibility of `χ_M` cannot be dropped from
  `charpoly_nrep_eq_mul`).

Not proved here:

* the hypotheses of the representative theorems, which are assumed: balance of
  every state (`hbal`, `Equiv1`), nonempty top tracks (`hne`), `C` nonempty
  (`hC`), strong connectivity of `N_C` (`hSC`), irreducibility of `χ_M` (`hM`), and
  `ℓ > 0` with `ℓ M = β ℓ` (for a primitive `σ` this is
  `Psc.PerronExistence.exists_pos_left_eigen_inc`, not imported here);
* that `β` is the only eigenvalue of `N_C` of modulus `β`, and the identification
  of `Q`, `R` in `factor_through_rep` with `Q₄ D`, `d Φ` of Theorem A;
* a representative-level instance with irreducible `χ_M`.  The hypotheses assume
  neither Pisot nor zero-return children: a `ChildSystem` takes any balanced
  factorizations as children, and a normalisation only forces `C` coincidence-free
  (`Psc.SignedCocycle.Normalisation.noncoincident`).  For a zero-return system
  (`Psc.Reduction.redSystem`) of a PIP `σ`, such an instance would be a closed
  coincidence-free component of the balanced pair algorithm, which the coincidence
  conjecture excludes; for other factorizations no exclusion is claimed.  A scratch
  search over images of length `≤ 3` found no such component (capped runs, not a
  verdict).  So the representative theorems are shown non-vacuous only up to `hM`
  (`wT_rep_hyps`), and `perron_root_rep` fully (`wT_perron_root`).
-/
import PscVerif.ParikhRank
import PscVerif.PerronSimple
import PscVerif.M0Pisot
import PscVerif.SignedIntertwiner

set_option linter.unusedSectionVars false

namespace Psc.KernelCofactor

open Matrix Polynomial

/-! ### The cofactor of an intertwiner onto the quotient -/

section Quotient

variable {F V Y W : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- A block upper-triangular endomorphism `(w, y) ↦ (A w + D y, B y)` of `W × Y`
has characteristic polynomial `χ_A χ_B`. -/
theorem charpoly_triangular (A : W →ₗ[F] W) (D : Y →ₗ[F] W) (B : Y →ₗ[F] Y) :
    (A.prodMap B + LinearMap.inl F W Y ∘ₗ D ∘ₗ LinearMap.snd F W Y).charpoly =
      A.charpoly * B.charpoly := by
  set bW := Module.finBasis F W
  set bY := Module.finBasis F Y
  rw [← LinearMap.charpoly_toMatrix _ (bW.prod bY), ← LinearMap.charpoly_toMatrix A bW,
    ← LinearMap.charpoly_toMatrix B bY,
    ← Matrix.charpoly_fromBlocks_zero₂₁ _ (LinearMap.toMatrix bY bW D)]
  congr 1
  ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply]

omit [FiniteDimensional F V] [FiniteDimensional F Y] in
/-- `ker p` is invariant under every `n` with `p ∘ n = m ∘ p`. -/
theorem ker_invariant {p : V →ₗ[F] Y} {n : V →ₗ[F] V} {m : Y →ₗ[F] Y}
    (h : p ∘ₗ n = m ∘ₗ p) : ∀ x ∈ LinearMap.ker p, n x ∈ LinearMap.ker p := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, hx, map_zero]

/-- **The cofactor.**  If `p : V → Y` is onto and `p ∘ n = m ∘ p`, then
`χ_n = χ_m · χ_{n | ker p}`. -/
theorem charpoly_eq_mul_restrict (p : V →ₗ[F] Y) (hp : Function.Surjective p)
    (n : V →ₗ[F] V) (m : Y →ₗ[F] Y) (h : p ∘ₗ n = m ∘ₗ p) :
    n.charpoly = m.charpoly * (n.restrict (ker_invariant h)).charpoly := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  have hs' : ∀ y, p (s y) = y := fun y => LinearMap.congr_fun hs y
  have hpn : ∀ v, p (n v) = m (p v) := fun v => LinearMap.congr_fun h v
  set K := LinearMap.ker p
  have hK : ∀ v, v - s (p v) ∈ K := fun v => by simp [K, hs']
  let f : K × Y →ₗ[F] V := K.subtype.coprod s
  let g : V →ₗ[F] K × Y := (LinearMap.codRestrict K (LinearMap.id - s ∘ₗ p) hK).prod p
  have hfg : f ∘ₗ g = LinearMap.id := by ext v; simp [f, g]
  have hgf : g ∘ₗ f = LinearMap.id :=
    LinearMap.ext fun ⟨k, y⟩ => Prod.ext
      (Subtype.ext (by simp [f, g, hs', LinearMap.mem_ker.1 k.2]))
      (by simp [f, g, hs', LinearMap.mem_ker.1 k.2])
  let e : (K × Y) ≃ₗ[F] V := LinearEquiv.ofLinearMap f g hfg hgf
  have hD : ∀ y, n (s y) - s (m y) ∈ K := fun y => by simp [K, hpn, hs']
  let D : Y →ₗ[F] K := LinearMap.codRestrict K (n ∘ₗ s - s ∘ₗ m) hD
  have hconj : e.symm.conj n = (n.restrict (ker_invariant h)).prodMap m +
      LinearMap.inl F K Y ∘ₗ D ∘ₗ LinearMap.snd F K Y :=
    LinearMap.ext fun ⟨k, y⟩ => Prod.ext (Subtype.ext (by
      simp [e, f, g, D, LinearEquiv.conj_apply, hpn, hs', LinearMap.mem_ker.1 k.2]))
      (by simp [e, f, g, D, LinearEquiv.conj_apply, hpn, hs', LinearMap.mem_ker.1 k.2])
  rw [← LinearEquiv.charpoly_conj e.symm n, hconj, charpoly_triangular, mul_comm]

end Quotient

/-! ### Injectivity of `f(A)` and coprimality with `χ_A` -/

section Coprime

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- `p(A) v = p(r) v` for an eigenvector `A v = r v`. -/
theorem aeval_mulVec_of_eigen {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (r : R) (v : n → R) (hv : A *ᵥ v = r • v) (p : R[X]) :
    aeval A p *ᵥ v = p.eval r • v := by
  have h := Module.End.aeval_apply_of_mem_apply_eq_smul (f := Matrix.toLinAlgEquiv' A) (p := p)
    (x := v) (μ := r) (by rw [Matrix.toLinAlgEquiv'_apply, hv])
  rwa [aeval_algHom_apply, Matrix.toLinAlgEquiv'_apply] at h

/-- Mapping a matrix along a field extension commutes with polynomial evaluation
(the field form of `Psc.PerronSimple.cast_aeval`). -/
theorem aeval_matrix_map {n L : Type*} [Fintype n] [DecidableEq n] [Field L] [Algebra F L]
    (B : Matrix n n F) (p : F[X]) :
    aeval (B.map (algebraMap F L)) p = (aeval B p).map (algebraMap F L) :=
  aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId F L) : Matrix n n F →ₐ[F] _) B p

/-- If `f(A)` is injective, no root of `f` in any field extension is a root of
`χ_A`: a common root `z` is an eigenvalue of `A` over the extension, and an
eigenvector for `z` is killed by `f(A)`. -/
theorem aeval_charpoly_ne_zero (A : W →ₗ[F] W) (f : F[X]) (hf : Function.Injective (aeval A f))
    {L : Type*} [Field L] [Algebra F L] (z : L) (hz : aeval z f = 0) :
    aeval z A.charpoly ≠ 0 := by
  intro hzA
  set b := Module.finBasis F W
  set B := LinearMap.toMatrix b b A
  obtain ⟨w, hw0, hw⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot
    (B.map (algebraMap F L)) z (by
      rw [charpoly_map, eval_map_algebraMap, LinearMap.charpoly_toMatrix, hzA])
  have hfw : (aeval B f).map (algebraMap F L) *ᵥ w = 0 := by
    rw [← aeval_matrix_map, ← Polynomial.aeval_map_algebraMap L,
      aeval_mulVec_of_eigen _ z w hw, eval_map_algebraMap, hz, zero_smul]
  have hdet : (aeval B f).det ≠ 0 := by
    rw [show aeval B f = LinearMap.toMatrix b b (aeval A f) from
      aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b) A f, LinearMap.det_toMatrix]
    exact (LinearMap.isUnit_det _
      ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hf))).ne_zero
  have h0 := exists_mulVec_eq_zero_iff.1 ⟨w, hw0, hfw⟩
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h0
  exact hdet ((map_eq_zero _).1 h0)

/-- **Coprimality.**  If `f(A)` is injective then `f` and `χ_A` are coprime
(test the roots in an algebraic closure). -/
theorem isCoprime_charpoly_of_injective (A : W →ₗ[F] W) (f : F[X])
    (hf : Function.Injective (aeval A f)) : IsCoprime f A.charpoly :=
  (isCoprime_iff_aeval_ne_zero_of_isAlgClosed F (AlgebraicClosure F) f A.charpoly).2 fun z =>
    or_iff_not_imp_left.2 fun hz => aeval_charpoly_ne_zero A f hf z (not_not.1 hz)

end Coprime

/-! ### Matrices: `N` on `ker P` -/

section Matrix

variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {M : Matrix κ κ F} {P : Matrix κ ι F} {N : Matrix ι ι F}

/-- `P N = M P` as linear maps. -/
theorem mulVecLin_comp_toLin' (h : P * N = M * P) :
    P.mulVecLin ∘ₗ Matrix.toLin' N = Matrix.toLin' M ∘ₗ P.mulVecLin :=
  LinearMap.ext fun v => by simp [Matrix.mulVec_mulVec, h]

/-- The restriction `N|ker P` of `N` to its invariant subspace `ker P`. -/
abbrev kerRestrict (h : P * N = M * P) :
    LinearMap.ker P.mulVecLin →ₗ[F] LinearMap.ker P.mulVecLin :=
  (Matrix.toLin' N).restrict (ker_invariant (mulVecLin_comp_toLin' h))

/-- **(a) `χ_N = χ_M · χ_{N | ker P}`** for an onto intertwiner `P N = M P`. -/
theorem charpoly_eq_mul_kerRestrict (h : P * N = M * P)
    (hP : Function.Surjective P.mulVecLin) :
    N.charpoly = M.charpoly * (kerRestrict h).charpoly := by
  have := charpoly_eq_mul_restrict _ hP _ _ (mulVecLin_comp_toLin' h)
  rwa [Matrix.charpoly_toLin', Matrix.charpoly_toLin'] at this

/-- **(a), converse**: given `P N = M P`, the cofactor identity holds exactly when
`P` is onto.  Degrees give `|ι| = |κ| + dim ker P`; rank–nullity then gives
`dim range P = |κ|`. -/
theorem charpoly_eq_mul_kerRestrict_iff (h : P * N = M * P) :
    N.charpoly = M.charpoly * (kerRestrict h).charpoly ↔ Function.Surjective P.mulVecLin := by
  refine ⟨fun hc => ?_, charpoly_eq_mul_kerRestrict h⟩
  have hdeg := congrArg natDegree hc
  rw [natDegree_mul (charpoly_monic M).ne_zero (LinearMap.charpoly_monic _).ne_zero,
    charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim, LinearMap.charpoly_natDegree] at hdeg
  have hrn := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  rw [← LinearMap.range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fintype_fun_eq_card]; omega)

/-- `f(N|ker P) = f(N)|ker P`. -/
theorem coe_aeval_kerRestrict (h : P * N = M * P) (f : F[X])
    (x : LinearMap.ker P.mulVecLin) :
    (aeval (kerRestrict h) f x : ι → F) = aeval N f *ᵥ x := by
  have := Psc.ConcentrationAlgebra.comp_aeval_of_intertwine (LinearMap.ker P.mulVecLin).subtype
    (kerRestrict h) (Matrix.toLin' N) (fun _ => rfl) f x
  rw [Submodule.subtype_apply] at this
  rw [this, ← Matrix.toLin'_apply]
  exact LinearMap.congr_fun
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix ι ι F ≃ₐ[F] _) N f) _

end Matrix

/-- A root `β` of an irreducible polynomial over a field of characteristic zero is
simple. -/
theorem rootMultiplicity_eq_one_of_irreducible {F L : Type*} [Field F] [CharZero F] [Field L]
    [Algebra F L] {f : F[X]} (hf : Irreducible f) {β : L} (hβ : aeval β f = 0) :
    rootMultiplicity β (f.map (algebraMap F L)) = 1 :=
  le_antisymm (rootMultiplicity_le_one_of_separable hf.separable.map β)
    ((rootMultiplicity_pos (map_ne_zero hf.ne_zero)).2 (by rwa [IsRoot, eval_map_algebraMap]))

/-! ### Perron simplicity -/

section Perron

open Psc.PerronSimple

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **(b) Perron simplicity, coprime form.**  Under the hypotheses of
`Psc.PerronSimple.charpoly_kerP_injective`, `χ_M` and `χ_{N | ker P}` are coprime
over `ℚ`.  No surjectivity of `P` is needed. -/
theorem isCoprime_charpoly_kerRestrict (N : Matrix ι ι ℚ) (hN : ∀ i j, 0 ≤ N i j)
    (hSC : PerronCore.StronglyConnected (N.map ((↑) : ℚ → ℝ)))
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : Irreducible M.charpoly)
    (P : Matrix (Fin 3) ι ℚ) (hPN : P * N = M * P)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hℓ : ℓ ᵥ* M.map ((↑) : ℚ → ℝ) = β • ℓ)
    (hL : ∀ i, 0 < (ℓ ᵥ* P.map ((↑) : ℚ → ℝ)) i) :
    IsCoprime M.charpoly (kerRestrict hPN).charpoly := by
  refine isCoprime_charpoly_of_injective _ _ ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
  have hx' := congrArg Subtype.val hx
  rw [coe_aeval_kerRestrict, ZeroMemClass.coe_zero] at hx'
  exact Subtype.ext (charpoly_kerP_injective N hN hSC M hM P hPN ℓ β hℓ hL x
    (LinearMap.mem_ker.1 x.2) hx')

/-- **(b) Perron simplicity, multiplicity form.**  If moreover `P` is onto, `β` is
a simple root of `χ_N` over `ℝ`. -/
theorem rootMultiplicity_charpoly_eq_one (N : Matrix ι ι ℚ) (hN : ∀ i j, 0 ≤ N i j)
    (hSC : PerronCore.StronglyConnected (N.map ((↑) : ℚ → ℝ)))
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : Irreducible M.charpoly)
    (P : Matrix (Fin 3) ι ℚ) (hPN : P * N = M * P)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hℓ : ℓ ᵥ* M.map ((↑) : ℚ → ℝ) = β • ℓ)
    (hL : ∀ i, 0 < (ℓ ᵥ* P.map ((↑) : ℚ → ℝ)) i) (hP : Function.Surjective P.mulVecLin) :
    rootMultiplicity β (N.charpoly.map (algebraMap ℚ ℝ)) = 1 := by
  have hcard : 3 ≤ Fintype.card ι := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_le_finrank_of_surjective hP
  obtain ⟨i0⟩ := Fintype.card_pos_iff.1 (by omega : 0 < Fintype.card ι)
  have hβ : aeval β M.charpoly = 0 :=
    isRoot_of_real_left_eigen M ℓ β (fun h => by simpa [h] using hL i0) hℓ
  have hg := (aeval_ne_zero_of_isCoprime
    (isCoprime_charpoly_kerRestrict N hN hSC M hM P hPN ℓ β hℓ hL) β).resolve_left (not_not.2 hβ)
  rw [charpoly_eq_mul_kerRestrict hPN hP, Polynomial.map_mul, rootMultiplicity_mul
    (mul_ne_zero (map_ne_zero (charpoly_monic M).ne_zero)
      (map_ne_zero (LinearMap.charpoly_monic _).ne_zero)),
    rootMultiplicity_eq_zero (show ¬ IsRoot ((kerRestrict hPN).charpoly.map (algebraMap ℚ ℝ)) β
      by rwa [IsRoot, eval_map_algebraMap]), add_zero]
  exact rootMultiplicity_eq_one_of_irreducible hM hβ

/-- **(b) `ρ(N) = β`.**  If `P N = M P`, `ℓ M = β ℓ` and `λ = ℓ P > 0`, then
`λ N = β λ`; so `β` is a real eigenvalue of `N`, and for `N ≥ 0` it bounds the modulus
of every complex eigenvalue (`Psc.ParikhIntertwiner.spectral_bound`).  Neither
irreducibility, nor strong connectivity, nor `Fin 3` is used. -/
theorem perron_root_of_intertwine {κ : Type*} [Fintype κ] [Nonempty ι] (N : Matrix ι ι ℚ)
    (hN : ∀ i j, 0 ≤ N i j) (M : Matrix κ κ ℚ) (P : Matrix κ ι ℚ) (hPN : P * N = M * P)
    (ℓ : κ → ℝ) (β : ℝ) (hℓ : ℓ ᵥ* M.map ((↑) : ℚ → ℝ) = β • ℓ)
    (hL : ∀ i, 0 < (ℓ ᵥ* P.map ((↑) : ℚ → ℝ)) i) :
    (∃ v : ι → ℝ, v ≠ 0 ∧ N.map ((↑) : ℚ → ℝ) *ᵥ v = β • v) ∧
      ∀ x : ι → ℂ, x ≠ 0 → ∀ μ : ℂ, N.map ((↑) : ℚ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ β := by
  set L := ℓ ᵥ* P.map ((↑) : ℚ → ℝ)
  have hPN' : P.map ((↑) : ℚ → ℝ) * N.map ((↑) : ℚ → ℝ) =
      M.map ((↑) : ℚ → ℝ) * P.map ((↑) : ℚ → ℝ) := by
    change P.map (Rat.castHom ℝ) * N.map (Rat.castHom ℝ) =
      M.map (Rat.castHom ℝ) * P.map (Rat.castHom ℝ)
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPN]
  have hLN : L ᵥ* N.map ((↑) : ℚ → ℝ) = β • L := by
    rw [vecMul_vecMul, hPN', ← vecMul_vecMul, hℓ, smul_vecMul]
  have hL0 : L ≠ 0 := fun h0 => (hL (Classical.arbitrary ι)).ne' (congrFun h0 _)
  refine ⟨Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot _ β
    (Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ β L hL0 hLN), fun x hx0 μ hx =>
      Psc.ParikhIntertwiner.spectral_bound _ L hL β hLN _ (fun i j => ?_) x hx0 μ hx⟩
  rw [Matrix.map_apply, Matrix.map_apply, Complex.norm_ratCast,
    abs_of_nonneg (Rat.cast_nonneg.2 (hN i j))]

/-- **(d) Theorem A(iv), in full.**  Under the hypotheses of
`Psc.PerronSimple.factor_through_parikh`, the factor `L'` of `Q = L' P` also
intertwines, `L' M = R L'`, and is injective unless `Q = 0`: `ker L'` is
`M`-invariant, hence `0` or everything (`Psc.Cyclicity.invariant_eq_bot_or_top`). -/
theorem factor_through_parikh_full (N : Matrix ι ι ℚ) (hN : ∀ i j, 0 ≤ N i j)
    (hSC : PerronCore.StronglyConnected (N.map ((↑) : ℚ → ℝ)))
    (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : Irreducible M.charpoly)
    (P : Matrix (Fin 3) ι ℚ) (hPN : P * N = M * P)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hℓ : ℓ ᵥ* M.map ((↑) : ℚ → ℝ) = β • ℓ)
    (hL : ∀ i, 0 < (ℓ ᵥ* P.map ((↑) : ℚ → ℝ)) i)
    {Y : Type*} [AddCommGroup Y] [Module ℚ Y] (Q : (ι → ℚ) →ₗ[ℚ] Y) (R : Y →ₗ[ℚ] Y)
    (hQ : Q ∘ₗ Matrix.toLin' N = R ∘ₗ Q) (hR : aeval R M.charpoly = 0)
    (hP : Function.Surjective (Matrix.mulVecLin P)) :
    ∃ L' : (Fin 3 → ℚ) →ₗ[ℚ] Y, Q = L' ∘ₗ Matrix.mulVecLin P ∧
      L' ∘ₗ Matrix.toLin' M = R ∘ₗ L' ∧ (Q ≠ 0 → Function.Injective L') := by
  obtain ⟨L', hL'⟩ := factor_through_parikh N hN hSC M hM P hPN ℓ β hℓ hL Q R hQ hR hP
  have hint : L' ∘ₗ Matrix.toLin' M = R ∘ₗ L' := LinearMap.ext fun x => by
    obtain ⟨v, rfl⟩ := hP x
    simpa [hL', Matrix.mulVec_mulVec, hPN] using LinearMap.congr_fun hQ v
  refine ⟨L', hL', hint, fun hQ0 => Psc.ConcentrationAlgebra.injective_of_irreducible L' _ R
    hint (fun h0 => hQ0 (by rw [hL', h0, LinearMap.zero_comp])) fun p hp =>
      Psc.Cyclicity.invariant_eq_bot_or_top M hM p fun x hx => by simpa using hp x hx⟩

end Perron

/-! ### Normalised representatives: `N_C = A + B`, `P_R` -/

section Rep

open Psc.Binomial Psc.Incidence Psc.ParikhIntertwiner Psc.SignedCocycle Psc.ParikhRank

variable {S : ChildSystem (Fin 3)} (P0 : Normalisation S)

/-- `N_C` over `ℝ`, two ways. -/
theorem nrepQ_map_real : (NrepQ P0).map ((↑) : ℚ → ℝ) = P0.Nrep.map (Nat.cast : ℕ → ℝ) := by
  ext i j; simp

/-- `M` over `ℝ`, two ways. -/
theorem incQ_map_real : (incQ S).map ((↑) : ℚ → ℝ) = (inc S.s).map (Nat.cast : ℕ → ℝ) := by
  ext i j; simp

/-- The pulled-back functional `ℓ P_R` is the representative functional `λ = Lrep ℓ`. -/
theorem vecMul_prepQ (ℓ : Fin 3 → ℝ) : ℓ ᵥ* (PrepQ P0).map ((↑) : ℚ → ℝ) = P0.Lrep ℓ := by
  funext j
  simp [vecMul, dotProduct, Normalisation.Lrep, Lc, Lfun, parikh, Prep]

/-- `ℓ P_R > 0`, from `lrep_pos`. -/
theorem vecMul_prepQ_pos (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 < ℓ a) (hne : ∀ T ∈ S.C, T.1 ≠ [])
    (j : P0.Rep) : 0 < (ℓ ᵥ* (PrepQ P0).map ((↑) : ℚ → ℝ)) j := by
  rw [vecMul_prepQ]; exact P0.lrep_pos ℓ hℓ hne j

variable (hM : Irreducible (incQ S).charpoly) (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2)
  (hne : ∀ T ∈ S.C, T.1 ≠ [])

include hM hne in
/-- **(a) on representatives**: `χ_{N_C} = χ_M · χ_{N_C | ker P_R}`. -/
theorem charpoly_nrep_eq_mul (hC : S.C.Nonempty) :
    (NrepQ P0).charpoly = (incQ S).charpoly * (kerRestrict (prepQ_nrepQ P0 hbal)).charpoly :=
  charpoly_eq_mul_kerRestrict _ (prep_surjective P0 hM hbal hne hC)

include hM hne in
/-- **The cofactor is integral**: `χ_{N_C | ker P_R}` is the image of an integer
polynomial (cancel `χ_M` in `Psc.ParikhRank.charpoly_dvd_rep_int`). -/
theorem cofactor_int (hC : S.C.Nonempty) :
    ∃ g : ℤ[X], (kerRestrict (prepQ_nrepQ P0 hbal)).charpoly = g.map (Int.castRingHom ℚ) := by
  obtain ⟨g, hg⟩ := charpoly_dvd_rep_int P0 hM hbal hne hC
  have hgQ := congrArg (Polynomial.map (Int.castRingHom ℚ)) hg
  rw [Polynomial.map_mul, ← Matrix.charpoly_map, ← Matrix.charpoly_map, Matrix.map_map,
    Matrix.map_map] at hgQ
  refine ⟨g, mul_left_cancel₀ (charpoly_monic (incQ S)).ne_zero ?_⟩
  rw [← charpoly_nrep_eq_mul P0 hM hbal hne hC]
  convert hgQ using 3 <;> ext <;> simp

variable (hSC : PerronCore.StronglyConnected (P0.Nrep.map (Nat.cast : ℕ → ℝ)))
  (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 < ℓ a) (β : ℝ)
  (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ)

include hM hne hSC hℓ hℓN in
/-- **(b) on representatives, coprime form**: `gcd(χ_M, χ_{N_C | ker P_R}) = 1`. -/
theorem isCoprime_rep :
    IsCoprime (incQ S).charpoly (kerRestrict (prepQ_nrepQ P0 hbal)).charpoly :=
  isCoprime_charpoly_kerRestrict (NrepQ P0) (fun _ _ => Nat.cast_nonneg _)
    (by rwa [nrepQ_map_real]) _ hM (PrepQ P0) _ ℓ β (by rwa [incQ_map_real])
    (vecMul_prepQ_pos P0 ℓ hℓ hne)

include hM hbal hne hSC hℓ hℓN in
/-- **(b) on representatives, multiplicity form**: `β` is a simple root of `χ_{N_C}`. -/
theorem rootMultiplicity_rep (hC : S.C.Nonempty) :
    rootMultiplicity β ((NrepQ P0).charpoly.map (algebraMap ℚ ℝ)) = 1 :=
  rootMultiplicity_charpoly_eq_one (NrepQ P0) (fun _ _ => Nat.cast_nonneg _)
    (by rwa [nrepQ_map_real]) _ hM (PrepQ P0) (prepQ_nrepQ P0 hbal) ℓ β
    (by rwa [incQ_map_real]) (vecMul_prepQ_pos P0 ℓ hℓ hne) (prep_surjective P0 hM hbal hne hC)

include hbal hne hℓ hℓN in
/-- **(b) `ρ(N_C) = β`** on representatives: `perron_root_of_intertwine` with
`λ = ℓ P_R = Lrep ℓ`.  Neither irreducibility of `χ_M` nor strong connectivity is
used. -/
theorem perron_root_rep (hC : S.C.Nonempty) :
    (∃ v : P0.Rep → ℝ, v ≠ 0 ∧ P0.Nrep.map (Nat.cast : ℕ → ℝ) *ᵥ v = β • v) ∧
      ∀ x : P0.Rep → ℂ, x ≠ 0 → ∀ μ : ℂ,
        P0.Nrep.map (Nat.cast : ℕ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ β := by
  obtain ⟨T, hT⟩ := hC
  have : Nonempty P0.Rep := (P0.cover T hT).elim (fun h => ⟨⟨T, h⟩⟩) fun h => ⟨⟨T.swap, h⟩⟩
  have h := perron_root_of_intertwine (NrepQ P0) (fun _ _ => Nat.cast_nonneg _) _ (PrepQ P0)
    (prepQ_nrepQ P0 hbal) ℓ β (by rwa [incQ_map_real]) (vecMul_prepQ_pos P0 ℓ hℓ hne)
  rwa [nrepQ_map_real, show (NrepQ P0).map ((↑) : ℚ → ℂ) = P0.Nrep.map Nat.cast by
    ext; simp] at h

include hM hbal hne hSC hℓ hℓN in
/-- **(b) `β` is the simple Perron root of `N_C`**: `rootMultiplicity_rep` and
`perron_root_rep`. -/
theorem simple_perron_root_rep (hC : S.C.Nonempty) :
    rootMultiplicity β ((NrepQ P0).charpoly.map (algebraMap ℚ ℝ)) = 1 ∧
      (∃ v : P0.Rep → ℝ, v ≠ 0 ∧ P0.Nrep.map (Nat.cast : ℕ → ℝ) *ᵥ v = β • v) ∧
      ∀ x : P0.Rep → ℂ, x ≠ 0 → ∀ μ : ℂ,
        P0.Nrep.map (Nat.cast : ℕ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ β :=
  ⟨rootMultiplicity_rep P0 hM hbal hne hSC ℓ hℓ β hℓN hC, perron_root_rep P0 hbal hne ℓ hℓ β hℓN hC⟩

include hM hbal hne hSC hℓ hℓN in
/-- **(d) Theorem A(iv) on representatives**: every `Q` intertwining `N_C` with an
`R` annihilated by `χ_M` factors as `Q = L' P_R` with `L' M = R L'`, and `L'` is
injective unless `Q = 0` (`factor_through_parikh_full`). -/
theorem factor_through_rep (hC : S.C.Nonempty) {Y : Type*} [AddCommGroup Y] [Module ℚ Y]
    (Q : (P0.Rep → ℚ) →ₗ[ℚ] Y) (R : Y →ₗ[ℚ] Y)
    (hQ : Q ∘ₗ Matrix.toLin' (NrepQ P0) = R ∘ₗ Q) (hR : aeval R (incQ S).charpoly = 0) :
    ∃ L' : (Fin 3 → ℚ) →ₗ[ℚ] Y, Q = L' ∘ₗ Matrix.mulVecLin (PrepQ P0) ∧
      L' ∘ₗ Matrix.toLin' (incQ S) = R ∘ₗ L' ∧ (Q ≠ 0 → Function.Injective L') :=
  factor_through_parikh_full (NrepQ P0) (fun _ _ => Nat.cast_nonneg _)
    (by rwa [nrepQ_map_real]) _ hM (PrepQ P0) (prepQ_nrepQ P0 hbal) ℓ β
    (by rwa [incQ_map_real]) (vecMul_prepQ_pos P0 ℓ hℓ hne) Q R hQ hR
    (prep_surjective P0 hM hbal hne hC)

end Rep

/-! ### Control: a state splitting of `M0` with `ker P ≠ 0` -/

section Control

open Psc.M0Pisot

/-- Four states `0, 1, 2a, 2b` over `M0` (`Psc.M0Pisot.M0`): `N i j` counts the
children `i` of `j`; the letter `2` is split into `2a`, `2b`, each with the
children `0`, `1` and the other copy. -/
def ctrlN : Matrix (Fin 4) (Fin 4) ℚ := !![5, 21, 1, 1; 6, 26, 1, 1; 6, 24, 0, 1; 0, 0, 1, 0]

/-- The Parikh map of the four states: `0 ↦ e₀`, `1 ↦ e₁`, `2a, 2b ↦ e₂`. -/
def ctrlP : Matrix (Fin 3) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1]

theorem ctrl_intertwine : ctrlP * ctrlN = M0 * ctrlP := by decide +kernel

theorem ctrl_irreducible : Irreducible M0.charpoly := f_is_charpoly ▸ f_irreducible

theorem ctrl_surjective : Function.Surjective ctrlP.mulVecLin :=
  Psc.ParikhRank.surjective_of_intertwine ctrl_intertwine ctrl_irreducible (by decide)

/-- `ker P ∋ e_{2a} - e_{2b} ≠ 0`. -/
theorem ctrl_ker_ne_bot : LinearMap.ker ctrlP.mulVecLin ≠ ⊥ :=
  (Submodule.ne_bot_iff _).2 ⟨![0, 0, 1, -1], by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; decide +kernel, by decide⟩

/-- **Control for (a)**: the hypotheses hold with `ker P ≠ 0`. -/
theorem ctrl_charpoly :
    ctrlN.charpoly = M0.charpoly * (kerRestrict ctrl_intertwine).charpoly :=
  charpoly_eq_mul_kerRestrict ctrl_intertwine ctrl_surjective

theorem ctrl_nonneg : ∀ i j, 0 ≤ ctrlN i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [ctrlN]

open Fin.NatCast in
/-- The cycle `0 → 3 → 2 → 1 → 0` of positive entries `N i (i - 1)` makes the
digraph of `ctrlN` strongly connected. -/
theorem ctrl_stronglyConnected : PerronCore.StronglyConnected (ctrlN.map ((↑) : ℚ → ℝ)) := by
  have step : ∀ i : Fin 4, 0 < ctrlN.map ((↑) : ℚ → ℝ) i (i - 1) := by
    intro i; fin_cases i <;> norm_num [ctrlN]
  have key : ∀ (k : ℕ) (i : Fin 4),
      Relation.TransGen (fun a b => 0 < ctrlN.map ((↑) : ℚ → ℝ) a b) i
        (i - ((k : Fin 4) + 1)) := by
    intro k
    induction k with
    | zero => intro i; rw [Nat.cast_zero, zero_add]; exact .single (step i)
    | succ k ih =>
      intro i
      refine (ih i).tail ?_
      convert step (i - ((k : Fin 4) + 1)) using 2
      push_cast; abel
  intro i j
  convert key (i - j - 1).val i using 1
  simp

/-- The Perron data of `M0` on the control: the root `b ∈ (31, 32)` of `χ_{M0}`,
the left eigenvector `ℓ = (6b, b² - 6b - 1, b + 1) > 0`, and `ℓ P > 0`. -/
theorem ctrl_perron : ∃ b : ℝ, 31 < b ∧ b < 32 ∧ ∃ ℓ : Fin 3 → ℝ, (∀ a, 0 < ℓ a) ∧
    ℓ ᵥ* M0.map ((↑) : ℚ → ℝ) = b • ℓ ∧ ∀ i, 0 < (ℓ ᵥ* ctrlP.map ((↑) : ℚ → ℝ)) i := by
  obtain ⟨b, ⟨hb1, hb2⟩, hb⟩ :=
    intermediate_value_Ioo (show (31 : ℝ) ≤ 32 by norm_num) g_continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (g 31) (g 32) by norm_num [g])
  have hg : b ^ 3 - 32 * b ^ 2 + 5 * b + 2 = 0 := hb
  have hℓ : ∀ a, 0 < ![6 * b, b ^ 2 - 6 * b - 1, b + 1] a := by
    intro a; fin_cases a <;> simp <;> nlinarith
  refine ⟨b, hb1, hb2, ![6 * b, b ^ 2 - 6 * b - 1, b + 1], hℓ, ?_, fun i => ?_⟩
  · funext j
    fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_three, M0] <;>
      first | ring1 | linear_combination (-1 : ℝ) * hg
  · fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_three, ctrlP] <;> nlinarith

/-- **Control for (b)**: the Perron hypotheses hold on the control, so `χ_{M0}` is
coprime to `χ_{N | ker P}`, and the Perron root `b ∈ (31, 32)` of `M0` is a simple
root of `χ_N` and its spectral radius. -/
theorem ctrl_isCoprime_and_simple :
    IsCoprime M0.charpoly (kerRestrict ctrl_intertwine).charpoly ∧
      ∃ b : ℝ, 31 < b ∧ b < 32 ∧ rootMultiplicity b (ctrlN.charpoly.map (algebraMap ℚ ℝ)) = 1 ∧
        (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ ctrlN.map ((↑) : ℚ → ℝ) *ᵥ v = b • v) ∧
        ∀ x : Fin 4 → ℂ, x ≠ 0 → ∀ μ : ℂ, ctrlN.map ((↑) : ℚ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ b := by
  obtain ⟨b, hb1, hb2, ℓ, -, hℓ, hL⟩ := ctrl_perron
  exact ⟨isCoprime_charpoly_kerRestrict ctrlN ctrl_nonneg ctrl_stronglyConnected M0
      ctrl_irreducible ctrlP ctrl_intertwine ℓ b hℓ hL,
    b, hb1, hb2, rootMultiplicity_charpoly_eq_one ctrlN ctrl_nonneg ctrl_stronglyConnected M0
      ctrl_irreducible ctrlP ctrl_intertwine ℓ b hℓ hL ctrl_surjective,
    perron_root_of_intertwine ctrlN ctrl_nonneg M0 ctrlP ctrl_intertwine ℓ b hℓ hL⟩

/-- **Control for (d)**: on the control, `Q = P` and `R = M0` (Cayley–Hamilton)
meet the hypotheses of `factor_through_parikh_full`, with `Q ≠ 0`. -/
theorem ctrl_factor : ctrlP.mulVecLin ≠ 0 ∧ ∃ L' : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ),
    ctrlP.mulVecLin = L' ∘ₗ ctrlP.mulVecLin ∧ L' ∘ₗ Matrix.toLin' M0 = Matrix.toLin' M0 ∘ₗ L' ∧
      (ctrlP.mulVecLin ≠ 0 → Function.Injective L') := by
  obtain ⟨b, -, -, ℓ, -, hℓ, hL⟩ := ctrl_perron
  refine ⟨fun h => by simpa [ctrlP] using congrFun (LinearMap.congr_fun h (Pi.single 0 1)) 0,
    factor_through_parikh_full ctrlN ctrl_nonneg ctrl_stronglyConnected M0 ctrl_irreducible ctrlP
      ctrl_intertwine ℓ b hℓ hL _ _ (mulVecLin_comp_toLin' ctrl_intertwine) ?_ ctrl_surjective⟩
  change aeval (Matrix.toLinAlgEquiv' M0) M0.charpoly = 0
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix (Fin 3) (Fin 3) ℚ ≃ₐ[ℚ] _) M0
    M0.charpoly).trans (by rw [aeval_self_charpoly, map_zero])

/-- On the control `N` acts on `ker P = {x : x₀ = x₁ = 0, x₂ + x₃ = 0}` as `-1`. -/
theorem ctrl_kerRestrict : kerRestrict ctrl_intertwine = 0 - (1 : ℚ) • 1 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun i => ?_)
  have hx := LinearMap.mem_ker.1 x.2
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  simp [ctrlP, mulVec, dotProduct, Fin.sum_univ_four] at h0 h1 h2
  fin_cases i <;> simp [ctrlN, mulVec, dotProduct, Fin.sum_univ_four, h0, h1] <;> linarith

/-- **The cofactor on the control**: `χ_{N | ker P} = X + 1`, so
`χ_N = χ_{M0} · (X + 1)`.  `dim ker P = 1` is read off the degrees of
`ctrl_charpoly`. -/
theorem ctrl_cofactor : (kerRestrict ctrl_intertwine).charpoly = X + 1 := by
  have hdeg := congrArg natDegree ctrl_charpoly
  rw [natDegree_mul (charpoly_monic _).ne_zero (LinearMap.charpoly_monic _).ne_zero,
    charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim, LinearMap.charpoly_natDegree,
    Fintype.card_fin, Fintype.card_fin] at hdeg
  rw [ctrl_kerRestrict, LinearMap.charpoly_sub_smul, LinearMap.charpoly_zero,
    show Module.finrank ℚ (LinearMap.ker ctrlP.mulVecLin) = 1 by omega, pow_one, X_comp, C_1]

/-- **Negative control: `P` onto cannot be dropped** from
`charpoly_eq_mul_kerRestrict`.  `P = 0` intertwines `ctrlN` with `M0` and the
identity fails (`charpoly_eq_mul_kerRestrict_iff`). -/
theorem neg_surjective_needed : ∃ h : (0 : Matrix (Fin 3) (Fin 4) ℚ) * ctrlN = M0 * 0,
    ctrlN.charpoly ≠ M0.charpoly * (kerRestrict h).charpoly :=
  ⟨by simp, fun hc => by
    obtain ⟨v, hv⟩ := (charpoly_eq_mul_kerRestrict_iff _).1 hc (fun _ => 1)
    simpa using congrFun hv 0⟩

/-- Two disjoint copies of `M0`: `diag(M0, M0)` on `Fin 3 ⊕ Fin 3`. -/
def blkN : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℚ := Matrix.fromBlocks M0 0 0 M0

/-- The Parikh map `[I | I]` of the two copies. -/
def blkP : Matrix (Fin 3) (Fin 3 ⊕ Fin 3) ℚ :=
  Matrix.of fun a => Sum.elim (fun k => if a = k then 1 else 0) fun k => if a = k then 1 else 0

theorem blk_intertwine : blkP * blkN = M0 * blkP := by decide +kernel

/-- **Negative control: strong connectivity cannot be dropped** from
`rootMultiplicity_charpoly_eq_one`.  On two disjoint copies of `M0`, `blkN ≥ 0`,
`blkP` is onto with `blkP blkN = M0 blkP` (`blk_intertwine`) and `ℓ blkP = (ℓ, ℓ) > 0`,
but `χ_{blkN} = χ_{M0}²`, so the Perron root `b` of `M0` is a double root. -/
theorem neg_sc_needed : (∀ i j, 0 ≤ blkN i j) ∧ Function.Surjective blkP.mulVecLin ∧
    ∃ b : ℝ, 31 < b ∧ b < 32 ∧ ∃ ℓ : Fin 3 → ℝ, ℓ ᵥ* M0.map ((↑) : ℚ → ℝ) = b • ℓ ∧
      (∀ j, 0 < (ℓ ᵥ* blkP.map ((↑) : ℚ → ℝ)) j) ∧
      rootMultiplicity b (blkN.charpoly.map (algebraMap ℚ ℝ)) = 2 := by
  obtain ⟨b, hb1, hb2, ℓ, hℓ0, hℓ, -⟩ := ctrl_perron
  have hβ : aeval b M0.charpoly = 0 := Psc.PerronSimple.isRoot_of_real_left_eigen M0 ℓ b
    (fun h => (hℓ0 0).ne' (by simp [h])) hℓ
  have hne : M0.charpoly.map (algebraMap ℚ ℝ) ≠ 0 := map_ne_zero (charpoly_monic _).ne_zero
  refine ⟨fun i j => ?_, Psc.ParikhRank.surjective_of_intertwine blk_intertwine
    ctrl_irreducible fun h => by simpa [blkP] using congrFun (congrFun h 0) (Sum.inl 0),
    b, hb1, hb2, ℓ, hℓ, fun j => ?_, ?_⟩
  · rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> norm_num [blkN, M0]
  · rcases j with j | j <;> fin_cases j <;>
      simpa [vecMul, dotProduct, Fin.sum_univ_three, blkP] using hℓ0 _
  · rw [blkN, charpoly_fromBlocks_zero₁₂, Polynomial.map_mul, rootMultiplicity_mul
      (mul_ne_zero hne hne), rootMultiplicity_eq_one_of_irreducible ctrl_irreducible hβ]

/-- Hence `blkN` is not strongly connected: every other hypothesis of
`rootMultiplicity_charpoly_eq_one` holds on it. -/
theorem blk_not_stronglyConnected :
    ¬ PerronCore.StronglyConnected (blkN.map ((↑) : ℚ → ℝ)) := fun hSC => by
  obtain ⟨hN, hP, b, -, -, ℓ, hℓ, hL, h2⟩ := neg_sc_needed
  rw [rootMultiplicity_charpoly_eq_one blkN hN hSC M0 ctrl_irreducible blkP blk_intertwine
    ℓ b hℓ hL hP] at h2
  exact absurd h2 (by norm_num)

end Control

/-! ### Representatives: `wTNorm`, every hypothesis but irreducibility of `χ_M` -/

section WT

open Psc.Binomial Psc.Incidence Psc.SignedCocycle Psc.ParikhRank Psc.SignedIntertwiner

theorem wT_nrep (i j : wTNorm.Rep) : wTNorm.Nrep i j = 1 := by
  obtain rfl := wTNorm_rep i
  obtain rfl := wTNorm_rep j
  decide

/-- **Control for the representative theorems.**  `wTNorm` (the zero-return system
`Psc.SignedIntertwiner.wT` of the identity substitution) meets every hypothesis of
`charpoly_nrep_eq_mul`, `cofactor_int`, `isCoprime_rep`, `rootMultiplicity_rep`,
`perron_root_rep`, `simple_perron_root_rep` and `factor_through_rep` except
irreducibility of `χ_M` (`M = I`): balance, nonempty tracks, `C ≠ ∅`, strong
connectivity of `N_C = (1)`, and `ℓ = 1 > 0` with `ℓ M = 1 · ℓ`. -/
theorem wT_rep_hyps :
    (∀ T ∈ wT.C, Equiv1 T.1 T.2) ∧ (∀ T ∈ wT.C, T.1 ≠ []) ∧ wT.C.Nonempty ∧
      PerronCore.StronglyConnected (wTNorm.Nrep.map (Nat.cast : ℕ → ℝ)) ∧
      ∃ ℓ : Fin 3 → ℝ, (∀ a, 0 < ℓ a) ∧
        ℓ ᵥ* (inc wT.s).map (Nat.cast : ℕ → ℝ) = (1 : ℝ) • ℓ := by
  refine ⟨fun T hT => (wT_equiv2 T hT).1, by decide, by decide, fun i j => ?_,
    fun _ => 1, fun _ => one_pos, ?_⟩
  · obtain rfl := wTNorm_rep i
    obtain rfl := wTNorm_rep j
    exact .single (by simp [wT_nrep])
  · have h0 : ∀ c : Fin 3, wT.s c = [c] := fun c => rfl
    funext c
    fin_cases c <;> simp [vecMul, dotProduct, Fin.sum_univ_three, h0]

/-- **Control for `perron_root_rep`**, which does not use irreducibility of `χ_M`:
on `wTNorm`, `β = 1` is an eigenvalue of `N_C` bounding every complex eigenvalue. -/
theorem wT_perron_root :
    (∃ v : wTNorm.Rep → ℝ, v ≠ 0 ∧ wTNorm.Nrep.map (Nat.cast : ℕ → ℝ) *ᵥ v = (1 : ℝ) • v) ∧
      ∀ x : wTNorm.Rep → ℂ, x ≠ 0 → ∀ μ : ℂ,
        wTNorm.Nrep.map (Nat.cast : ℕ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ 1 := by
  obtain ⟨hbal, hne, hC, -, ℓ, hℓ, hℓN⟩ := wT_rep_hyps
  exact perron_root_rep wTNorm hbal hne ℓ hℓ 1 hℓN hC

/-- **Negative control: irreducibility of `χ_M` cannot be dropped** from
`charpoly_nrep_eq_mul`.  On `wTNorm`, `deg χ_{N_C} = |R| = 1 < 3 = deg χ_M`, so `χ_M`
divides no factorization of `χ_{N_C}`. -/
theorem wT_no_cofactor (g : ℚ[X]) : (NrepQ wTNorm).charpoly ≠ (incQ wT).charpoly * g := by
  intro h
  have hg : g ≠ 0 := by
    rintro rfl
    exact (charpoly_monic _).ne_zero (by rw [h, mul_zero])
  have h1 := congrArg natDegree h
  have hc : Fintype.card wTNorm.Rep = 1 := Fintype.card_eq_one_iff.2 ⟨wTRep, wTNorm_rep⟩
  rw [natDegree_mul (charpoly_monic _).ne_zero hg, charpoly_natDegree_eq_dim,
    charpoly_natDegree_eq_dim, hc, Fintype.card_fin] at h1
  omega

/-- Hence `χ_M` of `wT` (`M = I`) is not irreducible: every other hypothesis of
`charpoly_nrep_eq_mul` holds (`wT_rep_hyps`) and its conclusion fails. -/
theorem wT_not_irreducible : ¬ Irreducible (incQ wT).charpoly := fun hM => by
  obtain ⟨hbal, hne, hC, -⟩ := wT_rep_hyps
  exact wT_no_cofactor _ (charpoly_nrep_eq_mul wTNorm hM hbal hne hC)

end WT

end Psc.KernelCofactor
