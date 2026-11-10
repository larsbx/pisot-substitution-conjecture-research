/-
# Rank and characteristic-polynomial clauses of the Parikh intertwiner

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `thm:parikh` (the clauses
after the column identity: `rank P_C = d`, `χ_M ∣ χ_{N_C}`, `m ≥ d`, and the
similarity when `m = d`); `docs/c4-concentration-attack-2026-11-06.md` §8.

The clauses are proved once, for an abstract intertwiner (`Abstract` section):
`P : ℚ^ι → ℚ³` and `N : ℚ^ι → ℚ^ι` with `P N = M P`, `P ≠ 0` and `χ_M`
irreducible.  Then

* `aeval_intertwine`: `P f(N) = f(M) P` for every rational polynomial `f`;
* `surjective_of_intertwine` (`rank P = d`): the range of `P` is `M`-invariant
  and nonzero, hence everything by `Psc.Cyclicity.invariant_eq_bot_or_top`;
* `card_ge_of_intertwine` (`m ≥ d`): `3 ≤ |ι|`;
* `charpoly_dvd_of_intertwine` (`χ_M ∣ χ_N`): Cayley–Hamilton for `N` and the
  intertwining give `χ_N(M) P = 0`; surjectivity gives `χ_N(M) = 0`; so
  `minpoly M ∣ χ_N`, and `minpoly M = χ_M` since `χ_M` is irreducible and monic;
  `charpoly_dvd_of_map_rat` (Gauss: the divisor is monic over `ℤ`) descends
  divisibility of rational characteristic polynomials to integer matrices, and
  `charpoly_dvd_int_of_rat` is its form for natural matrices (`map_natCast_intCast`
  casts a natural matrix through `ℤ`);
* `similar_of_intertwine` (`m = d`): for every `e : ι ≃ Fin 3`, the reindexed
  `Pe` is invertible and the reindexed `N` is `Pe⁻¹ M Pe`.

Two instantiations, over a `Psc.Binomial.ChildSystem S` on `Fin 3` with
`M = incQ S` (the cast of `Psc.Incidence.inc S.s`):

* **representatives (the manuscript's matrices).**  For a
  `Psc.SignedCocycle.Normalisation P` of a balanced system (`Equiv1` tracks),
  `Prep P` is the Parikh matrix of the representatives' top tracks and
  `prep_nrep` is `P_R N_C = M P_R` with `N_C = A + B` the representative
  matrix `Psc.SignedCocycle.Normalisation.Nrep`.  `prep_surjective`,
  `card_rep_ge`, `charpoly_dvd_rep`, `charpoly_dvd_rep_int`,
  `similar_rep_of_equiv`, `exists_similar_rep_of_card_eq` are the clauses of
  `thm:parikh` as stated in the manuscript, given `χ_M` irreducible, balance and
  (except for the `m = d` clause) `C` nonempty; the nonempty top tracks are
  derived (`Psc.SignedCocycle.Normalisation.top_ne_nil`);
* **the raw ordered double cover.**  `PcQ S`, `NcQ S` (casts of
  `Psc.ParikhIntertwiner.Pc S`, `Psc.ParikhIntertwiner.Nc S`, indexed by all of
  `C`, no balance needed).  `pc_surjective`, `card_ge`, `charpoly_dvd`,
  `charpoly_dvd_int` hold for it too.  Its `m = d` clause
  (`similar_of_equiv`, `exists_similar_of_card_eq`) is **vacuous whenever `C`
  admits a normalisation**: `card_state_eq_two_mul` gives `|C| = 2 |R|`, so
  `no_equiv_fin3`.  It is kept only for non-swap-closed systems.

Not proved here: the identification of the cofactor `χ_{N_C} / χ_M` with the
characteristic polynomial of `N_C` on `ker P_C`, and Perron simplicity of `β`
for `N_C` (both in `Psc.KernelCofactor`).  The hypotheses `C` nonempty and nonempty
top tracks exclude the degenerate `P = 0` (`prep_ne_zero`, `pcQ_ne_zero`); on
representatives the second follows from balance, on the double cover it is
assumed (`hne`).
-/
import PscVerif.ParikhIntertwiner
import PscVerif.SignedCocycle
import PscVerif.Cyclicity

namespace Psc.ParikhRank

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.ParikhIntertwiner Psc.SignedCocycle

/-- Casting a natural matrix through `ℤ`. -/
theorem map_natCast_intCast {m n R : Type*} [Ring R] (A : Matrix m n ℕ) :
    (A.map (Nat.cast : ℕ → ℤ)).map (Int.castRingHom R) = A.map (Nat.cast : ℕ → R) := by
  ext; simp

/-! ### The clauses for an abstract intertwiner -/

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix (Fin 3) (Fin 3) ℚ}
  {P : Matrix (Fin 3) ι ℚ} {N : Matrix ι ι ℚ}

theorem pow_intertwine (h : P * N = M * P) (n : ℕ) : P * N ^ n = M ^ n * P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← pow_succ]

/-- `P f(N) = f(M) P` for every rational polynomial `f`. -/
theorem aeval_intertwine (h : P * N = M * P) (f : ℚ[X]) :
    P * aeval N f = aeval M f * P := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul,
      Matrix.mul_smul, Matrix.smul_mul, pow_intertwine h]

/-- **`rank P = d`.** -/
theorem surjective_of_intertwine (h : P * N = M * P) (hM : Irreducible M.charpoly)
    (hP : P ≠ 0) : Function.Surjective (Matrix.mulVecLin P) := by
  rw [← LinearMap.range_eq_top]
  refine (Psc.Cyclicity.invariant_eq_bot_or_top M hM _ ?_).resolve_left ?_
  · rintro _ ⟨v, rfl⟩
    exact ⟨N *ᵥ v, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]⟩
  · intro hbot
    refine hP (ext_of_mulVec_single fun j => ?_)
    have : P *ᵥ Pi.single j 1 ∈ LinearMap.range P.mulVecLin := ⟨_, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    rw [this, Matrix.zero_mulVec]

/-- **`m ≥ d`.** -/
theorem card_ge_of_intertwine (h : P * N = M * P) (hM : Irreducible M.charpoly)
    (hP : P ≠ 0) : 3 ≤ Fintype.card ι := by
  have := LinearMap.finrank_le_finrank_of_surjective (surjective_of_intertwine h hM hP)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using this

/-- **`χ_M ∣ χ_N`** over `ℚ`. -/
theorem charpoly_dvd_of_intertwine (h : P * N = M * P) (hM : Irreducible M.charpoly)
    (hP : P ≠ 0) : M.charpoly ∣ N.charpoly := by
  have hz : aeval M N.charpoly * P = 0 := by
    rw [← aeval_intertwine h, aeval_self_charpoly, Matrix.mul_zero]
  have hzero : aeval M N.charpoly = 0 := by
    refine ext_of_mulVec_single fun i => ?_
    obtain ⟨v, hv⟩ := surjective_of_intertwine h hM hP (Pi.single i 1)
    rw [Matrix.mulVecLin_apply] at hv
    rw [← hv, Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec, Matrix.zero_mulVec]
  rw [minpoly.eq_of_irreducible_of_monic hM (aeval_self_charpoly M) (charpoly_monic M)]
  exact minpoly.dvd ℚ M hzero

/-- **Gauss.**  Divisibility of the rational characteristic polynomials of integer
matrices descends to `ℤ` (the divisor is monic). -/
theorem charpoly_dvd_of_map_rat {κ : Type*} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℤ}
    {B : Matrix ι ι ℤ}
    (h : (A.map (Int.castRingHom ℚ)).charpoly ∣ (B.map (Int.castRingHom ℚ)).charpoly) :
    A.charpoly ∣ B.charpoly := by
  rwa [← Polynomial.map_dvd_map (Int.castRingHom ℚ) Int.cast_injective (charpoly_monic _),
    ← charpoly_map, ← charpoly_map]

/-- **Gauss**, natural matrices: `charpoly_dvd_of_map_rat` on their integer casts
(`map_natCast_intCast`). -/
theorem charpoly_dvd_int_of_rat {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M₀ : Matrix κ κ ℕ} {N₀ : Matrix ι ι ℕ}
    (h : (M₀.map (Nat.cast : ℕ → ℚ)).charpoly ∣ (N₀.map (Nat.cast : ℕ → ℚ)).charpoly) :
    (M₀.map (Nat.cast : ℕ → ℤ)).charpoly ∣ (N₀.map (Nat.cast : ℕ → ℤ)).charpoly :=
  charpoly_dvd_of_map_rat (by rwa [map_natCast_intCast, map_natCast_intCast])

/-- **`m = d`.**  For `e : ι ≃ Fin 3`, the reindexed `Pe` is invertible and the
reindexed `N` is `Pe⁻¹ M Pe`. -/
theorem similar_of_intertwine (h : P * N = M * P) (hM : Irreducible M.charpoly)
    (hP : P ≠ 0) (e : ι ≃ Fin 3) :
    IsUnit (P.submatrix id e.symm) ∧
      N.submatrix e.symm e.symm = (P.submatrix id e.symm)⁻¹ * M * P.submatrix id e.symm := by
  set Pe := P.submatrix id e.symm
  have hPe : IsUnit Pe := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro x
    obtain ⟨v, hv⟩ := surjective_of_intertwine h hM hP x
    refine ⟨v ∘ e.symm, ?_⟩
    rw [← hv, Matrix.mulVecLin_apply, Matrix.submatrix_mulVec_equiv]
    ext; simp [Function.comp_def]
  refine ⟨hPe, ?_⟩
  have hint : Pe * N.submatrix e.symm e.symm = M * Pe := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, h,
      Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  rw [Matrix.mul_assoc, ← hint]
  exact (Matrix.nonsing_inv_mul_cancel_left Pe _ ((Matrix.isUnit_iff_isUnit_det Pe).mp hPe)).symm

end Abstract

variable (S : ChildSystem (Fin 3))

/-- The rational incidence matrix `M`. -/
abbrev incQ : Matrix (Fin 3) (Fin 3) ℚ := (inc S.s).map (Nat.cast : ℕ → ℚ)

/-! ### Representatives: the manuscript's `P_C` and `N_C = A + B` -/

section Rep

variable {α : Type*} [DecidableEq α] {S' : ChildSystem α} (P : Normalisation S')

/-- The Parikh matrix of the representatives' top tracks. -/
def Prep : Matrix α P.Rep ℕ := Matrix.of fun a j => j.1.1.count a

/-- **`thm:parikh` on representatives**: `P_R N_C = M P_R`, for balanced states. -/
theorem prep_nrep [Fintype α] (hbal : ∀ T ∈ S'.C, Equiv1 T.1 T.2) :
    Prep P * P.Nrep = inc S'.s * Prep P := by
  ext a j
  have h := congrFun (congrFun (pc_nc S') a) ⟨j.1, P.sub j.2⟩
  simp only [Matrix.mul_apply, Pc_apply, Nc_apply] at h
  rw [P.sum_state fun V => V.1.count a * (S'.children j.1).count V] at h
  simp only [Matrix.mul_apply, Prep, Matrix.of_apply]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans h
  have hb := hbal i.1 (P.sub i.2) a
  simp only [Prod.fst_swap, ← hb, Normalisation.Nrep, Normalisation.A, Normalisation.B,
    Matrix.add_apply, Matrix.of_apply]
  ring

theorem prep_ne_zero (hC : S'.C.Nonempty) (hne : ∀ T ∈ S'.C, T.1 ≠ []) :
    (Prep P).map (Nat.cast : ℕ → ℚ) ≠ 0 := by
  obtain ⟨T, hT⟩ := hC
  have hR : ∃ j : P.Rep, True := by
    rcases P.cover T hT with h | h
    · exact ⟨⟨T, h⟩, trivial⟩
    · exact ⟨⟨T.swap, h⟩, trivial⟩
  obtain ⟨j, -⟩ := hR
  obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil (hne j.1 (P.sub j.2))
  intro h0
  have := congrFun (congrFun h0 a) j
  simp only [Matrix.map_apply, Prep, Matrix.of_apply, hw, List.count_cons_self,
    Matrix.zero_apply, Nat.cast_add, Nat.cast_one] at this
  exact Nat.cast_add_one_ne_zero _ this

end Rep

section RepFin3

variable {S} (P : Normalisation S)

abbrev PrepQ : Matrix (Fin 3) P.Rep ℚ := (Prep P).map (Nat.cast : ℕ → ℚ)

abbrev NrepQ : Matrix P.Rep P.Rep ℚ := P.Nrep.map (Nat.cast : ℕ → ℚ)

theorem prepQ_nrepQ (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) :
    PrepQ P * NrepQ P = incQ S * PrepQ P := by
  change (Prep P).map (Nat.castRingHom ℚ) * P.Nrep.map (Nat.castRingHom ℚ) =
    (inc S.s).map (Nat.castRingHom ℚ) * (Prep P).map (Nat.castRingHom ℚ)
  rw [← Matrix.map_mul, ← Matrix.map_mul, prep_nrep P hbal]

variable (hM : Irreducible (incQ S).charpoly) (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2)
include hM hbal

/-- **`thm:parikh`, `rank P_C = d`**, on representatives.  The nonempty top tracks
needed for `P_R ≠ 0` follow from balance (`Psc.SignedCocycle.Normalisation.top_ne_nil`). -/
theorem prep_surjective (hC : S.C.Nonempty) : Function.Surjective (Matrix.mulVecLin (PrepQ P)) :=
  surjective_of_intertwine (prepQ_nrepQ P hbal) hM (prep_ne_zero P hC (P.top_ne_nil hbal))

/-- **`thm:parikh`, `m ≥ d`**, on representatives: `3 ≤ |R|`. -/
theorem card_rep_ge (hC : S.C.Nonempty) : 3 ≤ Fintype.card P.Rep :=
  card_ge_of_intertwine (prepQ_nrepQ P hbal) hM (prep_ne_zero P hC (P.top_ne_nil hbal))

/-- **`thm:parikh`, `χ_M ∣ χ_{N_C}`**, on representatives. -/
theorem charpoly_dvd_rep (hC : S.C.Nonempty) : (incQ S).charpoly ∣ (NrepQ P).charpoly :=
  charpoly_dvd_of_intertwine (prepQ_nrepQ P hbal) hM (prep_ne_zero P hC (P.top_ne_nil hbal))

/-- **`thm:parikh`, `χ_M ∣ χ_{N_C}` over `ℤ`**, on representatives. -/
theorem charpoly_dvd_rep_int (hC : S.C.Nonempty) :
    ((inc S.s).map (Nat.cast : ℕ → ℤ)).charpoly ∣ (P.Nrep.map (Nat.cast : ℕ → ℤ)).charpoly :=
  charpoly_dvd_int_of_rat (charpoly_dvd_rep P hM hbal hC)

/-- **`thm:parikh`, `m = d`**, on representatives. -/
theorem similar_rep_of_equiv (e : P.Rep ≃ Fin 3) :
    IsUnit ((PrepQ P).submatrix id e.symm) ∧
      (NrepQ P).submatrix e.symm e.symm =
        ((PrepQ P).submatrix id e.symm)⁻¹ * incQ S * (PrepQ P).submatrix id e.symm :=
  similar_of_intertwine (prepQ_nrepQ P hbal) hM
    (prep_ne_zero P ⟨(e.symm 0).1, P.sub (e.symm 0).2⟩ (P.top_ne_nil hbal)) e

/-- **`thm:parikh`, `m = d`, packaged**, on representatives: if `|R| = 3`. -/
theorem exists_similar_rep_of_card_eq (hcard : Fintype.card P.Rep = 3) :
    ∃ e : P.Rep ≃ Fin 3, IsUnit ((PrepQ P).submatrix id e.symm) ∧
      (NrepQ P).submatrix e.symm e.symm =
        ((PrepQ P).submatrix id e.symm)⁻¹ * incQ S * (PrepQ P).submatrix id e.symm :=
  ⟨Fintype.equivFinOfCardEq hcard, similar_rep_of_equiv P hM hbal _⟩

end RepFin3

/-! ### The raw ordered double cover -/

/-- The rational state Parikh matrix of the double cover. -/
abbrev PcQ : Matrix (Fin 3) (State S) ℚ := (Pc S).map (Nat.cast : ℕ → ℚ)

/-- The rational raw state matrix of the double cover. -/
abbrev NcQ : Matrix (State S) (State S) ℚ := (Nc S).map (Nat.cast : ℕ → ℚ)

/-- `P_C N_C = M P_C` over `ℚ`, on the double cover. -/
theorem pcQ_ncQ : PcQ S * NcQ S = incQ S * PcQ S := by
  change (Pc S).map (Nat.castRingHom ℚ) * (Nc S).map (Nat.castRingHom ℚ) =
    (inc S.s).map (Nat.castRingHom ℚ) * (Pc S).map (Nat.castRingHom ℚ)
  rw [← Matrix.map_mul, ← Matrix.map_mul, pc_nc]

/-- `P_C f(N_C) = f(M) P_C`, on the double cover. -/
theorem pcQ_aeval (f : ℚ[X]) : PcQ S * aeval (NcQ S) f = aeval (incQ S) f * PcQ S :=
  aeval_intertwine (pcQ_ncQ S) f

theorem pcQ_ne_zero (hC : S.C.Nonempty) (hne : ∀ T ∈ S.C, T.1 ≠ []) : PcQ S ≠ 0 := by
  obtain ⟨T, hT⟩ := hC
  obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil (hne T hT)
  intro h0
  have := congrFun (congrFun h0 a) ⟨T, hT⟩
  simp only [Matrix.map_apply, Pc_apply, hw, List.count_cons_self, Matrix.zero_apply,
    Nat.cast_add, Nat.cast_one] at this
  exact Nat.cast_add_one_ne_zero _ this

section Cover

variable (hM : Irreducible (incQ S).charpoly) (hne : ∀ T ∈ S.C, T.1 ≠ [])
include hM hne

/-- `rank P_C = d`, on the double cover. -/
theorem pc_surjective (hC : S.C.Nonempty) : Function.Surjective (Matrix.mulVecLin (PcQ S)) :=
  surjective_of_intertwine (pcQ_ncQ S) hM (pcQ_ne_zero S hC hne)

/-- `m ≥ d`, on the double cover. -/
theorem card_ge (hC : S.C.Nonempty) : 3 ≤ Fintype.card (State S) :=
  card_ge_of_intertwine (pcQ_ncQ S) hM (pcQ_ne_zero S hC hne)

/-- `χ_M ∣ χ_{N_C}` over `ℚ`, on the double cover. -/
theorem charpoly_dvd (hC : S.C.Nonempty) : (incQ S).charpoly ∣ (NcQ S).charpoly :=
  charpoly_dvd_of_intertwine (pcQ_ncQ S) hM (pcQ_ne_zero S hC hne)

/-- `χ_M ∣ χ_{N_C}` over `ℤ`, on the double cover. -/
theorem charpoly_dvd_int (hC : S.C.Nonempty) :
    ((inc S.s).map (Nat.cast : ℕ → ℤ)).charpoly ∣ ((Nc S).map (Nat.cast : ℕ → ℤ)).charpoly :=
  charpoly_dvd_int_of_rat (charpoly_dvd S hM hne hC)

/-- `m = d`, on the double cover.  Vacuous if `C` admits a normalisation
(`no_equiv_fin3`). -/
theorem similar_of_equiv (e : State S ≃ Fin 3) :
    IsUnit ((PcQ S).submatrix id e.symm) ∧
      (NcQ S).submatrix e.symm e.symm =
        ((PcQ S).submatrix id e.symm)⁻¹ * incQ S * (PcQ S).submatrix id e.symm :=
  similar_of_intertwine (pcQ_ncQ S) hM (pcQ_ne_zero S ⟨(e.symm 0).1, (e.symm 0).2⟩ hne) e

/-- `m = d`, packaged, on the double cover.  Vacuous if `C` admits a
normalisation (`card_state_eq_two_mul`). -/
theorem exists_similar_of_card_eq (hcard : Fintype.card (State S) = 3) :
    ∃ e : State S ≃ Fin 3, IsUnit ((PcQ S).submatrix id e.symm) ∧
      (NcQ S).submatrix e.symm e.symm =
        ((PcQ S).submatrix id e.symm)⁻¹ * incQ S * (PcQ S).submatrix id e.symm :=
  ⟨Fintype.equivFinOfCardEq hcard, similar_of_equiv S hM hne _⟩

end Cover

/-- With a normalisation, the double cover has `|C| = 2 |R|` states. -/
theorem card_state_eq_two_mul {α : Type*} [DecidableEq α] {S : ChildSystem α}
    (P : Normalisation S) : Fintype.card (State S) = 2 * P.R.card := by
  rw [Fintype.card_coe, P.C_eq, Finset.card_union_of_disjoint P.disjoint_image,
    Finset.card_image_of_injective _ Prod.swap_injective]
  ring

/-- So the double-cover `m = d` hypothesis is unsatisfiable under a normalisation. -/
theorem no_equiv_fin3 {S : ChildSystem (Fin 3)} (P : Normalisation S) :
    IsEmpty (State S ≃ Fin 3) := by
  refine ⟨fun e => ?_⟩
  have h := Fintype.card_congr e
  rw [card_state_eq_two_mul P, Fintype.card_fin] at h
  omega

end Psc.ParikhRank
