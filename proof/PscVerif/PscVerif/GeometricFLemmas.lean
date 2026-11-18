/-
# Lemmas 1 (1), 1 (3) and 4 of the (F)-class note: `ℓ`, interior addresses, powers, reversal

`docs/c4-geometric-f-class-2026-11-16.md` §2: Lemma 1 (1) (a rational vector killed by `ℓ` is
`0`), Lemma 1 (3) (no eigenvalue of `M` is `0` or a root of unity; `M^k − I` is invertible
over `ℚ`), Lemma 4 (1) (interior periodic addresses), 4 (2) ((F) for `σ` iff for `σ^m`) and
4 (3) ((F) for `σ` iff for the reversal `σ^R`).  `docs/c4-closure-attempt-2026-11-16.md` §15.2
records these lemmas as not machine-checked; this module checks them against the
repository's definitions.

**Setting.**  That of `PscVerif.GeometricFInclusion`: `α` a finite alphabet with decidable
equality, `s : α → List α`, `σ = Psc.Binomial.subst s`, `σ^m = Psc.Binomial.power s m`,
`M = Psc.GeometricF.incZ s` on integer vectors and `(inc s).map (Nat.cast : ℕ → ℚ)` over `ℚ`.
States, the prototile state map and property (F) are `Psc.GeometricF.IsState`, `Step`,
`StepN`, `PropertyF`; a length functional is an additive `L : (α → ℤ) →+ ℝ` with
`Psc.GeometricF.LengthData s L β`, on the standing class `Psc.GeometricF.lenHom ℓ`.  The
reversal is `Psc.GeometricF.reverseSubstitution s` and the reflection of states is
`Psc.GeometricF.reflectState` (`(j, v) ↦ (j, e_j − v)`), both of `PscVerif.GeometricFRank`.
The standing spectral hypotheses are used in the forms in which `PscVerif.GeometricFPisot`
states them: (I) `Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly`; (E) a real left
eigen-row `ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ`, nonzero or positive; and, for
Lemma 1 (3), a root of `χ_M` of modulus `> 1`.

**Definitions.**  `IsInteriorAddress s k e P Q v`: a factorisation `σ^k(e) = P e Q` with `P`,
`Q` nonempty and an integer vector `v` with `(M^k − I) v = p(P)` (the note's interior periodic
address `(k, e, P)`; `Q` is determined by `P`, and `v` by Lemma 1 (3),
`isInteriorAddress_unique`).  Helpers: `incQ_map_real`, `map_incZ_pow_sub_one`, `aeval_perron`,
`eval_perron_complex`, `L_reflectState`, `L_pvec_power`, `L_pow_sub_one_mulVec`,
`one_le_of_isInteriorAddress`.

**Proved here, in full** (`propext`, `Classical.choice`, `Quot.sound` only; no `sorry`):
* *Linear algebra over a field, any size.*  `charpoly_dvd_of_aeval_mulVec_eq_zero` (Bézout:
  `χ_A` irreducible and `q(A) w = 0`, `w ≠ 0`, give `χ_A ∣ q`); `linearIndependent_pow_mulVec`
  and `span_pow_mulVec_eq_top` (every nonzero vector is cyclic);
  **`eigenrow_eq_zero_of_irreducible`** (a left eigen-row over an extension that vanishes on a
  nonzero vector over the base field is `0`); `isUnit_aeval_of_root` (`q(A)` is invertible
  when some root of `χ_A` is not a root of `q`); `aeval_eq_zero_of_conj` (roots of an
  irreducible monic polynomial satisfy the same polynomial relations);
  `root_ne_zero_and_pow_ne_one`.
* **Lemma 1 (1).**  `eq_zero_of_dot_eq_zero` (rational form: `ℓ ≠ 0`, (I), (E) and
  `ℓ·w = 0`, `w ∈ ℚ^α`, give `w = 0`); **`lenHom_eq_zero_iff`**, `lenHom_injective` and
  `lenHom_zero_kernel` (the integer form `∀ v, lenHom ℓ v = 0 → v = 0`, which is the hypothesis
  `hzero` of `Psc.GeometricF.propertyF_reverse_iff` and `Psc.GeometricF.fc2_rank_transfer`);
  `lenHom_zero_kernel_of_pos` (positive `ℓ`).
* **Lemma 1 (3).**  **`eigenvalue_ne_zero_and_pow_ne_one`** (every complex eigenvalue `z` of
  `M` has `z ≠ 0` and `z^k ≠ 1` for `k ≥ 1`, given (I) and a root of modulus `> 1`);
  **`isUnit_incQ_pow_sub_one`** (`M^k − I` invertible over `ℚ`, `k ≥ 1`) and `isUnit_incQ`
  (`M` invertible), from a root `r` of `χ_M` in any field over `ℚ` with `r^k ≠ 1` (resp.
  `r ≠ 0`); `mulVec_pow_sub_one_injective` (the integer form); the Perron forms
  `isUnit_incQ_pow_sub_one_of_left_eigen`, `mulVec_pow_sub_one_injective_of_left_eigen`
  (`β > 1` real) and `eigenvalue_ne_zero_and_pow_ne_one_of_left_eigen`.
* **Lemma 4 (2).**  `stepN_power_to_stepN` (`(f_{σ^m})^k = f^{mk}`, from Lemma 2,
  `Psc.GeometricF.step_power_iff`), `stepN_to_stepN_power`, `stepN_mul_self`;
  **`propertyF_power_iff`** (`LengthData s L β`, `m ≥ 1`:
  `PropertyF (power s m) L ↔ PropertyF s L`); `lengthData_power_and_propertyF_iff` (the same
  with the length data passed to the power, `LengthData (power s m) L (β^m)`);
  `propertyF_power_zero_iff` (why `m ≥ 1`); `propertyF_power_iff_of_left_eigen`.
* **Lemma 4 (3).**  The exact correspondence of states: `reflectState_reflectState`,
  `isState_reflectState` (under `hzero`, a state with `v ≠ 0` reflects to a state with
  `e_j − v ≠ 0`), **`stepN_reverse_iff`** (`f_{σ^R}^k(x) = y` iff
  `f_σ^k(x̄) = ȳ` with `x̄ = reflectState x`, for states whose reflections are states),
  `periodic_reverse_iff`; the incidence matrix of `σ^R` is that of `σ`
  (`Psc.GeometricF.incZ_reverseSubstitution`).  The address form, which is the note's proof:
  **`isInteriorAddress_reverse`** (`(k, e, P, Q, v) ↦ (k, e, Q^R, P^R, e_e − v)`) and
  `isInteriorAddress_reverse_iff`, `noInteriorAddress_reverse_iff`,
  `propertyF_reverse_iff_of_addresses`.  **`propertyF_reverse_iff_of_irreducible`**: (I), (E),
  `ℓ > 0`, `β > 0` give `PropertyF (reverseSubstitution s) (lenHom ℓ) ↔ PropertyF s (lenHom ℓ)`
  (`Psc.GeometricF.propertyF_reverse_iff` with its `hzero` discharged by Lemma 1 (1));
  `fc2_rank_transfer_of_irreducible` (`Psc.GeometricF.fc2_rank_transfer` with `hzero`
  discharged the same way).
* **Lemma 4 (1).**  `periodic_iff_factorisation` (the note's first sentence: for a state
  `(j, v)`, `f^k(j, v) = (j, v)` iff `σ^k(j) = P j Q` with `(M^k − I) v = p(P)`; length data
  only) and `nonempty_of_factorisation` ("then `P` and `Q` are nonempty": `β > 1`, `hzero`,
  `k ≥ 1`, `v ≠ 0`); **`isInteriorAddress_of_periodic`** (`LengthData`, `β > 1`, `hzero`,
  `k ≥ 1`: an `f^k`-fixed state `(j, v)` with `v ≠ 0` gives a factorisation
  `σ^k(j) = P j Q` with `(M^k − I) v = p(P)`, `P`, `Q` nonempty);
  **`periodic_of_isInteriorAddress`** (`LengthData`, `β > 1`, no `hzero`: an interior address
  gives `k ≥ 1`, a state `(e, v)` with `v ≠ 0` and `f^k(e, v) = (e, v)`);
  `periodic_iff_isInteriorAddress`; **`propertyF_iff_no_interiorAddress`** ((F) says there is
  no interior periodic address); `isInteriorAddress_unique`;
  `propertyF_iff_no_interiorAddress_of_irreducible` (the standing-class form).
* **Non-vacuity, Tribonacci** (`Psc.Descendants.tribSubst`, PIP3): `trib_lemma1` (Lemma 1 (1)
  and (3) hold for every positive left eigen-row), `trib_propertyF_power`,
  `trib_propertyF_reverse` ((F) for every power and for the reversal `10/20/0`, from
  `Psc.GeometricFTriple.trib_propertyF`), `trib_no_interiorAddress`.
* **Negative controls.**  `ctrl_isInteriorAddress` (`01/12/021`:
  `(k, e, P, Q, v) = (1, 2, [0], [1], (−1, 0, 1))` is an interior periodic address, decided on
  words and integer vectors), `ctrl_not_propertyF'` (through Lemma 4 (1), the same conclusion as
  `Psc.GeometricFTriple.ctrl_not_propertyF`, for every positive left eigen-row);
  `ctrlRev_isInteriorAddress` (its reversal `10/21/120` has the address
  `(1, 2, [1], [0], (1, 0, 0))`, decided directly), `ctrlRev_isInteriorAddress_eq` (the same
  address is the image under `isInteriorAddress_reverse`), `ctrlRev_not_propertyF`,
  `ctrl_power_not_propertyF` ((F) fails for every power, Lemma 4 (2)); `carrier_lemma1_fails`
  (on the reducible strict control `10/102/211` both conclusions of Lemma 1 fail for every
  length data with `β > 1`: `w = (2, 0, −1) ≠ 0` has `ℓ·w = 0` and `(M − I) w = 0`),
  `carrier_periodic_not_interior` (there the state `(1, w)` is `f`-fixed with `w ≠ 0`, but
  `σ(1) = 102` has no factorisation `P 1 Q` with `P` nonempty: the forward direction of
  Lemma 4 (1) fails without Lemma 1 (1)), `carrier_not_propertyF` ((F) fails there), and
  `carrier_lengthData_gt_one` (length data with `β > 1` exist there, so these controls are not
  vacuous).

**Hypotheses and where they enter.**
* (I): Lemma 1 (1) and (3), through the Bézout step and Cayley–Hamilton
  (`charpoly_dvd_of_aeval_mulVec_eq_zero`); Lemma 1 (3) also through `minpoly` (the spectral
  form).  It is not used by Lemma 4 (2), nor by the converse direction of Lemma 4 (1).
* (E), `ℓ ≠ 0`: Lemma 1 (1).  The note's proof uses `w, Mw, M²w` on three letters; here
  `w, …, M^{n−1} w` on `n` letters, so any finite alphabet.
* A root of modulus `> 1` (or `r ≠ 0`, `r^k ≠ 1`): Lemma 1 (3); on the standing class the
  Perron root `β > 1`.
* `LengthData`: Lemma 2 (`f_{σ^m} = f^m` needs `f` total and single-valued), hence Lemma 4 (1),
  (2), (3).  `m ≥ 1` in Lemma 4 (2): `PropertyF (power s 0) L` says that every state is a vertex
  state (`propertyF_power_zero_iff`).  `β > 1` and `k ≥ 1` in Lemma 4 (1): `β^k > 1`.  `hzero`
  (Lemma 1 (1)) in the forward direction of Lemma 4 (1), where `carrier_periodic_not_interior`
  shows that it cannot be dropped, and in the state correspondence of Lemma 4 (3).

**Deviations from the note.**  Any finite alphabet.  The integrality condition
"`v := (M^k − I)^{-1} p(P) ∈ ℤ³`" is the existence of an integer `v` with `(M^k − I) v = p(P)`,
unique by Lemma 1 (3).  Lemma 4 (3) is proved twice: by the reflection of edges of
`PscVerif.GeometricFRank` (no `β > 1`), and by the note's correspondence of interior addresses
(`propertyF_reverse_iff_of_addresses`, with `β > 1`); both use `hzero`.  Lemma 1 (2) is
`PscVerif.GeometricFPisot` (properness) and is not repeated.

**Not proved here.**  Lemma 5 of the note (the identifications with Minervino–Thuswaldner and
with the leftmost-chain note); that `01/12/021` is PIP3 (the control uses only words and the
incidence matrix); (F) for any specimen other than those already on main; anything about
Theorems FC2, P, FC3, N, Fork beyond supplying the hypothesis `hzero`.  Universal C4 is open:
these lemmas are elementary facts about the state map and exclude no strict system.
-/
import PscVerif.GeometricFTriple
import PscVerif.GeometricFRank

namespace Psc.GeometricFLemmas

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.GeometricF

/-! ### Cyclic vectors and the Bézout step, over a field and any finite index type -/

section Cyclic

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Bézout step.**  If `χ_A` is irreducible and `q(A) w = 0` for a nonzero `w`, then
`χ_A ∣ q`: otherwise `a χ_A + b q = 1`, and Cayley–Hamilton gives `w = b(A) q(A) w = 0`. -/
theorem charpoly_dvd_of_aeval_mulVec_eq_zero (A : Matrix ι ι F) (hA : Irreducible A.charpoly)
    {w : ι → F} (hw : w ≠ 0) {q : F[X]} (hq : aeval A q *ᵥ w = 0) : A.charpoly ∣ q := by
  by_contra hndvd
  obtain ⟨a, b, hab⟩ := (hA.coprime_iff_not_dvd).mpr hndvd
  have h1 := congrArg (fun r => aeval A r *ᵥ w) hab
  simp only [map_add, map_mul, aeval_self_charpoly, mul_zero, zero_add, map_one,
    one_mulVec] at h1
  rw [← mulVec_mulVec, hq, mulVec_zero] at h1
  exact hw h1.symm

/-- **Cyclic vectors.**  If `χ_A` is irreducible, then for every nonzero `w` the vectors
`w, A w, …, A^{n−1} w` (`n = |ι|`) are linearly independent: a dependency is a nonzero `q`
of degree `< n` with `q(A) w = 0`, and `χ_A ∣ q` is impossible. -/
theorem linearIndependent_pow_mulVec (A : Matrix ι ι F) (hA : Irreducible A.charpoly)
    {w : ι → F} (hw : w ≠ 0) :
    LinearIndependent F fun k : Fin (Fintype.card ι) => A ^ (k : ℕ) *ᵥ w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set q : F[X] := ∑ i : Fin (Fintype.card ι), C (g i) * X ^ (i : ℕ) with hqdef
  have hq : aeval A q *ᵥ w = 0 := by
    rw [hqdef, map_sum, Matrix.sum_mulVec, ← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_mulVec]
  have hq0 : q = 0 :=
    eq_zero_of_dvd_of_degree_lt (charpoly_dvd_of_aeval_mulVec_eq_zero A hA hw hq)
      (by rw [charpoly_degree_eq_dim]; exact degree_sum_fin_lt g)
  intro i
  have h := congrArg (fun r : F[X] => r.coeff i) hq0
  simp only [hqdef, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro j _ hji
    have : (i : ℕ) ≠ j := fun h' => hji (Fin.ext h'.symm)
    simp [this]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

/-- The cyclic span of a nonzero vector is the whole space. -/
theorem span_pow_mulVec_eq_top (A : Matrix ι ι F) (hA : Irreducible A.charpoly) {w : ι → F}
    (hw : w ≠ 0) :
    Submodule.span F (Set.range fun k : Fin (Fintype.card ι) => A ^ (k : ℕ) *ᵥ w) = ⊤ :=
  (linearIndependent_pow_mulVec A hA hw).span_eq_top_of_card_eq_finrank' (by simp)

/-- **An eigen-row that vanishes on a nonzero vector over the base field is zero** (any size;
the `3 × 3` form with an abstract cyclicity hypothesis is
`Psc.ConcentrationAlgebra.eigenrow_eq_zero`).  If `ℓ A = β ℓ` over an extension `K` and
`ℓ·w = 0`, then `ℓ·Aᵏ w = βᵏ ℓ·w = 0`, and the `Aᵏ w` span `F^ι`. -/
theorem eigenrow_eq_zero_of_irreducible {K : Type*} [Field K] [Algebra F K]
    (A : Matrix ι ι F) (hA : Irreducible A.charpoly) {ℓ : ι → K} {β : K}
    (hℓ : ℓ ᵥ* A.map (algebraMap F K) = β • ℓ) {w : ι → F} (hw0 : w ≠ 0)
    (hw : ℓ ⬝ᵥ (algebraMap F K ∘ w) = 0) : ℓ = 0 := by
  let φ : (ι → F) →ₗ[F] K :=
    { toFun := fun u => ℓ ⬝ᵥ (algebraMap F K ∘ u)
      map_add' := fun u v => by simp [dotProduct, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [dotProduct, Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul,
          RingHom.id_apply]
        rw [Algebra.smul_def, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring }
  have hφ : ∀ u, φ (A *ᵥ u) = β * φ u := by
    intro u
    show ℓ ⬝ᵥ (algebraMap F K ∘ (A *ᵥ u)) = β * (ℓ ⬝ᵥ (algebraMap F K ∘ u))
    have e : algebraMap F K ∘ (A *ᵥ u) = A.map (algebraMap F K) *ᵥ (algebraMap F K ∘ u) := by
      ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e, Matrix.dotProduct_mulVec, hℓ, smul_dotProduct, smul_eq_mul]
  have hpow : ∀ k : ℕ, φ (A ^ k *ᵥ w) = 0 := by
    intro k
    induction k with
    | zero => simpa [φ] using hw
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, hφ, ih, mul_zero]
  have hker : LinearMap.ker φ = ⊤ := by
    rw [eq_top_iff, ← span_pow_mulVec_eq_top A hA hw0, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hpow k
  funext a
  have h : φ (Pi.single a 1) = 0 := by
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_top
  simpa [φ, dotProduct, Pi.single_apply] using h

/-- **The Bézout step, unit form.**  If `χ_A` is irreducible and some root `r` of `χ_A` in a
field over `F` is not a root of `q`, then `q(A)` is invertible: a kernel vector would give
`χ_A ∣ q`, hence `q(r) = 0`. -/
theorem isUnit_aeval_of_root {K : Type*} [Field K] [Algebra F K] (A : Matrix ι ι F)
    (hA : Irreducible A.charpoly) {r : K} (hr : aeval r A.charpoly = 0) {q : F[X]}
    (hq : aeval r q ≠ 0) : IsUnit (aeval A q) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨c, hc⟩ := charpoly_dvd_of_aeval_mulVec_eq_zero A hA hw0 hw
  exact hq (by rw [hc, map_mul, hr, zero_mul])

/-- **Conjugate roots satisfy the same relations.**  If `p` is irreducible and monic, `z` and
`r` are roots of `p` and `q(z) = 0`, then `q(r) = 0` (`p` is the minimal polynomial of `z`). -/
theorem aeval_eq_zero_of_conj {K : Type*} [Field K] [Algebra F K] {p q : F[X]}
    (hp : Irreducible p) (hmon : p.Monic) {z r : K} (hz : aeval z p = 0)
    (hr : aeval r p = 0) (hzq : aeval z q = 0) : aeval r q = 0 := by
  have h1 : p = minpoly F z := minpoly.eq_of_irreducible_of_monic hp hz hmon
  obtain ⟨c, hc⟩ : p ∣ q := h1 ▸ minpoly.dvd F z hzq
  rw [hc, map_mul, hr, zero_mul]

end Cyclic

/-- **Lemma 1 (3), for a polynomial.**  If `p ∈ ℚ[X]` is irreducible and monic and has a complex
root `r` with `1 < ‖r‖`, then no complex root of `p` is `0` or a root of unity: `z = 0` would
make `p ∣ X`, so `r = 0`; `z^k = 1` would make `p ∣ X^k − 1`, so `‖r‖ = 1`. -/
theorem root_ne_zero_and_pow_ne_one {p : ℚ[X]} (hp : Irreducible p) (hmon : p.Monic) {r : ℂ}
    (hr : aeval r p = 0) (hr1 : 1 < ‖r‖) {z : ℂ} (hz : aeval z p = 0) :
    z ≠ 0 ∧ ∀ k : ℕ, 1 ≤ k → z ^ k ≠ 1 := by
  constructor
  · rintro rfl
    have h := aeval_eq_zero_of_conj hp hmon hz hr (q := X) (by simp)
    rw [aeval_X] at h
    rw [h, norm_zero] at hr1
    linarith
  · intro k hk hzk
    have h := aeval_eq_zero_of_conj hp hmon hz hr (q := X ^ k - 1) (by simp [hzk])
    simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h
    have := Complex.norm_eq_one_of_pow_eq_one h (by omega)
    linarith

/-! ### Lemma 1 (1): a vector killed by `ℓ` is `0` -/

section Lemma1

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
/-- The rational incidence matrix, read over `ℝ`. -/
theorem incQ_map_real (s : α → List α) :
    ((inc s).map (Nat.cast : ℕ → ℚ)).map (algebraMap ℚ ℝ) = (inc s).map (Nat.cast : ℕ → ℝ) := by
  ext a c
  simp

/-- **Lemma 1 (1), rational form.**  Let `χ_M` be irreducible over `ℚ` and `ℓ ≠ 0` a real left
eigen-row, `ℓ M = β ℓ`.  If `w ∈ ℚ^α` and `ℓ·w = 0`, then `w = 0`. -/
theorem eq_zero_of_dot_eq_zero (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {w : α → ℚ}
    (hw : ∑ a, ℓ a * (w a : ℝ) = 0) : w = 0 := by
  by_contra hw0
  refine hℓ0 (eigenrow_eq_zero_of_irreducible _ hirr (K := ℝ) (β := β) ?_ hw0 ?_)
  · rw [incQ_map_real]
    exact hℓM
  · simpa [dotProduct] using hw

/-- **Lemma 1 (1), integer form**: `ℓ·v = 0 ⟺ v = 0` for `v ∈ ℤ^α`. -/
theorem lenHom_eq_zero_iff (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {v : α → ℤ} :
    lenHom ℓ v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have h := eq_zero_of_dot_eq_zero s hirr hℓ0 hℓM (w := fun a => (v a : ℚ))
      (by simpa [lenHom_apply] using hv)
    funext a
    have ha := congrFun h a
    simpa using ha
  · rintro rfl
    exact map_zero _

/-- **Lemma 1 (1)** in the form of the hypothesis `hzero` of
`Psc.GeometricF.propertyF_reverse_iff` and `Psc.GeometricF.fc2_rank_transfer`. -/
theorem lenHom_zero_kernel (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ∀ v : α → ℤ, lenHom ℓ v = 0 → v = 0 :=
  fun _ => (lenHom_eq_zero_iff s hirr hℓ0 hℓM).1

/-- The length functional is injective on `ℤ^α`: a state is a letter together with a
position in the module `ℓ·ℤ^α`. -/
theorem lenHom_injective (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    Function.Injective (lenHom ℓ) := fun v w h =>
  sub_eq_zero.1 ((lenHom_eq_zero_iff s hirr hℓ0 hℓM).1 (by rw [map_sub, h, sub_self]))

/-- **Lemma 1 (1)** for a positive left eigen-row (the Perron row). -/
theorem lenHom_zero_kernel_of_pos (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ∀ v : α → ℤ, lenHom ℓ v = 0 → v = 0 := by
  have := Psc.GeometricFPisot.nonempty_of_irreducible s hirr
  exact lenHom_zero_kernel s hirr (fun h => (hℓ (Classical.arbitrary α)).ne' (congrFun h _)) hℓM

end Lemma1

/-! ### Lemma 1 (3): no eigenvalue `0` or root of unity; `M^k − I` is invertible -/

section Lemma13

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **Lemma 1 (3), spectral form.**  If `χ_M` is irreducible over `ℚ` and has a complex root of
modulus `> 1`, then every complex eigenvalue `z` of `M` has `z ≠ 0` and `z^k ≠ 1` for
`k ≥ 1`. -/
theorem eigenvalue_ne_zero_and_pow_ne_one (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {r : ℂ}
    (hr : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval r = 0) (hr1 : 1 < ‖r‖) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) :
    z ≠ 0 ∧ ∀ k : ℕ, 1 ≤ k → z ^ k ≠ 1 :=
  root_ne_zero_and_pow_ne_one hirr (charpoly_monic _)
    (by rw [Psc.BPrime.aeval_charpoly]; exact hr) hr1
    (by rw [Psc.BPrime.aeval_charpoly]; exact hz)

/-- **Lemma 1 (3), `M^k − I` is invertible over `ℚ`.**  It suffices that `χ_M` is irreducible
and has a root `r`, in any field over `ℚ`, with `r^k ≠ 1` (on the standing class: the Perron
root `β > 1`, `isUnit_incQ_pow_sub_one_of_left_eigen`). -/
theorem isUnit_incQ_pow_sub_one (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {K : Type*} [Field K]
    [Algebra ℚ K] {r : K} (hr : aeval r ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) {k : ℕ}
    (hrk : r ^ k ≠ 1) : IsUnit (((inc s).map (Nat.cast : ℕ → ℚ)) ^ k - 1) := by
  have h := isUnit_aeval_of_root _ hirr hr (q := X ^ k - 1) (by simpa [sub_eq_zero] using hrk)
  simpa using h

/-- **Lemma 1 (3), `M` is invertible over `ℚ`** (no eigenvalue `0`), given a nonzero root. -/
theorem isUnit_incQ (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {K : Type*} [Field K]
    [Algebra ℚ K] {r : K} (hr : aeval r ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0)
    (hr0 : r ≠ 0) : IsUnit ((inc s).map (Nat.cast : ℕ → ℚ)) := by
  have h := isUnit_aeval_of_root _ hirr hr (q := X) (by simpa using hr0)
  simpa using h

/-- The integer matrix `M^k − I`, read over `ℚ`. -/
theorem map_incZ_pow_sub_one (s : α → List α) (k : ℕ) :
    (incZ s ^ k - 1).map (Int.castRingHom ℚ) = ((inc s).map (Nat.cast : ℕ → ℚ)) ^ k - 1 := by
  have h := map_sub (Int.castRingHom ℚ).mapMatrix (incZ s ^ k) 1
  rw [map_pow, map_one] at h
  simp only [RingHom.mapMatrix_apply] at h
  rw [h]
  congr 2

/-- **Lemma 1 (3), integer form**: `v ↦ (M^k − I) v` is injective on `ℤ^α`, so the vector `v` of
an interior periodic address is determined by `p(P)`. -/
theorem mulVec_pow_sub_one_injective (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {K : Type*} [Field K]
    [Algebra ℚ K] {r : K} (hr : aeval r ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) {k : ℕ}
    (hrk : r ^ k ≠ 1) : Function.Injective fun v : α → ℤ => (incZ s ^ k - 1) *ᵥ v := by
  intro v v' h
  have hU := isUnit_incQ_pow_sub_one s hirr hr hrk
  have e : ∀ u : α → ℤ, (Int.castRingHom ℚ) ∘ ((incZ s ^ k - 1) *ᵥ u) =
      (((inc s).map (Nat.cast : ℕ → ℚ)) ^ k - 1) *ᵥ ((Int.castRingHom ℚ) ∘ u) := by
    intro u
    funext a
    rw [Function.comp_apply, RingHom.map_mulVec, map_incZ_pow_sub_one]
  have h1 : (((inc s).map (Nat.cast : ℕ → ℚ)) ^ k - 1) *ᵥ ((Int.castRingHom ℚ) ∘ v) =
      (((inc s).map (Nat.cast : ℕ → ℚ)) ^ k - 1) *ᵥ ((Int.castRingHom ℚ) ∘ v') := by
    rw [← e, ← e]
    exact congrArg _ h
  have h2 := Matrix.mulVec_injective_iff_isUnit.2 hU h1
  funext a
  have h3 := congrFun h2 a
  simpa using h3

/-- The Perron root is a root of `χ_M`, over `ℝ`. -/
theorem aeval_perron (s : α → List α) {β : ℝ} {ℓ : α → ℝ} (hℓ0 : ℓ ≠ 0)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 := by
  rw [Psc.BPrime.aeval_charpoly]
  exact Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ β ℓ hℓ0 hℓM

/-- The Perron root is a root of `χ_M`, over `ℂ`. -/
theorem eval_perron_complex (s : α → List α) {β : ℝ} {ℓ : α → ℝ} (hℓ0 : ℓ ≠ 0)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval (β : ℂ) = 0 := by
  have hc : ((inc s).map (Nat.cast : ℕ → ℝ)).map ((↑) : ℝ → ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by
    ext; simp
  rw [← hc]
  exact Psc.PerronExistence.isRoot_ofReal_of_left_eigen _ ℓ hℓ0 β hℓM

/-- **Lemma 1 (3) on the standing class**: (I), a nonzero real left eigen-row for `β > 1`; then
`M^k − I` is invertible over `ℚ` for `k ≥ 1`, and so is `M`. -/
theorem isUnit_incQ_pow_sub_one_of_left_eigen (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 1 < β) :
    (∀ k : ℕ, 1 ≤ k → IsUnit (((inc s).map (Nat.cast : ℕ → ℚ)) ^ k - 1)) ∧
      IsUnit ((inc s).map (Nat.cast : ℕ → ℚ)) :=
  ⟨fun k hk => isUnit_incQ_pow_sub_one s hirr (aeval_perron s hℓ0 hℓM)
      (one_lt_pow₀ hβ (by omega)).ne',
    isUnit_incQ s hirr (aeval_perron s hℓ0 hℓM) (by linarith)⟩

/-- **Lemma 1 (3) on the standing class, integer form.** -/
theorem mulVec_pow_sub_one_injective_of_left_eigen (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 1 < β) {k : ℕ}
    (hk : 1 ≤ k) : Function.Injective fun v : α → ℤ => (incZ s ^ k - 1) *ᵥ v :=
  mulVec_pow_sub_one_injective s hirr (aeval_perron s hℓ0 hℓM) (one_lt_pow₀ hβ (by omega)).ne'

/-- **Lemma 1 (3) on the standing class, spectral form**: with the Perron root `β > 1` as the
root of modulus `> 1`. -/
theorem eigenvalue_ne_zero_and_pow_ne_one_of_left_eigen (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 1 < β) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) :
    z ≠ 0 ∧ ∀ k : ℕ, 1 ≤ k → z ^ k ≠ 1 :=
  eigenvalue_ne_zero_and_pow_ne_one s hirr (eval_perron_complex s hℓ0 hℓM)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hβ) hz

end Lemma13

/-! ### Lemma 4 (2): (F) for `σ` iff for `σ^m` -/

section Power

variable {α : Type*} [DecidableEq α] [Fintype α] {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

/-- `(f_{σ^m})^k = f^{mk}` on states, one direction (Lemma 2, `Psc.GeometricF.power_to_stepN`). -/
theorem stepN_power_to_stepN (hL : LengthData s L β) {m : ℕ} {x : α × (α → ℤ)}
    (hx : IsState L x) :
    ∀ (k : ℕ) {y : α × (α → ℤ)}, StepN (power s m) L k x y → StepN s L (m * k) x y
  | 0, _, h => by rw [Nat.mul_zero]; exact h
  | k + 1, _, ⟨z, hz, hzy⟩ => by
    rw [Nat.mul_succ]
    exact stepN_add (stepN_power_to_stepN hL hx k hz) m
      (power_to_stepN hL (stepN_isState hx k hz) hzy)

/-- `f^{mk} = (f_{σ^m})^k` on states, the other direction (`Psc.GeometricF.stepN_to_power`). -/
theorem stepN_to_stepN_power {m : ℕ} {x : α × (α → ℤ)} (hx : IsState L x) :
    ∀ (k : ℕ) {y : α × (α → ℤ)}, StepN s L (m * k) x y → StepN (power s m) L k x y
  | 0, _, h => by rw [Nat.mul_zero] at h; exact h
  | k + 1, _, h => by
    rw [Nat.mul_succ] at h
    obtain ⟨z, hz, hzy⟩ := stepN_split m h
    exact ⟨z, stepN_to_stepN_power hx k hz, stepN_to_power (stepN_isState hx _ hz) m hzy⟩

/-- A state of period `k` has period `kj` for every `j`. -/
theorem stepN_mul_self {k : ℕ} {x : α × (α → ℤ)} (h : StepN s L k x x) :
    ∀ j : ℕ, StepN s L (k * j) x x
  | 0 => rfl
  | j + 1 => by
    rw [Nat.mul_succ]
    exact stepN_add (stepN_mul_self h j) k h

/-- **Lemma 4 (2).**  For length data `L` of `σ` (which are length data of `σ^m`, eigenvalue
`β^m`: `Psc.GeometricF.LengthData.power`) and `m ≥ 1`, (F) holds for `σ^m` iff it holds for
`σ`: `f_{σ^m} = f^m` has the same periodic states as `f`.  `m ≥ 1` is needed: for `m = 0`
every state is fixed. -/
theorem propertyF_power_iff (hL : LengthData s L β) {m : ℕ} (hm : 1 ≤ m) :
    PropertyF (power s m) L ↔ PropertyF s L := by
  constructor
  · intro hF x hx k hk hper
    have h1 : StepN s L (m * k) x x := by
      rw [Nat.mul_comm]
      exact stepN_mul_self hper m
    exact hF x hx k hk (stepN_to_stepN_power hx k h1)
  · intro hF x hx k hk hper
    exact hF x hx (m * k) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
      (stepN_power_to_stepN hL hx k hper)

/-- **Why `m ≥ 1`**: `f_{σ⁰}` fixes every state, so (F) for `σ⁰` says that every state is a
vertex state. -/
theorem propertyF_power_zero_iff :
    PropertyF (power s 0) L ↔ ∀ x : α × (α → ℤ), IsState L x → x.2 = 0 := by
  constructor
  · intro hF x hx
    have hstep : Step (power s 0) L x x := by
      refine ⟨[], [], rfl, ?_, hx⟩
      rw [incZ_power, pow_zero, Matrix.one_mulVec, pvec_nil, sub_zero]
    exact hF x hx 1 le_rfl ⟨x, rfl, hstep⟩
  · intro h x hx _ _ _
    exact h x hx

/-- **Lemma 4 (2), with the length data passed to the power**: `L` is length data of `σ^m`
with eigenvalue `β^m`, and (F) for `σ^m` is (F) for `σ`. -/
theorem lengthData_power_and_propertyF_iff (hL : LengthData s L β) {m : ℕ} (hm : 1 ≤ m) :
    LengthData (power s m) L (β ^ m) ∧ (PropertyF (power s m) L ↔ PropertyF s L) :=
  ⟨hL.power m, propertyF_power_iff hL hm⟩

/-- **Lemma 4 (2)** for the length functional of a positive left eigen-row. -/
theorem propertyF_power_iff_of_left_eigen {ℓ : α → ℝ} (hβ : 0 < β) (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {m : ℕ} (hm : 1 ≤ m) :
    PropertyF (power s m) (lenHom ℓ) ↔ PropertyF s (lenHom ℓ) :=
  propertyF_power_iff (lengthData_of_left_eigen hβ hℓ hℓM) hm

end Power

/-! ### Lemma 4 (3): (F) for `σ` iff for `σ^R`, the correspondence of states -/

section Reverse

variable {α : Type*} [DecidableEq α] [Fintype α] {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

omit [Fintype α] in
/-- The reflection `(j, v) ↦ (j, e_j − v)` is an involution. -/
theorem reflectState_reflectState (x : α × (α → ℤ)) : reflectState (reflectState x) = x := by
  apply Prod.ext
  · rfl
  · show pvec [x.1] - (pvec [x.1] - x.2) = x.2
    abel

omit [Fintype α] in
theorem L_reflectState (x : α × (α → ℤ)) :
    L (reflectState x).2 = L (pvec [x.1]) - L x.2 :=
  map_sub L _ _

omit [Fintype α] in
/-- **The states of Lemma 4 (3).**  Under `hzero` (Lemma 1 (1)), a state `(j, v)` with `v ≠ 0`
has `0 < ℓ·v < ℓ_j`, so its reflection `(j, e_j − v)` is again a state with nonzero vector. -/
theorem isState_reflectState (hzero : ∀ v, L v = 0 → v = 0) {x : α × (α → ℤ)}
    (hx : IsState L x) (hx0 : x.2 ≠ 0) :
    IsState L (reflectState x) ∧ (reflectState x).2 ≠ 0 := by
  have hpos : 0 < L x.2 := lt_of_le_of_ne hx.1 (fun h => hx0 (hzero _ h.symm))
  have hlen := L_reflectState (L := L) x
  have hpos' : 0 < L (reflectState x).2 := by
    rw [hlen]
    exact sub_pos.mpr hx.2
  refine ⟨⟨hpos'.le, ?_⟩, fun h => ?_⟩
  · show L (reflectState x).2 < L (pvec [x.1])
    rw [hlen]
    exact sub_lt_self _ hpos
  · rw [h, map_zero] at hpos'
    exact lt_irrefl _ hpos'

/-- **Lemma 4 (3), the exact correspondence of orbits.**  For states `x`, `y` whose
reflections are states, `f_{σ^R}^k(x) = y` iff `f_σ^k(x̄) = ȳ`, `x̄ = reflectState x`.  The
reversal has the same incidence matrix (`Psc.GeometricF.incZ_reverseSubstitution`); the proof
reflects the integer edges (`Psc.GeometricF.edgeDescendant_reflect`). -/
theorem stepN_reverse_iff (hL : LengthData s L β) {k : ℕ} {x y : α × (α → ℤ)}
    (hx : IsState L x) (hy : IsState L y) (hx' : IsState L (reflectState x))
    (hy' : IsState L (reflectState y)) :
    StepN (reverseSubstitution s) L k x y ↔ StepN s L k (reflectState x) (reflectState y) := by
  constructor
  · intro h
    have he :=
      edgeDescendant_reflect ((stepN_iff_edgeDescendant hL.reverseSubstitution hx hy).mp h)
    rw [reverseSubstitution_reverse, ← edgeOfState_reflectState,
      ← edgeOfState_reflectState] at he
    exact (stepN_iff_edgeDescendant hL hx' hy').mpr he
  · intro h
    have he := (stepN_iff_edgeDescendant hL hx' hy').mp h
    rw [edgeOfState_reflectState, edgeOfState_reflectState] at he
    have he' := edgeDescendant_reflect he
    rw [reflectEdge_reflectEdge, reflectEdge_reflectEdge] at he'
    exact (stepN_iff_edgeDescendant hL.reverseSubstitution hx hy).mpr he'

/-- **Lemma 4 (3), periodic states.**  Under `hzero`, a state `x` with `x.2 ≠ 0` has period `k`
for `σ^R` iff its reflection has period `k` for `σ`. -/
theorem periodic_reverse_iff (hL : LengthData s L β) (hzero : ∀ v, L v = 0 → v = 0) {k : ℕ}
    {x : α × (α → ℤ)} (hx : IsState L x) (hx0 : x.2 ≠ 0) :
    StepN (reverseSubstitution s) L k x x ↔ StepN s L k (reflectState x) (reflectState x) :=
  stepN_reverse_iff hL hx hx (isState_reflectState hzero hx hx0).1
    (isState_reflectState hzero hx hx0).1

/-- **Lemma 4 (3) on the standing class.**  (I), a positive left eigen-row `ℓ M = β ℓ`,
`β > 0`: (F) holds for `σ^R` iff it holds for `σ`.  This is
`Psc.GeometricF.propertyF_reverse_iff` with its hypothesis `hzero` discharged by Lemma 1 (1). -/
theorem propertyF_reverse_iff_of_irreducible (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {ℓ : α → ℝ} (hβ : 0 < β)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    PropertyF (reverseSubstitution s) (lenHom ℓ) ↔ PropertyF s (lenHom ℓ) :=
  propertyF_reverse_iff (lengthData_of_left_eigen hβ hℓ hℓM)
    (lenHom_zero_kernel_of_pos s hirr hℓ hℓM)

/-- **`Psc.GeometricF.fc2_rank_transfer` on the standing class**: its hypothesis `hzero` is
Lemma 1 (1) (`lenHom_zero_kernel_of_pos`); the other hypotheses are unchanged. -/
theorem fc2_rank_transfer_of_irreducible (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {ℓ : α → ℝ} (hβ : 0 < β)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    {ν : (α → ℤ) → ℝ} {ρ : ℝ} {rank : ℕ} (hC : ContractionData s (lenHom ℓ) ν ρ)
    (hF : PropertyF s (lenHom ℓ)) (hRank : IsMaximumSize (StateFamily s (lenHom ℓ)) rank)
    (hRankRev : IsMaximumSize (StateFamily (reverseSubstitution s) (lenHom ℓ)) rank) :
    IsMaximumSize (LetterFamily (VertexCoincident s)) rank ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness s)) rank :=
  fc2_rank_transfer (lengthData_of_left_eigen hβ hℓ hℓM) hC
    (lenHom_zero_kernel_of_pos s hirr hℓ hℓM) hF hRank hRankRev

end Reverse

/-! ### Lemma 4 (1): interior periodic addresses -/

section Address

variable {α : Type*} [DecidableEq α] [Fintype α] {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

/-- An **interior periodic address** (note, Lemma 4 (1)): a factorisation `σ^k(e) = P e Q` with
`P` and `Q` nonempty, and an integer vector `v` with `(M^k − I) v = p(P)` (the integrality of
`(M^k − I)^{-1} p(P)`; `v` is unique by Lemma 1 (3), `isInteriorAddress_unique`). -/
def IsInteriorAddress (s : α → List α) (k : ℕ) (e : α) (P Q : List α) (v : α → ℤ) : Prop :=
  power s k e = P ++ e :: Q ∧ P ≠ [] ∧ Q ≠ [] ∧ (incZ s ^ k - 1) *ᵥ v = pvec P

/-- `ℓ·p(σ^k(e)) = β^k ℓ_e`. -/
theorem L_pvec_power (hL : LengthData s L β) (k : ℕ) (e : α) :
    L (pvec (power s k e)) = β ^ k * L (pvec [e]) := by
  rw [show power s k e = (subst s)^[k] [e] from rfl, pvec_iterate, hL.eigen_pow]

/-- `ℓ·(M^k − I) v = (β^k − 1) ℓ·v`. -/
theorem L_pow_sub_one_mulVec (hL : LengthData s L β) (k : ℕ) (v : α → ℤ) :
    L ((incZ s ^ k - 1) *ᵥ v) = (β ^ k - 1) * L v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, hL.eigen_pow]
  ring

/-- An interior address has `k ≥ 1` (`σ⁰(e) = e` has no nonempty prefix before `e`). -/
theorem one_le_of_isInteriorAddress {k : ℕ} {e : α} {P Q : List α} {v : α → ℤ}
    (h : IsInteriorAddress s k e P Q v) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    have h1 := h.1
    have h2 : power s 0 e = [e] := rfl
    rw [h2] at h1
    have hlen := congrArg List.length h1
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    exact h.2.1 (List.eq_nil_of_length_eq_zero (by omega))
  · exact hk

/-- **Lemma 4 (1), the note's first sentence.**  For length data and a state `(j, v)`:
`f^k(j, v) = (j, v)` iff `σ^k(j) = P j Q` for some factorisation with `(M^k − I) v = p(P)`.
Given such a factorisation, `M^k v − p(P) = v` has `ℓ`-value in `[0, ℓ_j)`, so it is the
factorisation used by `f^k` (Lemma 2).  Nonemptiness of `P` and `Q` is
`nonempty_of_factorisation`. -/
theorem periodic_iff_factorisation (hL : LengthData s L β) {k : ℕ} {j : α} {v : α → ℤ}
    (hx : IsState L (j, v)) :
    StepN s L k (j, v) (j, v) ↔
      ∃ P Q, power s k j = P ++ j :: Q ∧ (incZ s ^ k - 1) *ᵥ v = pvec P := by
  constructor
  · intro hper
    obtain ⟨P, Q, hw, hvP, -⟩ := stepN_to_power hx k hper
    change v = incZ (power s k) *ᵥ v - pvec P at hvP
    rw [incZ_power] at hvP
    refine ⟨P, Q, hw, ?_⟩
    have h := congrArg (fun u => incZ s ^ k *ᵥ v - u) hvP
    simp only [sub_sub_cancel] at h
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact h
  · rintro ⟨P, Q, hw, hPv⟩
    refine power_to_stepN hL hx ⟨P, Q, hw, ?_, hx⟩
    change v = incZ (power s k) *ᵥ v - pvec P
    rw [incZ_power, ← hPv, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel]

/-- **Lemma 4 (1), "then `P` and `Q` are nonempty".**  Length data with `β > 1`, `hzero`,
`k ≥ 1`, a state `(j, v)` with `v ≠ 0` and a factorisation `σ^k(j) = P j Q` with
`(M^k − I) v = p(P)`: `ℓ·p(P) = (β^k − 1) ℓ·v > 0` and `ℓ·p(Q) = (β^k − 1)(ℓ_j − ℓ·v) > 0`. -/
theorem nonempty_of_factorisation (hL : LengthData s L β) (hβ : 1 < β)
    (hzero : ∀ v, L v = 0 → v = 0) {k : ℕ} (hk : 1 ≤ k) {j : α} {v : α → ℤ}
    (hx : IsState L (j, v)) (hv : v ≠ 0) {P Q : List α} (hw : power s k j = P ++ j :: Q)
    (hPv : (incZ s ^ k - 1) *ᵥ v = pvec P) : P ≠ [] ∧ Q ≠ [] := by
  have hβk : 1 < β ^ k := one_lt_pow₀ hβ (by omega)
  have hLv : 0 < L v := lt_of_le_of_ne hx.1 (fun h => hv (hzero v h.symm))
  have hxj : L v < L (pvec [j]) := hx.2
  have hLP : L (pvec P) = (β ^ k - 1) * L v := by rw [← hPv, L_pow_sub_one_mulVec hL]
  have hLw := L_pvec_power hL k j
  rw [hw, pvec_append, pvec_cons, map_add, map_add] at hLw
  have hprod := mul_pos (sub_pos.2 hβk) hLv
  have hprod' := mul_pos (sub_pos.2 hβk) (sub_pos.2 hxj)
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [pvec_nil, map_zero] at hLP
    linarith
  · rintro rfl
    rw [pvec_nil, map_zero] at hLw
    nlinarith

/-- **Lemma 4 (1), forward.**  Let `L` be length data with `β > 1` and trivial kernel on `ℤ^α`
(Lemma 1 (1)), and `k ≥ 1`.  If `(j, v)` is a state with `v ≠ 0` and `f^k(j, v) = (j, v)`, then
`σ^k(j) = P j Q` with `(M^k − I) v = p(P)` and `P`, `Q` nonempty: `ℓ·p(P) = (β^k − 1) ℓ·v > 0`
and `ℓ·p(Q) = (β^k − 1)(ℓ_j − ℓ·v) > 0`. -/
theorem isInteriorAddress_of_periodic (hL : LengthData s L β) (hβ : 1 < β)
    (hzero : ∀ v, L v = 0 → v = 0) {k : ℕ} (hk : 1 ≤ k) {j : α} {v : α → ℤ}
    (hx : IsState L (j, v)) (hv : v ≠ 0) (hper : StepN s L k (j, v) (j, v)) :
    ∃ P Q, IsInteriorAddress s k j P Q v := by
  obtain ⟨P, Q, hw, hPv⟩ := (periodic_iff_factorisation hL hx).1 hper
  obtain ⟨hP, hQ⟩ := nonempty_of_factorisation hL hβ hzero hk hx hv hw hPv
  exact ⟨P, Q, hw, hP, hQ, hPv⟩

/-- **Lemma 4 (1), converse.**  For length data with `β > 1` (no `hzero`), an interior address
`σ^k(e) = P e Q`, `(M^k − I) v = p(P)`, gives `k ≥ 1`, a state `(e, v)` with `v ≠ 0`, and
`f^k(e, v) = (e, v)`: `ℓ·v = ℓ·p(P)/(β^k − 1) ∈ (0, ℓ_e)` because `P` and `Q` are nonempty. -/
theorem periodic_of_isInteriorAddress (hL : LengthData s L β) (hβ : 1 < β) {k : ℕ} {e : α}
    {P Q : List α} {v : α → ℤ} (h : IsInteriorAddress s k e P Q v) :
    1 ≤ k ∧ IsState L (e, v) ∧ v ≠ 0 ∧ StepN s L k (e, v) (e, v) := by
  have hk := one_le_of_isInteriorAddress h
  obtain ⟨hw, hP, hQ, hPv⟩ := h
  have hβk : 1 < β ^ k := one_lt_pow₀ hβ (by omega)
  have hLP : L (pvec P) = (β ^ k - 1) * L v := by rw [← hPv, L_pow_sub_one_mulVec hL]
  have hLw := L_pvec_power hL k e
  rw [hw, pvec_append, pvec_cons, map_add, map_add] at hLw
  have hP0 := L_pvec_pos hL.pos hP
  have hQ0 := L_pvec_pos hL.pos hQ
  have hb := sub_pos.2 hβk
  have hLv : 0 < L v := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hb.le hneg]
  have hLe : L v < L (pvec [e]) := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hb.le (sub_nonpos.2 hneg)]
  have hx : IsState L (e, v) := ⟨hLv.le, hLe⟩
  refine ⟨hk, hx, ?_, power_to_stepN hL hx ⟨P, Q, hw, ?_, hx⟩⟩
  · rintro rfl
    rw [Matrix.mulVec_zero] at hPv
    rw [← hPv, map_zero] at hP0
    exact lt_irrefl _ hP0
  · change v = incZ (power s k) *ᵥ v - pvec P
    rw [incZ_power, ← hPv, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel]

/-- **Lemma 4 (1).**  Under length data with `β > 1` and `hzero`, for `k ≥ 1`: `(j, v)` is a state
with `v ≠ 0` and `f^k(j, v) = (j, v)` iff `σ^k(j) = P j Q` with `(M^k − I) v = p(P)` and `P`,
`Q` nonempty. -/
theorem periodic_iff_isInteriorAddress (hL : LengthData s L β) (hβ : 1 < β)
    (hzero : ∀ v, L v = 0 → v = 0) {k : ℕ} (hk : 1 ≤ k) {j : α} {v : α → ℤ} :
    (IsState L (j, v) ∧ v ≠ 0 ∧ StepN s L k (j, v) (j, v)) ↔
      ∃ P Q, IsInteriorAddress s k j P Q v :=
  ⟨fun ⟨hx, hv, hper⟩ => isInteriorAddress_of_periodic hL hβ hzero hk hx hv hper,
    fun ⟨_, _, h⟩ => (periodic_of_isInteriorAddress hL hβ h).2⟩

/-- **Lemma 4 (1): (F) says there is no interior periodic address.** -/
theorem propertyF_iff_no_interiorAddress (hL : LengthData s L β) (hβ : 1 < β)
    (hzero : ∀ v, L v = 0 → v = 0) :
    PropertyF s L ↔ ∀ k e P Q v, ¬ IsInteriorAddress s k e P Q v := by
  constructor
  · intro hF k e P Q v h
    obtain ⟨hk, hx, hv, hper⟩ := periodic_of_isInteriorAddress hL hβ h
    exact hv (hF _ hx k hk hper)
  · intro hno x hx k hk hper
    by_contra hv
    obtain ⟨P, Q, h⟩ :=
      isInteriorAddress_of_periodic hL hβ hzero hk (j := x.1) (v := x.2) hx hv hper
    exact hno k x.1 P Q x.2 h

/-- **Uniqueness** (Lemma 1 (3)): on the standing class an interior address is determined by
`(k, e, P)`. -/
theorem isInteriorAddress_unique
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {ℓ : α → ℝ} (hℓ0 : ℓ ≠ 0)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 1 < β) {k : ℕ} {e : α}
    {P Q Q' : List α} {v v' : α → ℤ} (h : IsInteriorAddress s k e P Q v)
    (h' : IsInteriorAddress s k e P Q' v') : Q = Q' ∧ v = v' := by
  have hQ := List.append_cancel_left (h.1.symm.trans h'.1)
  refine ⟨(List.cons.inj hQ).2, ?_⟩
  exact mulVec_pow_sub_one_injective_of_left_eigen s hirr hℓ0 hℓM hβ
    (one_le_of_isInteriorAddress h) (h.2.2.2.trans h'.2.2.2.symm)

/-- **Lemma 4 (1) on the standing class**: (I), a positive left eigen-row for `β > 1`; (F) holds
iff there is no interior periodic address. -/
theorem propertyF_iff_no_interiorAddress_of_irreducible (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {ℓ : α → ℝ} (hβ : 1 < β)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    PropertyF s (lenHom ℓ) ↔ ∀ k e P Q v, ¬ IsInteriorAddress s k e P Q v :=
  propertyF_iff_no_interiorAddress (lengthData_of_left_eigen (by linarith) hℓ hℓM) hβ
    (lenHom_zero_kernel_of_pos s hirr hℓ hℓM)

/-! #### Lemma 4 (3), the note's proof: interior addresses of `σ` and `σ^R` correspond -/

/-- **The correspondence of addresses**: `σ^k(e) = P e Q`, `(M^k − I) v = p(P)` gives
`(σ^R)^k(e) = Q^R e P^R` and `(M^k − I)(e_e − v) = p(Q) = p(Q^R)`, the same incidence matrix. -/
theorem isInteriorAddress_reverse {k : ℕ} {e : α} {P Q : List α} {v : α → ℤ}
    (h : IsInteriorAddress s k e P Q v) :
    IsInteriorAddress (reverseSubstitution s) k e Q.reverse P.reverse (pvec [e] - v) := by
  obtain ⟨hw, hP, hQ, hPv⟩ := h
  refine ⟨?_, by simpa using hQ, by simpa using hP, ?_⟩
  · rw [power_reverseSubstitution, hw]
    simp
  · have hpow : incZ s ^ k *ᵥ pvec [e] = pvec P + pvec [e] + pvec Q := by
      rw [← pvec_iterate, show (subst s)^[k] [e] = power s k e from rfl, hw, pvec_append,
        pvec_cons]
      abel
    rw [incZ_reverseSubstitution, pvec_reverse, Matrix.mulVec_sub, hPv, Matrix.sub_mulVec,
      Matrix.one_mulVec, hpow]
    abel

/-- The correspondence of addresses is an involution. -/
theorem isInteriorAddress_reverse_iff {k : ℕ} {e : α} {P Q : List α} {v : α → ℤ} :
    IsInteriorAddress (reverseSubstitution s) k e Q.reverse P.reverse (pvec [e] - v) ↔
      IsInteriorAddress s k e P Q v := by
  refine ⟨fun h => ?_, isInteriorAddress_reverse⟩
  have h' := isInteriorAddress_reverse h
  rw [reverseSubstitution_reverse, List.reverse_reverse, List.reverse_reverse,
    sub_sub_cancel] at h'
  exact h'

/-- `σ` has an interior periodic address iff `σ^R` has one. -/
theorem noInteriorAddress_reverse_iff :
    (∀ k e P Q v, ¬ IsInteriorAddress (reverseSubstitution s) k e P Q v) ↔
      ∀ k e P Q v, ¬ IsInteriorAddress s k e P Q v := by
  constructor
  · intro h k e P Q v hA
    exact h _ _ _ _ _ (isInteriorAddress_reverse hA)
  · intro h k e P Q v hA
    have h' := isInteriorAddress_reverse hA
    rw [reverseSubstitution_reverse] at h'
    exact h _ _ _ _ _ h'

/-- **Lemma 4 (3), the note's route** through Lemma 4 (1) (`β > 1`, `hzero`); a cross-check of
`Psc.GeometricF.propertyF_reverse_iff`, which needs no `β > 1`. -/
theorem propertyF_reverse_iff_of_addresses (hL : LengthData s L β) (hβ : 1 < β)
    (hzero : ∀ v, L v = 0 → v = 0) :
    PropertyF (reverseSubstitution s) L ↔ PropertyF s L := by
  rw [propertyF_iff_no_interiorAddress hL.reverseSubstitution hβ hzero,
    propertyF_iff_no_interiorAddress hL hβ hzero]
  exact noInteriorAddress_reverse_iff

end Address

/-! ### Non-vacuity: Tribonacci -/

section Tribonacci

open Psc.Descendants (tribSubst)

/-- **Lemma 1 (1) and (3) hold for Tribonacci** `0 ↦ 01, 1 ↦ 02, 2 ↦ 0` (PIP3, `χ_M` irreducible:
`Psc.BPrime.trib_irreducible`), for every positive left eigen-row `ℓ`: `ℓ·v = 0` only for
`v = 0`; `M^k − I` (`k ≥ 1`) and `M` are invertible over `ℚ`; no complex eigenvalue is `0` or a
root of unity. -/
theorem trib_lemma1 {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    (∀ v : Fin 3 → ℤ, lenHom ℓ v = 0 → v = 0) ∧
      (∀ k : ℕ, 1 ≤ k → IsUnit (((inc tribSubst).map (Nat.cast : ℕ → ℚ)) ^ k - 1)) ∧
      IsUnit ((inc tribSubst).map (Nat.cast : ℕ → ℚ)) ∧
      ∀ z : ℂ, ((inc tribSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 →
        z ≠ 0 ∧ ∀ k : ℕ, 1 ≤ k → z ^ k ≠ 1 := by
  have hβ : 1 < β := Psc.BPrimeCore.one_lt_perron tribSubst Psc.BPrime.trib_prim hℓ hℓM
  have hℓ0 : ℓ ≠ 0 := fun h => (hℓ 0).ne' (congrFun h 0)
  obtain ⟨h1, h2⟩ :=
    isUnit_incQ_pow_sub_one_of_left_eigen tribSubst Psc.BPrime.trib_irreducible hℓ0 hℓM hβ
  exact ⟨lenHom_zero_kernel_of_pos tribSubst Psc.BPrime.trib_irreducible hℓ hℓM, h1, h2,
    fun z hz => eigenvalue_ne_zero_and_pow_ne_one_of_left_eigen tribSubst
      Psc.BPrime.trib_irreducible hℓ0 hℓM hβ hz⟩

/-- **Lemma 4 (2) on Tribonacci**: (F) holds for every power `σ^m`, `m ≥ 1`
(`Psc.GeometricFTriple.trib_propertyF`). -/
theorem trib_propertyF_power {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) {m : ℕ} (hm : 1 ≤ m) :
    PropertyF (power tribSubst m) (lenHom ℓ) := by
  have hβ : 1 < β := Psc.BPrimeCore.one_lt_perron tribSubst Psc.BPrime.trib_prim hℓ hℓM
  exact (propertyF_power_iff_of_left_eigen (by linarith) hℓ hℓM hm).2
    (Psc.GeometricFTriple.trib_propertyF hℓ hℓM)

/-- **Lemma 4 (3) on Tribonacci**: (F) holds for the reversal `10/20/0`. -/
theorem trib_propertyF_reverse {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    PropertyF (reverseSubstitution tribSubst) (lenHom ℓ) := by
  have hβ : 1 < β := Psc.BPrimeCore.one_lt_perron tribSubst Psc.BPrime.trib_prim hℓ hℓM
  exact (propertyF_reverse_iff_of_irreducible tribSubst Psc.BPrime.trib_irreducible
    (by linarith) hℓ hℓM).2 (Psc.GeometricFTriple.trib_propertyF hℓ hℓM)

/-- **Lemma 4 (1) on Tribonacci**: no interior periodic address. -/
theorem trib_no_interiorAddress (k : ℕ) (e : Fin 3) (P Q : List (Fin 3)) (v : Fin 3 → ℤ) :
    ¬ IsInteriorAddress tribSubst k e P Q v := by
  obtain ⟨β, -, ℓ, hℓ, hℓM⟩ :=
    Psc.PerronExistence.exists_pos_left_eigen_inc tribSubst Psc.BPrime.trib_prim
  have hβ : 1 < β := Psc.BPrimeCore.one_lt_perron tribSubst Psc.BPrime.trib_prim hℓ hℓM
  exact (propertyF_iff_no_interiorAddress_of_irreducible tribSubst Psc.BPrime.trib_irreducible
    hβ hℓ hℓM).1 (Psc.GeometricFTriple.trib_propertyF hℓ hℓM) k e P Q v

end Tribonacci

/-! ### Negative controls -/

section Controls

open Psc.GeometricFTriple (ctrlSubst ctrl_prim)
open Psc.StrictSystem (carrierSubst carrier_primitive)

/-- **`01/12/021` has an interior periodic address**: `σ(2) = 0·2·1` and
`(M − I)(−1, 0, 1) = e₀ = p(0)`; decided on words and integer vectors. -/
theorem ctrl_isInteriorAddress : IsInteriorAddress ctrlSubst 1 2 [0] [1] ![-1, 0, 1] := by
  refine ⟨by decide, by simp, by simp, ?_⟩
  rw [pow_one]
  decide

/-- **(F) fails on `01/12/021`**, through Lemma 4 (1) (the converse direction, which needs no
`hzero`): the same conclusion as `Psc.GeometricFTriple.ctrl_not_propertyF`, reached from the
address. -/
theorem ctrl_not_propertyF' {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc ctrlSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ¬ PropertyF ctrlSubst (lenHom ℓ) := by
  have hβ : 1 < β := Psc.BPrimeCore.one_lt_perron ctrlSubst ctrl_prim hℓ hℓM
  obtain ⟨hk, hx, hv, hper⟩ := periodic_of_isInteriorAddress
    (lengthData_of_left_eigen (by linarith) hℓ hℓM) hβ ctrl_isInteriorAddress
  exact fun hF => hv (hF _ hx 1 hk hper)

/-- **The reversal `10/21/120` of the control has the corresponding address**
`(1, 2, 1, 0, e₂ − (−1, 0, 1) = (1, 0, 0))`, decided directly on words. -/
theorem ctrlRev_isInteriorAddress :
    IsInteriorAddress (reverseSubstitution ctrlSubst) 1 2 [1] [0] ![1, 0, 0] := by
  refine ⟨by decide, by simp, by simp, ?_⟩
  rw [pow_one]
  decide

/-- The address of the reversal is the image of the control's address under
`isInteriorAddress_reverse` (a cross-check of the correspondence of Lemma 4 (3)). -/
theorem ctrlRev_isInteriorAddress_eq :
    (pvec [(2 : Fin 3)] - ![-1, 0, 1] : Fin 3 → ℤ) = ![1, 0, 0] ∧
      IsInteriorAddress (reverseSubstitution ctrlSubst) 1 2 [1].reverse [0].reverse
        (pvec [(2 : Fin 3)] - ![-1, 0, 1]) :=
  ⟨by decide, isInteriorAddress_reverse ctrl_isInteriorAddress⟩

/-- **(F) fails on the reversal `10/21/120`**, for every positive left eigen-row of the common
incidence matrix. -/
theorem ctrlRev_not_propertyF {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc ctrlSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ¬ PropertyF (reverseSubstitution ctrlSubst) (lenHom ℓ) := by
  have hβ : 1 < β := Psc.BPrimeCore.one_lt_perron ctrlSubst ctrl_prim hℓ hℓM
  obtain ⟨hk, hx, hv, hper⟩ := periodic_of_isInteriorAddress
    (lengthData_of_left_eigen (by linarith) hℓ hℓM).reverseSubstitution hβ
    ctrlRev_isInteriorAddress
  exact fun hF => hv (hF _ hx 1 hk hper)

/-- **(F) fails on every power of the control** (Lemma 4 (2)). -/
theorem ctrl_power_not_propertyF {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc ctrlSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) {m : ℕ} (hm : 1 ≤ m) :
    ¬ PropertyF (power ctrlSubst m) (lenHom ℓ) := by
  have hβ : 1 < β := Psc.BPrimeCore.one_lt_perron ctrlSubst ctrl_prim hℓ hℓM
  rw [propertyF_power_iff_of_left_eigen (by linarith) hℓ hℓM hm]
  exact ctrl_not_propertyF' hℓ hℓM

/-- **Lemma 1 fails on the reducible strict control `10/102/211`** (`χ_M = (X − 1)(X² − 2X − 2)`,
`Psc.StrictSystem.carrierSubst`): for every length data with `β > 1`, the integer vector
`w = (2, 0, −1) ≠ 0` has `ℓ·w = 0` (against (1)) and `(M − I) w = 0` (against (3)).
Irreducibility of `χ_M` cannot be dropped. -/
theorem carrier_lemma1_fails {L : (Fin 3 → ℤ) →+ ℝ} {β : ℝ}
    (hL : LengthData carrierSubst L β) (hβ : 1 < β) :
    (![2, 0, -1] : Fin 3 → ℤ) ≠ 0 ∧ L ![2, 0, -1] = 0 ∧
      (incZ carrierSubst - 1) *ᵥ ![2, 0, -1] = 0 := by
  have hMw : incZ carrierSubst *ᵥ (![2, 0, -1] : Fin 3 → ℤ) = ![2, 0, -1] := by decide
  refine ⟨by decide, ?_, by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hMw, sub_self]⟩
  have h := hL.eigen ![2, 0, -1]
  rw [hMw] at h
  have h2 : (β - 1) * L ![2, 0, -1] = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · exact h3

/-- **Where Lemma 4 (1) stops without Lemma 1 (1)**: on `10/102/211`, for every length data with
`β > 1`, the state `(1, (2, 0, −1))` is `f`-fixed with nonzero vector, but `σ(1) = 102` has no
factorisation `P 1 Q` with `P` nonempty, so there is no interior address `(1, 1, P, Q, w)`.  The
forward direction of Lemma 4 (1) needs `hzero`. -/
theorem carrier_periodic_not_interior {L : (Fin 3 → ℤ) →+ ℝ} {β : ℝ}
    (hL : LengthData carrierSubst L β) (hβ : 1 < β) :
    IsState L ((1 : Fin 3), (![2, 0, -1] : Fin 3 → ℤ)) ∧
      StepN carrierSubst L 1 ((1 : Fin 3), ![2, 0, -1]) ((1 : Fin 3), ![2, 0, -1]) ∧
      ∀ P Q v, ¬ IsInteriorAddress carrierSubst 1 1 P Q v := by
  obtain ⟨-, hLw, -⟩ := carrier_lemma1_fails hL hβ
  have hx : IsState L ((1 : Fin 3), (![2, 0, -1] : Fin 3 → ℤ)) := by
    refine ⟨?_, ?_⟩
    · show 0 ≤ L ![2, 0, -1]
      rw [hLw]
    · show L ![2, 0, -1] < L (pvec [(1 : Fin 3)])
      rw [hLw]
      exact hL.pos 1
  refine ⟨hx, ⟨_, rfl, [], [0, 2], rfl, ?_, hx⟩, ?_⟩
  · show (![2, 0, -1] : Fin 3 → ℤ) = incZ carrierSubst *ᵥ ![2, 0, -1] - pvec []
    rw [pvec_nil, sub_zero]
    decide
  · rintro P Q v ⟨hw, hP, -, -⟩
    obtain ⟨a, P', rfl⟩ := List.exists_cons_of_ne_nil hP
    have hw' : [(1 : Fin 3), 0, 2] = a :: (P' ++ 1 :: Q) := hw
    have h1 : [(0 : Fin 3), 2] = P' ++ 1 :: Q := (List.cons.inj hw').2
    have h2 : (1 : Fin 3) ∈ [(0 : Fin 3), 2] := by
      rw [h1]
      simp
    revert h2
    decide

/-- **(F) fails on `10/102/211`** for every length data with `β > 1`. -/
theorem carrier_not_propertyF {L : (Fin 3 → ℤ) →+ ℝ} {β : ℝ}
    (hL : LengthData carrierSubst L β) (hβ : 1 < β) : ¬ PropertyF carrierSubst L := by
  obtain ⟨hx, hper, -⟩ := carrier_periodic_not_interior hL hβ
  intro hF
  have h := hF _ hx 1 le_rfl hper
  revert h
  decide

/-- The carrier controls are not vacuous: `10/102/211` has a positive left eigen-row with
`β > 1` (it is primitive, `Psc.StrictSystem.carrier_primitive`). -/
theorem carrier_lengthData_gt_one : ∃ (β : ℝ) (ℓ : Fin 3 → ℝ), (∀ a, 0 < ℓ a) ∧
    LengthData carrierSubst (lenHom ℓ) β ∧ 1 < β := by
  obtain ⟨β, hβ0, ℓ, hℓ, hℓM⟩ :=
    Psc.PerronExistence.exists_pos_left_eigen_inc carrierSubst carrier_primitive
  exact ⟨β, ℓ, hℓ, lengthData_of_left_eigen hβ0 hℓ hℓM,
    Psc.BPrimeCore.one_lt_perron carrierSubst carrier_primitive hℓ hℓM⟩

end Controls

end Psc.GeometricFLemmas
