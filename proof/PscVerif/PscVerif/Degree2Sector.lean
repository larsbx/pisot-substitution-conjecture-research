/-
# The degree-two sector over three letters: `rank Q₂ = 3`, `χ_{Λ²M} ∣ χ_S`, parity

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `thm:deg23` (Degrees two and
three, `d = 3`), clauses (i) and (ii); `docs/c4-degree2-parity-sieve.md`;
`docs/c4-concentration-attack-2026-11-06.md` §8.

Setting (`Sector`).  `S : Psc.Binomial.ChildSystem (Fin 3)` with
`P : Psc.SignedCocycle.Normalisation S`, every state balanced (`Equiv1`, i.e.
`r(C) ≥ 2`), some representative `j` with `kw j ≠ 0` (`r(C) = 2`), and `χ_M`
irreducible over `ℚ` for `M = Psc.ParikhRank.incQ S`.  `Q₂ = Psc.SignedIntertwiner.Q2 P`
is the column matrix of the wedge coordinates `kw` on the representatives.  The
manuscript's cocycle matrix `S = A - B` is written `Ssign` below (it is `P.Ssign`; the
letter `S` names the child system), and `N_C = P.Nrep = A + B`.  The manuscript's
`|C|` counts each state once, i.e. it is `|R| = Fintype.card P.Rep` here (the Lean
`S.C` holds both orientations).

## Proved here, in full

* `charpoly_fin_three`: `χ_M = X³ - tr(M) X² + U X - det M` with `U = tr(Λ²M)` (the
  sum of the principal `2 × 2` minors), over any commutative ring;
  **`charpoly_wedge2`** (`thm:deg23` (i), the formula):
  `χ_{Λ²M} = X³ - U X² + det(M) tr(M) X - det(M)²`, from
  `trace_wedge2_wedge2` (`tr Λ²Λ²M = det M · tr M`) and `det_wedge2`
  (`det Λ²M = (det M)²`); `wedge2_map`: `Λ²` commutes with ring homomorphisms.
* `charpoly_dvd_of_map_rat` (Gauss, integer matrices): divisibility of the rational
  characteristic polynomials of two integer matrices descends to `ℤ`;
  `map_natCast_intCast` casts a natural matrix through `ℤ`.
* Any alphabet: `ssign_mod_two` (`Ssign ≡ N_C (mod 2)` entrywise, as matrices over
  `ZMod 2`: `A - B = A + B` in characteristic two); `charpoly_ssign_mod_two`
  (`χ_Ssign ≡ χ_{N_C} (mod 2)`); `ne_nil_of_balanced` (a balanced state of a
  normalisation has a nonempty top track, via `Psc.SignedCocycle.Normalisation.noncoincident`
  and `Psc.PrimitiveExpansion.tracks_ne_nil`; so the nonempty-track hypothesis `hne` of
  `Psc.ParikhRank.charpoly_dvd_rep_int` and its siblings is redundant there).
* Over a field: `natDegree_lcm_charpoly` (`3 ≤ deg lcm(χ_A, χ_B) ≤ 6` for `3 × 3`
  `A`, `B`), `natDegree_lcm_of_isCoprime` (`= 6` when coprime).  For an integer `M`
  with `det M` odd and `tr M ≢ U (mod 2)`: `isCoprime_mod_two` (`χ_M mod 2` and
  `χ_{Λ²M} mod 2` are coprime: they are `X³ + X + 1` and `X³ + X² + 1` in some order,
  `isCoprime_cubics_mod_two`) and **`natDegree_lcm_eq_six`** (their lcm has degree `6`).
* In the setting (`thm:deg23` (ii)); `incZ`, `incF2`, `Q2Q`, `SsignQ`, `nrepF2` are
  the casts, with `incZ_map_rat`, `incZ_map_two`, `q2Q_ne_zero`:
  - `q2Q_ssignQ`: `Q₂ Ssign = Λ²M Q₂` over `ℚ` (from `Psc.SignedIntertwiner.q2_mul_ssign`);
  - **`q2_surjective`**, **`rank_q2`**: `rank_ℚ Q₂ = 3`
    (`Psc.ParikhRank.surjective_of_intertwine` with `Psc.Cyclicity.irreducible_wedge2`);
  - `card_rep_ge_three`: `3 ≤ |R|`, read off `Q₂`; an alternative proof of
    `Psc.ParikhRank.card_rep_ge`, needing neither `S.C.Nonempty` nor `hne`;
  - **`charpoly_wedge2_dvd_ssign`**, **`charpoly_wedge2_dvd_ssign_int`**:
    `χ_{Λ²M} ∣ χ_Ssign` over `ℚ` and over `ℤ`;
  - **`charpoly_dvd_nrep_mod_two`**, **`charpoly_wedge2_dvd_nrep_mod_two`**,
    **`lcm_dvd_nrep_mod_two`**: modulo `2`, `χ_M`, `χ_{Λ²M}` and hence their lcm
    divide `χ_{N_C}`; **`card_rep_ge_natDegree_lcm`**: `|R| ≥ deg lcm`, a value in
    `{3, 4, 5, 6}`;
  - **`card_rep_ge_six`** (the parity clause): if `det M` is odd and
    `tr M ≢ U (mod 2)`, then `|R| ≥ 6`.
* Controls.
  - `plastic` (`plasticSubst`: `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 01`): `plastic_charpoly`
    (`χ_M = X³ - X - 1`), `plastic_irreducible` (Selmer,
    `Polynomial.X_pow_sub_X_sub_one_irreducible_rat`), `plastic_odd`,
    `plastic_trace` (`det = 1`, `tr = 0`, `U = -1`, by `decide`), `plastic_lcm`
    (`deg lcm = 6`).  So the hypotheses of `isCoprime_mod_two` and
    `natDegree_lcm_eq_six`, and the *matrix-level* hypotheses `hM`, `hdet`, `htr` of
    `card_rep_ge_six`, are jointly met by an actual substitution.
  - Boundary control `exA_sector`, `exA_not_irreducible`, **`irreducible_needed`**:
    `Psc.SignedIntertwiner.exA` meets every *state-level* hypothesis (a
    normalisation, balanced states, `kw ≠ 0`) but has `|R| = 1 < 3`, and its
    `χ_M` has the root `1`; so `hM` cannot be dropped from `card_rep_ge_three`.

## Not proved here

* **No non-vacuity control for the full hypothesis set** of the `Sector` theorems
  (a normalisation of a child system over `Fin 3` with balanced states, `kw ≠ 0`
  and `χ_M` irreducible), and none is to be expected: the `Sector` theorems are
  necessary conditions on a hypothetical strict component, not facts about a known
  one.  Informally (not formalized here):
  1. `χ_M` irreducible makes `M` an irreducible nonnegative matrix, so `prop:cocycle`
     gives `ρ(Ssign) ≤ β`; with `χ_{Λ²M} ∣ χ_Ssign` every `β βᵢ` has modulus `≤ β`,
     and irreducibility excludes `|βᵢ| = 1`; so `σ` is irreducible Pisot.
  2. Every depth-`n` descendant block (`ChildSystem.desc`) of a state `T` is a state,
     hence balanced and noncoincident, hence has a mismatched position.  With `L` the
     largest state length, `σⁿ(T.1)` and `σⁿ(T.2)` disagree at a fraction `≥ 1/L` of
     positions for every `n`, so some potential overlap descending from `T` is
     nonproductive.
  3. The states need not be legal words, but pure discrete spectrum gives formal
     productivity (every potential overlap productive) on three letters
     (`docs/formal-productivity-reduction-2026-10-04.md`, the route of
     `thm:seedwise`; human review pending).  So a full control is a three-letter
     counterexample to PSC.
     Formal productivity is also checked directly on the 4,554-member corpus, which
     contains `plasticSubst` as specimen `1 2 4`: no formal nonproductive state and no
     closed carrier (`docs/formal-overlap-carriers-2026-10-04.md`; finite evidence).
     So `plastic` cannot be extended to a full control.
  The matrix-level hypotheses alone are met (`plastic`), and the state-level ones
  alone are met (`exA_sector`).
* `thm:deg23` (i) beyond the formula: irreducibility of `χ_{Λ²M}` is
  `Psc.Cyclicity.irreducible_wedge2`; the modulus statement `ρ(Λ²M) = β|β₂| < β` is
  not formalized.  `thm:deg23` (iii) (`r(C) = 3`) is not treated.
* The table of the eight parity classes of `(tr M, U, det M) mod 2`; only the
  bound `deg lcm ∈ [3, 6]` and the value `6` in the stated case are proved.
* The first-defect selection (`r(C) = 2` means here: all states balanced, some
  `kw ≠ 0`), and anything about `|C|` beyond the representatives (`|C| = 2|R|`
  is `Psc.ParikhRank.card_state_eq_two_mul`).
-/
import PscVerif.SignedIntertwiner
import PscVerif.ParikhRank
import PscVerif.Cyclicity
import PscVerif.PrimitiveExpansion

namespace Psc.Degree2Sector

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.SignedCocycle Psc.Intertwiner2
  Psc.Cyclicity Psc.ParikhRank Psc.SignedIntertwiner

/-! ### `thm:deg23` (i): the characteristic polynomial of `Λ²M` -/

section Wedge

variable {R : Type*} [CommRing R]

/-- `Λ²` commutes with ring homomorphisms. -/
theorem wedge2_map {R' : Type*} [CommRing R'] (f : R →+* R') (M : Matrix (Fin 3) (Fin 3) R) :
    wedge2 (M.map f) = (wedge2 M).map f := by
  ext I J; simp [wedge2]

/-- `χ_M = X³ - tr(M) X² + U X - det M`, with `U = tr(Λ²M)` the sum of the principal
`2 × 2` minors. -/
theorem charpoly_fin_three (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C (wedge2 M).trace * X - C M.det := by
  simp only [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, charmatrix_apply,
    wedge2, pairFst, pairSnd, Matrix.of_apply, diagonal, Fin.isValue, ↓reduceIte, Fin.reduceEq,
    zero_sub, mul_neg, neg_mul, neg_neg, zero_ne_one, one_ne_zero, map_add, map_sub, map_mul,
    cons_val_zero, cons_val_one, cons_val]
  ring

/-- `tr(Λ²Λ²M) = det M · tr M`. -/
theorem trace_wedge2_wedge2 (M : Matrix (Fin 3) (Fin 3) R) :
    (wedge2 (wedge2 M)).trace = M.det * M.trace := by
  simp only [wedge2, pairFst, pairSnd, Fin.isValue, of_apply, trace_fin_three, det_fin_three,
    cons_val_zero, cons_val_one, cons_val]
  ring

/-- `det Λ²M = (det M)²`. -/
theorem det_wedge2 (M : Matrix (Fin 3) (Fin 3) R) : (wedge2 M).det = M.det ^ 2 := by
  simp only [wedge2, pairFst, pairSnd, Fin.isValue, det_fin_three, of_apply, cons_val_zero,
    cons_val_one, cons_val]
  ring

/-- **`thm:deg23` (i), the formula**: with `U = tr(Λ²M)` as in `charpoly_fin_three`,
`χ_{Λ²M} = X³ - U X² + det(M) tr(M) X - det(M)²`. -/
theorem charpoly_wedge2 (M : Matrix (Fin 3) (Fin 3) R) :
    (wedge2 M).charpoly =
      X ^ 3 - C (wedge2 M).trace * X ^ 2 + C (M.det * M.trace) * X - C (M.det ^ 2) := by
  rw [charpoly_fin_three, trace_wedge2_wedge2, det_wedge2]

end Wedge

/-! ### Gauss for integer matrices -/

/-- **Gauss.**  Divisibility of the rational characteristic polynomials of integer
matrices descends to `ℤ` (the divisor is monic).  The natural-matrix form is
`Psc.ParikhRank.charpoly_dvd_int_of_rat`. -/
theorem charpoly_dvd_of_map_rat {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [DecidableEq ι] {A : Matrix κ κ ℤ} {B : Matrix ι ι ℤ}
    (h : (A.map (Int.castRingHom ℚ)).charpoly ∣ (B.map (Int.castRingHom ℚ)).charpoly) :
    A.charpoly ∣ B.charpoly := by
  rwa [← Polynomial.map_dvd_map (Int.castRingHom ℚ) Int.cast_injective (charpoly_monic _),
    ← charpoly_map, ← charpoly_map]

/-- Casting a natural matrix through `ℤ`. -/
theorem map_natCast_intCast {m n R : Type*} [Ring R] (A : Matrix m n ℕ) :
    (A.map (Nat.cast : ℕ → ℤ)).map (Int.castRingHom R) = A.map (Nat.cast : ℕ → R) := by
  ext; simp

/-! ### Parity -/

/-- **`Ssign ≡ N_C (mod 2)`**: `A - B = A + B` over `ZMod 2`. -/
theorem ssign_mod_two {α : Type*} [DecidableEq α] {S : ChildSystem α} (P : Normalisation S) :
    P.Ssign.map (Int.cast : ℤ → ZMod 2) = P.Nrep.map (Nat.cast : ℕ → ZMod 2) := by
  ext i j
  simp [Normalisation.Ssign, Normalisation.Nrep, CharTwo.sub_eq_add]

/-- `χ_Ssign ≡ χ_{N_C} (mod 2)`. -/
theorem charpoly_ssign_mod_two {α : Type*} [DecidableEq α] {S : ChildSystem α}
    (P : Normalisation S) :
    P.Ssign.charpoly.map (Int.castRingHom (ZMod 2)) =
      (P.Nrep.map (Nat.cast : ℕ → ZMod 2)).charpoly := by
  rw [← charpoly_map]; exact congrArg charpoly (ssign_mod_two P)

/-- A balanced state of a normalisation has a nonempty top track: it is noncoincident.  So
the hypothesis `hne` of `Psc.ParikhRank.charpoly_dvd_rep_int` and its siblings follows from
their other hypotheses. -/
theorem ne_nil_of_balanced {α : Type*} [DecidableEq α] {S : ChildSystem α}
    (P : Normalisation S) (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) : ∀ T ∈ S.C, T.1 ≠ [] :=
  fun T hT => (Psc.PrimitiveExpansion.tracks_ne_nil (hbal T hT) (P.noncoincident T hT)).1

section Lcm

variable {F : Type*} [Field F] [DecidableEq F]

/-- The lcm of two `3 × 3` characteristic polynomials has degree between `3` and `6`. -/
theorem natDegree_lcm_charpoly (A B : Matrix (Fin 3) (Fin 3) F) :
    3 ≤ (lcm A.charpoly B.charpoly).natDegree ∧
      (lcm A.charpoly B.charpoly).natDegree ≤ 6 := by
  have hA := charpoly_monic A
  have hB := charpoly_monic B
  have hl : lcm A.charpoly B.charpoly ≠ 0 := lcm_ne_zero_iff.2 ⟨hA.ne_zero, hB.ne_zero⟩
  have h3 := natDegree_le_of_dvd (dvd_lcm_left A.charpoly B.charpoly) hl
  have h6 := natDegree_le_of_dvd (lcm_dvd (dvd_mul_right A.charpoly B.charpoly)
    (dvd_mul_left B.charpoly A.charpoly)) (hA.mul hB).ne_zero
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at h3
  rw [hA.natDegree_mul hB, charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim,
    Fintype.card_fin] at h6
  exact ⟨h3, h6⟩

/-- Coprime `3 × 3` characteristic polynomials have an lcm of degree `6`. -/
theorem natDegree_lcm_of_isCoprime (A B : Matrix (Fin 3) (Fin 3) F)
    (h : IsCoprime A.charpoly B.charpoly) : (lcm A.charpoly B.charpoly).natDegree = 6 := by
  have hA := charpoly_monic A
  have hB := charpoly_monic B
  have hl : lcm A.charpoly B.charpoly ≠ 0 := lcm_ne_zero_iff.2 ⟨hA.ne_zero, hB.ne_zero⟩
  have h1 := natDegree_le_of_dvd (h.mul_dvd (dvd_lcm_left _ _) (dvd_lcm_right _ _)) hl
  rw [hA.natDegree_mul hB, charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim,
    Fintype.card_fin] at h1
  exact le_antisymm (natDegree_lcm_charpoly A B).2 h1

end Lcm

/-- `X³ - t X² + u X - 1` and `X³ - u X² + t X - 1` are coprime over `ZMod 2` when
`t ≠ u`: they are `X³ + X + 1` and `X³ + X² + 1`, and
`1 = X (X³ + X + 1) + (X + 1) (X³ + X² + 1)`. -/
theorem isCoprime_cubics_mod_two {t u : ZMod 2} (h : t ≠ u) :
    IsCoprime (X ^ 3 - C t * X ^ 2 + C u * X - 1 : (ZMod 2)[X])
      (X ^ 3 - C u * X ^ 2 + C t * X - 1) := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    rw [← C_ofNat]; exact C_eq_zero.2 rfl
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
    revert t u; decide
  · refine ⟨X, X + 1, ?_⟩
    simp only [map_zero, map_one]
    linear_combination (X ^ 4 - X - 1) * h2
  · refine ⟨X + 1, X, ?_⟩
    simp only [map_zero, map_one]
    linear_combination (X ^ 4 - X - 1) * h2

/-- **Parity clause, algebra**: for an integer `M` with `det M` odd and
`tr M ≢ U (mod 2)` (`U = tr Λ²M`), the reductions mod `2` of `χ_M` and `χ_{Λ²M}`
are coprime. -/
theorem isCoprime_mod_two (M : Matrix (Fin 3) (Fin 3) ℤ) (hdet : Odd M.det)
    (htr : ¬ M.trace ≡ (wedge2 M).trace [ZMOD 2]) :
    IsCoprime (M.map (Int.cast : ℤ → ZMod 2)).charpoly
      (wedge2 (M.map (Int.cast : ℤ → ZMod 2))).charpoly := by
  set M₂ := M.map (Int.cast : ℤ → ZMod 2)
  have hd : M₂.det = 1 := by
    rw [← Int.cast_det]; exact ZMod.intCast_eq_one_iff_odd.2 hdet
  have ht : M₂.trace ≠ (wedge2 M₂).trace := by
    rw [show M₂ = M.map (Int.castRingHom (ZMod 2)) from rfl, wedge2_map,
      ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace]
    simpa [ZMod.intCast_eq_intCast_iff] using htr
  rw [charpoly_wedge2, charpoly_fin_three _, hd, one_mul, one_pow, map_one]
  exact isCoprime_cubics_mod_two ht

/-- **Parity clause, degree**: for an integer `M` with `det M` odd and `tr M ≢ U (mod 2)`,
`lcm(χ_M mod 2, χ_{Λ²M} mod 2)` has degree `6`. -/
theorem natDegree_lcm_eq_six (M : Matrix (Fin 3) (Fin 3) ℤ) (hdet : Odd M.det)
    (htr : ¬ M.trace ≡ (wedge2 M).trace [ZMOD 2]) :
    (lcm (M.map (Int.cast : ℤ → ZMod 2)).charpoly
      (wedge2 (M.map (Int.cast : ℤ → ZMod 2))).charpoly).natDegree = 6 :=
  natDegree_lcm_of_isCoprime _ _ (isCoprime_mod_two M hdet htr)

/-! ### The setting of `thm:deg23` (ii) -/

/-- The integer incidence matrix. -/
abbrev incZ (S : ChildSystem (Fin 3)) : Matrix (Fin 3) (Fin 3) ℤ :=
  (inc S.s).map (Nat.cast : ℕ → ℤ)

/-- The incidence matrix mod `2`. -/
abbrev incF2 (S : ChildSystem (Fin 3)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  (inc S.s).map (Nat.cast : ℕ → ZMod 2)

theorem incZ_map_rat (S : ChildSystem (Fin 3)) : (incZ S).map (Int.castRingHom ℚ) = incQ S :=
  map_natCast_intCast _

theorem incZ_map_two (S : ChildSystem (Fin 3)) :
    (incZ S).map (Int.castRingHom (ZMod 2)) = incF2 S :=
  map_natCast_intCast _

section Sector

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)

/-- `Q₂` over `ℚ`. -/
abbrev Q2Q : Matrix (Fin 3) P.Rep ℚ := (Q2 P).map (Int.cast : ℤ → ℚ)

/-- The cocycle matrix `S` over `ℚ`. -/
abbrev SsignQ : Matrix P.Rep P.Rep ℚ := P.Ssign.map (Int.cast : ℤ → ℚ)

/-- `N_C` mod `2`. -/
abbrev nrepF2 : Matrix P.Rep P.Rep (ZMod 2) := P.Nrep.map (Nat.cast : ℕ → ZMod 2)

/-- `Q₂ Ssign = Λ²M Q₂` over `ℚ`. -/
theorem q2Q_ssignQ (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) :
    Q2Q P * SsignQ P = wedge2 (incQ S) * Q2Q P := by
  change (Q2 P).map (Int.castRingHom ℚ) * P.Ssign.map (Int.castRingHom ℚ) =
    wedge2 (incQ S) * (Q2 P).map (Int.castRingHom ℚ)
  rw [← incZ_map_rat, wedge2_map, ← Matrix.map_mul, ← Matrix.map_mul, q2_mul_ssign P hbal]

theorem q2Q_ne_zero (hK : ∃ j : P.Rep, kw j.1.1 j.1.2 ≠ 0) : Q2Q P ≠ 0 := by
  obtain ⟨j, hj⟩ := hK
  intro h0
  refine hj (funext fun I => ?_)
  have := congrFun (congrFun h0 I) j
  simpa [Q2] using this

variable (hM : Irreducible (incQ S).charpoly) (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2)
  (hK : ∃ j : P.Rep, kw j.1.1 j.1.2 ≠ 0)
include hM hbal hK

/-- **`thm:deg23` (ii), `rank Q₂ = 3`**: `Q₂` is onto `Λ²ℚ³`. -/
theorem q2_surjective : Function.Surjective (Matrix.mulVecLin (Q2Q P)) :=
  surjective_of_intertwine (q2Q_ssignQ P hbal) (irreducible_wedge2 _ hM) (q2Q_ne_zero P hK)

/-- **`thm:deg23` (ii)**: `rank_ℚ Q₂ = 3`. -/
theorem rank_q2 : (Q2Q P).rank = 3 := by
  rw [Matrix.rank, LinearMap.range_eq_top.2 (q2_surjective P hM hbal hK), finrank_top,
    Module.finrank_fin_fun]

/-- `3 ≤ |R|`, read off `Q₂` (`rank Q₂ = 3`): an alternative proof of
`Psc.ParikhRank.card_rep_ge`, which reads it off `P_R` and also assumes `S.C.Nonempty` and
nonempty tracks. -/
theorem card_rep_ge_three : 3 ≤ Fintype.card P.Rep :=
  card_ge_of_intertwine (q2Q_ssignQ P hbal) (irreducible_wedge2 _ hM) (q2Q_ne_zero P hK)

/-- **`thm:deg23` (ii), `χ_{Λ²M} ∣ χ_Ssign`** over `ℚ`. -/
theorem charpoly_wedge2_dvd_ssign : (wedge2 (incQ S)).charpoly ∣ (SsignQ P).charpoly :=
  charpoly_dvd_of_intertwine (q2Q_ssignQ P hbal) (irreducible_wedge2 _ hM) (q2Q_ne_zero P hK)

/-- **`thm:deg23` (ii), `χ_{Λ²M} ∣ χ_Ssign`** over `ℤ` (Gauss). -/
theorem charpoly_wedge2_dvd_ssign_int : (wedge2 (incZ S)).charpoly ∣ P.Ssign.charpoly := by
  refine charpoly_dvd_of_map_rat ?_
  rw [← wedge2_map, incZ_map_rat]
  exact charpoly_wedge2_dvd_ssign P hM hbal hK

/-- **`thm:deg23` (ii), parity, `χ_M ∣ χ_{N_C}` mod `2`**. -/
theorem charpoly_dvd_nrep_mod_two : (incF2 S).charpoly ∣ (nrepF2 P).charpoly := by
  obtain ⟨j, -⟩ := hK
  have h := Polynomial.map_dvd (Int.castRingHom (ZMod 2))
    (charpoly_dvd_rep_int P hM hbal (ne_nil_of_balanced P hbal) ⟨j.1, P.sub j.2⟩)
  rwa [← charpoly_map, ← charpoly_map, map_natCast_intCast, map_natCast_intCast] at h

/-- **`thm:deg23` (ii), parity, `χ_{Λ²M} ∣ χ_{N_C}` mod `2`**: `χ_{Λ²M} ∣ χ_Ssign` and
`Ssign ≡ N_C`. -/
theorem charpoly_wedge2_dvd_nrep_mod_two :
    (wedge2 (incF2 S)).charpoly ∣ (nrepF2 P).charpoly := by
  have h := Polynomial.map_dvd (Int.castRingHom (ZMod 2))
    (charpoly_wedge2_dvd_ssign_int P hM hbal hK)
  rwa [← charpoly_map, ← wedge2_map, incZ_map_two, charpoly_ssign_mod_two] at h

/-- **`thm:deg23` (ii), parity**: `lcm(χ_M, χ_{Λ²M}) ∣ χ_{N_C}` mod `2`. -/
theorem lcm_dvd_nrep_mod_two :
    lcm (incF2 S).charpoly (wedge2 (incF2 S)).charpoly ∣ (nrepF2 P).charpoly :=
  lcm_dvd (charpoly_dvd_nrep_mod_two P hM hbal hK)
    (charpoly_wedge2_dvd_nrep_mod_two P hM hbal hK)

/-- **`thm:deg23` (ii), `|R| ≥ deg lcm(χ_M mod 2, χ_{Λ²M} mod 2)`**; the degree lies
in `{3, 4, 5, 6}` (`natDegree_lcm_charpoly`). -/
theorem card_rep_ge_natDegree_lcm :
    (lcm (incF2 S).charpoly (wedge2 (incF2 S)).charpoly).natDegree ≤ Fintype.card P.Rep := by
  have := natDegree_le_of_dvd (lcm_dvd_nrep_mod_two P hM hbal hK) (charpoly_monic _).ne_zero
  rwa [charpoly_natDegree_eq_dim] at this

/-- **`thm:deg23` (ii), the parity clause**: if `det M` is odd and
`tr M ≢ U (mod 2)`, the lcm has degree `6` (`natDegree_lcm_eq_six`), so `|R| ≥ 6`. -/
theorem card_rep_ge_six (hdet : Odd (incZ S).det)
    (htr : ¬ (incZ S).trace ≡ (wedge2 (incZ S)).trace [ZMOD 2]) : 6 ≤ Fintype.card P.Rep := by
  have h6 : (lcm (incF2 S).charpoly (wedge2 (incF2 S)).charpoly).natDegree = 6 :=
    incZ_map_two S ▸ natDegree_lcm_eq_six _ hdet htr
  exact h6 ▸ card_rep_ge_natDegree_lcm P hM hbal hK

end Sector

/-! ### Controls -/

/-- `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 01`: `χ_M = X³ - X - 1` (the smallest Pisot number). -/
def plasticSubst : Fin 3 → List (Fin 3) := ![[1], [2], [0, 1]]

/-- Its integer incidence matrix. -/
def plastic : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

theorem plastic_inc : (inc plasticSubst).map (Nat.cast : ℕ → ℤ) = plastic := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- `χ_M = X³ - X - 1` over `ℚ`. -/
theorem plastic_charpoly :
    ((inc plasticSubst).map (Nat.cast : ℕ → ℚ)).charpoly = X ^ 3 - X - 1 := by
  rw [← map_natCast_intCast, plastic_inc, charpoly_fin_three]
  simp only [plastic, Int.coe_castRingHom, trace_fin_three, det_fin_three, wedge2, pairFst,
    pairSnd, Fin.isValue, map_apply, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
    cons_val_one, cons_val, Int.cast_zero, Int.cast_one, map_zero, map_one, map_neg, add_zero,
    zero_add, zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, sub_self, neg_mul,
    sub_left_inj]
  ring

/-- `hM` holds for `plasticSubst` (Selmer: `X³ - X - 1` is irreducible). -/
theorem plastic_irreducible :
    Irreducible ((inc plasticSubst).map (Nat.cast : ℕ → ℚ)).charpoly := by
  rw [plastic_charpoly]; exact X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

/-- `hdet` holds for `plastic`: `det = 1`. -/
theorem plastic_odd : Odd plastic.det := by
  rw [Matrix.det_fin_three]; decide

/-- `htr` holds for `plastic`: `tr = 0`, `U = -1`. -/
theorem plastic_trace : ¬ plastic.trace ≡ (wedge2 plastic).trace [ZMOD 2] := by
  simp only [Matrix.trace_fin_three]; decide

/-- `deg lcm = 6` for `plastic`. -/
theorem plastic_lcm :
    (lcm (plastic.map (Int.cast : ℤ → ZMod 2)).charpoly
      (wedge2 (plastic.map (Int.cast : ℤ → ZMod 2))).charpoly).natDegree = 6 :=
  natDegree_lcm_eq_six _ plastic_odd plastic_trace

/-- **Boundary control**: `Psc.SignedIntertwiner.exA` meets the state-level hypotheses
(a normalisation, balanced states, `kw ≠ 0`) and has `|R| = 1 < 3`; its `χ_M` has the
root `1` (`exA_not_irreducible`). -/
theorem exA_sector : (∀ T ∈ exA.C, Equiv1 T.1 T.2) ∧
    (∃ j : exANorm.Rep, kw j.1.1 j.1.2 ≠ 0) ∧ Fintype.card exANorm.Rep = 1 :=
  ⟨exA_balanced, ⟨exARep, show kw exAPair.1 exAPair.2 ≠ 0 by rw [exA_kw]; decide⟩,
    Fintype.card_eq_one_iff.2 ⟨exARep, exANorm_rep⟩⟩

theorem exA_not_irreducible : ¬ Irreducible (incQ exA).charpoly := fun h =>
  not_isRoot_of_irreducible _ h 1 (by
    rw [eval_charpoly, Matrix.det_fin_three]
    simp [exA, exASubst])

/-- **`hM` cannot be dropped from `card_rep_ge_three`**: the state-level hypotheses alone
do not give `3 ≤ |R|` (`exA_sector`). -/
theorem irreducible_needed : ¬ ∀ (S : ChildSystem (Fin 3)) (P : Normalisation S),
    (∀ T ∈ S.C, Equiv1 T.1 T.2) → (∃ j : P.Rep, kw j.1.1 j.1.2 ≠ 0) →
      3 ≤ Fintype.card P.Rep := fun h => by
  have := h exA exANorm exA_sector.1 exA_sector.2.1
  rw [exA_sector.2.2] at this; omega

end Psc.Degree2Sector
