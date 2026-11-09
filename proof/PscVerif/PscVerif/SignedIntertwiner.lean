/-
# The signed first-defect intertwiner `Q_r S = Φ_r Q_r` (`r = 2, 3`)

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `thm:defect-intertwiner`
(with `lem:conc-subst`, `lem:descendants`, `prop:cocycle`);
`docs/c4-concentration-attack-2026-11-06.md` §8.

Setting.  `S : Psc.Binomial.ChildSystem α` over a finite alphabet and
`P : Psc.SignedCocycle.Normalisation S`, a choice of normalised representatives
`R` (`C = R ⊔ swap R`), with the cocycle matrix `S = A - B` on the
representatives (`Psc.SignedCocycle.Normalisation.Ssign`: `A i j` counts the
children of `j` equal to `i`, `B i j` those equal to `i.swap`).  The integer
incidence matrix is `M = (inc S.s).map (Nat.cast : ℕ → ℤ)`, `M a c = |σ c|_a`.

The word-level identities `K_r(σT) = M^{⊗r} K_r(T)` and block additivity are
`PscVerif.Intertwiner2` / `PscVerif.Intertwiner3`, stated over the *raw
ordered* children.  This file adds the sign bookkeeping: a child equal to
`i.swap` contributes `K_r(i.swap) = - K_r(i)`, so regrouping the children of a
representative `j` by representative gives exactly the column `j` of `S`.

## What is proved, in full

* `sum_children_signed`: for any `f` into an additive group that is odd under
  the swap on representatives (`f i.swap = - f i`), the sum of `f` over the
  children of a representative `j` is `Σ_i S i j • f i`.
* Degree two, any finite alphabet (`k2_rep`): if every state of `C` is balanced
  (`Equiv1`), then for every representative `j` and letters `a b`,
  `Σ_{c,d} M a c · M b d · K₂(j)_{cd} = Σ_i S i j · K₂(i)_{ab}`;
  matrix form `q2full_mul_ssign`: `Q₂ S = (M ⊗ₖ M) Q₂` with `Q₂` the
  `(α × α) × R` column matrix of `K₂`.
* Degree two, `α = Fin 3`, wedge coordinates (`wedge2_mulVec_kw_rep`): under the
  same balance hypothesis,
  `Λ²M *ᵥ kw j = Σ_i S i j • kw i` (`Psc.Cyclicity.wedge2`,
  `Psc.Intertwiner2.kw`); matrix form `q2_mul_ssign`: `Q₂ S = Λ²M Q₂` with
  `Q₂ : Matrix (Fin 3) R ℤ` the column matrix of `kw`.  This is
  `Q₂ S = Φ₂ Q₂`; it needs only `Equiv1`, no `Equiv2`.
* Degree three, any finite alphabet (`k3_rep`): if every state of `C` is
  2-binomially equivalent (`Equiv2`), then
  `Σ_{x,y,z} M a x · M b y · M e z · K₃(j)_{xyz} = Σ_i S i j · K₃(i)_{abe}`;
  matrix form `q3_mul_ssign`: `Q₃ S = (M ⊗ₖ (M ⊗ₖ M)) Q₃` with `Q₃` the
  `(α × α × α) × R` column matrix of `K₃` (27 rows over `Fin 3`).  This is
  `Q₃ S = Φ₃ Q₃` with `Φ₃ = M^{⊗3}` on the full tensor cube.  The swap
  antisymmetry `K₃ v u = - K₃ u v` is `Psc.Intertwiner3.k3_swap`.
* `q3_col_mem_lie3` (`α = Fin 3`): under `Equiv2`, every column of `Q₃` lies in
  `Lie₃` (`Psc.Lie3.k3Vec_mem_span_lyndon`), which `M^{⊗3}` preserves
  (`Psc.Lie3.phi3_mem_span`); so `Q₃ S = Φ₃ Q₃` holds with `Φ₃` the restriction
  of `M^{⊗3}` to `Lie₃`.
* Non-vacuity controls over `Fin 3` (all hypotheses checked by `decide`):
  - `exA` (`0 ↦ 0`, `1 ↦ 101`, `2 ↦ 2`; `C = {(01,10), (10,01)}`, children
    of `(01,10)` are `(01,10), (01,10)`): a zero-return system (`exA_red`:
    its children are the blocks of `Psc.Reduction.red`), `S = (2)`
    (`exA_ssign`), and `exA_wedge`: `Λ²M *ᵥ kw (01,10) = 2 • kw (01,10)` with
    `kw (01,10) = (1,0,0) ≠ 0` (`exA_kw`);
  - `wT` (the identity substitution, `C = {(0112201,1200112), swap}`, built by
    `Psc.Reduction.redSystem` and normalised by
    `Psc.Reduction.redNormalisation`): the pair is irreducible and `Equiv2`,
    `S = (1)` (`wT_ssign`), and `wT_k3`: `M^{⊗3} K₃ = K₃` with
    `K₃_{010} = 2 ≠ 0` (`wT_k3_ne`).  A zero-return system with `K₃ ≠ 0`;
  - `exB` (`0 ↦ 1`, `1 ↦ 0`, `2 ↦ 2`; `C = {(0110,1001), (1001,0110)}`, the
    only child of `(0110,1001)` declared to be its swap): an **algebra-only**
    control.  Its state is reducible (`exB_reducible`) and its declared
    children are not those of `red` (`exB_not_red`), so it is not a
    zero-return system; it exercises the sign `-1`: `S = (-1)` (`exB_ssign`),
    `exB_k3`: `M^{⊗3} K₃(0110,1001) = - K₃(0110,1001)`, with
    `K₃(0110,1001)_{010} = 2 ≠ 0` (`exB_k3_ne`).
  These substitutions are not primitive (`exA`, `exB`: the letter `2` is inert;
  `wT`: the identity); they are controls that the hypotheses are satisfiable
  with `S ≠ 0` and `K_r ≠ 0`, not PIP specimens.

## What is not proved here

* Any spectral consequence (eigenrow arguments on `Φ₃ | Lie₃`, `thm:deg23`,
  Concentration); the restriction of `Φ_r` to `Λ²` / `Lie₃` is only available
  over `Fin 3`.
* The *first*-defect selection of the manuscript (that `r` is the least degree
  with `K_r ≠ 0` on `C`): the hypotheses here are the vanishing of the lower
  defects on every state, which is what the identity uses; nothing is claimed
  about degrees `r ≥ 4`.
* `swap_mem`, `children_swap` remain hypotheses of `Normalisation` here; for
  children computed by zero-return reduction, `children_swap` is derived in
  `Psc.Reduction.redNormalisation`.  Nothing about the balanced-pair algorithm
  reaching `C`, or about a different choice of `R` (diagonal `±1`
  conjugation).
-/
import PscVerif.SignedCocycle
import PscVerif.Intertwiner2
import PscVerif.Intertwiner3
import PscVerif.Reduction
import PscVerif.Lie3

namespace Psc.SignedIntertwiner

open Matrix Psc.Binomial Psc.Incidence Psc.ParikhIntertwiner Psc.SignedCocycle
open Psc.Intertwiner2 Psc.Intertwiner3 Psc.Cyclicity
open scoped Kronecker

section General

variable {α : Type*} [Fintype α] [DecidableEq α] {S : ChildSystem α}
  (P : Normalisation S)

/-- **Signed regrouping of the children.**  For `f` odd under the swap on the
representatives, the sum of `f` over the children of a representative `j` is
`Σ_i S i j • f i`: a child equal to `i` counts `+f i`, one equal to `i.swap`
counts `f i.swap = -f i`. -/
theorem sum_children_signed {G : Type*} [AddCommGroup G] (f : List α × List α → G)
    (hf : ∀ i : P.Rep, f i.1.swap = -f i.1) (j : P.Rep) :
    ((S.children j.1).map f).sum = ∑ i : P.Rep, P.Ssign i j • f i.1 := by
  rw [sum_children_eq_sum_state S f ⟨j.1, P.sub j.2⟩]
  simp only [Nc_apply]
  rw [P.sum_state (fun V => (S.children j.1).count V • f V)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf, smul_neg, ← sub_eq_add_neg, Normalisation.Ssign, Matrix.of_apply, sub_smul,
    natCast_zsmul, natCast_zsmul]
  rfl

/-- For balanced states, `(M ⊗ M) K₂(T)` is the sum of the `K₂` of the raw ordered
children of `T ∈ C` (`k2_subst` with `k2_join`). -/
theorem k2_image_children (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) {T : List α × List α}
    (hT : T ∈ S.C) (a b : α) :
    ∑ c, ∑ d, (inc S.s a c : ℤ) * inc S.s b d * K2 T.1 T.2 c d =
      ((S.children T).map fun U => K2 U.1 U.2 a b).sum := by
  rw [← k2_subst S.s (hbal T hT), ← S.top T hT, ← S.bot T hT]
  exact k2_join _ (fun U hU => hbal U (S.closed T hT U hU)) a b

/-- **Signed degree-two intertwiner** (`thm:defect-intertwiner`, `r = 2`): for
balanced states, `(M ⊗ M) K₂(j) = Σ_i S i j · K₂(i)` on the representatives. -/
theorem k2_rep (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) (j : P.Rep) (a b : α) :
    ∑ c, ∑ d, (inc S.s a c : ℤ) * inc S.s b d * K2 j.1.1 j.1.2 c d =
      ∑ i : P.Rep, P.Ssign i j * K2 i.1.1 i.1.2 a b := by
  rw [k2_image_children hbal (P.sub j.2)]
  exact sum_children_signed P (fun U => K2 U.1 U.2 a b) (fun i => k2_swap _ _ a b) j

/-- The column matrix `Q₂` of `K₂` on the representatives, rows `α × α`. -/
def Q2full : Matrix (α × α) P.Rep ℤ := Matrix.of fun t j => K2 j.1.1 j.1.2 t.1 t.2

/-- **`Q₂ S = (M ⊗ M) Q₂`** on the full tensor square, for balanced states. -/
theorem q2full_mul_ssign (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) :
    Q2full P * P.Ssign =
      ((inc S.s).map (Nat.cast : ℕ → ℤ) ⊗ₖ (inc S.s).map (Nat.cast : ℕ → ℤ)) *
        Q2full P := by
  ext ⟨a, b⟩ j
  simp only [mul_apply, Q2full, of_apply, kroneckerMap_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  rw [k2_rep P hbal j a b]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- For 2-binomially equivalent states, `M^{⊗3} K₃(T)` is the sum of the `K₃` of
the raw ordered children of `T ∈ C` (`k3_subst` with `k3_children`). -/
theorem k3_image_children (hbal : ∀ T ∈ S.C, Equiv2 T.1 T.2) {T : List α × List α}
    (hT : T ∈ S.C) (a b e : α) :
    ∑ x, ∑ y, ∑ z, (inc S.s a x : ℤ) * inc S.s b y * inc S.s e z * K3 T.1 T.2 x y z =
      ((S.children T).map fun U => K3 U.1 U.2 a b e).sum := by
  rw [← k3_subst S.s (hbal T hT)]
  exact k3_children S hT (fun U hU => hbal U (S.closed T hT U hU)) a b e

/-- **Signed degree-three intertwiner** (`thm:defect-intertwiner`, `r = 3`): for
2-binomially equivalent states, `M^{⊗3} K₃(j) = Σ_i S i j · K₃(i)` on the
representatives. -/
theorem k3_rep (hbal : ∀ T ∈ S.C, Equiv2 T.1 T.2) (j : P.Rep) (a b e : α) :
    ∑ x, ∑ y, ∑ z, (inc S.s a x : ℤ) * inc S.s b y * inc S.s e z * K3 j.1.1 j.1.2 x y z =
      ∑ i : P.Rep, P.Ssign i j * K3 i.1.1 i.1.2 a b e := by
  rw [k3_image_children hbal (P.sub j.2)]
  exact sum_children_signed P (fun U => K3 U.1 U.2 a b e) (fun i => k3_swap _ _ a b e) j

/-- The column matrix `Q₃` of `K₃` on the representatives, rows `α × α × α`. -/
def Q3 : Matrix (α × α × α) P.Rep ℤ :=
  Matrix.of fun t j => K3 j.1.1 j.1.2 t.1 t.2.1 t.2.2

/-- **`Q₃ S = M^{⊗3} Q₃`** (`Φ₃ = M ⊗ (M ⊗ M)` on the full tensor cube), for
2-binomially equivalent states. -/
theorem q3_mul_ssign (hbal : ∀ T ∈ S.C, Equiv2 T.1 T.2) :
    Q3 P * P.Ssign =
      ((inc S.s).map (Nat.cast : ℕ → ℤ) ⊗ₖ
        ((inc S.s).map (Nat.cast : ℕ → ℤ) ⊗ₖ (inc S.s).map (Nat.cast : ℕ → ℤ))) *
        Q3 P := by
  ext ⟨a, b, e⟩ j
  simp only [mul_apply, Q3, of_apply, kroneckerMap_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans ?_
  rw [← k3_rep P hbal j a b e]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  ring

end General

/-! ### Degree two in the wedge coordinates over `Fin 3` -/

section Wedge

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)

/-- **Signed degree-two intertwiner, wedge form** (`Q₂ S = Φ₂ Q₂`, column `j`):
for balanced states, `Λ²M *ᵥ kw j = Σ_i S i j • kw i`. -/
theorem wedge2_mulVec_kw_rep (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) (j : P.Rep) :
    wedge2 ((inc S.s).map (Nat.cast : ℕ → ℤ)) *ᵥ kw j.1.1 j.1.2 =
      ∑ i : P.Rep, P.Ssign i j • kw i.1.1 i.1.2 := by
  have hj := P.sub j.2
  rw [wedge2_mulVec_kw_eq_sum_children S hj (hbal _ hj)
    fun U hU => hbal U (S.closed _ hj U hU)]
  exact sum_children_signed P (fun U => kw U.1 U.2) (fun i => kw_swap _ _) j

/-- The column matrix `Q₂` of the wedge coordinates `kw` on the representatives. -/
def Q2 : Matrix (Fin 3) P.Rep ℤ := Matrix.of fun I j => kw j.1.1 j.1.2 I

/-- **`Q₂ S = Λ²M Q₂`** in the basis `(e₀∧e₁, e₀∧e₂, e₁∧e₂)`, for balanced
states (no `Equiv2` hypothesis). -/
theorem q2_mul_ssign (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) :
    Q2 P * P.Ssign = wedge2 ((inc S.s).map (Nat.cast : ℕ → ℤ)) * Q2 P := by
  ext I j
  have h := congrFun (wedge2_mulVec_kw_rep P hbal j) I
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [mul_apply, Q2, of_apply, h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Wedge

/-! ### `Q₃` lands in `Lie₃` -/

/-- Under `Equiv2`, each column of `Q₃` lies in `Lie₃`, an `M^{⊗3}`-invariant
subspace (`Psc.Lie3.phi3_mem_span`). -/
theorem q3_col_mem_lie3 {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv2 T.1 T.2) (j : P.Rep) :
    Psc.Lie3.k3Vec j.1.1 j.1.2 ∈ Submodule.span ℚ (Set.range (Psc.Lie3.lyndon (R := ℚ))) :=
  Psc.Lie3.k3Vec_mem_span_lyndon (hbal j.1 (P.sub j.2))

/-! ### Non-vacuity controls over `Fin 3` -/

/-- `0 ↦ 0`, `1 ↦ 101`, `2 ↦ 2`. -/
def exASubst : Fin 3 → List (Fin 3) := ![[0], [1, 0, 1], [2]]

/-- The pair `(01, 10)`. -/
def exAPair : List (Fin 3) × List (Fin 3) := ([0, 1], [1, 0])

/-- `σ(01) = 01·01`, `σ(10) = 10·10`: each state is its own child, twice. -/
def exA : ChildSystem (Fin 3) where
  s := exASubst
  C := {exAPair, exAPair.swap}
  children := fun T => [T, T]
  top := by decide
  bot := by decide
  closed := by decide
  nonempty := by decide

/-- `exA` normalised by `R = {(01, 10)}`. -/
def exANorm : Normalisation exA where
  R := {exAPair}
  swap_mem := by decide
  children_swap := by decide
  sub := by decide
  cover := by decide
  not_both := by decide

theorem exA_balanced : ∀ T ∈ exA.C, Equiv1 T.1 T.2 := by
  unfold Equiv1; decide

/-- `exA` is a zero-return system: its children are the blocks of `red`. -/
theorem exA_red : ∀ T ∈ exA.C,
    exA.children T = Psc.Reduction.red (subst exA.s T.1) (subst exA.s T.2) := by
  decide

/-- The unique representative of `exANorm`. -/
def exARep : exANorm.Rep := ⟨exAPair, Finset.mem_singleton_self _⟩

theorem exANorm_rep (i : exANorm.Rep) : i = exARep :=
  Subtype.ext (Finset.mem_singleton.1 i.2)

/-- `S = (2)`: both children carry the sign `+1`. -/
theorem exA_ssign (i j : exANorm.Rep) : exANorm.Ssign i j = 2 := by
  obtain rfl := exANorm_rep i
  obtain rfl := exANorm_rep j
  decide

/-- `kw (01, 10) = (1, 0, 0)`, so the column of `Q₂` is nonzero. -/
theorem exA_kw : kw exAPair.1 exAPair.2 = ![1, 0, 0] := by
  funext I; fin_cases I <;> decide

/-- `wedge2_mulVec_kw_rep` on `exA`: `Λ²M · kw (01,10) = 2 • kw (01,10)`. -/
theorem exA_wedge :
    wedge2 ((inc exA.s).map (Nat.cast : ℕ → ℤ)) *ᵥ kw exAPair.1 exAPair.2 =
      (2 : ℤ) • kw exAPair.1 exAPair.2 := by
  have : Subsingleton exANorm.Rep :=
    ⟨fun i j => (exANorm_rep i).trans (exANorm_rep j).symm⟩
  have h := wedge2_mulVec_kw_rep exANorm exA_balanced exARep
  rwa [Fintype.sum_subsingleton _ exARep, exA_ssign] at h

/-- The identity substitution. -/
def idSubst : Fin 3 → List (Fin 3) := fun a => [a]

/-- The irreducible 2-binomially equivalent pair `(0112201, 1200112)`
(`Psc.ConcentrationControls.factors_equiv2`). -/
def wTPair : List (Fin 3) × List (Fin 3) := ([0, 1, 1, 2, 2, 0, 1], [1, 2, 0, 0, 1, 1, 2])

/-- The zero-return system of `wTPair` under the identity: each state is its
own only child. -/
def wT : ChildSystem (Fin 3) :=
  Psc.Reduction.redSystem idSubst (by decide) {wTPair, wTPair.swap} (by decide) (by decide)

/-- `wT` normalised by `R = {wTPair}`, via `Psc.Reduction.redNormalisation`. -/
def wTNorm : Normalisation wT :=
  Psc.Reduction.redNormalisation idSubst (by decide) {wTPair, wTPair.swap} (by decide)
    (by decide) (by decide) {wTPair} (by decide) (by decide) (by decide)

theorem wT_equiv2 : ∀ T ∈ wT.C, Equiv2 T.1 T.2 := by
  unfold Equiv2 Equiv1; decide

theorem wT_irreducible : IrreduciblePair wTPair.1 wTPair.2 := by decide

def wTRep : wTNorm.Rep := ⟨wTPair, Finset.mem_singleton_self _⟩

theorem wTNorm_rep (i : wTNorm.Rep) : i = wTRep :=
  Subtype.ext (Finset.mem_singleton.1 i.2)

/-- `S = (1)`. -/
theorem wT_ssign (i j : wTNorm.Rep) : wTNorm.Ssign i j = 1 := by
  obtain rfl := wTNorm_rep i
  obtain rfl := wTNorm_rep j
  decide

theorem wT_k3_ne : K3 wTPair.1 wTPair.2 0 1 0 = 2 := by decide

/-- `k3_rep` on `wT`: `M^{⊗3} K₃ = K₃`. -/
theorem wT_k3 (a b e : Fin 3) :
    ∑ x, ∑ y, ∑ z, (inc wT.s a x : ℤ) * inc wT.s b y * inc wT.s e z *
      K3 wTPair.1 wTPair.2 x y z = K3 wTPair.1 wTPair.2 a b e := by
  have : Subsingleton wTNorm.Rep :=
    ⟨fun i j => (wTNorm_rep i).trans (wTNorm_rep j).symm⟩
  have h := k3_rep wTNorm wT_equiv2 wTRep a b e
  rwa [Fintype.sum_subsingleton _ wTRep, wT_ssign, one_mul] at h

/-- `0 ↦ 1`, `1 ↦ 0`, `2 ↦ 2`. -/
def exBSubst : Fin 3 → List (Fin 3) := ![[1], [0], [2]]

/-- The 2-binomially equivalent pair `(0110, 1001)`. -/
def exBPair : List (Fin 3) × List (Fin 3) := ([0, 1, 1, 0], [1, 0, 0, 1])

/-- `σ(0110) = 1001`, `σ(1001) = 0110`; the only child of a state is declared
to be its swap.  An algebra-only control: see `exB_reducible`, `exB_not_red`. -/
def exB : ChildSystem (Fin 3) where
  s := exBSubst
  C := {exBPair, exBPair.swap}
  children := fun T => [T.swap]
  top := by decide
  bot := by decide
  closed := by decide
  nonempty := by decide

/-- `exB` normalised by `R = {(0110, 1001)}`. -/
def exBNorm : Normalisation exB where
  R := {exBPair}
  swap_mem := by decide
  children_swap := by decide
  sub := by decide
  cover := by decide
  not_both := by decide

theorem exB_equiv2 : ∀ T ∈ exB.C, Equiv2 T.1 T.2 := by
  unfold Equiv2 Equiv1; decide

/-- The state of `exB` is reducible (zero return after `01 / 10`). -/
theorem exB_reducible : ¬ IrreduciblePair exBPair.1 exBPair.2 := by decide

/-- The declared children of `exB` are not the zero-return blocks. -/
theorem exB_not_red :
    exB.children exBPair ≠ Psc.Reduction.red (subst exB.s exBPair.1) (subst exB.s exBPair.2) := by
  decide

/-- The unique representative of `exBNorm`. -/
def exBRep : exBNorm.Rep := ⟨exBPair, Finset.mem_singleton_self _⟩

theorem exBNorm_rep (i : exBNorm.Rep) : i = exBRep :=
  Subtype.ext (Finset.mem_singleton.1 i.2)

/-- `S = (-1)`: the only child carries the sign `-1`. -/
theorem exB_ssign (i j : exBNorm.Rep) : exBNorm.Ssign i j = -1 := by
  obtain rfl := exBNorm_rep i
  obtain rfl := exBNorm_rep j
  decide

/-- `K₃(0110, 1001)_{010} = 2`, so the column of `Q₃` is nonzero. -/
theorem exB_k3_ne : K3 exBPair.1 exBPair.2 0 1 0 = 2 := by decide

/-- `k3_rep` on `exB`: `M^{⊗3} K₃(0110,1001) = - K₃(0110,1001)`. -/
theorem exB_k3 (a b e : Fin 3) :
    ∑ x, ∑ y, ∑ z, (inc exB.s a x : ℤ) * inc exB.s b y * inc exB.s e z *
      K3 exBPair.1 exBPair.2 x y z = -K3 exBPair.1 exBPair.2 a b e := by
  have : Subsingleton exBNorm.Rep :=
    ⟨fun i j => (exBNorm_rep i).trans (exBNorm_rep j).symm⟩
  have h := k3_rep exBNorm exB_equiv2 exBRep a b e
  rwa [Fintype.sum_subsingleton _ exBRep, exB_ssign, neg_one_mul] at h

end Psc.SignedIntertwiner
