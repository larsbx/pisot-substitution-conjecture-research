/-
# The Parikh intertwiner, the positive left functional, and the cocycle bound

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `thm:parikh` (column
identity of the abelianisation), and the `ρ(S) ≤ β` step of `prop:cocycle`;
`docs/c4-concentration-attack-2026-11-06.md`.

Over a finite alphabet `α` with decidable equality, `Psc.Incidence.inc s` is
the incidence matrix `N a c = |s c|_a` of a substitution `s : α → List α`
(column `c` is the Parikh vector of the image of `c`), and `parikh w a = |w|_a`.

Proved here, in full:

* `parikh_subst`: `parikh (subst s w) = N *ᵥ parikh w` (over `ℕ`), for every
  word `w`;
* `parikh_children_top`, `parikh_children_bot` (`thm:parikh`, column identity):
  in a `Psc.Binomial.ChildSystem`, for every state `T ∈ C`, the Parikh vectors
  of the children of `T` sum, on each track, to `N` applied to the Parikh vector
  of that track of `T`; `parikh_tracks_eq`, `parikh_children_balanced`: when
  `T` is balanced (`Equiv1 T.1 T.2`) the two tracks of `T` have the same Parikh
  vector, hence the two child sums coincide;
* `Lfun_pos` (the positivity step `λ = ℓᵀP_C > 0` in the proof of
  `thm:parikh`): for a strictly positive weight `ℓ : α → ℝ` and
  a nonempty word `w`, `0 < L ℓ w := ∑ a, ℓ a * |w|_a`;
* `Lfun_subst`, `Lfun_children_top`, `Lfun_children_bot`: if `ℓ` is a left
  eigenvector of `N` (as a real matrix), `ℓ ᵥ* N = β • ℓ`, then
  `L ℓ (subst s w) = β * L ℓ w`, and in a child system
  `∑_{U child of T} L ℓ U.i = β * L ℓ T.i` on each track `i`;
* `spectral_bound_of_subinvariant` (`prop:cocycle`, `ρ(S) ≤ β`, abstract
  matrix lemma in row form): for a real matrix `N` with a strictly positive
  row vector `L` that is subinvariant, `(L ᵥ* N) j ≤ β * L j` for every `j`
  (i.e. `λ N ≤ β λ`; the remark after `thm:parikh` writes the same condition
  transposed, `N_C L ≤ β L`), any complex matrix `S` entrywise dominated by `N`
  (`‖S i j‖ ≤ N i j`) and any eigenpair `S *ᵥ x = μ • x` with `x ≠ 0`, we have
  `‖μ‖ ≤ β`.  That the state system of an escaping SCC is subinvariant is
  **not** derived here; subinvariance is a hypothesis;
* `spectral_bound`: the special case `L ᵥ* N = β • L` (a strictly positive
  left eigenvector).

State-indexed matrices of a child system (section `ChildMatrices`, `thm:parikh`
in matrix form), for a `ChildSystem S` over a finite alphabet:

* `State S`, the states `{T // T ∈ S.C}` as a finite type;
* `Nc S`, the state matrix: `Nc S i j` is the number of times `i` occurs among
  the **raw ordered children** of `j` (with multiplicity, no signs).  Caveat:
  this is not the manuscript's representative matrix `N_C = A + B` on
  unordered/normalised states; for a swap-closed `C` (with every `(u, v)` also
  `(v, u)`) `Nc S` is the oriented double cover of it;
* `Pc S`, the Parikh matrix of the top tracks, and `Lc S ℓ`, the state
  functional `λ = ℓᵀ P_C` (`Lc S ℓ j = L ℓ (top track of j)`);
* `sum_children_eq_sum_state`: a sum over the children of a state regrouped by
  state with multiplicity `Nc S`;
* `pc_nc`: `P_C N_C = N P_C` (`Pc S * Nc S = inc S.s * Pc S`);
* `lc_nc`: if `ℓ ᵥ* N = β • ℓ` then `λ N_C = β λ`;
* `lc_pos`: `λ > 0` when `ℓ > 0` and every state has a nonempty top track;
* `spectral_bound_childSystem`: combining these with `spectral_bound`, any
  complex state matrix entrywise dominated by `Nc S` has every eigenvalue of
  modulus at most `β`;
* `perron_root_childSystem`: under the same hypotheses and `C` nonempty, `β`
  is an eigenvalue of `Nc S` (`λ N_C = β λ` with `λ ≠ 0` gives
  `det (N_C - β) = 0`, hence a right eigenvector) and every complex eigenvalue
  has modulus at most `β`, so `ρ(N_C) = β`.

The specific cocycle `S = A - B` of `prop:cocycle` on normalised
representatives, its antisymmetric lift to `Nc S`, and `ρ(S) ≤ β` are in
`PscVerif.SignedCocycle`.

Not proved here: existence of the positive left eigenvector (Perron–Frobenius
for a primitive incidence matrix; it is a hypothesis), and that `β` is the
Perron root of the incidence matrix itself (nonnegativity of `N` is implied by
the domination hypothesis and not assumed separately).
-/
import PscVerif.Incidence
import PscVerif.PerronCore
import PscVerif.ConcentrationAlgebra

namespace Psc.ParikhIntertwiner

open Matrix Psc.Binomial Psc.Incidence

section Parikh

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Parikh vector of a word: `parikh w a = |w|_a`. -/
def parikh (w : List α) : α → ℕ := fun a => w.count a

omit [Fintype α] in
theorem parikh_append (x y : List α) : parikh (x ++ y) = parikh x + parikh y := by
  funext a; simp [parikh]

omit [Fintype α] in
theorem parikh_nil : parikh ([] : List α) = 0 := by
  funext a; simp [parikh]

omit [Fintype α] in
theorem parikh_flatten (ws : List (List α)) :
    parikh ws.flatten = (ws.map parikh).sum := by
  induction ws with
  | nil => simp [parikh_nil]
  | cons w ws ih => simp [List.flatten_cons, parikh_append, ih]

/-- The incidence matrix applied to the Parikh vector of a single letter
recovers the Parikh vector of its image. -/
theorem inc_mulVec_single (s : α → List α) (c : α) :
    (inc s) *ᵥ parikh [c] = parikh (s c) := by
  funext a
  simp only [mulVec, dotProduct, inc_apply, parikh, List.count_singleton']
  rw [Finset.sum_eq_single c]
  · simp
  · intro d _ hd
    have : ¬ c = d := fun h => hd h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ c) h

/-- **Parikh intertwining.** `P(σ w) = N P(w)`. -/
theorem parikh_subst (s : α → List α) (w : List α) :
    parikh (subst s w) = (inc s) *ᵥ parikh w := by
  funext a
  simp only [parikh, count_subst, mulVec, dotProduct]

/-- **`thm:parikh`, column identity, top track.** -/
theorem parikh_children_top (S : ChildSystem α) (T : List α × List α) (hT : T ∈ S.C) :
    ((S.children T).map (fun U => parikh U.1)).sum = (inc S.s) *ᵥ parikh T.1 := by
  rw [← parikh_subst, ← S.top T hT, parikh_flatten, List.map_map]
  rfl

/-- **`thm:parikh`, column identity, bottom track.** -/
theorem parikh_children_bot (S : ChildSystem α) (T : List α × List α) (hT : T ∈ S.C) :
    ((S.children T).map (fun U => parikh U.2)).sum = (inc S.s) *ᵥ parikh T.2 := by
  rw [← parikh_subst, ← S.bot T hT, parikh_flatten, List.map_map]
  rfl

omit [Fintype α] in
/-- A balanced pair has equal Parikh vectors on its two tracks. -/
theorem parikh_tracks_eq {u v : List α} (h : Equiv1 u v) : parikh u = parikh v := by
  funext a; exact h a

/-- For a balanced state the two child sums of Parikh vectors coincide. -/
theorem parikh_children_balanced (S : ChildSystem α) (T : List α × List α) (hT : T ∈ S.C)
    (hbal : Equiv1 T.1 T.2) :
    ((S.children T).map (fun U => parikh U.1)).sum =
      ((S.children T).map (fun U => parikh U.2)).sum := by
  rw [parikh_children_top S T hT, parikh_children_bot S T hT, parikh_tracks_eq hbal]

/-! ### The positive left functional -/

/-- `L ℓ w = ∑ a, ℓ a * |w|_a`, the length functional of the weight `ℓ`. -/
noncomputable def Lfun (ℓ : α → ℝ) (w : List α) : ℝ := ∑ a, ℓ a * (parikh w a : ℝ)

theorem Lfun_append (ℓ : α → ℝ) (x y : List α) :
    Lfun ℓ (x ++ y) = Lfun ℓ x + Lfun ℓ y := by
  simp only [Lfun, parikh_append, Pi.add_apply, Nat.cast_add, mul_add,
    Finset.sum_add_distrib]

theorem Lfun_nil (ℓ : α → ℝ) : Lfun ℓ ([] : List α) = 0 := by
  simp [Lfun, parikh_nil]

theorem Lfun_flatten (ℓ : α → ℝ) (ws : List (List α)) :
    Lfun ℓ ws.flatten = (ws.map (Lfun ℓ)).sum := by
  induction ws with
  | nil => simp [Lfun_nil]
  | cons w ws ih => simp [List.flatten_cons, Lfun_append, ih]

/-- **The positivity step `λ = ℓᵀP_C > 0` in the proof of `thm:parikh`.** A
strictly positive weight gives a strictly positive
length to every nonempty word. -/
theorem Lfun_pos (ℓ : α → ℝ) (hℓ : ∀ a, 0 < ℓ a) (w : List α) (hw : w ≠ []) :
    0 < Lfun ℓ w := by
  obtain ⟨c, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  unfold Lfun
  refine Finset.sum_pos' (fun a _ => mul_nonneg (hℓ a).le (Nat.cast_nonneg _))
    ⟨c, Finset.mem_univ c, ?_⟩
  refine mul_pos (hℓ c) ?_
  have : 0 < parikh (c :: w') c := by
    simp [parikh]
  exact_mod_cast this

/-- **Eigen-identity of the left functional.** If `ℓ ᵥ* N = β • ℓ` then
`L(σ w) = β L(w)`. -/
theorem Lfun_subst (s : α → List α) (ℓ : α → ℝ) (β : ℝ)
    (hℓ : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (w : List α) :
    Lfun ℓ (subst s w) = β * Lfun ℓ w := by
  have hcast : (fun a => (parikh (subst s w) a : ℝ)) =
      (inc s).map (Nat.cast : ℕ → ℝ) *ᵥ (fun a => (parikh w a : ℝ)) := by
    funext a
    rw [parikh_subst]
    exact RingHom.map_mulVec (Nat.castRingHom ℝ) (inc s) (parikh w) a
  have h1 : Lfun ℓ (subst s w) = ℓ ⬝ᵥ (fun a => (parikh (subst s w) a : ℝ)) := rfl
  have h2 : Lfun ℓ w = ℓ ⬝ᵥ (fun a => (parikh w a : ℝ)) := rfl
  rw [h1, h2, hcast, dotProduct_mulVec, hℓ, smul_dotProduct, smul_eq_mul]

/-- Children form, top track: `∑_{U} L(U.1) = β L(T.1)`. -/
theorem Lfun_children_top (S : ChildSystem α) (ℓ : α → ℝ) (β : ℝ)
    (hℓ : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (T : List α × List α) (hT : T ∈ S.C) :
    ((S.children T).map (fun U => Lfun ℓ U.1)).sum = β * Lfun ℓ T.1 := by
  rw [← Lfun_subst S.s ℓ β hℓ, ← S.top T hT, Lfun_flatten, List.map_map]
  rfl

/-- Children form, bottom track: `∑_{U} L(U.2) = β L(T.2)`. -/
theorem Lfun_children_bot (S : ChildSystem α) (ℓ : α → ℝ) (β : ℝ)
    (hℓ : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (T : List α × List α) (hT : T ∈ S.C) :
    ((S.children T).map (fun U => Lfun ℓ U.2)).sum = β * Lfun ℓ T.2 := by
  rw [← Lfun_subst S.s ℓ β hℓ, ← S.bot T hT, Lfun_flatten, List.map_map]
  rfl

end Parikh

/-! ### The spectral bound `ρ(S) ≤ β` -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`prop:cocycle`, `ρ(S) ≤ β`, subinvariant form** (an abstract matrix
lemma).  If the row vector `L` is strictly positive and subinvariant for `N` in
row form, `λ N ≤ β λ`, i.e. `(L ᵥ* N) j ≤ β * L j` for every `j`, and the
complex matrix `S` is entrywise dominated by `N`, then every eigenvalue `μ` of
`S` (with eigenvector `x ≠ 0`) satisfies `‖μ‖ ≤ β`.  The escape/leak remark
after `thm:parikh` writes the subinvariance transposed (`N_C L ≤ β L` when
children may leave `C`); that an escaping SCC is subinvariant is not derived
here. -/
theorem spectral_bound_of_subinvariant (N : Matrix ι ι ℝ) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : ∀ j, (L ᵥ* N) j ≤ β * L j) (S : Matrix ι ι ℂ)
    (hS : ∀ i j, ‖S i j‖ ≤ N i j) (x : ι → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hx : S *ᵥ x = μ • x) :
    ‖μ‖ ≤ β := by
  set a : ι → ℝ := fun i => ‖x i‖
  -- entrywise `‖μ‖ a ≤ N a`
  have hrow : ∀ i, ‖μ‖ * a i ≤ (N *ᵥ a) i := by
    intro i
    obtain ⟨h1, h2, h3⟩ := Psc.PerronCore.row_chain N S hS x μ hx i
    rw [h1]; exact h2.trans h3
  -- pair with `L`: `‖μ‖ (L ⬝ a) ≤ L ⬝ (N a) = (L N) ⬝ a ≤ β (L ⬝ a)`
  have h2 : ‖μ‖ * (L ⬝ᵥ a) ≤ L ⬝ᵥ (N *ᵥ a) := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hrow i) (hL i).le
  have h3 : L ⬝ᵥ (N *ᵥ a) ≤ β * (L ⬝ᵥ a) := by
    rw [dotProduct_mulVec]; simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hLN j) (norm_nonneg _)
  -- `L ⬝ |x| > 0`
  have hpos : 0 < L ⬝ᵥ a := by
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hL i).le (norm_nonneg _))
      ⟨j, Finset.mem_univ j, mul_pos (hL j) (norm_pos_iff.2 hj)⟩
  exact le_of_mul_le_mul_right (h2.trans h3) hpos

/-- **`prop:cocycle`, `ρ(S) ≤ β`.**  If `N` has a strictly positive left
eigenvector `L ᵥ* N = β • L` and the complex matrix `S` is entrywise dominated
by `N`, then every eigenvalue `μ` of `S` (with eigenvector `x ≠ 0`) satisfies
`‖μ‖ ≤ β`.  The special case `L ᵥ* N = β • L` of
`spectral_bound_of_subinvariant`. -/
theorem spectral_bound (N : Matrix ι ι ℝ) (L : ι → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* N = β • L) (S : Matrix ι ι ℂ) (hS : ∀ i j, ‖S i j‖ ≤ N i j)
    (x : ι → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hx : S *ᵥ x = μ • x) :
    ‖μ‖ ≤ β :=
  spectral_bound_of_subinvariant N L hL β (fun j => by rw [hLN]; rfl) S hS x hx0 μ hx

end Spectral

/-! ### State-indexed matrices of a child system (`thm:parikh` in matrix form) -/

section ChildMatrices

variable {α : Type*} [Fintype α] [DecidableEq α] (S : ChildSystem α)

/-- The states of a child system, as a finite type. -/
abbrev State := {T // T ∈ S.C}

/-- The state matrix `N_C`: `Nc i j` is the number of times `i` occurs among the
raw ordered children of `j` (with multiplicity, no signs).  For a swap-closed
`C` this is the oriented double cover of the manuscript's representative matrix
`N_C = A + B`, not that matrix itself. -/
def Nc : Matrix (State S) (State S) ℕ := Matrix.of fun i j => (S.children j.1).count i.1

omit [Fintype α] in
@[simp] theorem Nc_apply (i j : State S) : Nc S i j = (S.children j.1).count i.1 := rfl

/-- The state Parikh matrix `P_C`: column `j` is the Parikh vector of the top
track of `j`. -/
def Pc : Matrix α (State S) ℕ := Matrix.of fun a j => j.1.1.count a

omit [Fintype α] in
@[simp] theorem Pc_apply (a : α) (j : State S) : Pc S a j = j.1.1.count a := rfl

/-- The state functional `λ = ℓᵀ P_C`: `Lc ℓ j = L ℓ (top track of j)`. -/
noncomputable def Lc (ℓ : α → ℝ) : State S → ℝ := fun j => Lfun ℓ j.1.1

omit [Fintype α] in
/-- A sum over the children of a state, regrouped by state with multiplicity. -/
theorem sum_children_eq_sum_state {M : Type*} [AddCommMonoid M]
    (f : List α × List α → M) (j : State S) :
    ((S.children j.1).map f).sum = ∑ i : State S, Nc S i j • f i.1 := by
  simp only [Nc_apply]
  rw [Finset.sum_list_map_count (S.children j.1) f, Finset.sum_coe_sort S.C
    (fun x : List α × List α => ((S.children j.1).count x • f x : M))]
  convert Finset.sum_subset (s₁ := (S.children j.1).toFinset) (s₂ := S.C)
    (f := fun x => (S.children j.1).count x • f x) ?_ ?_ using 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    -- the two sides count with different (lawful) `BEq` instances on pairs
    congr 1; simp only [List.count_eq_countP]; congr 1; funext x; simp
  · intro U hU
    exact S.closed j.1 j.2 U (List.mem_toFinset.1 hU)
  · intro U _ hU
    rw [List.count_eq_zero_of_not_mem (mt List.mem_toFinset.2 hU), zero_smul]

/-- **`thm:parikh`, matrix form.**  `P_C N_C = N P_C`. -/
theorem pc_nc : Pc S * Nc S = inc S.s * Pc S := by
  ext a j
  have h := congrFun ((sum_children_eq_sum_state S (fun U => parikh U.1) j).symm.trans
    (parikh_children_top S j.1 j.2)) a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, parikh,
    inc_apply] at h
  simp only [Matrix.mul_apply, Pc_apply, inc_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Left eigen-identity of the state functional.**  If `ℓ ᵥ* N = β • ℓ` then
`λ N_C = β λ` for `λ = Lc ℓ`. -/
theorem lc_nc (ℓ : α → ℝ) (β : ℝ) (hℓ : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    Lc S ℓ ᵥ* (Nc S).map (Nat.cast : ℕ → ℝ) = β • Lc S ℓ := by
  funext j
  rw [Pi.smul_apply, smul_eq_mul, Lc, ← Lfun_children_top S ℓ β hℓ j.1 j.2,
    sum_children_eq_sum_state S (fun U => Lfun ℓ U.1) j]
  simp only [vecMul, dotProduct, Matrix.map_apply, nsmul_eq_mul, Lc, Nc_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The state functional is strictly positive when `ℓ` is and every state has a
nonempty top track. -/
theorem lc_pos (ℓ : α → ℝ) (hℓ : ∀ a, 0 < ℓ a) (hne : ∀ T ∈ S.C, T.1 ≠ []) (j : State S) :
    0 < Lc S ℓ j :=
  Lfun_pos ℓ hℓ j.1.1 (hne j.1 j.2)

/-- **`prop:cocycle`, `ρ(S) ≤ β`, for a child system.**  If `ℓ > 0` is a left
eigenvector of the incidence matrix, `ℓ ᵥ* N = β • ℓ`, and every state has a
nonempty top track, then any complex state matrix `S'` entrywise dominated by
`N_C` (`‖S' i j‖ ≤ Nc i j`) has every eigenvalue of modulus at most `β`.

The cocycle matrix of `prop:cocycle` (signed children, normalised
representatives) is treated in `PscVerif.SignedCocycle`
(`Psc.SignedCocycle.Normalisation.cocycle_spectral_bound`, via its
antisymmetric lift to `N_C`). -/
theorem spectral_bound_childSystem (ℓ : α → ℝ) (hℓ : ∀ a, 0 < ℓ a)
    (hne : ∀ T ∈ S.C, T.1 ≠ []) (β : ℝ)
    (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (S' : Matrix (State S) (State S) ℂ) (hS' : ∀ i j, ‖S' i j‖ ≤ Nc S i j)
    (x : State S → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hx : S' *ᵥ x = μ • x) :
    ‖μ‖ ≤ β :=
  spectral_bound ((Nc S).map (Nat.cast : ℕ → ℝ)) (Lc S ℓ) (lc_pos S ℓ hℓ hne) β
    (lc_nc S ℓ β hℓN) S' (fun i j => by simpa using hS' i j) x hx0 μ hx

/-- **The Perron root of the raw state matrix is `β`.**  Under the hypotheses of
`spectral_bound_childSystem` and with `C` nonempty, `β` is an eigenvalue of
`Nc` (the positive left eigenvector `λ` of `lc_nc` makes `β` a root of `χ_Nc`,
hence a right eigenvalue), and every complex eigenvalue of `Nc` has modulus at
most `β`; so `ρ(Nc) = β`.  `Nc` counts raw ordered children (for a swap-closed
system, the oriented double cover); `ρ(Nrep) = β` for the manuscript's
representative matrix `N_C = A + B` is not derived here. -/
theorem perron_root_childSystem (ℓ : α → ℝ) (hℓ : ∀ a, 0 < ℓ a)
    (hne : ∀ T ∈ S.C, T.1 ≠ []) (β : ℝ)
    (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hC : S.C.Nonempty) :
    (∃ v : State S → ℝ, v ≠ 0 ∧ (Nc S).map (Nat.cast : ℕ → ℝ) *ᵥ v = β • v) ∧
      ∀ x : State S → ℂ, x ≠ 0 → ∀ μ : ℂ,
        (Nc S).map (Nat.cast : ℕ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ β := by
  refine ⟨?_, fun x hx0 μ hx =>
    spectral_bound_childSystem S ℓ hℓ hne β hℓN _ (fun i j => by simp) x hx0 μ hx⟩
  obtain ⟨T, hT⟩ := hC
  have hL0 : Lc S ℓ ≠ 0 := fun h => (lc_pos S ℓ hℓ hne ⟨T, hT⟩).ne' (congrFun h _)
  obtain ⟨v, hv0, hv⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot _ β
    (Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ β (Lc S ℓ) hL0 (lc_nc S ℓ β hℓN))
  exact ⟨v, hv0, hv⟩

end ChildMatrices

end Psc.ParikhIntertwiner
