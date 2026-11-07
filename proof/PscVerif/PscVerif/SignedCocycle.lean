/-
# The signed cocycle on normalised representatives

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, §`sec:orientation` and
`prop:cocycle` (the bound `ρ(S) ≤ β`); `docs/c4-concentration-attack-2026-11-06.md`.

Setting.  `S : Psc.Binomial.ChildSystem α` over a finite alphabet, with its raw
ordered state matrix `Psc.ParikhIntertwiner.Nc S` (`Nc i j` = number of times
`i` occurs among the children of `j`).  A `Normalisation S` records a choice
of normalised representatives (any choice; the manuscript's lexicographic
choice is one):

* `swap_mem`: `C` is swap-closed (`T ∈ C → T.swap ∈ C`);
* `children_swap`: the children of `T.swap` are the swaps of the children of
  `T`, in order (swapping a parent's sides swaps all its children's sides);
* `R ⊆ C` is a set of representatives: every `T ∈ C` has `T ∈ R` or
  `T.swap ∈ R` (`cover`), never both (`not_both`; for a noncoincident `T`,
  `T ≠ T.swap`).  So `C = R ⊔ swap R` (`C_eq`), and `C` is coincidence-free
  (`noncoincident`: no `T ∈ C` has `T.1 = T.2`).

Indexing by the representatives `Rep = {T // T ∈ R}`, with `A i j` the number of
times `i` occurs among the children of `j` (sign `+1`) and `B i j` the number
of times `i.swap` occurs (sign `-1`), the manuscript's matrices are
`N_C = A + B` (`Nrep`, over `ℕ`) and `S = A - B` (`Ssign`, over `ℤ`).

Proved here, in full:

* `lift_eigen`, `lift_ne_zero` (the lift to the raw ordered system): if
  `Ssign *ᵥ x = μ • x` over a commutative ring, the antisymmetric lift
  `x̃ T = x T` (`T ∈ R`), `x̃ T = - x T.swap` (`T.swap ∈ R`) satisfies
  `Nc *ᵥ x̃ = μ • x̃`, and `x̃ ≠ 0` when `x ≠ 0`.  So every eigenvalue of the
  cocycle `S` is an eigenvalue of the oriented double cover `Nc`;
* **`cocycle_spectral_bound`** (`prop:cocycle`, `ρ(S) ≤ β`): under the
  hypotheses of `Psc.ParikhIntertwiner.spectral_bound_childSystem` (`ℓ > 0`,
  `ℓ ᵥ* N = β • ℓ`, nonempty top tracks), every complex eigenvalue of `Ssign`
  has modulus at most `β`;
* `rep_eigen`, `lrep_pos` (`thm:parikh` on representatives): if the states are
  balanced, `λ N_C = β λ` for `λ j = L ℓ (top track of j)`, and `λ > 0`;
  `ssign_abs_le`: `|S i j| ≤ N_C i j` entrywise; `cocycle_spectral_bound_rep`
  combines them with `Psc.ParikhIntertwiner.spectral_bound` into a second
  proof of the bound on the representatives, under balance;
* Non-vacuity, `thueMorseNorm`, `thueMorse_nrep`, `thueMorse_ssign`,
  `thueMorse_left_eigen`: the Thue–Morse child system `Psc.Binomial.thueMorse`
  (`0 ↦ 01`, `1 ↦ 10`, `C = {(01,10), (10,01)}`) with `R = {(01,10)}` meets
  every hypothesis of `Normalisation` (by `decide`), with `N_C = (2)`,
  `S = (0)`, and the positive left eigenvector `ℓ = (1, 1)`, `β = 2`;
  `thueMorse_cocycle_bound` instantiates the bound and `thueMorse_ssign_ne_nrep`
  pins the sign convention `S ≠ N_C`.  (Here `S = 0`, so the bound itself is
  trivial on this example; no control with a nonzero eigenvalue of `S` is
  included.)

Not proved here: the gauge / voltage-graph statements of `prop:cocycle`, the
strict inequality `ρ(S) < β` when a parent-child pair occurs with both signs,
the equality case (`Psc.Wielandt` treats it abstractly), and the existence of
the positive left eigenvector `ℓ` (a hypothesis).  `swap_mem` and
`children_swap` are hypotheses here; in the manuscript they follow from
computing children by zero-return reduction.  That a different choice of `R`
conjugates `S` by a diagonal `±1` matrix is not proved.
-/
import PscVerif.ParikhIntertwiner

namespace Psc.SignedCocycle

open Matrix Psc.Binomial Psc.Incidence Psc.ParikhIntertwiner

variable {α : Type*} [DecidableEq α]

/-- Normalised representatives of a swap-closed child system (§`sec:orientation`). -/
structure Normalisation (S : ChildSystem α) where
  /-- The normalised representatives. -/
  R : Finset (List α × List α)
  swap_mem : ∀ T ∈ S.C, T.swap ∈ S.C
  children_swap : ∀ T ∈ S.C, S.children T.swap = (S.children T).map Prod.swap
  sub : R ⊆ S.C
  cover : ∀ T ∈ S.C, T ∈ R ∨ T.swap ∈ R
  not_both : ∀ T ∈ R, T.swap ∉ R

namespace Normalisation

variable {S : ChildSystem α} (P : Normalisation S)

/-- The representatives, as a finite type. -/
abbrev Rep := {T // T ∈ P.R}

/-- `A i j`: occurrences of `i` (sign `+1`) among the children of `j`. -/
def A : Matrix P.Rep P.Rep ℕ := Matrix.of fun i j => (S.children j.1).count i.1

/-- `B i j`: occurrences of `i.swap` (sign `-1`) among the children of `j`. -/
def B : Matrix P.Rep P.Rep ℕ := Matrix.of fun i j => (S.children j.1).count i.1.swap

/-- The representative state matrix `N_C = A + B`. -/
def Nrep : Matrix P.Rep P.Rep ℕ := P.A + P.B

/-- The cocycle matrix `S = A - B`. -/
def Ssign : Matrix P.Rep P.Rep ℤ := Matrix.of fun i j => (P.A i j : ℤ) - P.B i j

/-- `C = R ⊔ swap R`. -/
theorem C_eq : S.C = P.R ∪ P.R.image Prod.swap := by
  ext T
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hT
    exact (P.cover T hT).imp id fun h => ⟨T.swap, h, Prod.swap_swap T⟩
  · rintro (h | ⟨U, hU, rfl⟩)
    · exact P.sub h
    · exact P.swap_mem U (P.sub hU)

include P in
/-- A normalisation forces `C` to be coincidence-free: a coincident state
`T = T.swap` would lie in `R` together with its swap. -/
theorem noncoincident : ∀ T ∈ S.C, T.1 ≠ T.2 := by
  intro T hT h
  have hs : T.swap = T := Prod.ext h.symm h
  rcases P.cover T hT with hR | hR
  · exact P.not_both T hR (hs ▸ hR)
  · exact P.not_both _ hR (by rw [Prod.swap_swap, ← hs]; exact hR)

theorem disjoint_image : Disjoint P.R (P.R.image Prod.swap) := by
  rw [Finset.disjoint_left]
  rintro T hT hT'
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hT'
  exact P.not_both U hU hT

/-- A sum over the states, split into representatives and their swaps. -/
theorem sum_state {M : Type*} [AddCommMonoid M] [Fintype α]
    (F : List α × List α → M) :
    ∑ U : State S, F U.1 = ∑ i : P.Rep, (F i.1 + F i.1.swap) := by
  rw [Finset.sum_coe_sort S.C F, P.C_eq, Finset.sum_union P.disjoint_image,
    Finset.sum_image fun x _ y _ h => Prod.swap_injective h, ← Finset.sum_add_distrib,
    ← Finset.sum_coe_sort P.R]

/-- The children of a swapped representative count the swapped pair. -/
theorem count_children_swap (i : P.Rep) (V : List α × List α) :
    (S.children i.1.swap).count V = (S.children i.1).count V.swap := by
  rw [P.children_swap _ (P.sub i.2),
    ← List.count_map_of_injective _ _ Prod.swap_injective V.swap, Prod.swap_swap]

/-! ### The antisymmetric lift -/

section Lift

variable {K : Type*} [CommRing K]

/-- The antisymmetric extension of `x` to all pairs: `x V` on `R`, `- x V.swap`
on `swap R`, `0` elsewhere. -/
def anti (x : P.Rep → K) (V : List α × List α) : K :=
  if h : V ∈ P.R then x ⟨V, h⟩ else if h' : V.swap ∈ P.R then -x ⟨V.swap, h'⟩ else 0

theorem anti_rep (x : P.Rep → K) (i : P.Rep) : P.anti x i.1 = x i := dite_eq_left i.2

theorem anti_swap_rep (x : P.Rep → K) (i : P.Rep) : P.anti x i.1.swap = -x i := by
  rw [anti, dite_eq_right (P.not_both i.1 i.2), dite_eq_left (by simp)]
  rfl

/-- The antisymmetric lift `x̃` of `x` to the raw ordered states. -/
def lift (x : P.Rep → K) : State S → K := fun T => P.anti x T.1

theorem ssign_cast (i j : P.Rep) :
    ((P.Ssign i j : ℤ) : K) =
      ((S.children j.1).count i.1 : K) - (S.children j.1).count i.1.swap := by
  simp [Ssign, A, B]

variable [Fintype α]

/-- `N_C x̃ = Σ_i (|ch i|_T - |ch i|_{T.swap}) x i`. -/
theorem mulVec_lift (x : P.Rep → K) (T : State S) :
    ((Nc S).map (Nat.cast : ℕ → K) *ᵥ P.lift x) T =
      ∑ i : P.Rep,
        (((S.children i.1).count T.1 : K) - (S.children i.1).count T.1.swap) * x i := by
  simp only [mulVec, dotProduct, Matrix.map_apply, Nc_apply, lift]
  rw [P.sum_state fun V => ((S.children V).count T.1 : K) * P.anti x V]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [P.anti_rep, P.anti_swap_rep, P.count_children_swap]
  ring

/-- **The lift.**  An eigenvector of the cocycle `S` lifts antisymmetrically to an
eigenvector of the raw ordered state matrix `N_C`, with the same eigenvalue. -/
theorem lift_eigen (x : P.Rep → K) (μ : K)
    (hx : P.Ssign.map (Int.cast : ℤ → K) *ᵥ x = μ • x) :
    (Nc S).map (Nat.cast : ℕ → K) *ᵥ P.lift x = μ • P.lift x := by
  funext T
  rw [P.mulVec_lift, Pi.smul_apply, smul_eq_mul]
  by_cases h : T.1 ∈ P.R
  · have := congrFun hx ⟨T.1, h⟩
    simp only [mulVec, dotProduct, Matrix.map_apply, P.ssign_cast, Pi.smul_apply,
      smul_eq_mul] at this
    rw [this, lift, anti, dite_eq_left h]
  · have h' := (P.cover T.1 T.2).resolve_left h
    have := congrFun hx ⟨T.1.swap, h'⟩
    simp only [mulVec, dotProduct, Matrix.map_apply, P.ssign_cast, Pi.smul_apply,
      smul_eq_mul, Prod.swap_swap] at this
    rw [lift, anti, dite_eq_right h, dite_eq_left h', mul_neg, ← this,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype α] in
theorem lift_ne_zero (x : P.Rep → K) (hx0 : x ≠ 0) : P.lift x ≠ 0 := by
  intro h
  apply hx0
  funext i
  have := congrFun h ⟨i.1, P.sub i.2⟩
  rwa [lift, P.anti_rep] at this

end Lift

variable [Fintype α]

/-- **`prop:cocycle`, `ρ(S) ≤ β`.**  Under the hypotheses of
`spectral_bound_childSystem` (`ℓ > 0` with `ℓ ᵥ* N = β • ℓ`, nonempty top
tracks), every complex eigenvalue of the cocycle matrix `S = A - B` on the
normalised representatives has modulus at most `β`. -/
theorem cocycle_spectral_bound (ℓ : α → ℝ) (hℓ : ∀ a, 0 < ℓ a)
    (hne : ∀ T ∈ S.C, T.1 ≠ []) (β : ℝ)
    (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (x : P.Rep → ℂ) (hx0 : x ≠ 0) (μ : ℂ)
    (hx : P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) :
    ‖μ‖ ≤ β :=
  spectral_bound_childSystem S ℓ hℓ hne β hℓN _ (fun i j => by simp) (P.lift x)
    (P.lift_ne_zero x hx0) μ (P.lift_eigen x μ hx)

/-! ### `thm:parikh` on the representatives -/

/-- The functional `λ j = L ℓ (top track of j)` on the representatives. -/
noncomputable def Lrep (ℓ : α → ℝ) : P.Rep → ℝ := fun j => Lc S ℓ ⟨j.1, P.sub j.2⟩

theorem lrep_pos (ℓ : α → ℝ) (hℓ : ∀ a, 0 < ℓ a) (hne : ∀ T ∈ S.C, T.1 ≠ [])
    (j : P.Rep) : 0 < P.Lrep ℓ j :=
  lc_pos S ℓ hℓ hne _

/-- **Representative eigen-identity** `λ N_C = β λ`: balanced tracks have equal
Parikh vectors, so a child counted with either sign contributes the same
`L ℓ`. -/
theorem rep_eigen (ℓ : α → ℝ) (β : ℝ)
    (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) :
    P.Lrep ℓ ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • P.Lrep ℓ := by
  funext j
  have h := congrFun (lc_nc S ℓ β hℓN) ⟨j.1, P.sub j.2⟩
  simp only [vecMul, dotProduct, Matrix.map_apply, Nc_apply, Lc, Pi.smul_apply,
    smul_eq_mul] at h ⊢
  rw [P.sum_state fun V => Lfun ℓ V.1 * ((S.children j.1).count V : ℝ)] at h
  simp only [Lrep, Lc]
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : Lfun ℓ i.1.swap.1 = Lfun ℓ i.1.1 := by
    simp only [Prod.fst_swap, Lfun, parikh_tracks_eq (hbal i.1 (P.sub i.2))]
  simp only [Nrep, A, B, Matrix.add_apply, Matrix.of_apply, Nat.cast_add, hL]
  ring

omit [Fintype α] in
/-- `|S| ≤ N_C` entrywise. -/
theorem ssign_abs_le (i j : P.Rep) : |P.Ssign i j| ≤ P.Nrep i j := by
  simp only [Ssign, Nrep, Matrix.of_apply, Matrix.add_apply, Nat.cast_add]
  rw [abs_le]
  constructor <;> omega

/-- **`ρ(S) ≤ β` on the representatives directly**, for balanced states: the
abstract bound `Psc.ParikhIntertwiner.spectral_bound` applied to `N_C = A + B`
with `λ = Lrep ℓ` (`rep_eigen`, `lrep_pos`) and `|S| ≤ N_C` (`ssign_abs_le`).
A second route to `cocycle_spectral_bound`, avoiding the double cover. -/
theorem cocycle_spectral_bound_rep (ℓ : α → ℝ) (hℓ : ∀ a, 0 < ℓ a)
    (hne : ∀ T ∈ S.C, T.1 ≠ []) (β : ℝ)
    (hℓN : ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hbal : ∀ T ∈ S.C, Equiv1 T.1 T.2) (x : P.Rep → ℂ) (hx0 : x ≠ 0) (μ : ℂ)
    (hx : P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) :
    ‖μ‖ ≤ β :=
  spectral_bound (P.Nrep.map (Nat.cast : ℕ → ℝ)) (P.Lrep ℓ) (P.lrep_pos ℓ hℓ hne) β
    (P.rep_eigen ℓ β hℓN hbal) _ (fun i j => by
      have h := P.ssign_abs_le i j
      simp only [Matrix.map_apply, Complex.norm_intCast]
      exact_mod_cast h) x hx0 μ hx

end Normalisation

/-! ### Non-vacuity: Thue–Morse -/

/-- The Thue–Morse child system normalised by `R = {(01, 10)}`. -/
def thueMorseNorm : Normalisation thueMorse where
  R := {tmPair}
  swap_mem := by decide
  children_swap := by decide
  sub := by decide
  cover := by decide
  not_both := by decide

/-- The only representative is `(01, 10)`. -/
theorem thueMorseNorm_rep (i : thueMorseNorm.Rep) :
    i = ⟨tmPair, Finset.mem_singleton_self _⟩ :=
  Subtype.ext (Finset.mem_singleton.1 i.2)

/-- `N_C = (2)`: each state has the two children `(01,10)`, `(10,01)`. -/
theorem thueMorse_nrep (i j : thueMorseNorm.Rep) : thueMorseNorm.Nrep i j = 2 := by
  obtain rfl := thueMorseNorm_rep i
  obtain rfl := thueMorseNorm_rep j
  rfl

/-- `S = (0)`: the two children carry opposite signs. -/
theorem thueMorse_ssign (i j : thueMorseNorm.Rep) : thueMorseNorm.Ssign i j = 0 := by
  obtain rfl := thueMorseNorm_rep i
  obtain rfl := thueMorseNorm_rep j
  rfl

/-- `ℓ = (1, 1)` is a positive left eigenvector of the Thue–Morse incidence
matrix with `β = 2`, so `cocycle_spectral_bound` applies to `thueMorseNorm`. -/
theorem thueMorse_left_eigen :
    (fun _ => (1 : ℝ)) ᵥ* (inc thueMorse.s).map (Nat.cast : ℕ → ℝ) =
      (2 : ℝ) • fun _ => 1 := by
  funext c
  fin_cases c <;>
    simp [vecMul, dotProduct, Fin.sum_univ_two, thueMorse, thueMorseSubst] <;> norm_num

/-- `cocycle_spectral_bound` instantiated on Thue–Morse (`ℓ = (1,1)`, `β = 2`). -/
theorem thueMorse_cocycle_bound (x : thueMorseNorm.Rep → ℂ) (hx0 : x ≠ 0) (μ : ℂ)
    (hx : thueMorseNorm.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) : ‖μ‖ ≤ 2 :=
  thueMorseNorm.cocycle_spectral_bound (fun _ => 1) (fun _ => one_pos)
    (by decide) 2 thueMorse_left_eigen x hx0 μ hx

/-- The sign convention is pinned: on Thue–Morse `S = A - B ≠ A + B = N_C`. -/
theorem thueMorse_ssign_ne_nrep (i j : thueMorseNorm.Rep) :
    thueMorseNorm.Ssign i j ≠ thueMorseNorm.Nrep i j := by
  rw [thueMorse_ssign, thueMorse_nrep]; decide

end Psc.SignedCocycle
