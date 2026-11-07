/-
# The orientation cocycle: gauge criterion, strict bound, equality case

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `prop:cocycle` (the gauge
criterion, and the clauses after `ρ(S) ≤ β`: the strict inequality when a
parent–child pair occurs with both signs, the primitive equality case) and
§`sec:orientation` (the choice of normalised representatives);
`docs/c4-concentration-attack-2026-11-06.md` §8.

Setting.  `P : Psc.SignedCocycle.Normalisation S` for a child system `S`, with
`A i j` (resp. `B i j`) the number of children of `j` equal to `i` (resp.
`i.swap`), `N_C = A + B` (`Nrep`) and `S = A - B` (`Ssign`) on the
representatives `Rep`.  The spectral hypotheses are those of `Psc.Wielandt`:
`hSC : StronglyConnected (N_C cast to ℝ)` and a positive left eigenvector `L`,
`L ᵥ* N_C = β • L`; an eigenvalue of `S` is a pair `x ≠ 0`, `S x = μ x` over `ℂ`.
Primitivity is `hprim : ∃ k, ∀ i j, 0 < (N_C ^ k) i j`; `k = 0` is allowed (it
occurs only for one representative), so this is weaker than `∃ k ≥ 1`, which
`nrep_stronglyConnected` takes.

Proved here, in full:

* abstract, over any finite index type: `pow_apply_of_twist`
  (`(c D N D⁻¹)^k = c^k D N^k D⁻¹` entrywise), `phase_real`,
  **`extremal_eq_sign_mul`** (Wielandt's `S = c D N D⁻¹` with `S` real and
  closed walks of two consecutive lengths `k`, `k+1` at one vertex force
  `c = ±1`, i.e. `μ = ±β`), `primitive_extremal` (with `N ^ k > 0`: moreover
  `S = s D N D`, via `Psc.Wielandt.gauge_of_real`), `stronglyConnected_of_pow_pos`;
* (a) strict inequality: `sign_pure_of_extremal` (in the equality case
  `|S| = N_C`, i.e. `A i j = 0 ∨ B i j = 0` for all `i, j`) and
  **`cocycle_spectral_strict`**: if `A i j > 0` and `B i j > 0` for some `i, j`,
  every complex eigenvalue of `S` has modulus `< β`;
* (b) primitive equality case: **`cocycle_primitive_extremal`**: if moreover
  `hprim` and `‖μ‖ = β`, then `μ = s β` and `S i j = s D i N_C i j D j` with
  `s = ±1`, `D i = ±1` (integers); `cocycle_primitive_eigenvalue`
  (`μ = β ∨ μ = -β`), `cocycle_primitive_gauge` (`μ = β` with a gauge, or
  `μ = -β` with an anti-gauge); `nrep_stronglyConnected` (`N_C ^ k > 0` with
  `k ≥ 1` implies `hSC`);
* (c) gauges.  The gauge equation: `IsGauge`, `IsAntiGauge`; `isGauge_iff`
  (`g` is a gauge iff `S i j = g i N_C i j g j`), `isAntiGauge_iff`
  (`S i j = - g i N_C i j g j`), the matrix forms `ssign_eq_diagonal_iff`,
  `exists_gauge_iff` (`S = D N_C D`, `D = diag g`), `exists_antiGauge_iff`
  (`S = - D N_C D`); `not_gauge_of_both`; `diag_conj_eigen`;
  `extremal_of_gauge` (`Rep` nonempty and `L`, no `hSC`, no `hprim`: a gauge or
  an anti-gauge gives an eigenvalue `±β`); **`cocycle_extremal_iff`** (`Rep`
  nonempty, `hSC`, `hprim`: `S` has an eigenvalue of modulus `β` iff a gauge or
  an anti-gauge exists).
  The gauge criterion of `prop:cocycle`: `SignedWalk` (walks of the child graph
  with their sign product), `SignedWalk.sign`, `SignedWalk.append`,
  `exists_signedWalk`, `IsGauge.walk`, `IsGauge.closed_walk`;
  **`exists_gauge_iff_closed_walks`** (`hSC`: a gauge exists iff every closed
  walk has sign product `+1`); the walk count: `walkCount_succ`,
  `walkCount_nonneg` (`|S ^ n| ≤ N_C ^ n`), `SignedWalk.count_pos`,
  `signedWalk_of_pos`, `signedWalk_iff_pos` (a walk `a → b` of length `n` and
  sign `s` exists iff `(N_C ^ n) b a + s (S ^ n) b a > 0`),
  **`closed_walks_iff_pow_diag`** (no `hSC`: every closed walk is positive iff
  `(S ^ n) a a = (N_C ^ n) a a` for all `n, a`), **`exists_gauge_iff_pow_diag`**;
* (d) choice of representatives: `toRep`, `repEquiv`, `repSign`,
  `counts_repEquiv`, `nrep_repEquiv`, `ssign_repEquiv`,
  **`choice_of_representatives`** (`e : R₁ ≃ R₂`, `δ = ±1` with
  `S₂ (e i) (e j) = δ i δ j S₁ i j`, `N₂ (e i) (e j) = N₁ i j`),
  `ssign_eq_reindex`, `charpoly_ssign_eq` (`χ_S` is independent of `R`),
  `diag_conj_transfer`, `exists_gauge_congr`, `exists_antiGauge_congr`;
* non-vacuity controls (`oneRep_hyps`, `oneRep_eigen` for one-representative
  systems; `sum_of_two`, `stronglyConnected_of_two` for two):
  Thue–Morse `thueMorseNorm` (`A = B = (1)`, `S = 0`, `N_C = (2)`):
  `thueMorse_strict` with `thueMorse_eigen`, `thueMorse_no_gauge`,
  `thueMorse_neg_walk` (a closed walk of sign `-1`), `thueMorse_not_extremal`;
  `exA` (`S = N_C = (2)`, `μ = β = 2`): `exA_sign_pure`,
  `exA_primitive_extremal` (with `s = 1`), `exA_isGauge`, `exA_extremal`,
  `exA_pow_diag`; `exB` (`S = -N_C = (-1)`, `μ = -β = -1`):
  `exB_primitive_gauge` (its anti-gauge branch), `exB_isAntiGauge`;
  `fin2_primitive_extremal` (abstract `N = (1 1; 1 1)`, `Sr = (1 -1; -1 1)`,
  `μ = β = 2`: the conclusion holds, and every `D` it can return has
  `D 0 = -D 1`); `qNorm` (the permutation `0 ↦ 2, 1 ↦ 3, 2 ↦ 0, 3 ↦ 1` with
  `R = {(01,10), (32,23)}`, `S = -N_C`): `qNorm_sc`, `qNorm_gauge` (the
  non-constant gauge `(1, -1)`; every gauge is non-constant; the constant sign
  is an anti-gauge; every closed walk is positive); `twoSys` (zero-return
  system of `(0101,1010)`, `(01,10)` under the identity) with
  `R₁ = {(0101,1010), (01,10)}`, `R₂ = {(0101,1010), (10,01)}`: `two_ssign`
  (`S₁ = 2`, `S₂ = -2`, `δ = -1` at the off-diagonal entry, by `decide`);
* counter-calibrations (a hypothesis cannot be dropped): `neg_sc_strict`
  (`bNorm`: `R = {(0110,1001), (01,10)}` under the identity, not strongly
  connected, a pair with both signs, `L = (2, 1)`, `β = 1` and the eigenvalue
  `1 = β`: `hSC` is needed in `cocycle_spectral_strict`); `neg_sc_gauge`
  (`bNorm`: every closed walk is positive and there is no gauge: `hSC` is needed
  in `exists_gauge_iff_closed_walks`); `neg_primitive` (`pNorm`: the
  permutation `0 ↦ 2, 1 ↦ 3, 2 ↦ 1, 3 ↦ 0` with `R = {(01,10), (23,32)}`,
  `hSC`, `L = (1, 1)`, `β = 1`, `N_C ^ 2 = 1`, the eigenvalue `i`, neither gauge
  nor anti-gauge: `hprim` is needed in `cocycle_primitive_eigenvalue`,
  `cocycle_primitive_gauge` and `cocycle_extremal_iff`).

Not proved here: the remaining clauses of `prop:cocycle` (the morphisms `U`,
`V` with `σ ∘ U = U ∘ τ_C`; strong connectivity of the oriented double cover and
its morphism `W` when no gauge exists); the anti-gauge analogue of the walk
criterion (closed walks of length `n` with sign `(-1)^n`); the equality case for
imprimitive `N_C` (only `Psc.Wielandt.cycle_relation`, `(μ/β)^(2ℓ) = 1`, is
available there, and `neg_primitive` shows `μ` need not be real); the existence
of `L` and `β = ρ(N_C)` (Perron–Frobenius; a hypothesis here, supplied under
balance by `Psc.SignedCocycle.Normalisation.rep_eigen`, and for primitive `N_C`
by `Psc.PerronExistence.exists_pos_left_eigen` with `β` pinned by
`eigenvalue_eq_of_pos_left_eigen`, or for a primitive substitution with balanced
states by `Psc.PerronExistence.perron_root_rep_of_primitive`; that module is not
imported here).  Scope of the controls: the only
non-constant `D` in the primitive equality case is the abstract
`fin2_primitive_extremal`; the one-representative controls `exA`, `exB` have
constant `D`, are not primitive substitutions (the letter `2` is inert), and
`exB` is an algebra-only child system; `qNorm`, `pNorm` are permutations
(period `2`, so `qNorm` exercises the gauge criterion but not the primitive
equality case); the strict-inequality control on a normalisation
(Thue–Morse) has `S = 0`; `twoSys` and `bNorm` are not strongly connected.
-/
import PscVerif.SignedCocycle
import PscVerif.Wielandt
import PscVerif.PerronCore
import PscVerif.SignedIntertwiner
import PscVerif.ConcentrationAlgebra

namespace Psc.CocycleSpectrum

open Matrix Psc.PerronCore Psc.Wielandt Psc.Binomial Psc.SignedCocycle

/-! ### Abstract: an extremal phase is real under aperiodicity -/

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Powers of a twisted diagonal similarity `S = c · D N D⁻¹`:
`(S ^ k) i j = c ^ k d i (N ^ k) i j (d j)⁻¹`. -/
theorem pow_apply_of_twist (S : Matrix ι ι ℂ) (N : Matrix ι ι ℝ) (c : ℂ) (d : ι → ℂ)
    (hd : ∀ i, d i ≠ 0) (h : ∀ i j, S i j = c * d i * N i j * (d j)⁻¹) (k : ℕ) (i j : ι) :
    (S ^ k) i j = c ^ k * d i * ((N ^ k) i j : ℂ) * (d j)⁻¹ := by
  induction k generalizing j with
  | zero =>
    by_cases hij : i = j
    · subst hij; simp [hd i]
    · simp [Matrix.one_apply_ne hij]
  | succ k ih =>
    simp only [pow_succ, mul_apply, ih, h, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp [hd l]

/-- If a real matrix is a twisted diagonal similarity `Sr = c · D N D⁻¹` and
`(N ^ k) i i`, `(N ^ (k+1)) i i` are positive, then the phase `c` is real:
`c ^ n = (Sr ^ n) i i / (N ^ n) i i` for `n = k, k + 1`. -/
theorem phase_real (N : Matrix ι ι ℝ) (Sr : Matrix ι ι ℝ) (c : ℂ) (hc : c ≠ 0) (d : ι → ℂ)
    (hd : ∀ i, d i ≠ 0) (h : ∀ i j, (Sr i j : ℂ) = c * d i * N i j * (d j)⁻¹) (i : ι) (k : ℕ)
    (hk : 0 < (N ^ k) i i) (hk1 : 0 < (N ^ (k + 1)) i i) : ∃ r : ℝ, c = r := by
  have hS : ∀ n, (((Sr ^ n) i i : ℝ) : ℂ) = c ^ n * ((N ^ n) i i : ℂ) := by
    intro n
    have := pow_apply_of_twist (Sr.map Complex.ofRealHom) N c d hd (fun i j => h i j) n i i
    have hm := congrFun (congrFun (Matrix.map_pow Sr Complex.ofRealHom n) i) i
    rw [Matrix.map_apply] at hm
    rw [← Complex.ofRealHom_eq_coe, hm, this]; field_simp [hd i]
  have hNk : ((N ^ k) i i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk.ne'
  have hNk1 : ((N ^ (k + 1)) i i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk1.ne'
  have hck : c ^ k ≠ 0 := pow_ne_zero _ hc
  refine ⟨(Sr ^ (k + 1)) i i / (N ^ (k + 1)) i i / ((Sr ^ k) i i / (N ^ k) i i), ?_⟩
  push_cast
  rw [hS k, hS (k + 1)]
  field_simp
  ring

/-- **Aperiodic extremal eigenvalues are `±β`.**  In the setting of
`Psc.Wielandt.wielandt` with a real `Sr`, if some vertex `i` carries closed
walks of two consecutive lengths `k`, `k + 1` (`(N ^ k) i i > 0`,
`(N ^ (k+1)) i i > 0`), then an eigenvalue of modulus `β` is `s β` with
`s = ±1`. -/
theorem extremal_eq_sign_mul (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* N = β • L) (Sr : Matrix ι ι ℝ)
    (hS : ∀ i j, |Sr i j| ≤ N i j) (x : ι → ℂ) (hx0 : x ≠ 0) (μ : ℂ) (hμ : ‖μ‖ = β)
    (hx : Sr.map ((↑) : ℝ → ℂ) *ᵥ x = μ • x) (i : ι) (k : ℕ) (hk : 0 < (N ^ k) i i)
    (hk1 : 0 < (N ^ (k + 1)) i i) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ μ = ((s * β : ℝ) : ℂ) := by
  have hS' : ∀ i j, ‖(Sr.map ((↑) : ℝ → ℂ)) i j‖ ≤ N i j := fun i j => by
    simpa [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using hS i j
  have hβ : 0 < β := beta_pos N hSC L hL β hLN _ hS' x hx0 μ hμ hx
  obtain ⟨hc, hd, hW⟩ := wielandt N hSC L hL β hLN _ hS' x hx0 μ hμ hx
  have hdne : ∀ i, x i / (‖x i‖ : ℂ) ≠ 0 := fun i h => by
    have := hd i; rw [h, norm_zero] at this; exact zero_ne_one this
  have hc0 : μ / (β : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hc; exact zero_ne_one hc
  obtain ⟨r, hr⟩ := phase_real N Sr _ hc0 _ hdne (fun i j => hW i j) i k hk hk1
  have hβC : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hβ.ne'
  have hμc : μ = μ / (β : ℂ) * β := by field_simp
  rcases eq_one_or_neg_one_of_real r hr hc with h1 | h1
  · exact ⟨1, Or.inl rfl, by rw [hμc, h1]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, by rw [hμc, h1]; push_cast; ring⟩

/-- **Primitive equality case (abstract).**  If moreover some power of `N` is
entrywise positive, an eigenvalue of modulus `β` of the real matrix `Sr` is
`s β` with `s = ±1`, and `Sr = s · D N D` for a diagonal sign matrix `D`. -/
theorem primitive_extremal (N : Matrix ι ι ℝ) (hSC : StronglyConnected N) (L : ι → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* N = β • L) (Sr : Matrix ι ι ℝ)
    (hS : ∀ i j, |Sr i j| ≤ N i j) (hprim : ∃ k, ∀ i j, 0 < (N ^ k) i j) (x : ι → ℂ)
    (hx0 : x ≠ 0) (μ : ℂ) (hμ : ‖μ‖ = β) (hx : Sr.map ((↑) : ℝ → ℂ) *ᵥ x = μ • x) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ μ = ((s * β : ℝ) : ℂ) ∧
      ∃ D : ι → ℝ, (∀ i, D i = 1 ∨ D i = -1) ∧ ∀ i j, Sr i j = s * D i * N i j * D j := by
  have hN : ∀ i j, 0 ≤ N i j := fun i j => (abs_nonneg _).trans (hS i j)
  obtain ⟨i, -⟩ := Function.ne_iff.1 hx0
  obtain ⟨k, hk⟩ := hprim
  obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1 (hSC i i)
  have hk1 : 0 < (N ^ (k + 1)) i i := by
    rw [pow_succ, mul_apply]
    exact (mul_pos (hk i b) hb).trans_le (Finset.single_le_sum (f := fun l => (N ^ k) i l * N l i)
      (fun l _ => mul_nonneg (hk i l).le (hN l i)) (Finset.mem_univ b))
  obtain ⟨s, hs, hμs⟩ := extremal_eq_sign_mul N hSC L hL β hLN Sr hS x hx0 μ hμ hx i k (hk i i) hk1
  exact ⟨s, hs, hμs, gauge_of_real N hSC L hL β hLN Sr hS s hs x hx0 (hμs ▸ hx)⟩

/-- A non-negative matrix with an entrywise positive power `N ^ k`, `k ≥ 1`, is
strongly connected (a positive entry of `N ^ (n+1)` is a walk of length `n + 1`).
This is the `Relation.TransGen` form of Mathlib's `Matrix.IsPrimitive.isIrreducible`
(which is stated for the quiver of `N`). -/
theorem stronglyConnected_of_pow_pos (N : Matrix ι ι ℝ) (hN : ∀ i j, 0 ≤ N i j) {k : ℕ}
    (hk : 0 < k) (hpos : ∀ i j, 0 < (N ^ k) i j) : StronglyConnected N := by
  have key : ∀ n i j, 0 < (N ^ (n + 1)) i j → Relation.TransGen (fun a b => 0 < N a b) i j := by
    intro n
    induction n with
    | zero => exact fun i j h => .single (by simpa using h)
    | succ n ih =>
      intro i j h
      rw [pow_succ, mul_apply] at h
      obtain ⟨l, hl⟩ : ∃ l, 0 < (N ^ (n + 1)) i l * N l j := by
        by_contra hc
        exact (Finset.sum_nonpos fun l _ => not_lt.1 fun h' => hc ⟨l, h'⟩).not_gt h
      have hb : 0 < N l j :=
        (hN l j).lt_of_ne fun h0 => by rw [← h0, mul_zero] at hl; exact hl.false
      exact .tail (ih i l ((pos_iff_pos_of_mul_pos hl).2 hb)) hb
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact fun i j => key n i j (hpos i j)

end Abstract

/-! ### The cocycle on normalised representatives -/

section Cocycle

variable {α : Type*} [DecidableEq α] {S : ChildSystem α} (P : Normalisation S)

/-- `S` cast to `ℝ` and then to `ℂ` is `S` cast to `ℂ`. -/
theorem ssign_map_real :
    (P.Ssign.map (Int.cast : ℤ → ℝ)).map ((↑) : ℝ → ℂ) = P.Ssign.map (Int.cast : ℤ → ℂ) := by
  ext; simp

/-- Powers of `N_C` commute with the cast to `ℝ`. -/
theorem nrep_pow_cast (k : ℕ) (i j : P.Rep) :
    ((P.Nrep.map (Nat.cast : ℕ → ℝ)) ^ k) i j = ((P.Nrep ^ k) i j : ℝ) := by
  have hm := congrFun (congrFun (Matrix.map_pow P.Nrep (Nat.castRingHom ℝ) k) i) j
  rw [Matrix.map_apply, Nat.coe_castRingHom] at hm
  exact hm.symm

/-- A primitive `N_C` (`N_C ^ k > 0` for some `k ≥ 1`) is strongly connected, so
the hypothesis `hSC` below is implied by primitivity. -/
theorem nrep_stronglyConnected (hprim : ∃ k ≥ 1, ∀ i j, 0 < (P.Nrep ^ k) i j) :
    StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)) := by
  obtain ⟨k, hk, hpos⟩ := hprim
  exact stronglyConnected_of_pow_pos _ (fun i j => by simp) hk fun i j => by
    rw [nrep_pow_cast]; exact_mod_cast hpos i j

/-- `|S| ≤ N_C` entrywise, over `ℝ`. -/
theorem ssign_real_abs_le (i j : P.Rep) :
    |(P.Ssign.map (Int.cast : ℤ → ℝ)) i j| ≤ (P.Nrep.map (Nat.cast : ℕ → ℝ)) i j := by
  simp only [Matrix.map_apply]; exact_mod_cast P.ssign_abs_le i j

/-- `|S| ≤ N_C` entrywise, over `ℂ`. -/
theorem ssign_norm_le (i j : P.Rep) :
    ‖(P.Ssign.map (Int.cast : ℤ → ℂ)) i j‖ ≤ (P.Nrep.map (Nat.cast : ℕ → ℝ)) i j := by
  simp only [Matrix.map_apply, Complex.norm_intCast]; exact_mod_cast P.ssign_abs_le i j

/-- **Equality case: every parent–child pair carries one sign.**  If `N_C` is
strongly connected with a positive left eigenvector for `β` and the cocycle
`S` has an eigenvalue of modulus `β`, then `|S| = N_C`: for every `i, j`,
`A i j = 0` or `B i j = 0`. -/
theorem sign_pure_of_extremal (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)))
    (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L) (x : P.Rep → ℂ) (hx0 : x ≠ 0)
    (μ : ℂ) (hμ : ‖μ‖ = β) (hx : P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x)
    (i j : P.Rep) : P.A i j = 0 ∨ P.B i j = 0 := by
  obtain ⟨-, h⟩ := abs_eigen_real_pos _ hSC L hL β hLN _ (ssign_real_abs_le P) x hx0 μ hμ
    (by rw [ssign_map_real P]; exact hx)
  have h' : |((P.A i j : ℤ) - P.B i j)| = (P.A i j : ℤ) + P.B i j := by
    have := h i j
    simp only [Matrix.map_apply, Normalisation.Ssign, Normalisation.Nrep, Matrix.of_apply,
      Matrix.add_apply] at this
    exact_mod_cast this
  rcases abs_cases ((P.A i j : ℤ) - P.B i j) with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

/-- **`prop:cocycle`, strict inequality.**  If `N_C` is strongly connected with
a positive left eigenvector for `β`, and some parent–child pair occurs with both
signs (`A i j > 0`, `B i j > 0`), every complex eigenvalue of `S` has modulus
`< β`. -/
theorem cocycle_spectral_strict (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)))
    (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L) (i j : P.Rep) (hA : 0 < P.A i j)
    (hB : 0 < P.B i j) (x : P.Rep → ℂ) (hx0 : x ≠ 0) (μ : ℂ)
    (hx : P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) : ‖μ‖ < β := by
  refine lt_of_le_of_ne (Psc.ParikhIntertwiner.spectral_bound _ L hL β hLN _ (ssign_norm_le P)
    x hx0 μ hx) fun h => ?_
  rcases sign_pure_of_extremal P hSC L hL β hLN x hx0 μ h hx i j with h | h <;> omega

/-- A real sign `±1` is the cast of an integer sign. -/
theorem exists_int_sign {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ (t : ℝ) = s := by
  rcases hs with rfl | rfl
  · exact ⟨1, Or.inl rfl, by norm_num⟩
  · exact ⟨-1, Or.inr rfl, by norm_num⟩

/-- **`prop:cocycle`, primitive equality case.**  If `N_C` is strongly connected
with a positive left eigenvector for `β`, some power of `N_C` is entrywise
positive, and `S` has an eigenvalue `μ` of modulus `β`, then `μ = s β` with
`s = ±1`, and `S = s · D N_C D` for an integer sign vector `D`
(`s = 1`: gauge case, `s = -1`: anti-gauge case). -/
theorem cocycle_primitive_extremal (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)))
    (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L)
    (hprim : ∃ k, ∀ i j, 0 < (P.Nrep ^ k) i j) (x : P.Rep → ℂ) (hx0 : x ≠ 0) (μ : ℂ)
    (hμ : ‖μ‖ = β) (hx : P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ μ = s * β ∧
      ∃ D : P.Rep → ℤ, (∀ i, D i = 1 ∨ D i = -1) ∧
        ∀ i j, P.Ssign i j = s * D i * P.Nrep i j * D j := by
  have hprim' : ∃ k, ∀ i j, 0 < ((P.Nrep.map (Nat.cast : ℕ → ℝ)) ^ k) i j := by
    obtain ⟨k, hk⟩ := hprim
    exact ⟨k, fun i j => by rw [nrep_pow_cast]; exact_mod_cast hk i j⟩
  obtain ⟨s, hs, hμs, D, hD, hSD⟩ := primitive_extremal _ hSC L hL β hLN _
    (ssign_real_abs_le P) hprim' x hx0 μ hμ (by rw [ssign_map_real P]; exact hx)
  obtain ⟨t, ht, rfl⟩ := exists_int_sign hs
  choose D' hD' hDD using fun i => exists_int_sign (hD i)
  refine ⟨t, ht, by rw [hμs]; push_cast; ring, D', hD', fun i j => ?_⟩
  have := hSD i j
  simp only [Matrix.map_apply, ← hDD] at this
  exact_mod_cast this

/-- In the primitive equality case the extremal eigenvalue is `β` or `-β`. -/
theorem cocycle_primitive_eigenvalue
    (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ))) (L : P.Rep → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L)
    (hprim : ∃ k, ∀ i j, 0 < (P.Nrep ^ k) i j) (x : P.Rep → ℂ) (hx0 : x ≠ 0) (μ : ℂ)
    (hμ : ‖μ‖ = β) (hx : P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) :
    μ = β ∨ μ = -β := by
  obtain ⟨s, hs | hs, hμs, -⟩ := cocycle_primitive_extremal P hSC L hL β hLN hprim x hx0 μ hμ hx
  · left; rw [hμs, hs]; push_cast; ring
  · right; rw [hμs, hs]; push_cast; ring

end Cocycle

/-! ### Gauges: the gauge equation and the extremal eigenvalue -/

section Gauge

variable {α : Type*} [DecidableEq α] {S : ChildSystem α} (P : Normalisation S)

/-- A **gauge** (`prop:cocycle`): a sign `g i = ±1` on the representatives with
`g i = g j` whenever `i` is a `+1` child of `j` and `g i = -g j` whenever it is
a `-1` child. -/
def IsGauge (g : P.Rep → ℤ) : Prop :=
  (∀ i, g i = 1 ∨ g i = -1) ∧ ∀ i j, (0 < P.A i j → g i = g j) ∧ (0 < P.B i j → g i = -g j)

/-- An **anti-gauge**: a gauge for the cocycle with every sign reversed. -/
def IsAntiGauge (g : P.Rep → ℤ) : Prop :=
  (∀ i, g i = 1 ∨ g i = -1) ∧ ∀ i j, (0 < P.A i j → g i = -g j) ∧ (0 < P.B i j → g i = g j)

omit [DecidableEq α] in
/-- One entry of the gauge equation. -/
theorem sign_entry_iff (a b : ℕ) {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    (((0 < a → x = y) ∧ (0 < b → x = -y)) ↔ (a : ℤ) - b = x * (a + b) * y) ∧
      (((0 < a → x = -y) ∧ (0 < b → x = y)) ↔ (a : ℤ) - b = -(x * (a + b) * y)) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    refine ⟨⟨fun ⟨h1, h2⟩ => ?_, fun h => ⟨fun _ => ?_, fun _ => ?_⟩⟩,
      ⟨fun ⟨h1, h2⟩ => ?_, fun h => ⟨fun _ => ?_, fun _ => ?_⟩⟩⟩ <;> omega

/-- **The gauge equation.**  For a sign vector `g`, `g` is a gauge iff
`S i j = g i · N_C i j · g j` for all `i, j`.  (The gauge criterion of
`prop:cocycle`, in terms of closed walks, is `exists_gauge_iff_closed_walks`.) -/
theorem isGauge_iff (g : P.Rep → ℤ) :
    IsGauge P g ↔ (∀ i, g i = 1 ∨ g i = -1) ∧ ∀ i j, P.Ssign i j = g i * P.Nrep i j * g j := by
  refine and_congr_right fun hg => forall_congr' fun i => forall_congr' fun j => ?_
  simp only [Normalisation.Ssign, Normalisation.Nrep, Matrix.of_apply, Matrix.add_apply,
    Nat.cast_add]
  exact (sign_entry_iff _ _ (hg i) (hg j)).1

/-- **The anti-gauge equation.**  `g` is an anti-gauge iff
`S i j = - g i · N_C i j · g j`. -/
theorem isAntiGauge_iff (g : P.Rep → ℤ) :
    IsAntiGauge P g ↔
      (∀ i, g i = 1 ∨ g i = -1) ∧ ∀ i j, P.Ssign i j = -(g i * P.Nrep i j * g j) := by
  refine and_congr_right fun hg => forall_congr' fun i => forall_congr' fun j => ?_
  simp only [Normalisation.Ssign, Normalisation.Nrep, Matrix.of_apply, Matrix.add_apply,
    Nat.cast_add]
  exact (sign_entry_iff _ _ (hg i) (hg j)).2

/-- The entrywise identity `S i j = s · g i N_C i j g j` is the matrix identity
`S = s · D N_C D` with `D = diag g`. -/
theorem ssign_eq_diagonal_iff (g : P.Rep → ℤ) (s : ℤ) :
    (∀ i j, P.Ssign i j = s * (g i * P.Nrep i j * g j)) ↔
      P.Ssign = s • (diagonal g * P.Nrep.map (Nat.cast : ℕ → ℤ) * diagonal g) := by
  rw [← Matrix.ext_iff]
  simp [diagonal_mul, mul_diagonal]

/-- **The gauge equation, matrix form**: a gauge exists iff `S = D N_C D` for a
diagonal integer sign matrix `D`. -/
theorem exists_gauge_iff :
    (∃ g, IsGauge P g) ↔ ∃ g : P.Rep → ℤ, (∀ i, g i = 1 ∨ g i = -1) ∧
      P.Ssign = diagonal g * P.Nrep.map (Nat.cast : ℕ → ℤ) * diagonal g := by
  simp only [isGauge_iff]
  refine exists_congr fun g => and_congr_right fun _ => ?_
  simpa using ssign_eq_diagonal_iff P g 1

/-- **The anti-gauge equation, matrix form**: an anti-gauge exists iff
`S = - D N_C D` for a diagonal integer sign matrix `D`. -/
theorem exists_antiGauge_iff :
    (∃ g, IsAntiGauge P g) ↔ ∃ g : P.Rep → ℤ, (∀ i, g i = 1 ∨ g i = -1) ∧
      P.Ssign = -(diagonal g * P.Nrep.map (Nat.cast : ℕ → ℤ) * diagonal g) := by
  simp only [isAntiGauge_iff]
  refine exists_congr fun g => and_congr_right fun _ => ?_
  simpa using ssign_eq_diagonal_iff P g (-1)

/-- A parent–child pair with both signs obstructs every gauge and every anti-gauge. -/
theorem not_gauge_of_both {i j : P.Rep} (hA : 0 < P.A i j) (hB : 0 < P.B i j)
    (g : P.Rep → ℤ) : ¬ IsGauge P g ∧ ¬ IsAntiGauge P g := by
  refine ⟨fun ⟨hg, h⟩ => ?_, fun ⟨hg, h⟩ => ?_⟩ <;>
    have h1 := (h i j).1 hA <;> have h2 := (h i j).2 hB <;> rcases hg j with h3 | h3 <;> omega

/-- A diagonal sign conjugation `S = s · D N_C D` carries a `β`-eigenvector `v`
of `N_C` to the `s β`-eigenvector `D v` of `S`, over any commutative ring. -/
theorem diag_conj_eigen {K : Type*} [CommRing K] (g : P.Rep → ℤ) (hg : ∀ i, g i = 1 ∨ g i = -1)
    (s : ℤ) (hS : ∀ i j, P.Ssign i j = s * (g i * P.Nrep i j * g j)) (v : P.Rep → K) (β : K)
    (hv : P.Nrep.map (Nat.cast : ℕ → K) *ᵥ v = β • v) :
    P.Ssign.map (Int.cast : ℤ → K) *ᵥ (fun i => (g i : K) * v i) =
      ((s : K) * β) • fun i => (g i : K) * v i := by
  funext i
  have hi := congrFun hv i
  simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  have h2 : ∀ j, (g j : K) * g j = 1 := fun j => by rcases hg j with h | h <;> simp [h]
  calc ∑ j, ((P.Ssign i j : ℤ) : K) * ((g j : K) * v j)
      = ∑ j, (s : K) * g i * ((P.Nrep i j : K) * v j) * ((g j : K) * g j) :=
        Finset.sum_congr rfl fun j _ => by rw [hS i j]; push_cast; ring
    _ = (s : K) * g i * ∑ j, (P.Nrep i j : K) * v j := by simp only [h2, mul_one, Finset.mul_sum]
    _ = (s : K) * β * ((g i : K) * v i) := by rw [hi]; ring

/-- **Primitive equality case, gauge form**: under the hypotheses of
`cocycle_primitive_extremal`, either `μ = β` and a gauge exists, or `μ = -β`
and an anti-gauge exists. -/
theorem cocycle_primitive_gauge (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)))
    (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L)
    (hprim : ∃ k, ∀ i j, 0 < (P.Nrep ^ k) i j) (x : P.Rep → ℂ) (hx0 : x ≠ 0) (μ : ℂ)
    (hμ : ‖μ‖ = β) (hx : P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) :
    (μ = β ∧ ∃ g, IsGauge P g) ∨ (μ = -β ∧ ∃ g, IsAntiGauge P g) := by
  obtain ⟨s, hs | hs, hμs, D, hD, hSD⟩ :=
    cocycle_primitive_extremal P hSC L hL β hLN hprim x hx0 μ hμ hx <;> subst hs
  · exact Or.inl ⟨by rw [hμs]; push_cast; ring,
      D, (isGauge_iff P D).2 ⟨hD, fun i j => by rw [hSD]; ring⟩⟩
  · exact Or.inr ⟨by rw [hμs]; push_cast; ring,
      D, (isAntiGauge_iff P D).2 ⟨hD, fun i j => by rw [hSD]; ring⟩⟩

/-- **A gauge or an anti-gauge gives an extremal eigenvalue.**  If `N_C` has a
positive left eigenvector `L` for `β` and `Rep` is nonempty, then a gauge
(anti-gauge) `g` makes `D v`, `D = diag g`, a `β`- (`-β`-) eigenvector of `S`, for
the right `β`-eigenvector `v` of `N_C` that `L` provides
(`Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot`).  Neither strong
connectivity nor primitivity is used.  `Nonempty P.Rep` cannot be dropped: with
no representatives the constant sign is a gauge and there is no eigenvector. -/
theorem extremal_of_gauge [Nonempty P.Rep] (L : P.Rep → ℝ) (hL : ∀ i, 0 < L i) (β : ℝ)
    (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L)
    (h : (∃ g, IsGauge P g) ∨ ∃ g, IsAntiGauge P g) :
    ∃ x : P.Rep → ℂ, x ≠ 0 ∧ ∃ μ : ℂ, ‖μ‖ = β ∧ P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x := by
  obtain ⟨i₀⟩ := ‹Nonempty P.Rep›
  have hβ : 0 ≤ β := beta_nonneg _ (fun i j => by simp) L hL β hLN i₀
  have hLC : (fun i => (L i : ℂ)) ᵥ* P.Nrep.map (Nat.cast : ℕ → ℂ) =
      (β : ℂ) • fun i => (L i : ℂ) := by
    funext j
    have := congrArg (fun r : ℝ => (r : ℂ)) (congrFun hLN j)
    simpa [vecMul, dotProduct] using this
  have hL0 : (fun i => (L i : ℂ)) ≠ 0 := fun h => by
    have := congrFun h i₀; simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
    exact (hL i₀).ne' this
  obtain ⟨v, hv0, hv⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot _ _
    (Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ _ _ hL0 hLC)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  have key : ∀ (g : P.Rep → ℤ), (∀ i, g i = 1 ∨ g i = -1) → ∀ s : ℤ, (s = 1 ∨ s = -1) →
      (∀ i j, P.Ssign i j = s * (g i * P.Nrep i j * g j)) →
      ∃ x : P.Rep → ℂ, x ≠ 0 ∧ ∃ μ : ℂ, ‖μ‖ = β ∧
        P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x := by
    intro g hg s hs hS
    refine ⟨fun i => (g i : ℂ) * v i, fun h => ?_, (s : ℂ) * β, ?_,
      diag_conj_eigen P g hg s hS v β hv⟩
    · have := congrFun h j
      rcases hg j with h1 | h1 <;> simp [h1] at this <;> exact hj this
    · rcases hs with rfl | rfl <;> simp [Complex.norm_real, abs_of_nonneg hβ]
  rcases h with ⟨g, hg⟩ | ⟨g, hg⟩
  · obtain ⟨hg1, hS⟩ := (isGauge_iff P g).1 hg
    exact key g hg1 1 (Or.inl rfl) fun i j => by rw [hS]; ring
  · obtain ⟨hg1, hS⟩ := (isAntiGauge_iff P g).1 hg
    exact key g hg1 (-1) (Or.inr rfl) fun i j => by rw [hS]; ring

/-- **`ρ(S) = β` iff a gauge or an anti-gauge exists** (primitive `N_C`,
`Rep` nonempty): `S` has an eigenvalue of modulus `β` exactly when
`S = ± D N_C D`.  Forward: `cocycle_primitive_gauge`; backward:
`extremal_of_gauge`, which needs neither `hSC` nor `hprim`. -/
theorem cocycle_extremal_iff [Nonempty P.Rep]
    (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ))) (L : P.Rep → ℝ)
    (hL : ∀ i, 0 < L i) (β : ℝ) (hLN : L ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = β • L)
    (hprim : ∃ k, ∀ i j, 0 < (P.Nrep ^ k) i j) :
    (∃ x : P.Rep → ℂ, x ≠ 0 ∧ ∃ μ : ℂ, ‖μ‖ = β ∧ P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) ↔
      (∃ g, IsGauge P g) ∨ ∃ g, IsAntiGauge P g :=
  ⟨fun ⟨x, hx0, μ, hμ, hx⟩ =>
    (cocycle_primitive_gauge P hSC L hL β hLN hprim x hx0 μ hμ hx).imp And.right And.right,
    extremal_of_gauge P L hL β hLN⟩

end Gauge

/-! ### The gauge criterion: closed walks of the child graph -/

section Walks

variable {α : Type*} [DecidableEq α] {S : ChildSystem α} (P : Normalisation S)

omit [DecidableEq α] in
/-- `-s` is a sign when `s` is. -/
theorem sign_neg {s : ℤ} (hs : s = 1 ∨ s = -1) : -s = 1 ∨ -s = -1 := by
  rcases hs with rfl | rfl <;> simp

/-- `SignedWalk P a n b s`: a walk of length `n` from `a` to `b` in the child
graph on the representatives whose occurrence signs multiply to `s`.  Each
occurrence of `c` (sign `+1`, counted by `A c b`) or of `c.swap` (sign `-1`,
counted by `B c b`) among the children of `b` is an edge `b → c`. -/
inductive SignedWalk (a : P.Rep) : ℕ → P.Rep → ℤ → Prop
  | nil : SignedWalk a 0 a 1
  | plus {n : ℕ} {b c : P.Rep} {s : ℤ} :
      SignedWalk a n b s → 0 < P.A c b → SignedWalk a (n + 1) c s
  | minus {n : ℕ} {b c : P.Rep} {s : ℤ} :
      SignedWalk a n b s → 0 < P.B c b → SignedWalk a (n + 1) c (-s)

namespace SignedWalk

variable {P} {a b c : P.Rep} {n m : ℕ} {s t : ℤ}

/-- The sign of a walk is `±1`. -/
theorem sign (h : SignedWalk P a n b s) : s = 1 ∨ s = -1 := by
  induction h with
  | nil => exact Or.inl rfl
  | plus _ _ ih => exact ih
  | minus _ _ ih => exact sign_neg ih

/-- Concatenating walks multiplies their signs. -/
theorem append (h₁ : SignedWalk P a n b s) (h₂ : SignedWalk P b m c t) :
    SignedWalk P a (n + m) c (s * t) := by
  induction h₂ with
  | nil => simpa using h₁
  | plus _ hA ih => exact ih.plus hA
  | minus _ hB ih => rw [mul_neg]; exact ih.minus hB

end SignedWalk

/-- In a strongly connected child graph every representative is joined to every
other by a signed walk. -/
theorem exists_signedWalk (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)))
    (a b : P.Rep) : ∃ n s, SignedWalk P a n b s := by
  have step : ∀ {c d : P.Rep}, 0 < (P.Nrep.map (Nat.cast : ℕ → ℝ)) c d →
      (∃ n s, SignedWalk P a n d s) → ∃ n s, SignedWalk P a n c s := by
    rintro c d h ⟨n, s, hw⟩
    simp only [Matrix.map_apply, Nat.cast_pos, Normalisation.Nrep, Matrix.add_apply] at h
    rcases Nat.eq_zero_or_pos (P.A c d) with hA | hA
    · exact ⟨_, _, hw.minus (by omega)⟩
    · exact ⟨_, _, hw.plus hA⟩
  obtain h := hSC b a
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact step h ⟨0, 1, .nil⟩
  | head h _ ih => exact step h ih

variable {P} in
/-- A gauge propagates along walks: `g b = s · g a` for a walk `a → b` of sign `s`. -/
theorem IsGauge.walk {g : P.Rep → ℤ} (hg : IsGauge P g) {a b : P.Rep} {n : ℕ} {s : ℤ}
    (h : SignedWalk P a n b s) : g b = s * g a := by
  induction h with
  | nil => ring
  | plus _ hA ih => rw [(hg.2 _ _).1 hA, ih]
  | minus _ hB ih => rw [(hg.2 _ _).2 hB, ih]; ring

variable {P} in
/-- Under a gauge every closed walk has sign product `+1` (no connectivity is
needed for this direction). -/
theorem IsGauge.closed_walk {g : P.Rep → ℤ} (hg : IsGauge P g) {a : P.Rep} {n : ℕ} {s : ℤ}
    (h : SignedWalk P a n a s) : s = 1 := by
  have := hg.walk h
  rcases hg.1 a with h1 | h1 <;> rw [h1] at this <;> linarith

/-- **`prop:cocycle`, gauge criterion** (the voltage-graph condition).  If `N_C`
is strongly connected, a gauge exists iff every closed walk of the child graph
has sign product `+1`.  Backward: fix `r`; all walks `r → i` have one sign (two
of different signs, closed up by a walk `i → r` from `hSC`, would give a closed
walk of sign `-1`), and that sign is the gauge.  `hSC` cannot be dropped
(`neg_sc_gauge`). -/
theorem exists_gauge_iff_closed_walks
    (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ))) :
    (∃ g, IsGauge P g) ↔ ∀ a n s, SignedWalk P a n a s → s = 1 := by
  refine ⟨fun ⟨g, hg⟩ a n s h => hg.closed_walk h, fun h => ?_⟩
  rcases isEmpty_or_nonempty P.Rep with hE | ⟨⟨r⟩⟩
  · exact ⟨fun _ => 1, isEmptyElim, isEmptyElim⟩
  have uniq : ∀ {i n m s t}, SignedWalk P r n i s → SignedWalk P r m i t → s = t := by
    intro i n m s t h₁ h₂
    obtain ⟨k, u, hu⟩ := exists_signedWalk P hSC i r
    have e₁ := h _ _ _ (h₁.append hu)
    have e₂ := h _ _ _ (h₂.append hu)
    rcases hu.sign with rfl | rfl <;> linarith
  classical
  let g : P.Rep → ℤ := fun i => if ∃ n, SignedWalk P r n i 1 then 1 else -1
  have hg : ∀ {i n s}, SignedWalk P r n i s → g i = s := fun {i n s} hw => by
    rcases hw.sign with rfl | rfl
    · exact ite_eq_left ⟨n, hw⟩
    · exact ite_eq_right fun ⟨m, hm⟩ => absurd (uniq hw hm) (by norm_num)
  refine ⟨g, fun i => ?_, fun i j => ?_⟩
  · obtain ⟨n, s, hw⟩ := exists_signedWalk P hSC r i
    rw [hg hw]; exact hw.sign
  · obtain ⟨n, s, hw⟩ := exists_signedWalk P hSC r j
    exact ⟨fun hA => by rw [hg hw, hg (hw.plus hA)], fun hB => by rw [hg hw, hg (hw.minus hB)]⟩

/-- One step of the walk count `W_s(n) = N_C ^ n + s · S ^ n` (over `ℤ`):
`W_s(n+1) c a = ∑ b, A c b · W_s(n) b a + B c b · W_{-s}(n) b a`. -/
theorem walkCount_succ (s : ℤ) (n : ℕ) (c a : P.Rep) :
    ((P.Nrep ^ (n + 1)) c a : ℤ) + s * (P.Ssign ^ (n + 1)) c a =
      ∑ b, ((P.A c b : ℤ) * (((P.Nrep ^ n) b a : ℤ) + s * (P.Ssign ^ n) b a) +
        (P.B c b : ℤ) * (((P.Nrep ^ n) b a : ℤ) + -s * (P.Ssign ^ n) b a)) := by
  rw [pow_succ', pow_succ', mul_apply, mul_apply, Nat.cast_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Normalisation.Nrep, Normalisation.Ssign, Matrix.add_apply, Matrix.of_apply,
    Nat.cast_mul, Nat.cast_add]
  ring

/-- `W_{±1}(n) ≥ 0`, i.e. `|S ^ n| ≤ N_C ^ n` entrywise. -/
theorem walkCount_nonneg (n : ℕ) : ∀ {s : ℤ}, (s = 1 ∨ s = -1) → ∀ b a : P.Rep,
    0 ≤ ((P.Nrep ^ n) b a : ℤ) + s * (P.Ssign ^ n) b a := by
  induction n with
  | zero =>
    intro s hs b a
    by_cases h : b = a
    · subst h; rcases hs with rfl | rfl <;> simp
    · simp [Matrix.one_apply_ne h]
  | succ n ih =>
    intro s hs c a
    rw [walkCount_succ]
    exact Finset.sum_nonneg fun b _ => add_nonneg (mul_nonneg (by positivity) (ih hs b a))
      (mul_nonneg (by positivity) (ih (sign_neg hs) b a))

/-- A walk `a → b` of length `n` and sign `s` is counted by `W_s(n) b a > 0`. -/
theorem SignedWalk.count_pos {a b : P.Rep} {n : ℕ} {s : ℤ} (h : SignedWalk P a n b s) :
    0 < ((P.Nrep ^ n) b a : ℤ) + s * (P.Ssign ^ n) b a := by
  induction h with
  | nil => norm_num
  | @plus n b c s hw hA ih =>
    rw [walkCount_succ]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun b' _ => add_nonneg
      (mul_nonneg (by positivity) (walkCount_nonneg P n hw.sign b' a))
      (mul_nonneg (by positivity) (walkCount_nonneg P n (sign_neg hw.sign) b' a)))
      (Finset.mem_univ b))
    exact lt_add_of_pos_of_le (mul_pos (by exact_mod_cast hA) ih)
      (mul_nonneg (by positivity) (walkCount_nonneg P n (sign_neg hw.sign) b a))
  | @minus n b c s hw hB ih =>
    rw [walkCount_succ]
    simp only [neg_neg]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun b' _ => add_nonneg
      (mul_nonneg (by positivity) (walkCount_nonneg P n (sign_neg hw.sign) b' a))
      (mul_nonneg (by positivity) (walkCount_nonneg P n hw.sign b' a)))
      (Finset.mem_univ b))
    exact lt_add_of_le_of_pos
      (mul_nonneg (by positivity) (walkCount_nonneg P n (sign_neg hw.sign) b a))
      (mul_pos (by exact_mod_cast hB) ih)

omit [DecidableEq α] in
/-- A positive sum `m₁ w₁ + m₂ w₂` with `m₁, m₂ ∈ ℕ` has a positive summand. -/
theorem pos_of_nat_mul_add {m₁ m₂ : ℕ} {w₁ w₂ : ℤ} (h : 0 < (m₁ : ℤ) * w₁ + m₂ * w₂) :
    (0 < m₁ ∧ 0 < w₁) ∨ (0 < m₂ ∧ 0 < w₂) := by
  have k : ∀ (m : ℕ) (w : ℤ), ¬ (0 < m ∧ 0 < w) → (m : ℤ) * w ≤ 0 := fun m w hmw => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) (not_lt.1 fun hw => hmw ⟨hm, hw⟩)
  by_contra hc
  rw [not_or] at hc
  linarith [k _ _ hc.1, k _ _ hc.2]

/-- Conversely, `W_s(n) c a > 0` gives a walk `a → c` of length `n` and sign `s`. -/
theorem signedWalk_of_pos (a : P.Rep) (n : ℕ) : ∀ {s : ℤ} {c : P.Rep}, (s = 1 ∨ s = -1) →
    0 < ((P.Nrep ^ n) c a : ℤ) + s * (P.Ssign ^ n) c a → SignedWalk P a n c s := by
  induction n with
  | zero =>
    intro s c hs h
    by_cases hca : c = a
    · subst hca
      rcases hs with rfl | rfl
      · exact .nil
      · simp at h
    · simp [Matrix.one_apply_ne hca] at h
  | succ n ih =>
    intro s c hs h
    rw [walkCount_succ] at h
    obtain ⟨b, hb⟩ : ∃ b, 0 < (P.A c b : ℤ) * (((P.Nrep ^ n) b a : ℤ) + s * (P.Ssign ^ n) b a) +
        (P.B c b : ℤ) * (((P.Nrep ^ n) b a : ℤ) + -s * (P.Ssign ^ n) b a) := by
      by_contra hc
      exact (Finset.sum_nonpos fun b _ => not_lt.1 fun h' => hc ⟨b, h'⟩).not_gt h
    rcases pos_of_nat_mul_add hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (ih hs h2).plus h1
    · simpa using (ih (sign_neg hs) h2).minus h1

/-- **Walks and the walk count**: for `s = ±1`, a walk `a → b` of length `n` and
sign `s` exists iff `(N_C ^ n) b a + s (S ^ n) b a > 0`. -/
theorem signedWalk_iff_pos {s : ℤ} (hs : s = 1 ∨ s = -1) (a b : P.Rep) (n : ℕ) :
    SignedWalk P a n b s ↔ 0 < ((P.Nrep ^ n) b a : ℤ) + s * (P.Ssign ^ n) b a :=
  ⟨SignedWalk.count_pos P, signedWalk_of_pos P a n hs⟩

/-- **Closed walks, walk-count form.**  `(N_C ^ n) a a` counts the closed walks
of length `n` at `a` (with occurrence multiplicity) and `(S ^ n) a a` sums their
signs, so every closed walk has sign `+1` iff `(S ^ n) a a = (N_C ^ n) a a` for
all `n, a`.  No connectivity is needed. -/
theorem closed_walks_iff_pow_diag :
    (∀ a n s, SignedWalk P a n a s → s = 1) ↔
      ∀ n a, (P.Ssign ^ n) a a = ((P.Nrep ^ n) a a : ℤ) := by
  constructor
  · intro h n a
    have h₁ := walkCount_nonneg P n (s := -1) (Or.inr rfl) a a
    have h₂ : ¬ 0 < ((P.Nrep ^ n) a a : ℤ) + -1 * (P.Ssign ^ n) a a := fun hp =>
      absurd (h a n (-1) (signedWalk_of_pos P a n (Or.inr rfl) hp)) (by norm_num)
    linarith
  · intro h a n s hw
    rcases hw.sign with rfl | rfl
    · rfl
    · have := hw.count_pos; rw [h n a] at this; exfalso; linarith

/-- **Gauge criterion, walk-count form**: for strongly connected `N_C`, a gauge
exists iff `(S ^ n) a a = (N_C ^ n) a a` for all `n` and `a`. -/
theorem exists_gauge_iff_pow_diag (hSC : StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ))) :
    (∃ g, IsGauge P g) ↔ ∀ n a, (P.Ssign ^ n) a a = ((P.Nrep ^ n) a a : ℤ) :=
  (exists_gauge_iff_closed_walks P hSC).trans (closed_walks_iff_pow_diag P)

end Walks

/-! ### Changing the representatives -/

section Choice

variable {α : Type*} [DecidableEq α] {S : ChildSystem α}

/-- The representative of a state `V ∈ C` for a normalisation `P`: `V` itself
if `V ∈ R`, its swap otherwise. -/
def toRep (P : Normalisation S) (V : List α × List α) (hV : V ∈ S.C) : P.Rep :=
  if h : V ∈ P.R then ⟨V, h⟩ else ⟨V.swap, (P.cover V hV).resolve_left h⟩

/-- The state underlying `toRep P V hV`. -/
theorem toRep_val (P : Normalisation S) (V : List α × List α) (hV : V ∈ S.C) :
    (toRep P V hV).1 = if V ∈ P.R then V else V.swap := by
  unfold toRep; split_ifs <;> rfl

/-- The bijection between the representatives of two normalisations of the same
child system: a representative of `P₁` goes to whichever of itself and its swap
lies in `R₂`. -/
def repEquiv (P₁ P₂ : Normalisation S) : P₁.Rep ≃ P₂.Rep where
  toFun i := toRep P₂ i.1 (P₁.sub i.2)
  invFun i := toRep P₁ i.1 (P₂.sub i.2)
  left_inv i := Subtype.ext <| by
    by_cases h : i.1 ∈ P₂.R <;> simp [toRep_val, h, i.2, P₁.not_both _ i.2]
  right_inv i := Subtype.ext <| by
    by_cases h : i.1 ∈ P₁.R <;> simp [toRep_val, h, i.2, P₂.not_both _ i.2]

/-- The sign `δ i = +1` if `P₁` and `P₂` choose the same orientation of `i`,
`-1` otherwise. -/
def repSign (P₁ P₂ : Normalisation S) (i : P₁.Rep) : ℤ := if i.1 ∈ P₂.R then 1 else -1

/-- `δ i = ±1`. -/
theorem repSign_sign (P₁ P₂ : Normalisation S) (i : P₁.Rep) :
    repSign P₁ P₂ i = 1 ∨ repSign P₁ P₂ i = -1 := by
  unfold repSign; split_ifs <;> simp

/-- The counts `A`, `B` of `P₂` at `(e i, e j)`: unchanged if `δ i δ j = 1`,
exchanged if `δ i δ j = -1`. -/
theorem counts_repEquiv (P₁ P₂ : Normalisation S) (i j : P₁.Rep) :
    ((P₂.A (repEquiv P₁ P₂ i) (repEquiv P₁ P₂ j) : ℤ) - P₂.B (repEquiv P₁ P₂ i) (repEquiv P₁ P₂ j) =
        repSign P₁ P₂ i * repSign P₁ P₂ j * ((P₁.A i j : ℤ) - P₁.B i j)) ∧
      P₂.A (repEquiv P₁ P₂ i) (repEquiv P₁ P₂ j) + P₂.B (repEquiv P₁ P₂ i) (repEquiv P₁ P₂ j) =
        P₁.A i j + P₁.B i j := by
  by_cases hi : i.1 ∈ P₂.R <;> by_cases hj : j.1 ∈ P₂.R <;>
    simp only [Normalisation.A, Normalisation.B, Matrix.of_apply, repEquiv, Equiv.coe_fn_mk,
      toRep_val, repSign, hi, hj, ite_true, ite_false, P₁.count_children_swap, Prod.swap_swap] <;>
    constructor <;> first | trivial | ring1

/-- **`N_C` does not depend on the choice of representatives.** -/
theorem nrep_repEquiv (P₁ P₂ : Normalisation S) (i j : P₁.Rep) :
    P₂.Nrep (repEquiv P₁ P₂ i) (repEquiv P₁ P₂ j) = P₁.Nrep i j := by
  simpa only [Normalisation.Nrep, Matrix.add_apply] using (counts_repEquiv P₁ P₂ i j).2

/-- **`S` changes by a diagonal `±1` conjugation**:
`S₂ (e i) (e j) = δ i δ j S₁ i j`. -/
theorem ssign_repEquiv (P₁ P₂ : Normalisation S) (i j : P₁.Rep) :
    P₂.Ssign (repEquiv P₁ P₂ i) (repEquiv P₁ P₂ j) =
      repSign P₁ P₂ i * repSign P₁ P₂ j * P₁.Ssign i j := by
  simpa only [Normalisation.Ssign, Matrix.of_apply] using (counts_repEquiv P₁ P₂ i j).1

/-- **Choice of representatives** (§`sec:orientation`).  For two normalisations
of the same child system there are a bijection `e : R₁ ≃ R₂`, sending each
representative to itself or to its swap, and signs `δ i = ±1` (`+1` exactly
when `e` keeps the orientation), with `S₂ (e i) (e j) = δ i δ j S₁ i j` and
`N₂ (e i) (e j) = N₁ i j`. -/
theorem choice_of_representatives (P₁ P₂ : Normalisation S) :
    ∃ (e : P₁.Rep ≃ P₂.Rep) (δ : P₁.Rep → ℤ),
      (∀ i, ((e i).1 = i.1 ∧ δ i = 1) ∨ ((e i).1 = i.1.swap ∧ δ i = -1)) ∧
      ∀ i j, P₂.Ssign (e i) (e j) = δ i * δ j * P₁.Ssign i j ∧
        P₂.Nrep (e i) (e j) = P₁.Nrep i j := by
  refine ⟨repEquiv P₁ P₂, repSign P₁ P₂, fun i => ?_, fun i j =>
    ⟨ssign_repEquiv P₁ P₂ i j, nrep_repEquiv P₁ P₂ i j⟩⟩
  by_cases h : i.1 ∈ P₂.R
  · exact Or.inl ⟨by simp [repEquiv, toRep_val, h], by simp [repSign, h]⟩
  · exact Or.inr ⟨by simp [repEquiv, toRep_val, h], by simp [repSign, h]⟩

/-- Matrix form: `S₂ = e (Δ S₁ Δ) e⁻¹` with `Δ = diag δ`. -/
theorem ssign_eq_reindex (P₁ P₂ : Normalisation S) :
    P₂.Ssign = reindex (repEquiv P₁ P₂) (repEquiv P₁ P₂)
      (diagonal (repSign P₁ P₂) * P₁.Ssign * diagonal (repSign P₁ P₂)) := by
  ext a b
  obtain ⟨i, rfl⟩ := (repEquiv P₁ P₂).surjective a
  obtain ⟨j, rfl⟩ := (repEquiv P₁ P₂).surjective b
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, mul_diagonal, diagonal_mul,
    ssign_repEquiv]
  ring

/-- **The characteristic polynomial of `S` does not depend on the choice of
representatives.** -/
theorem charpoly_ssign_eq (P₁ P₂ : Normalisation S) : P₂.Ssign.charpoly = P₁.Ssign.charpoly := by
  have hΔ : diagonal (repSign P₁ P₂) * diagonal (repSign P₁ P₂) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; rcases repSign_sign P₁ P₂ i with h | h <;> simp [h]
  rw [ssign_eq_reindex P₁ P₂, charpoly_reindex, charpoly_mul_comm, ← Matrix.mul_assoc, hΔ,
    Matrix.one_mul]

/-- A sign conjugation `S₁ = s · D N₁ D` transfers to `S₂ = s · D' N₂ D'` with
`D' (e i) = δ i D i`. -/
theorem diag_conj_transfer (P₁ P₂ : Normalisation S) (g : P₁.Rep → ℤ)
    (hg : ∀ i, g i = 1 ∨ g i = -1) (s : ℤ)
    (hS : ∀ i j, P₁.Ssign i j = s * (g i * P₁.Nrep i j * g j)) :
    ∃ g' : P₂.Rep → ℤ, (∀ i, g' (repEquiv P₁ P₂ i) = repSign P₁ P₂ i * g i) ∧
      (∀ a, g' a = 1 ∨ g' a = -1) ∧ ∀ a b, P₂.Ssign a b = s * (g' a * P₂.Nrep a b * g' b) := by
  refine ⟨fun a => repSign P₁ P₂ ((repEquiv P₁ P₂).symm a) * g ((repEquiv P₁ P₂).symm a),
    fun i => by simp only [Equiv.symm_apply_apply], fun a => ?_, fun a b => ?_⟩
  · rcases repSign_sign P₁ P₂ ((repEquiv P₁ P₂).symm a) with h | h <;>
      rcases hg ((repEquiv P₁ P₂).symm a) with h' | h' <;> simp [h, h']
  · obtain ⟨i, rfl⟩ := (repEquiv P₁ P₂).surjective a
    obtain ⟨j, rfl⟩ := (repEquiv P₁ P₂).surjective b
    simp only [Equiv.symm_apply_apply, ssign_repEquiv, nrep_repEquiv, hS]
    ring

/-- **The existence of a gauge does not depend on the choice of representatives.** -/
theorem exists_gauge_congr (P₁ P₂ : Normalisation S) :
    (∃ g, IsGauge P₁ g) ↔ ∃ g, IsGauge P₂ g := by
  have h : ∀ P₁ P₂ : Normalisation S, (∃ g, IsGauge P₁ g) → ∃ g, IsGauge P₂ g := by
    rintro P₁ P₂ ⟨g, hg⟩
    obtain ⟨hg1, hS⟩ := (isGauge_iff P₁ g).1 hg
    obtain ⟨_, -, h1, h2⟩ := diag_conj_transfer P₁ P₂ g hg1 1 fun i j => by rw [hS]; ring
    exact ⟨_, (isGauge_iff P₂ _).2 ⟨h1, fun a b => by rw [h2]; ring⟩⟩
  exact ⟨h P₁ P₂, h P₂ P₁⟩

/-- **The existence of an anti-gauge does not depend on the choice of
representatives.** -/
theorem exists_antiGauge_congr (P₁ P₂ : Normalisation S) :
    (∃ g, IsAntiGauge P₁ g) ↔ ∃ g, IsAntiGauge P₂ g := by
  have h : ∀ P₁ P₂ : Normalisation S, (∃ g, IsAntiGauge P₁ g) → ∃ g, IsAntiGauge P₂ g := by
    rintro P₁ P₂ ⟨g, hg⟩
    obtain ⟨hg1, hS⟩ := (isAntiGauge_iff P₁ g).1 hg
    obtain ⟨_, -, h1, h2⟩ := diag_conj_transfer P₁ P₂ g hg1 (-1) fun i j => by rw [hS]; ring
    exact ⟨_, (isAntiGauge_iff P₂ _).2 ⟨h1, fun a b => by rw [h2]; ring⟩⟩
  exact ⟨h P₁ P₂, h P₂ P₁⟩

end Choice

/-! ### Non-vacuity controls -/

section Controls

open Psc.SignedIntertwiner

/-- A sum over a two-element type. -/
theorem sum_of_two {ι M : Type*} [Fintype ι] [AddCommMonoid M] {a b : ι} (hab : a ≠ b)
    (h : ∀ i, i = a ∨ i = b) (f : ι → M) : ∑ i, f i = f a + f b :=
  Fintype.sum_eq_add a b hab fun x hx => ((h x).elim hx.1 hx.2).elim

/-- On two indices `a, b`, positive entries `N a b`, `N b a` make `N` strongly
connected. -/
theorem stronglyConnected_of_two {ι : Type*} {N : Matrix ι ι ℝ} {a b : ι}
    (h : ∀ i, i = a ∨ i = b) (hab : 0 < N a b) (hba : 0 < N b a) : StronglyConnected N :=
  fun i j => by
    rcases h i with rfl | rfl <;> rcases h j with rfl | rfl
    exacts [.tail (.single hab) hba, .single hab, .single hba, .tail (.single hba) hab]

variable {α : Type*} [DecidableEq α] {S : ChildSystem α}

/-- A normalisation with a single representative `r` and `N_C = (n)`, `n > 0`,
meets the standing hypotheses: `N_C` is strongly connected and primitive
(`k = 1`), and `λ = (1)` is a positive left eigenvector for `β = n`. -/
theorem oneRep_hyps (P : Normalisation S) (r : P.Rep) (hr : ∀ i, i = r) (hn : 0 < P.Nrep r r) :
    StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)) ∧
      (fun _ => (1 : ℝ)) ᵥ* P.Nrep.map (Nat.cast : ℕ → ℝ) = (P.Nrep r r : ℝ) • (fun _ => 1) ∧
      ∃ k, ∀ i j, 0 < (P.Nrep ^ k) i j := by
  have : Subsingleton P.Rep := ⟨fun a b => (hr a).trans (hr b).symm⟩
  have hprim : ∀ i j, 0 < (P.Nrep ^ 1) i j := fun i j => by rw [pow_one, hr i, hr j]; exact hn
  refine ⟨nrep_stronglyConnected P ⟨1, le_rfl, hprim⟩, ?_, ⟨1, hprim⟩⟩
  funext j
  rw [vecMul, dotProduct, Fintype.sum_subsingleton _ r, hr j]
  simp

/-- With a single representative `r`, the constant vector is an eigenvector of
`S` for the eigenvalue `S r r`. -/
theorem oneRep_eigen (P : Normalisation S) (r : P.Rep) (hr : ∀ i, i = r) :
    P.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ (fun _ => 1) = ((P.Ssign r r : ℤ) : ℂ) • fun _ => 1 := by
  have : Subsingleton P.Rep := ⟨fun a b => (hr a).trans (hr b).symm⟩
  funext i
  rw [mulVec, dotProduct, Fintype.sum_subsingleton _ r, hr i]
  simp

/-- The constant vector `1` is nonzero. -/
theorem one_ne_zero_vec (P : Normalisation S) (r : P.Rep) : (fun _ : P.Rep => (1 : ℂ)) ≠ 0 :=
  fun h => one_ne_zero (congrFun h r)

/-! #### Thue–Morse: both signs, strict inequality, neither gauge nor anti-gauge -/

/-- The unique representative of `thueMorseNorm`. -/
def tmRep : thueMorseNorm.Rep := ⟨tmPair, Finset.mem_singleton_self _⟩

/-- `A = (1)`: the child `(01,10)` of `(01,10)` carries the sign `+1`. -/
theorem thueMorse_A (i j : thueMorseNorm.Rep) : thueMorseNorm.A i j = 1 := by
  obtain rfl := thueMorseNorm_rep i
  obtain rfl := thueMorseNorm_rep j
  rfl

/-- `B = (1)`: the child `(10,01)` of `(01,10)` carries the sign `-1`. -/
theorem thueMorse_B (i j : thueMorseNorm.Rep) : thueMorseNorm.B i j = 1 := by
  obtain rfl := thueMorseNorm_rep i
  obtain rfl := thueMorseNorm_rep j
  rfl

/-- `cocycle_spectral_strict` on Thue–Morse: the pair `(01,10) → (01,10)`
occurs with both signs, so every eigenvalue of `S` has modulus `< 2`. -/
theorem thueMorse_strict (x : thueMorseNorm.Rep → ℂ) (hx0 : x ≠ 0) (μ : ℂ)
    (hx : thueMorseNorm.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x) : ‖μ‖ < 2 := by
  obtain ⟨hSC, hLN, -⟩ := oneRep_hyps thueMorseNorm tmRep thueMorseNorm_rep
    (by rw [thueMorse_nrep]; norm_num)
  rw [thueMorse_nrep] at hLN
  exact cocycle_spectral_strict thueMorseNorm hSC _ (fun _ => one_pos) 2 (by exact_mod_cast hLN)
    tmRep tmRep (by rw [thueMorse_A]; norm_num) (by rw [thueMorse_B]; norm_num) x hx0 μ hx

/-- The eigen-hypothesis of `thueMorse_strict` is met: `S 1 = 0 · 1`. -/
theorem thueMorse_eigen :
    thueMorseNorm.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ (fun _ => 1) = (0 : ℂ) • fun _ => 1 := by
  rw [oneRep_eigen thueMorseNorm tmRep thueMorseNorm_rep, thueMorse_ssign]; simp

/-- Thue–Morse has neither a gauge nor an anti-gauge. -/
theorem thueMorse_no_gauge (g : thueMorseNorm.Rep → ℤ) :
    ¬ IsGauge thueMorseNorm g ∧ ¬ IsAntiGauge thueMorseNorm g :=
  not_gauge_of_both thueMorseNorm (i := tmRep) (j := tmRep) (by rw [thueMorse_A]; norm_num)
    (by rw [thueMorse_B]; norm_num) g

/-- `exists_gauge_iff_closed_walks` on Thue–Morse: the child `(10,01)` of
`(01,10)` is a closed walk of length `1` and sign `-1`, so there is no gauge. -/
theorem thueMorse_neg_walk :
    SignedWalk thueMorseNorm tmRep 1 tmRep (-1) ∧ ¬ ∃ g, IsGauge thueMorseNorm g := by
  have hw : SignedWalk thueMorseNorm tmRep 1 tmRep (-1) :=
    SignedWalk.minus SignedWalk.nil (by rw [thueMorse_B]; norm_num)
  obtain ⟨hSC, -, -⟩ := oneRep_hyps thueMorseNorm tmRep thueMorseNorm_rep
    (by rw [thueMorse_nrep]; norm_num)
  exact ⟨hw, fun hg => absurd ((exists_gauge_iff_closed_walks _ hSC).1 hg _ _ _ hw)
    (by norm_num)⟩

/-! #### `exA`: the gauge case, `S = N_C = (2)`, `μ = β = 2` -/

/-- `N_C = (2)` for `exA`. -/
theorem exA_nrep (i j : exANorm.Rep) : exANorm.Nrep i j = 2 := by
  obtain rfl := exANorm_rep i
  obtain rfl := exANorm_rep j
  decide

/-- `cocycle_primitive_extremal` on `exA` (`β = 2`, `x = 1`, `μ = 2`): its sign is
`s = 1` (forced by `μ = s β`), so `S = D N_C D`. -/
theorem exA_primitive_extremal :
    ∃ D : exANorm.Rep → ℤ, (∀ i, D i = 1 ∨ D i = -1) ∧
      ∀ i j, exANorm.Ssign i j = D i * exANorm.Nrep i j * D j := by
  obtain ⟨hSC, hLN, hprim⟩ := oneRep_hyps exANorm exARep exANorm_rep
    (by rw [exA_nrep]; norm_num)
  rw [exA_nrep] at hLN
  obtain ⟨s, hs, hμ, D, hD, hSD⟩ := cocycle_primitive_extremal exANorm hSC _ (fun _ => one_pos)
    2 (by exact_mod_cast hLN) hprim _ (one_ne_zero_vec exANorm exARep) 2 (by simp)
    (by rw [oneRep_eigen exANorm exARep exANorm_rep, exA_ssign]; simp)
  obtain rfl : s = 1 := by
    rcases hs with rfl | rfl
    · rfl
    · norm_num at hμ
  exact ⟨D, hD, fun i j => by rw [hSD]; ring⟩

/-- `sign_pure_of_extremal` on `exA` (`β = 2`, `x = 1`, `μ = 2`). -/
theorem exA_sign_pure (i j : exANorm.Rep) : exANorm.A i j = 0 ∨ exANorm.B i j = 0 := by
  obtain ⟨hSC, hLN, -⟩ := oneRep_hyps exANorm exARep exANorm_rep
    (by rw [exA_nrep]; norm_num)
  rw [exA_nrep] at hLN
  exact sign_pure_of_extremal exANorm hSC _ (fun _ => one_pos) 2 (by exact_mod_cast hLN)
    _ (one_ne_zero_vec exANorm exARep) 2 (by simp)
    (by rw [oneRep_eigen exANorm exARep exANorm_rep, exA_ssign]; simp) i j

/-- The constant sign `1` is a gauge of `exA`. -/
theorem exA_isGauge : IsGauge exANorm fun _ => 1 :=
  (isGauge_iff exANorm _).2 ⟨fun _ => Or.inl rfl, fun i j => by rw [exA_ssign, exA_nrep]; rfl⟩

/-- `cocycle_extremal_iff` on `exA`, backward direction: the gauge `1` yields
an eigenvalue of modulus `β = 2`. -/
theorem exA_extremal :
    ∃ x : exANorm.Rep → ℂ, x ≠ 0 ∧ ∃ μ : ℂ, ‖μ‖ = 2 ∧
      exANorm.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x := by
  have : Nonempty exANorm.Rep := ⟨exARep⟩
  obtain ⟨hSC, hLN, hprim⟩ := oneRep_hyps exANorm exARep exANorm_rep
    (by rw [exA_nrep]; norm_num)
  rw [exA_nrep] at hLN
  exact (cocycle_extremal_iff exANorm hSC _ (fun _ => one_pos) 2 (by exact_mod_cast hLN)
    hprim).2 (Or.inl ⟨_, exA_isGauge⟩)

/-- `exists_gauge_iff_pow_diag` on `exA`: the gauge `1` gives
`(S ^ n) a a = (N_C ^ n) a a` (both are `2 ^ n`). -/
theorem exA_pow_diag : ∀ n a, (exANorm.Ssign ^ n) a a = ((exANorm.Nrep ^ n) a a : ℤ) := by
  obtain ⟨hSC, -, -⟩ := oneRep_hyps exANorm exARep exANorm_rep (by rw [exA_nrep]; norm_num)
  exact (exists_gauge_iff_pow_diag exANorm hSC).1 ⟨_, exA_isGauge⟩

/-- `cocycle_extremal_iff` on Thue–Morse, forward direction: with neither a
gauge nor an anti-gauge, `S` has no eigenvalue of modulus `β = 2`. -/
theorem thueMorse_not_extremal :
    ¬ ∃ x : thueMorseNorm.Rep → ℂ, x ≠ 0 ∧ ∃ μ : ℂ, ‖μ‖ = 2 ∧
      thueMorseNorm.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x := by
  have : Nonempty thueMorseNorm.Rep := ⟨tmRep⟩
  obtain ⟨hSC, hLN, hprim⟩ := oneRep_hyps thueMorseNorm tmRep thueMorseNorm_rep
    (by rw [thueMorse_nrep]; norm_num)
  rw [thueMorse_nrep] at hLN
  rw [cocycle_extremal_iff thueMorseNorm hSC _ (fun _ => one_pos) 2 (by exact_mod_cast hLN) hprim]
  rintro (⟨g, hg⟩ | ⟨g, hg⟩)
  exacts [(thueMorse_no_gauge g).1 hg, (thueMorse_no_gauge g).2 hg]

/-! #### `exB`: the anti-gauge case, `S = -N_C = (-1)`, `μ = -β = -1` -/

/-- `N_C = (1)` for `exB`. -/
theorem exB_nrep (i j : exBNorm.Rep) : exBNorm.Nrep i j = 1 := by
  obtain rfl := exBNorm_rep i
  obtain rfl := exBNorm_rep j
  decide

/-- `cocycle_primitive_gauge` on `exB` (`β = 1`, `x = 1`, `μ = -1`): its
anti-gauge branch. -/
theorem exB_primitive_gauge : (-1 : ℂ) = -((1 : ℝ) : ℂ) ∧ ∃ g, IsAntiGauge exBNorm g := by
  obtain ⟨hSC, hLN, hprim⟩ := oneRep_hyps exBNorm exBRep exBNorm_rep
    (by rw [exB_nrep]; norm_num)
  rw [exB_nrep] at hLN
  exact (cocycle_primitive_gauge exBNorm hSC _ (fun _ => one_pos) 1 (by exact_mod_cast hLN)
    hprim _ (one_ne_zero_vec exBNorm exBRep) (-1) (by simp)
    (by rw [oneRep_eigen exBNorm exBRep exBNorm_rep, exB_ssign]; simp)).resolve_left
    fun ⟨h, _⟩ => by norm_num at h

/-- The constant sign `1` is an anti-gauge of `exB`, and `exB` has no gauge
(its only child carries the sign `-1`). -/
theorem exB_isAntiGauge : IsAntiGauge exBNorm (fun _ => 1) ∧ ∀ g, ¬ IsGauge exBNorm g := by
  refine ⟨(isAntiGauge_iff exBNorm _).2 ⟨fun _ => Or.inl rfl, fun i j => by
    rw [exB_ssign, exB_nrep]; rfl⟩, fun g ⟨hg, h⟩ => ?_⟩
  have := (h exBRep exBRep).2 (by decide)
  rcases hg exBRep with h1 | h1 <;> omega

/-! #### The abstract equality case with a non-constant `D` -/

/-- `N = (1 1; 1 1)`. -/
def fin2N : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

/-- `Sr = (1 -1; -1 1) = D N D` with `D = diag (1, -1)`. -/
def fin2S : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

/-- `primitive_extremal` with a non-constant `D`: for `N = fin2N`, `Sr = fin2S`,
`L = (1, 1)`, `β = 2`, `x = (1, -1)`, `μ = 2` its hypotheses hold, so
`fin2S = s · D N D`; and every such `(s, D)` has `s = 1` and `D 0 = -D 1`. -/
theorem fin2_primitive_extremal :
    (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ (2 : ℂ) = ((s * 2 : ℝ) : ℂ) ∧
      ∃ D : Fin 2 → ℝ, (∀ i, D i = 1 ∨ D i = -1) ∧
        ∀ i j, fin2S i j = s * D i * fin2N i j * D j) ∧
    ∀ (s : ℝ) (D : Fin 2 → ℝ), (∀ i, D i = 1 ∨ D i = -1) →
      (∀ i j, fin2S i j = s * D i * fin2N i j * D j) → s = 1 ∧ D 0 = -D 1 := by
  have hN : ∀ i j, 0 < fin2N i j := fun i j => by fin_cases i <;> fin_cases j <;> simp [fin2N]
  refine ⟨primitive_extremal fin2N ?_ ![1, 1] ?_ 2 ?_ fin2S ?_ ⟨1, by simpa using hN⟩ ![1, -1]
    ?_ 2 ?_ ?_, ?_⟩
  · exact stronglyConnected_of_pow_pos _ (fun i j => (hN i j).le) one_pos (by simpa using hN)
  · intro i; fin_cases i <;> simp
  · ext j; fin_cases j <;> simp [fin2N, vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num
  · intro i j; fin_cases i <;> fin_cases j <;> simp [fin2S, fin2N]
  · intro h; have := congrFun h 0; simp at this
  · simp
  · ext i; fin_cases i <;> simp [fin2S, mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · intro s D hD h
    have h00 := h 0 0
    have h01 := h 0 1
    simp only [fin2S, fin2N, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01
    rcases hD 0 with e | e <;> rcases hD 1 with e' | e' <;> rw [e, e'] at h01 <;> rw [e] at h00 <;>
      rw [e, e'] <;> constructor <;> linarith

/-! #### Permutation systems on two representatives -/

/-- `(01,10)` over `Fin 4`. -/
def pT : List (Fin 4) × List (Fin 4) := ([0, 1], [1, 0])

/-- `(23,32)` over `Fin 4`. -/
def pU : List (Fin 4) × List (Fin 4) := ([2, 3], [3, 2])

/-- The permutation substitution `0 ↦ 2, 1 ↦ 3, 2 ↦ 0, 3 ↦ 1`:
`σ(01,10) = (23,32)` and `σ(23,32) = (01,10)`. -/
def qSubst : Fin 4 → List (Fin 4) := ![[2], [3], [0], [1]]

/-- The child system of `qSubst` on `(01,10)`, `(23,32)` and their swaps. -/
def qSys : ChildSystem (Fin 4) :=
  Psc.Reduction.redSystem qSubst (by decide) {pT, pT.swap, pU, pU.swap} (by decide) (by decide)

/-- `R = {(01,10), (32,23)}`: both children carry the sign `-1`, so `A = 0` and
`S = -N_C`, `N_C = (0 1; 1 0)`. -/
def qNorm : Normalisation qSys :=
  Psc.Reduction.redNormalisation qSubst (by decide) {pT, pT.swap, pU, pU.swap} (by decide)
    (by decide) (by decide) {pT, pU.swap} (by decide) (by decide) (by decide)

/-- The representative `(01,10)` of `qNorm`. -/
def qT : qNorm.Rep := ⟨pT, by decide⟩

/-- The representative `(32,23)` of `qNorm`. -/
def qU : qNorm.Rep := ⟨pU.swap, by decide⟩

/-- `qNorm` has the two representatives `qT`, `qU`. -/
theorem qNorm_rep (i : qNorm.Rep) : i = qT ∨ i = qU := by revert i; decide

/-- `N_C` of `qNorm` is strongly connected (`(01,10) ⇄ (32,23)`). -/
theorem qNorm_sc : StronglyConnected (qNorm.Nrep.map (Nat.cast : ℕ → ℝ)) :=
  stronglyConnected_of_two qNorm_rep (by rw [Matrix.map_apply, Nat.cast_pos]; decide)
    (by rw [Matrix.map_apply, Nat.cast_pos]; decide)

/-- **A non-constant gauge**: `g = (1, -1)` is a gauge of `qNorm`, every gauge
has `g qU = -g qT`, the constant sign is an anti-gauge, and by
`exists_gauge_iff_closed_walks` (`qNorm_sc`) every closed walk of `qNorm` has
sign `+1`. -/
theorem qNorm_gauge :
    IsGauge qNorm (fun i => if i = qT then 1 else -1) ∧
      (∀ g, IsGauge qNorm g → g qU = -g qT) ∧ IsAntiGauge qNorm (fun _ => 1) ∧
      ∀ a n s, SignedWalk qNorm a n a s → s = 1 := by
  have hg : IsGauge qNorm (fun i => if i = qT then 1 else -1) :=
    (isGauge_iff qNorm _).2 ⟨fun i => by split_ifs <;> simp, fun i j => by
      rcases qNorm_rep i with rfl | rfl <;> rcases qNorm_rep j with rfl | rfl <;> decide⟩
  refine ⟨hg, fun g h => (h.2 qU qT).2 (by decide), (isAntiGauge_iff qNorm _).2
    ⟨fun _ => Or.inl rfl, fun i j => by
      rcases qNorm_rep i with rfl | rfl <;> rcases qNorm_rep j with rfl | rfl <;> decide⟩,
    (exists_gauge_iff_closed_walks qNorm qNorm_sc).1 ⟨_, hg⟩⟩

/-- The permutation substitution `0 ↦ 2, 1 ↦ 3, 2 ↦ 1, 3 ↦ 0`:
`σ(01,10) = (23,32)` and `σ(23,32) = (10,01)`. -/
def pSubst : Fin 4 → List (Fin 4) := ![[2], [3], [1], [0]]

/-- The child system of `pSubst` on `(01,10)`, `(23,32)` and their swaps. -/
def pSys : ChildSystem (Fin 4) :=
  Psc.Reduction.redSystem pSubst (by decide) {pT, pT.swap, pU, pU.swap} (by decide) (by decide)

/-- `R = {(01,10), (23,32)}`: `S = (0 -1; 1 0)`, `N_C = (0 1; 1 0)`. -/
def pNorm : Normalisation pSys :=
  Psc.Reduction.redNormalisation pSubst (by decide) {pT, pT.swap, pU, pU.swap} (by decide)
    (by decide) (by decide) {pT, pU} (by decide) (by decide) (by decide)

/-- The representative `(01,10)` of `pNorm`. -/
def rT : pNorm.Rep := ⟨pT, by decide⟩

/-- The representative `(23,32)` of `pNorm`. -/
def rU : pNorm.Rep := ⟨pU, by decide⟩

/-- `pNorm` has the two representatives `rT`, `rU`. -/
theorem pNorm_rep (i : pNorm.Rep) : i = rT ∨ i = rU := by revert i; decide

/-- **Primitivity cannot be dropped** from `cocycle_primitive_eigenvalue`,
`cocycle_primitive_gauge` and the forward direction of `cocycle_extremal_iff`.
For `pNorm`, `N_C` is strongly connected with `L = (1, 1)`, `β = 1`, but no
power of `N_C` is positive (`N_C ^ 2 = 1`), and `S` has the eigenvalue `i`, of
modulus `β` and neither `β` nor `-β`; there is neither a gauge nor an
anti-gauge. -/
theorem neg_primitive :
    StronglyConnected (pNorm.Nrep.map (Nat.cast : ℕ → ℝ)) ∧
      (fun _ => (1 : ℝ)) ᵥ* pNorm.Nrep.map (Nat.cast : ℕ → ℝ) = (1 : ℝ) • (fun _ => 1) ∧
      (¬ ∃ k, ∀ i j, 0 < (pNorm.Nrep ^ k) i j) ∧
      (∃ x : pNorm.Rep → ℂ, x ≠ 0 ∧ pNorm.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = Complex.I • x) ∧
      ‖Complex.I‖ = 1 ∧ ¬ (Complex.I = ((1 : ℝ) : ℂ) ∨ Complex.I = -((1 : ℝ) : ℂ)) ∧
      ∀ g, ¬ IsGauge pNorm g ∧ ¬ IsAntiGauge pNorm g := by
  have hTU : rT ≠ rU := by decide
  obtain ⟨n₁, n₂, n₃, n₄⟩ : pNorm.Nrep rT rT = 0 ∧ pNorm.Nrep rT rU = 1 ∧
      pNorm.Nrep rU rT = 1 ∧ pNorm.Nrep rU rU = 0 := by decide
  obtain ⟨s₁, s₂, s₃, s₄⟩ : pNorm.Ssign rT rT = 0 ∧ pNorm.Ssign rT rU = -1 ∧
      pNorm.Ssign rU rT = 1 ∧ pNorm.Ssign rU rU = 0 := by decide
  have hsq : pNorm.Nrep * pNorm.Nrep = 1 := by
    ext i j; rw [mul_apply, sum_of_two hTU pNorm_rep]
    rcases pNorm_rep i with rfl | rfl <;> rcases pNorm_rep j with rfl | rfl <;> decide
  have hUT : rU ≠ rT := by decide
  refine ⟨stronglyConnected_of_two pNorm_rep (by simp [n₂]) (by simp [n₃]), ?_, ?_,
    ⟨fun i => if i = rT then Complex.I else 1, fun h => by simpa [hUT] using congrFun h rU, ?_⟩,
    Complex.norm_I, by simp [Complex.ext_iff], fun g => ?_⟩
  · funext j; rw [vecMul, dotProduct, sum_of_two hTU pNorm_rep]
    rcases pNorm_rep j with rfl | rfl <;> simp [n₁, n₂, n₃, n₄]
  · rintro ⟨k, hk⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · have := hk rT rU
      rw [pow_mul, sq, hsq, one_pow, Matrix.one_apply_ne hTU] at this
      exact lt_irrefl 0 this
    · have := hk rT rT
      rw [pow_succ, pow_mul, sq, hsq, one_pow, Matrix.one_mul, n₁] at this
      exact lt_irrefl 0 this
  · funext i; rw [mulVec, dotProduct, sum_of_two hTU pNorm_rep]
    rcases pNorm_rep i with rfl | rfl <;> simp [s₁, s₂, s₃, s₄, hUT]
  · have hA : 0 < pNorm.A rU rT := by decide
    have hB : 0 < pNorm.B rT rU := by decide
    refine ⟨fun ⟨hg, h⟩ => ?_, fun ⟨hg, h⟩ => ?_⟩ <;>
      have h1 := (h rU rT).1 hA <;> have h2 := (h rT rU).2 hB <;> rcases hg rT with h3 | h3 <;>
      omega

/-! #### Strong connectivity cannot be dropped -/

/-- `(0110, 1001)`; under the identity its zero-return blocks are `(01,10)`, `(10,01)`. -/
def bPair : List (Fin 3) × List (Fin 3) := ([0, 1, 1, 0], [1, 0, 0, 1])

/-- The zero-return system of `{(0110,1001), (01,10)}` and their swaps under the
identity substitution. -/
def bSys : ChildSystem (Fin 3) :=
  Psc.Reduction.redSystem idSubst (by decide) {bPair, bPair.swap, exAPair, exAPair.swap}
    (by decide) (by decide)

/-- `R = {(0110,1001), (01,10)}`. -/
def bNorm : Normalisation bSys :=
  Psc.Reduction.redNormalisation idSubst (by decide)
    {bPair, bPair.swap, exAPair, exAPair.swap} (by decide) (by decide) (by decide)
    {bPair, exAPair} (by decide) (by decide) (by decide)

/-- The representative `(0110,1001)` of `bNorm`. -/
def bT : bNorm.Rep := ⟨bPair, by decide⟩

/-- The representative `(01,10)` of `bNorm`. -/
def bU : bNorm.Rep := ⟨exAPair, by decide⟩

/-- `bNorm` has the two representatives `bT`, `bU`. -/
theorem bNorm_rep (i : bNorm.Rep) : i = bT ∨ i = bU := by revert i; decide

/-- `(0110,1001)` is nobody's child. -/
theorem bNorm_nrep_T (b : bNorm.Rep) : bNorm.Nrep bT b = 0 := by
  rcases bNorm_rep b with rfl | rfl <;> decide

/-- The only occurrence of sign `-1` is `(10,01)` among the children of `(0110,1001)`. -/
theorem bNorm_B (c b : bNorm.Rep) (h : 0 < bNorm.B c b) : c = bU ∧ b = bT := by
  rcases bNorm_rep c with rfl | rfl <;> rcases bNorm_rep b with rfl | rfl <;> revert h <;> decide

/-- `N_C` of `bNorm` is not strongly connected: nothing leads to `(0110,1001)`. -/
theorem bNorm_not_sc : ¬ StronglyConnected (bNorm.Nrep.map (Nat.cast : ℕ → ℝ)) := fun h => by
  obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.1 (h bT bT)
  simp [bNorm_nrep_T] at hb

/-- **Strong connectivity cannot be dropped from `cocycle_spectral_strict`.**  In
`bNorm` the pair `((01,10), (0110,1001))` occurs with both signs, `L = (2, 1)` is
a positive left eigenvector of `N_C` for `β = 1`, and `S` has the eigenvalue
`1 = β`; `N_C` is not strongly connected. -/
theorem neg_sc_strict :
    ¬ StronglyConnected (bNorm.Nrep.map (Nat.cast : ℕ → ℝ)) ∧
      ∃ L : bNorm.Rep → ℝ, (∀ i, 0 < L i) ∧
        L ᵥ* bNorm.Nrep.map (Nat.cast : ℕ → ℝ) = (1 : ℝ) • L ∧
        0 < bNorm.A bU bT ∧ 0 < bNorm.B bU bT ∧
        ∃ x : bNorm.Rep → ℂ, x ≠ 0 ∧ ∃ μ : ℂ,
          bNorm.Ssign.map (Int.cast : ℤ → ℂ) *ᵥ x = μ • x ∧ ¬ ‖μ‖ < 1 := by
  have hTU : bT ≠ bU := by decide
  obtain ⟨n₁, n₂, n₃, n₄⟩ : bNorm.Nrep bT bT = 0 ∧ bNorm.Nrep bT bU = 0 ∧
      bNorm.Nrep bU bT = 2 ∧ bNorm.Nrep bU bU = 1 := by decide
  obtain ⟨s₁, s₂⟩ : bNorm.Ssign bT bU = 0 ∧ bNorm.Ssign bU bU = 1 := by decide
  have hUT : bU ≠ bT := by decide
  refine ⟨bNorm_not_sc, fun i => if i = bT then 2 else 1,
    fun i => by dsimp only; split_ifs <;> norm_num, ?_, by decide, by decide,
    fun i => if i = bU then 1 else 0,
    fun h => by simpa using congrFun h bU, 1, ?_, by simp⟩
  · funext j; rw [vecMul, dotProduct, sum_of_two hTU bNorm_rep]
    rcases bNorm_rep j with rfl | rfl <;> simp [n₁, n₂, n₃, n₄, hUT]
  · funext i; rw [mulVec, dotProduct, sum_of_two hTU bNorm_rep]
    rcases bNorm_rep i with rfl | rfl <;> simp [s₁, s₂, hTU]

/-- **Strong connectivity cannot be dropped from `exists_gauge_iff_closed_walks`.**
Every closed walk of `bNorm` has sign `+1` (no walk enters `(0110,1001)`, and
from `(01,10)` only the `+1` loop is available), but the pair with both signs
rules out a gauge. -/
theorem neg_sc_gauge :
    ¬ StronglyConnected (bNorm.Nrep.map (Nat.cast : ℕ → ℝ)) ∧
      (∀ a n s, SignedWalk bNorm a n a s → s = 1) ∧ ¬ ∃ g, IsGauge bNorm g := by
  refine ⟨bNorm_not_sc, fun a n s h => ?_, fun ⟨g, hg⟩ =>
    (not_gauge_of_both bNorm (i := bU) (j := bT) (by decide) (by decide) g).1 hg⟩
  have key : ∀ {b m t}, SignedWalk bNorm a m b t →
      (b = bT → a = bT ∧ t = 1) ∧ (a = bU → t = 1) := by
    intro b m t hw
    induction hw with
    | nil => exact ⟨fun h => ⟨h, rfl⟩, fun _ => rfl⟩
    | @plus m b c t _ hA ih =>
      refine ⟨fun hc => absurd hA ?_, ih.2⟩
      subst hc
      have := bNorm_nrep_T b
      simp only [Normalisation.Nrep, Matrix.add_apply] at this
      omega
    | @minus m b c t _ hB ih =>
      obtain ⟨rfl, rfl⟩ := bNorm_B c b hB
      obtain ⟨rfl, rfl⟩ := ih.1 rfl
      exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  rcases bNorm_rep a with rfl | rfl
  exacts [((key h).1 rfl).2, (key h).2 rfl]

/-! #### Two representatives: changing `R` flips an off-diagonal sign -/

/-- The reducible balanced pair `(0101, 1010)`; under the identity its
zero-return blocks are `(01,10), (01,10)`. -/
def twoPair : List (Fin 3) × List (Fin 3) := ([0, 1, 0, 1], [1, 0, 1, 0])

/-- The zero-return system of `{(0101,1010), (01,10)}` and their swaps under the
identity substitution. -/
def twoSys : ChildSystem (Fin 3) :=
  Psc.Reduction.redSystem idSubst (by decide) {twoPair, twoPair.swap, exAPair, exAPair.swap}
    (by decide) (by decide)

/-- `R₁ = {(0101,1010), (01,10)}`. -/
def twoNorm₁ : Normalisation twoSys :=
  Psc.Reduction.redNormalisation idSubst (by decide)
    {twoPair, twoPair.swap, exAPair, exAPair.swap} (by decide) (by decide) (by decide)
    {twoPair, exAPair} (by decide) (by decide) (by decide)

/-- `R₂ = {(0101,1010), (10,01)}`. -/
def twoNorm₂ : Normalisation twoSys :=
  Psc.Reduction.redNormalisation idSubst (by decide)
    {twoPair, twoPair.swap, exAPair, exAPair.swap} (by decide) (by decide) (by decide)
    {twoPair, exAPair.swap} (by decide) (by decide) (by decide)

/-- The representatives `(0101,1010)` and `(01,10)` of `R₁`. -/
def twoRep : twoNorm₁.Rep := ⟨twoPair, by decide⟩
@[inherit_doc twoRep] def twoRepA : twoNorm₁.Rep := ⟨exAPair, by decide⟩

/-- `ssign_repEquiv` on `twoSys`: `S₁ = 2` at `((01,10), (0101,1010))`, while
`S₂ = -2` at the corresponding representatives `((10,01), (0101,1010))`, and
`δ = (1, -1)`. -/
theorem two_ssign :
    twoNorm₁.Ssign twoRepA twoRep = 2 ∧
      twoNorm₂.Ssign (repEquiv twoNorm₁ twoNorm₂ twoRepA) (repEquiv twoNorm₁ twoNorm₂ twoRep) = -2 ∧
      repSign twoNorm₁ twoNorm₂ twoRepA = -1 ∧ repSign twoNorm₁ twoNorm₂ twoRep = 1 ∧
      (repEquiv twoNorm₁ twoNorm₂ twoRepA).1 = exAPair.swap := by
  decide

end Controls

end Psc.CocycleSpectrum
