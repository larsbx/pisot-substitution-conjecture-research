/-
# Geometric realization of the legal tiling hull

This module constructs the geometric-realization map of the legal two-sided hull of
`PeriodicPartnerHull` onto the solenoid of the substitution matrix, and proves the properties
that `PeriodicPartnerHull.PublishedInputs` previously took as fields:

* `realize_inflate`: the realization semiconjugates inflation to the solenoid shift `Â`;
* `shiftS_bijective`: `Â` is a bijection, also in the nonunit case;
* `realize_translate`: translation by `t` is carried to the flow `t ↦ (t β⁻ⁿ u)ₙ`;
* `realize_r4`: (R4): a periodic tiling with a tile ending at the origin realizes to `0`.

Construction.  `M b a` counts `b` in `σ a`, so the length vector `ℓ` satisfies `ℓ M = β ℓ`.
`PisotData` supplies a right eigenvector `u` with `ℓ ⬝ u = 1` and a uniform contraction of
`M` on `ker ℓ` (the Pisot contraction).  Given a bijective inflation (recognizability), every
hull element `T` has desubstitutions `Tₙ`, with `inflate Tₙ₊₁ = Tₙ`.  If the origin tile of
`Tₙ` starts at `xₙ`, then `xₙ = β xₙ₊₁ + ℓ ⬝ cₙ` for the letter count `cₙ` of a prefix of a
substitution image, and

  `G(T) = -x₀ u - Σₖ Mᵏ π(cₖ)`,   `π(v) = v - (ℓ ⬝ v) u`,

converges.  Its class modulo `ℤᵈ` is the limit of `-βⁿ xₙ u` and the torus map; the sequence
of torus maps of `Tₙ` is the solenoid point.  The torus map alone would only semiconjugate to
the endomorphism `M` of `ℝᵈ / ℤᵈ`, which is not invertible when `|det M| ≠ 1`.

This is the construction of Baker--Barge--Kwapisz (2006), Definition 3.1, for the lattice
`ℤᵈ` and the normalisation in which a vertex-periodic tiling realizes to `0`.  The finite-fibre
theorem (their Theorem 4.2) and BDS periodicization remain named inputs.

See `docs/c4-geometric-realization-stop-go-2026-11-19.md` for the source decision.
-/
import PscVerif.PeriodicPartnerHull
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix

namespace Psc.PeriodicPartnerRealization

open Function Filter Set Matrix Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerHull
  Psc.PeriodicPartnerHull.LengthSubst
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## The integer lattice and the torus -/

/-- The integer vectors `ℤᵈ ⊂ ℝᵈ`. -/
def lattice (α : Type*) : AddSubgroup (α → ℝ) where
  carrier := {v | ∀ a, v a ∈ range ((↑) : ℤ → ℝ)}
  zero_mem' _ := ⟨0, by simp⟩
  add_mem' {v w} hv hw a := by
    obtain ⟨m, hm⟩ := hv a
    obtain ⟨n, hn⟩ := hw a
    exact ⟨m + n, by simp [hm, hn]⟩
  neg_mem' {v} hv a := by
    obtain ⟨m, hm⟩ := hv a
    exact ⟨-m, by simp [hm]⟩

theorem isClosed_lattice : IsClosed (lattice α : Set (α → ℝ)) := by
  have : (lattice α : Set (α → ℝ)) = ⋂ a, (fun v : α → ℝ => v a) ⁻¹' range ((↑) : ℤ → ℝ) := by
    ext v
    simp [lattice]
  rw [this]
  exact isClosed_iInter fun a => Real.isClosed_range_intCast.preimage (continuous_apply a)

/-- The torus `ℝᵈ / ℤᵈ`. -/
abbrev Torus (α : Type*) : Type _ := (α → ℝ) ⧸ lattice α

/-! ## The substitution matrix -/

section Matrix

variable (S : LengthSubst α)

/-- The letter counts of a word. -/
def ab (w : List α) : α → ℝ := fun b => (w.count b : ℝ)

/-- The substitution matrix: `M b a` is the number of `b` in `σ a`. -/
def mat : Matrix α α ℝ := fun b a => ((S.σ a).count b : ℝ)

theorem ab_mem_lattice (w : List α) : ab w ∈ lattice α := fun b => ⟨(w.count b : ℤ), by
  simp [ab]⟩

theorem dot_ab (w : List α) : S.ℓ ⬝ᵥ ab w = (w.map S.ℓ).sum := by
  induction w with
  | nil => simp [ab, dotProduct]
  | cons a w ih =>
    simp only [ab, dotProduct, List.count_cons, beq_iff_eq, Nat.cast_add, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, mul_add, Finset.sum_add_distrib, List.map_cons,
      List.sum_cons] at ih ⊢
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [ih]; ring

theorem dot_single (a : α) : S.ℓ ⬝ᵥ Pi.single a 1 = S.ℓ a := by
  simp [dotProduct_single]

theorem single_mem_lattice (a : α) : (Pi.single a 1 : α → ℝ) ∈ lattice α := fun b => by
  by_cases h : b = a
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

/-- `ℓ` is a left eigenvector: `ℓ ⬝ M v = β (ℓ ⬝ v)`. -/
theorem dot_mat_mulVec (v : α → ℝ) : S.ℓ ⬝ᵥ ((mat S) *ᵥ v) = S.β * (S.ℓ ⬝ᵥ v) := by
  rw [dotProduct_mulVec]
  have h : vecMul S.ℓ (mat S) = S.β • S.ℓ := by
    funext a
    have := (dot_ab S) (S.σ a)
    rw [S.eigen] at this
    simpa [vecMul, dotProduct, mat, ab, mul_comm] using this
  rw [h, smul_dotProduct, smul_eq_mul]

theorem mulVec_mem_lattice {v : α → ℝ} (hv : v ∈ lattice α) : (mat S) *ᵥ v ∈ lattice α := by
  intro b
  choose n hn using hv
  refine ⟨∑ a, ((S.σ a).count b : ℤ) * n a, ?_⟩
  simp [mulVec, dotProduct, mat, hn]

theorem pow_mulVec_mem_lattice {v : α → ℝ} (hv : v ∈ lattice α) (n : ℕ) :
    ((mat S) ^ n) *ᵥ v ∈ lattice α := by
  induction n with
  | zero => simpa using hv
  | succ n ih => rw [pow_succ', ← mulVec_mulVec]; exact (mulVec_mem_lattice S) ih

/-- The endomorphism of `ℝᵈ` induced by the substitution matrix. -/
def matHom : (α → ℝ) →+ (α → ℝ) := (Matrix.mulVecLin (mat S)).toAddMonoidHom

/-- The endomorphism of the torus induced by the substitution matrix. -/
def torusMap : Torus α →+ Torus α :=
  QuotientAddGroup.map _ _ (matHom S) fun _ hv => (mulVec_mem_lattice S) hv

theorem torusMap_mk (v : α → ℝ) :
    (torusMap S) (v : Torus α) = (((mat S) *ᵥ v : α → ℝ) : Torus α) := rfl

end Matrix

/-! ## Pisot data -/

/-- The linear-algebra input of the realization: a right eigenvector `u` for `β` normalised by
`ℓ ⬝ u = 1`, and the Pisot contraction of `M` on `ker ℓ`.  For an irreducible Pisot matrix
this is the spectral statement that every conjugate of `β` has modulus `< 1`. -/
structure PisotData (S : LengthSubst α) where
  u : α → ℝ
  u_eigen : (mat S) *ᵥ u = S.β • u
  dot_u : S.ℓ ⬝ᵥ u = 1
  C : ℝ
  C_nonneg : 0 ≤ C
  ρ : ℝ
  ρ_nonneg : 0 ≤ ρ
  ρ_lt_one : ρ < 1
  contract : ∀ v, S.ℓ ⬝ᵥ v = 0 → ∀ n : ℕ, ‖((mat S) ^ n) *ᵥ v‖ ≤ C * ρ ^ n * ‖v‖

namespace PisotData

variable {S : LengthSubst α} (P : PisotData S)

/-- The projection onto `ker ℓ` along `u`. -/
def proj (v : α → ℝ) : α → ℝ := v - (S.ℓ ⬝ᵥ v) • P.u

theorem dot_proj (v : α → ℝ) : S.ℓ ⬝ᵥ P.proj v = 0 := by
  simp [proj, dotProduct_sub, dotProduct_smul, P.dot_u]

theorem proj_neg (v : α → ℝ) : P.proj (-v) = -P.proj v := by
  simp only [proj, dotProduct_neg, neg_smul, sub_neg_eq_add]
  abel

theorem pow_mulVec_u (n : ℕ) : ((mat S) ^ n) *ᵥ P.u = S.β ^ n • P.u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, P.u_eigen, smul_smul, pow_succ, mul_comm]

/-- The key identity: `Mⁿ c - Mⁿ π(c) = βⁿ (ℓ ⬝ c) u`. -/
theorem pow_mulVec_proj (c : α → ℝ) (n : ℕ) :
    ((mat S) ^ n) *ᵥ P.proj c = ((mat S) ^ n) *ᵥ c - (S.β ^ n * (S.ℓ ⬝ᵥ c)) • P.u := by
  rw [proj, mulVec_sub, mulVec_smul, P.pow_mulVec_u, smul_smul, mul_comm]

theorem norm_pow_proj_le (c : α → ℝ) (n : ℕ) :
    ‖((mat S) ^ n) *ᵥ P.proj c‖ ≤ P.C * P.ρ ^ n * ‖P.proj c‖ :=
  P.contract _ (P.dot_proj c) n

/-! ### Level sequences

A level sequence is the abstract bookkeeping of the origin tiles of the desubstitutions:
`x k = β x (k+1) + ℓ ⬝ c k` with integer `c k` from a finite set of projected norms. -/

/-- The partial sums `-x₀ u - Σ_{k<n} Mᵏ π(cₖ)`. -/
def psum (x : ℕ → ℝ) (c : ℕ → α → ℝ) (n : ℕ) : α → ℝ :=
  -(x 0 • P.u) - ∑ k ∈ Finset.range n, ((mat S) ^ k) *ᵥ P.proj (c k)

/-- The partial sums agree with `-βⁿ xₙ u` modulo `ℤᵈ`. -/
theorem partial_sub_mem {x : ℕ → ℝ} {c : ℕ → α → ℝ}
    (hx : ∀ k, x k = S.β * x (k + 1) + S.ℓ ⬝ᵥ c k) (hc : ∀ k, c k ∈ lattice α) (n : ℕ) :
    P.psum x c n - (-((S.β ^ n * x n) • P.u)) ∈ lattice α := by
  induction n with
  | zero => simp [psum]
  | succ n ih =>
    have key : P.psum x c (n + 1) - (-((S.β ^ (n + 1) * x (n + 1)) • P.u)) =
        (P.psum x c n - (-((S.β ^ n * x n) • P.u))) - ((mat S) ^ n) *ᵥ c n := by
      simp only [psum, Finset.sum_range_succ, P.pow_mulVec_proj]
      rw [hx n]
      simp only [add_smul, mul_add]
      rw [show S.β ^ (n + 1) * x (n + 1) = S.β ^ n * (S.β * x (n + 1)) by ring]
      abel
    rw [key]
    exact sub_mem ih ((pow_mulVec_mem_lattice S) (hc n) n)

/-- Summability of the realization series from a uniform bound on the projected counts. -/
theorem summable {c : ℕ → α → ℝ} {K : ℝ} (hK : ∀ k, ‖P.proj (c k)‖ ≤ K) :
    Summable fun k => ((mat S) ^ k) *ᵥ P.proj (c k) := by
  refine Summable.of_norm_bounded (g := fun k => P.C * K * P.ρ ^ k)
    ((summable_geometric_of_lt_one P.ρ_nonneg P.ρ_lt_one).mul_left _) fun k => ?_
  calc ‖((mat S) ^ k) *ᵥ P.proj (c k)‖ ≤ P.C * P.ρ ^ k * ‖P.proj (c k)‖ := P.norm_pow_proj_le _ k
    _ ≤ P.C * P.ρ ^ k * K :=
      mul_le_mul_of_nonneg_left (hK k) (mul_nonneg P.C_nonneg (pow_nonneg P.ρ_nonneg k))
    _ = P.C * K * P.ρ ^ k := by ring

/-- The realization vector `-x₀ u - Σₖ Mᵏ π(cₖ)` of a level sequence. -/
noncomputable def vec (x : ℕ → ℝ) (c : ℕ → α → ℝ) : α → ℝ :=
  -(x 0 • P.u) - ∑' k, (mat S ^ k) *ᵥ P.proj (c k)

theorem tendsto_psum {x : ℕ → ℝ} {c : ℕ → α → ℝ} {K : ℝ} (hK : ∀ k, ‖P.proj (c k)‖ ≤ K) :
    Tendsto (P.psum x c) atTop (𝓝 (P.vec x c)) :=
  tendsto_const_nhds.sub (P.summable hK).hasSum.tendsto_sum_nat

theorem tendsto_pow_proj_zero {d : ℕ → α → ℝ} {K : ℝ} (hK : ∀ n, ‖P.proj (d n)‖ ≤ K) :
    Tendsto (fun n => (mat S ^ n) *ᵥ P.proj (d n)) atTop (𝓝 0) := by
  have hρ := (tendsto_pow_atTop_nhds_zero_of_lt_one P.ρ_nonneg P.ρ_lt_one).const_mul (P.C * K)
  rw [mul_zero] at hρ
  refine squeeze_zero_norm (fun n => ?_) hρ
  calc ‖(mat S ^ n) *ᵥ P.proj (d n)‖ ≤ P.C * P.ρ ^ n * ‖P.proj (d n)‖ := P.norm_pow_proj_le _ n
    _ ≤ P.C * P.ρ ^ n * K :=
      mul_le_mul_of_nonneg_left (hK n) (mul_nonneg P.C_nonneg (pow_nonneg P.ρ_nonneg n))
    _ = P.C * K * P.ρ ^ n := by ring

/-- **Translation.**  If, eventually, `βⁿ x'ₙ = βⁿ xₙ + βⁿ (ℓ ⬝ dₙ) - t` with integer `dₙ` of
bounded projection, then the two realization vectors differ by `t u` modulo `ℤᵈ`. -/
theorem vec_sub_mem_of_eventually {x x' : ℕ → ℝ} {c c' : ℕ → α → ℝ}
    (hx : ∀ k, x k = S.β * x (k + 1) + S.ℓ ⬝ᵥ c k) (hc : ∀ k, c k ∈ lattice α)
    (hx' : ∀ k, x' k = S.β * x' (k + 1) + S.ℓ ⬝ᵥ c' k) (hc' : ∀ k, c' k ∈ lattice α)
    {K K' K'' : ℝ} (hK : ∀ k, ‖P.proj (c k)‖ ≤ K) (hK' : ∀ k, ‖P.proj (c' k)‖ ≤ K')
    {t : ℝ} {N : ℕ}
    (hd : ∀ n, ∃ d ∈ lattice α, ‖P.proj d‖ ≤ K'' ∧
      (N ≤ n → S.β ^ n * x' n = S.β ^ n * x n + S.β ^ n * (S.ℓ ⬝ᵥ d) - t)) :
    P.vec x' c' - P.vec x c - t • P.u ∈ lattice α := by
  choose d hdL hdK hdeq using hd
  have hlim : Tendsto (fun n => P.psum x' c' n - P.psum x c n - t • P.u -
      (mat S ^ n) *ᵥ P.proj (d n)) atTop (𝓝 (P.vec x' c' - P.vec x c - t • P.u - 0)) :=
    (((P.tendsto_psum hK').sub (P.tendsto_psum hK)).sub tendsto_const_nhds).sub
      (P.tendsto_pow_proj_zero hdK)
  rw [sub_zero] at hlim
  refine isClosed_lattice.mem_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
  have h1 := P.partial_sub_mem hx' hc' n
  have h2 := P.partial_sub_mem hx hc n
  have key : P.psum x' c' n - P.psum x c n - t • P.u - (mat S ^ n) *ᵥ P.proj (d n) =
      (P.psum x' c' n - -((S.β ^ n * x' n) • P.u)) - (P.psum x c n - -((S.β ^ n * x n) • P.u))
        - (mat S ^ n) *ᵥ d n := by
    rw [P.pow_mulVec_proj, hdeq n hn]
    simp only [add_smul, sub_smul]
    abel
  rw [key]
  exact sub_mem (sub_mem h1 h2) (pow_mulVec_mem_lattice S (hdL n) n)

/-- **Inflation.**  Prepending one level multiplies the realization vector by `M`, modulo the
integer vector `c'₀`. -/
theorem vec_shift {x x' : ℕ → ℝ} {c c' : ℕ → α → ℝ}
    (hx' : x' 0 = S.β * x 0 + S.ℓ ⬝ᵥ c' 0)
    (hcs : ∀ k, c' (k + 1) = c k) {K K' : ℝ} (hK : ∀ k, ‖P.proj (c k)‖ ≤ K)
    (hK' : ∀ k, ‖P.proj (c' k)‖ ≤ K') :
    P.vec x' c' = mat S *ᵥ P.vec x c - c' 0 := by
  have hcont : Continuous fun v : α → ℝ => mat S *ᵥ v :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have h1 : Tendsto (fun n => P.psum x' c' (n + 1) - mat S *ᵥ P.psum x c n) atTop
      (𝓝 (P.vec x' c' - mat S *ᵥ P.vec x c)) :=
    ((P.tendsto_psum hK').comp (tendsto_add_atTop_nat 1)).sub
      ((hcont.tendsto _).comp (P.tendsto_psum hK))
  have hconst : ∀ n, P.psum x' c' (n + 1) - mat S *ᵥ P.psum x c n = -c' 0 := by
    intro n
    simp only [psum, Finset.sum_range_succ', mulVec_sub, mulVec_neg, mulVec_smul, P.u_eigen,
      mulVec_sum, mulVec_mulVec, pow_succ', hcs, pow_zero, one_mulVec, hx', PisotData.proj,
      add_smul, smul_smul, mul_comm (x 0) S.β]
    abel
  have h2 := tendsto_nhds_unique h1 (by simp only [hconst]; exact tendsto_const_nhds)
  have h3 : P.vec x' c' = (P.vec x' c' - mat S *ᵥ P.vec x c) + mat S *ᵥ P.vec x c := by abel
  rw [h3, h2]
  abel

end PisotData

/-! ## Tiles of a hull element -/

section Tiles

variable {S : LengthSubst α}

/-- A placed tile starts after a prefix of the placed word. -/
theorem place_prefix {w : List α} {y : ℝ} {q : α × ℝ} (hq : q ∈ S.place w y) :
    ∃ p ∈ w.inits, q.2 = y + (p.map S.ℓ).sum := by
  induction w generalizing y with
  | nil => simp [LengthSubst.place] at hq
  | cons a w ih =>
    simp only [LengthSubst.place, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨[], by simp, by simp⟩
    · obtain ⟨p, hp, hq2⟩ := ih hq
      refine ⟨a :: p, by simp [hp], ?_⟩
      rw [hq2]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- The unique tile of `T` whose support contains `z`. -/
noncomputable def tileAt (T : S.Hull) (z : ℝ) : α × ℝ := (T.2.1 z).exists.choose

theorem tileAt_spec (T : S.Hull) (z : ℝ) : tileAt T z ∈ T.1 ∧ z ∈ S.supp (tileAt T z) :=
  (T.2.1 z).exists.choose_spec

theorem tileAt_eq {T : S.Hull} {z : ℝ} {p : α × ℝ} (hp : p ∈ T.1) (hz : z ∈ S.supp p) :
    tileAt T z = p :=
  (T.2.1 z).unique (tileAt_spec T z) ⟨hp, hz⟩

/-- The tile containing the origin. -/
noncomputable def origin (T : S.Hull) : α × ℝ := tileAt T 0

theorem origin_translate (s : ℝ) (U : S.Hull) :
    origin (translate s U) = ((tileAt U s).1, (tileAt U s).2 - s) := by
  obtain ⟨hmem, h1, h2⟩ := tileAt_spec U s
  refine tileAt_eq ?_ ⟨?_, ?_⟩
  · change ((tileAt U s).1, (tileAt U s).2 - s + s) ∈ U.1
    simpa using hmem
  · change (tileAt U s).2 - s ≤ 0
    linarith
  · change 0 < (tileAt U s).2 - s + S.ℓ (tileAt U s).1
    linarith

/-- The tile starting where a tile ends. -/
theorem tileAt_next {U : S.Hull} {q : α × ℝ} (hq : q ∈ U.1) :
    (tileAt U (q.2 + S.ℓ q.1)).2 = q.2 + S.ℓ q.1 := by
  obtain ⟨hmem, h1, h2⟩ := tileAt_spec U (q.2 + S.ℓ q.1)
  refine le_antisymm h1 (not_lt.mp fun hlt => ?_)
  set r := tileAt U (q.2 + S.ℓ q.1)
  have hw : max q.2 r.2 ∈ S.supp q ∧ max q.2 r.2 ∈ S.supp r := by
    have hq0 := S.ℓ_pos q.1
    refine ⟨⟨le_max_left _ _, max_lt (by linarith) hlt⟩, ⟨le_max_right _ _, ?_⟩⟩
    exact max_lt (by linarith) (by linarith [S.ℓ_pos r.1])
  have := (U.2.1 _).unique ⟨hmem, hw.2⟩ ⟨hq, hw.1⟩
  rw [this] at h2
  exact lt_irrefl _ h2

/-- The minimal tile length. -/
noncomputable def minLen [Nonempty α] (S : LengthSubst α) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty S.ℓ

theorem minLen_pos [Nonempty α] : 0 < minLen S :=
  (Finset.lt_inf'_iff _).mpr fun a _ => S.ℓ_pos a

theorem minLen_le [Nonempty α] (a : α) : minLen S ≤ S.ℓ a :=
  Finset.inf'_le _ (Finset.mem_univ a)

/-- Every tile has a tile ending at its left endpoint. -/
theorem exists_prev [Nonempty α] {U : S.Hull} {q : α × ℝ} (hq : q ∈ U.1) :
    ∃ b, (b, q.2 - S.ℓ b) ∈ U.1 := by
  have hm := minLen_pos (S := S)
  obtain ⟨hmem, h1, h2⟩ := tileAt_spec U (q.2 - minLen S)
  set r := tileAt U (q.2 - minLen S)
  have hle : r.2 + S.ℓ r.1 ≤ q.2 := by
    by_contra hlt
    have := (U.2.1 q.2).unique ⟨hmem, by constructor <;> linarith⟩
      ⟨hq, ⟨le_rfl, by linarith [S.ℓ_pos q.1]⟩⟩
    rw [this] at h1
    linarith
  have hnext := tileAt_next hmem
  obtain ⟨hmem', h1', h2'⟩ := tileAt_spec U (r.2 + S.ℓ r.1)
  refine ⟨r.1, ?_⟩
  have heq : r.2 + S.ℓ r.1 = q.2 := by
    by_contra hne
    have hlt : r.2 + S.ℓ r.1 < q.2 := lt_of_le_of_ne hle hne
    set r' := tileAt U (r.2 + S.ℓ r.1)
    have hlen := minLen_le (S := S) r'.1
    have := (U.2.1 q.2).unique ⟨hmem', by constructor <;> linarith⟩
      ⟨hq, ⟨le_rfl, by linarith [S.ℓ_pos q.1]⟩⟩
    rw [this] at hnext
    linarith
  have : r = (r.1, q.2 - S.ℓ r.1) := Prod.ext rfl (by simp; linarith)
  rw [← this]
  exact hmem

/-- A tile containing a point within `minLen` of the origin is the origin tile or one of its two
neighbours: its start differs from the origin tile's by `ℓ ⬝ d`, `d ∈ {0, eₐ, -e_b}`. -/
theorem tileAt_near [Nonempty α] (U : S.Hull) {s : ℝ} (hs : |s| < minLen S) :
    ∃ d ∈ ({0} ∪ range (fun a => (Pi.single a 1 : α → ℝ)) ∪
        range (fun a => -(Pi.single a 1 : α → ℝ))),
      (tileAt U s).2 = (origin U).2 + S.ℓ ⬝ᵥ d := by
  obtain ⟨hmem, h1, h2⟩ : origin U ∈ U.1 ∧ 0 ∈ S.supp (origin U) := tileAt_spec U 0
  set q := origin U
  have hs' := abs_lt.mp hs
  rcases lt_or_ge s q.2 with hlt | hge
  · obtain ⟨b, hb⟩ := exists_prev hmem
    refine ⟨-(Pi.single b 1), Or.inr ⟨b, rfl⟩, ?_⟩
    rw [tileAt_eq hb ⟨by change q.2 - S.ℓ b ≤ s; linarith [minLen_le (S := S) b],
      by change s < q.2 - S.ℓ b + S.ℓ b; linarith⟩]
    simp
    ring
  · rcases lt_or_ge s (q.2 + S.ℓ q.1) with hlt' | hge'
    · refine ⟨0, Or.inl (Or.inl rfl), ?_⟩
      rw [tileAt_eq hmem ⟨hge, hlt'⟩]
      simp
    · refine ⟨Pi.single q.1 1, Or.inl (Or.inr ⟨q.1, rfl⟩), ?_⟩
      obtain ⟨hn, hn1, hn2⟩ := tileAt_spec U (q.2 + S.ℓ q.1)
      have hstart := tileAt_next hmem
      set r := tileAt U (q.2 + S.ℓ q.1)
      rw [tileAt_eq hn ⟨by linarith, by linarith [minLen_le (S := S) r.1]⟩, hstart, dot_single]

/-- The tile of an inflation at `z` lies in the image of the tile at `z / β`. -/
theorem tileAt_inflate [Nonempty α] (U : S.Hull) (z : ℝ) :
    tileAt (inflateH U) z ∈ S.place (S.σ (tileAt U (z / S.β)).1) (S.β * (tileAt U (z / S.β)).2) := by
  obtain ⟨⟨p, hp, hq⟩, hz⟩ := tileAt_spec (inflateH U) z
  rw [tileAt_eq hp (S.mem_supp_parent hq hz)]
  exact hq

end Tiles

/-! ## The realization -/

section Realization

variable {S : LengthSubst α} [Nonempty α] (P : PisotData S)

namespace PisotData

/-- A uniform bound for the projected letter counts of prefixes of substitution images. -/
noncomputable def offsetBound : ℝ :=
  ∑ a, ((S.σ a).inits.map fun w => ‖P.proj (ab w)‖).sum

theorem le_offsetBound {a : α} {w : List α} (hw : w ∈ (S.σ a).inits) :
    ‖P.proj (ab w)‖ ≤ P.offsetBound := by
  have h1 : ‖P.proj (ab w)‖ ≤ ((S.σ a).inits.map fun w => ‖P.proj (ab w)‖).sum :=
    List.single_le_sum (by simp) _ (List.mem_map_of_mem hw)
  refine h1.trans (Finset.single_le_sum (f := fun a =>
    ((S.σ a).inits.map fun w => ‖P.proj (ab w)‖).sum) (fun a _ => List.sum_nonneg (by simp)) (Finset.mem_univ a))

/-- A uniform bound for the projected unit vectors. -/
noncomputable def unitBound : ℝ := ∑ a, ‖P.proj (Pi.single a 1)‖

theorem near_bound {d : α → ℝ} (hd : d ∈ ({0} ∪ range (fun a => (Pi.single a 1 : α → ℝ)) ∪
        range (fun a => -(Pi.single a 1 : α → ℝ)))) :
    d ∈ lattice α ∧ ‖P.proj d‖ ≤ P.unitBound := by
  have hnn : 0 ≤ P.unitBound := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hle (a : α) : ‖P.proj (Pi.single a 1)‖ ≤ P.unitBound :=
    Finset.single_le_sum (f := fun a => ‖P.proj (Pi.single a 1)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  rcases hd with (rfl | ⟨a, rfl⟩) | ⟨a, rfl⟩
  · exact ⟨zero_mem _, by simpa [PisotData.proj] using hnn⟩
  · exact ⟨single_mem_lattice a, hle a⟩
  · exact ⟨neg_mem (single_mem_lattice a), by rw [P.proj_neg, norm_neg]; exact hle a⟩

end PisotData

variable {P}

/-- The prefix count placing the origin tile of `inflate U` in the image of `U`'s. -/
noncomputable def offset (U : S.Hull) : α → ℝ :=
  ab (place_prefix (by simpa using tileAt_inflate U 0)).choose

theorem offset_eq (U : S.Hull) :
    (origin (inflateH U)).2 = S.β * (origin U).2 + S.ℓ ⬝ᵥ offset U := by
  obtain ⟨_, hpos⟩ := (place_prefix (by simpa using tileAt_inflate U 0)).choose_spec
  rw [offset, dot_ab]
  exact hpos

theorem offset_mem (U : S.Hull) : offset U ∈ lattice α := ab_mem_lattice _

variable (P)

theorem offset_bound (U : S.Hull) : ‖P.proj (offset U)‖ ≤ P.offsetBound :=
  P.le_offsetBound (place_prefix (by simpa using tileAt_inflate U 0)).choose_spec.1

/-! ### Desubstitution under recognizability -/

variable (hR : Bijective (inflateH (S := S)))

/-- The desubstitution, the inverse of inflation (recognizability). -/
noncomputable def desub : S.Hull → S.Hull := surjInv hR.2

theorem inflateH_desub (T : S.Hull) : inflateH (desub hR T) = T := surjInv_eq hR.2 T

theorem desub_inflateH (T : S.Hull) : desub hR (inflateH T) = T :=
  hR.1 (inflateH_desub hR _)

/-- The `n`-th desubstitution `Tₙ`. -/
noncomputable def level (n : ℕ) (T : S.Hull) : S.Hull := (desub hR)^[n] T

theorem inflateH_level_succ (n : ℕ) (T : S.Hull) :
    inflateH (level hR (n + 1) T) = level hR n T := by
  rw [level, iterate_succ_apply', inflateH_desub]; rfl

theorem level_succ_inflateH (n : ℕ) (T : S.Hull) :
    level hR (n + 1) (inflateH T) = level hR n T := by
  rw [level, iterate_succ_apply, desub_inflateH]; rfl

theorem level_add (m n : ℕ) (T : S.Hull) : level hR (m + n) T = level hR m (level hR n T) :=
  iterate_add_apply _ m n T

theorem level_inflate_iterate (n : ℕ) (T : S.Hull) : level hR n (inflateH^[n] T) = T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', level_succ_inflateH, ih]

theorem desub_translate (t : ℝ) (U : S.Hull) :
    desub hR (translate t U) = translate (t / S.β) (desub hR U) := by
  apply hR.1
  rw [inflateH_desub, inflateH_translate, inflateH_desub,
    mul_div_cancel₀ t S.β_pos.ne']

theorem level_translate (t : ℝ) (n : ℕ) (T : S.Hull) :
    level hR n (translate t T) = translate (t / S.β ^ n) (level hR n T) := by
  induction n with
  | zero => simp [level]
  | succ n ih =>
    rw [level, iterate_succ_apply', ← level, ih, desub_translate, div_div, ← pow_succ]
    simp only [level, iterate_succ_apply']

/-- The origin-tile starts `xₙ` of the desubstitutions. -/
noncomputable def xs (T : S.Hull) (n : ℕ) : ℝ := (origin (level hR n T)).2

/-- The prefix counts `cₙ` linking consecutive levels. -/
noncomputable def cs (T : S.Hull) (n : ℕ) : α → ℝ := offset (level hR (n + 1) T)

theorem xs_succ (T : S.Hull) (n : ℕ) :
    xs hR T n = S.β * xs hR T (n + 1) + S.ℓ ⬝ᵥ cs hR T n := by
  have h := offset_eq (level hR (n + 1) T)
  rw [inflateH_level_succ] at h
  exact h

theorem cs_mem (T : S.Hull) (n : ℕ) : cs hR T n ∈ lattice α := offset_mem _

theorem cs_bound (T : S.Hull) (n : ℕ) : ‖P.proj (cs hR T n)‖ ≤ P.offsetBound :=
  offset_bound P _

/-- The realization vector `G(T) ∈ ℝᵈ`. -/
noncomputable def realVec (T : S.Hull) : α → ℝ := P.vec (xs hR T) (cs hR T)

/-- The torus map `T ↦ G(T) mod ℤᵈ`. -/
noncomputable def torusRealize (T : S.Hull) : Torus α := (realVec P hR T : Torus α)

/-- The torus map semiconjugates inflation to the matrix endomorphism. -/
theorem torusRealize_inflate (T : S.Hull) :
    torusRealize P hR (inflateH T) = torusMap S (torusRealize P hR T) := by
  have hshift := P.vec_shift (x := xs hR T) (c := cs hR T) (x' := xs hR (inflateH T))
    (c' := cs hR (inflateH T)) ?_ ?_ (cs_bound P hR T) (cs_bound P hR _)
  · rw [torusRealize, torusRealize, realVec, realVec, hshift, torusMap_mk,
      QuotientAddGroup.mk_sub, (QuotientAddGroup.eq_zero_iff _).mpr (cs_mem hR _ 0), sub_zero]
  · have h := offset_eq T
    simpa [xs, cs, level, desub_inflateH] using h
  · intro k
    simp only [cs]
    rw [level_succ_inflateH]

/-- The torus map carries translation by `t` to translation by `t u`. -/
theorem torusRealize_translate (hβ : 1 < S.β) (t : ℝ) (T : S.Hull) :
    torusRealize P hR (translate t T) = torusRealize P hR T + ((t • P.u : α → ℝ) : Torus α) := by
  have hβ0 : 0 < S.β := S.β_pos
  have hlim : Tendsto (fun n : ℕ => t / S.β ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hβ)
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, |t / S.β ^ n| < minLen S := eventually_atTop.mp
    ((by simpa using hlim.abs : Tendsto (fun n : ℕ => |t / S.β ^ n|) atTop (𝓝 0)).eventually
      (gt_mem_nhds (minLen_pos (S := S))))
  have hmem := P.vec_sub_mem_of_eventually (xs_succ hR T) (cs_mem hR T)
    (xs_succ hR (translate t T)) (cs_mem hR _) (cs_bound P hR T) (cs_bound P hR _)
    (K'' := P.unitBound) (t := t) (N := N) fun n => ?_
  · rw [torusRealize, torusRealize, realVec, realVec, ← QuotientAddGroup.mk_add,
      QuotientAddGroup.eq]
    convert neg_mem hmem using 1
    abel
  · by_cases hn : N ≤ n
    · obtain ⟨d, hd, heq⟩ := tileAt_near (level hR n T) (hN n hn)
      obtain ⟨hdL, hdK⟩ := P.near_bound hd
      refine ⟨d, hdL, hdK, fun _ => ?_⟩
      have hx : xs hR (translate t T) n = xs hR T n + S.ℓ ⬝ᵥ d - t / S.β ^ n := by
        rw [xs, level_translate, origin_translate, heq, xs, origin]
      rw [hx, mul_sub, mul_add, mul_div_cancel₀ t (pow_pos hβ0 n).ne']
    · exact ⟨0, zero_mem _, (P.near_bound (Or.inl (Or.inl rfl))).2, fun h => absurd h hn⟩

/-- A periodic tiling with a tile ending at the origin realizes to `0` on the torus. -/
theorem torusRealize_periodic_vertex {T : S.Hull} {p : ℕ} (hp : 0 < p)
    (hper : inflateH^[p] T = T) {b : α} (hend : EndsAt T 0 b) : torusRealize P hR T = 0 := by
  have hlevel : level hR p T = T := by
    conv_lhs => rw [← hper]
    exact level_inflate_iterate hR p T
  have hlevel_mul (k : ℕ) : level hR (p * k) T = T := by
    rw [level, iterate_mul]; exact iterate_fixed hlevel k
  have hx0 : (origin T).2 = 0 := by
    have h := tileAt_next (U := T) hend
    simp only [zero_sub, neg_add_cancel] at h
    exact h
  have hsub : Tendsto (fun k : ℕ => p * k) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => hk.trans (Nat.le_mul_of_pos_left k hp)⟩
  have hmem : realVec P hR T ∈ lattice α := by
    refine isClosed_lattice.mem_of_tendsto
      ((P.tendsto_psum (cs_bound P hR T)).comp hsub) (Eventually.of_forall fun k => ?_)
    have h := P.partial_sub_mem (xs_succ hR T) (cs_mem hR T) (p * k)
    simp only [xs, hlevel_mul, hx0, mul_zero, zero_smul, neg_zero, sub_zero] at h
    exact h
  exact (QuotientAddGroup.eq_zero_iff _).mpr hmem

end Realization


/-! ## The solenoid -/

section Solenoid

variable (S : LengthSubst α)

/-- The solenoid of `M`: sequences of torus points with `M zₙ₊₁ = zₙ`, the inverse limit of
the torus endomorphism.  It is an additive group. -/
def solenoid : AddSubgroup (ℕ → Torus α) where
  carrier := {z | ∀ n, torusMap S (z (n + 1)) = z n}
  zero_mem' n := map_zero _
  add_mem' {z w} hz hw n := by simp [map_add, hz n, hw n]
  neg_mem' {z} hz n := by simp [map_neg, hz n]

/-- The solenoid as a type. -/
abbrev Solenoid : Type _ := ↥(solenoid S)

/-- The shift `Â`, coordinatewise `M`. -/
def shiftS (z : Solenoid S) : Solenoid S :=
  ⟨fun n => torusMap S (z.1 n), fun n => congrArg (torusMap S) (z.2 n)⟩

theorem shiftS_zero : shiftS S 0 = 0 := Subtype.ext (funext fun _ => map_zero _)

/-- `Â` is a bijection in every case: its inverse forgets the first coordinate.  The torus
endomorphism `M` itself is not injective when `|det M| ≠ 1`. -/
theorem shiftS_bijective : Bijective (shiftS S) := by
  refine ⟨fun z w h => Subtype.ext (funext fun n => ?_), fun z => ?_⟩
  · have := congrFun (congrArg Subtype.val h) (n + 1)
    simp only [shiftS] at this
    rw [← z.2 n, ← w.2 n, this]
  · exact ⟨⟨fun n => z.1 (n + 1), fun n => z.2 (n + 1)⟩,
      Subtype.ext (funext fun n => z.2 n)⟩

/-- In the unit case the first coordinate already determines a solenoid point. -/
theorem coord_zero_injective (hM : Injective (torusMap S)) :
    Injective fun z : Solenoid S => z.1 0 := by
  intro z w h
  refine Subtype.ext (funext fun n => ?_)
  induction n with
  | zero => exact h
  | succ n ih => exact hM (by rw [z.2 n, w.2 n, ih])

theorem iterate_coord (z : Solenoid S) (k n : ℕ) : (torusMap S)^[k] (z.1 (n + k)) = z.1 n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply, ← add_assoc, z.2, ih]

end Solenoid

section SolenoidRealization

variable {S : LengthSubst α} [Nonempty α] (P : PisotData S) (hR : Bijective (inflateH (S := S)))

/-- **The geometric-realization map** `T ↦ (G(Tₙ) mod ℤᵈ)ₙ` into the solenoid. -/
noncomputable def realize (T : S.Hull) : Solenoid S :=
  ⟨fun n => torusRealize P hR (level hR n T), fun n => by
    rw [← torusRealize_inflate, inflateH_level_succ]⟩

/-- The realization semiconjugates inflation to the solenoid shift. -/
theorem realize_inflate (T : S.Hull) :
    realize P hR (inflateH T) = shiftS S (realize P hR T) := by
  refine Subtype.ext (funext fun n => ?_)
  change torusRealize P hR (level hR n (inflateH T)) = torusMap S (torusRealize P hR (level hR n T))
  cases n with
  | zero => exact torusRealize_inflate P hR T
  | succ n =>
    rw [level_succ_inflateH, ← torusRealize_inflate, inflateH_level_succ]

theorem realize_semiconj : Semiconj (realize P hR) inflateH (shiftS S) := realize_inflate P hR

/-- The translation flow on the solenoid, `(zₙ) ↦ (zₙ + t β⁻ⁿ u)`. -/
noncomputable def flow (t : ℝ) (z : Solenoid S) : Solenoid S :=
  z + ⟨fun n => (((t / S.β ^ n) • P.u : α → ℝ) : Torus α), fun n => by
    show torusMap S (((t / S.β ^ (n + 1)) • P.u : α → ℝ) : Torus α) =
      (((t / S.β ^ n) • P.u : α → ℝ) : Torus α)
    rw [torusMap_mk, mulVec_smul, P.u_eigen, smul_smul, pow_succ,
      div_mul_eq_mul_div, mul_div_mul_right _ _ S.β_pos.ne']⟩

/-- The realization carries translation to the solenoid flow. -/
theorem realize_translate (hβ : 1 < S.β) (t : ℝ) (T : S.Hull) :
    realize P hR (translate t T) = flow P t (realize P hR T) := by
  refine Subtype.ext (funext fun n => ?_)
  change torusRealize P hR (level hR n (translate t T)) =
    torusRealize P hR (level hR n T) + (((t / S.β ^ n) • P.u : α → ℝ) : Torus α)
  rw [level_translate, torusRealize_translate P hR hβ]

/-- **(R4)** for the constructed map: a periodic tiling with a tile ending at the origin
realizes to `0`. -/
theorem realize_r4 : R4ZeroFibre inflateH (realize P hR) 0 EndsAt := by
  intro T b hT hend
  obtain ⟨p, hp, hper⟩ := hT
  have hper' : inflateH^[p] T = T := hper
  have hlevel : level hR p T = T := by
    conv_lhs => rw [← hper']
    exact level_inflate_iterate hR p T
  have h0 : (realize P hR T).1 0 = 0 := torusRealize_periodic_vertex P hR hp hper' hend
  refine Subtype.ext (funext fun n => ?_)
  set z := realize P hR T
  -- `Mᵖ` fixes each coordinate and `Mⁿ` kills it.
  have hfix : (torusMap S)^[p] (z.1 n) = z.1 n := by
    conv_lhs => rw [show z.1 n = z.1 (n + p) by
      change torusRealize P hR (level hR n T) = torusRealize P hR (level hR (n + p) T)
      rw [level_add, hlevel]]
    exact iterate_coord S z p n
  have hkill : (torusMap S)^[n] (z.1 n) = 0 := by
    simpa [h0] using iterate_coord S z n 0
  have hmul : (torusMap S)^[p * n] (z.1 n) = z.1 n := by
    rw [iterate_mul]; exact iterate_fixed hfix n
  have hle : n ≤ p * n := Nat.le_mul_of_pos_left n hp
  rw [← hmul, ← Nat.sub_add_cancel hle, iterate_add_apply, hkill]
  exact iterate_fixed (map_zero _) _

/-- The published inputs of `PeriodicPartnerHull` with the realization, its semiconjugacy, the
distinguished point and (R4) **constructed**.  Recognizability, BDS periodicization and the
finite-fibre theorem for this map remain inputs. -/
noncomputable def publishedInputs
    (hBDS : BDSPeriodicization (inflateH (S := S)) translate
      (Psc.PeriodicPartnerAsymptotic.TranslationRightAsymptotic translate))
    (hfin : ∀ q, {T | realize P hR T = q}.Finite) : PublishedInputs S (Solenoid S) where
  inflate_injective := hR.1
  bds := hBDS
  A := shiftS S
  realize := realize P hR
  semiconj := realize_semiconj P hR
  finite_fibres := hfin
  q₀ := 0
  q₀_fixed := shiftS_zero S
  r4 := realize_r4 P hR

end SolenoidRealization

end Psc.PeriodicPartnerRealization
