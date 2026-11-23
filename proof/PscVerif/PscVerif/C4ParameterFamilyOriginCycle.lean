import PscVerif.C4ParameterFamilyZeroFibreAnchor
import PscVerif.ShiftedRadixCycle

/-!
# The origin-tile recurrence of the literal family has one interior cycle

For `k ≥ 2` the premise `PeriodicLatticeOriginsClassified` of the anchor
reduction is proved. A placed tile with a lattice start is `(a, -len v)`
for an integer vector `v`. Its origin child is `(a', -len v')` with
`v' = M v - (d', e', 0)`, where `d'` and `e'` count the `0`s and `1`s
before the child. Along an orbit the middle coordinate `w` satisfies the
shifted radix recurrence of `Psc.ShiftedRadixCycle`, whose only eventual
behaviour is the three-phase cycle. The anchor theorem and the all-pairs
witness statement follow without a premise.

Source decision: `docs/c4-zero-fibre-anchor-proof-2026-11-22.md`.
-/

namespace Psc.ParameterFamilyOriginCycle

open Function Matrix Set
open Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.ParameterFamilyRows (substitution)
open Psc.ParameterFamilyWords (ones)
open Psc.PeriodicPartnerEvenTails (place_append)
open Psc.ShiftedRadixCycle
open Psc.ParameterFamilyZeroFibreAnchor Psc.ParameterFamilyRecognizability

variable (k : ℕ) (hk : 1 ≤ k)

/-- The length of an integer vector. -/
noncomputable def len (v₀ v₁ v₂ : ℤ) : ℝ :=
  v₀ * expansion k hk + v₁ * expansion k hk ^ 2 + v₂ * (expansion k hk + 2)

/-- Multiplication by the expansion is the incidence matrix on vectors. -/
theorem expansion_mul_len (v₀ v₁ v₂ : ℤ) :
    expansion k hk * len k hk v₀ v₁ v₂ = len k hk (v₁ + 2 * v₂) (v₀ + k * v₁ + v₂) v₁ := by
  unfold len
  push_cast
  linear_combination (v₁ : ℝ) * expansion_equation k hk

theorem mem_place_ones {m : ℕ} {x : ℝ} {q : Fin 3 × ℝ}
    (hq : q ∈ (geometry k hk).place (ones m) x) :
    ∃ j : ℕ, j < m ∧ q = (1, x + j * (geometry k hk).ℓ 1) := by
  induction m generalizing x with
  | zero => simp [ones, LengthSubst.place] at hq
  | succ m ih =>
    simp only [ones, List.replicate_succ, LengthSubst.place, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨j, hj, rfl⟩ := ih hq
      exact ⟨j + 1, by omega, Prod.ext rfl (by push_cast; ring)⟩

theorem place_image_one (x : ℝ) :
    (geometry k hk).place (substitution k 1) x =
      (0, x) :: ((geometry k hk).place (ones k) (x + (geometry k hk).ℓ 0) ++
        [(2, x + (geometry k hk).ℓ 0 + (k : ℝ) * (geometry k hk).ℓ 1)]) := by
  simp [substitution, LengthSubst.place, place_append, ones, nsmul_eq_mul]

/-- One step of the origin-tile map on a lattice tile whose support
contains the origin. -/
theorem origin_step (a : Fin 3) (v₀ v₁ v₂ : ℤ)
    (h₁ : -len k hk v₀ v₁ v₂ ≤ 0)
    (h₂ : 0 < -len k hk v₀ v₁ v₂ + (geometry k hk).ℓ a) :
    ∃ (a' : Fin 3) (d' e' : ℤ), Child k ((a : ℕ) : ℤ) ((a' : ℕ) : ℤ) d' e' ∧
      originChild (geometry k hk) (a, -len k hk v₀ v₁ v₂) =
        (a', -len k hk (v₁ + 2 * v₂ - d') (v₀ + k * v₁ + v₂ - e') v₁) ∧
      -len k hk (v₁ + 2 * v₂ - d') (v₀ + k * v₁ + v₂ - e') v₁ ≤ 0 ∧
      0 < -len k hk (v₁ + 2 * v₂ - d') (v₀ + k * v₁ + v₂ - e') v₁ + (geometry k hk).ℓ a' := by
  set S := geometry k hk with hS
  set x := -len k hk v₀ v₁ v₂ with hx
  have hβ : 0 < S.β := S.β_pos
  have hcov : (0 : ℝ) ∈ Ico (S.β * x) (S.β * x + ((S.σ a).map S.ℓ).sum) := by
    rw [S.eigen]
    constructor <;> nlinarith
  obtain ⟨p, hp, hz⟩ := S.place_cover hcov
  have hchild : originChild S (a, x) = p := originChild_eq hp hz
  have hmul := expansion_mul_len k hk v₀ v₁ v₂
  have key : ∀ (a' : Fin 3) (d' e' : ℤ), Child k ((a : ℕ) : ℤ) ((a' : ℕ) : ℤ) d' e' →
      p = (a', S.β * x + d' * S.ℓ 0 + e' * S.ℓ 1) →
      ∃ (a' : Fin 3) (d' e' : ℤ), Child k ((a : ℕ) : ℤ) ((a' : ℕ) : ℤ) d' e' ∧
        originChild S (a, x) =
          (a', -len k hk (v₁ + 2 * v₂ - d') (v₀ + k * v₁ + v₂ - e') v₁) ∧
        -len k hk (v₁ + 2 * v₂ - d') (v₀ + k * v₁ + v₂ - e') v₁ ≤ 0 ∧
        0 < -len k hk (v₁ + 2 * v₂ - d') (v₀ + k * v₁ + v₂ - e') v₁ + S.ℓ a' := by
    intro a' d' e' hC hpe
    have hpos : S.β * x + d' * S.ℓ 0 + e' * S.ℓ 1 =
        -len k hk (v₁ + 2 * v₂ - d') (v₀ + k * v₁ + v₂ - e') v₁ := by
      have h0 : S.ℓ 0 = expansion k hk := rfl
      have h1 : S.ℓ 1 = expansion k hk ^ 2 := rfl
      have hb : S.β = expansion k hk := rfl
      rw [h0, h1, hb, hx]
      unfold len at hmul ⊢
      push_cast at hmul ⊢
      linear_combination -hmul
    subst hpe
    refine ⟨a', d', e', hC, ?_, ?_, ?_⟩
    · rw [hchild, hpos]
    · have h := hz.1
      change S.β * x + d' * S.ℓ 0 + e' * S.ℓ 1 ≤ 0 at h
      rwa [hpos] at h
    · have h := hz.2
      change 0 < S.β * x + d' * S.ℓ 0 + e' * S.ℓ 1 + S.ℓ a' at h
      rwa [hpos] at h
  fin_cases a
  · have hp' : p = (1, S.β * x) := by
      simpa [hS, substitution, LengthSubst.place] using hp
    exact key 1 0 0 (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by simp [hp'])
  · have hp' : p ∈ S.place (substitution k 1) (S.β * x) := hp
    rw [hS, place_image_one, List.mem_cons, List.mem_append, List.mem_singleton] at hp'
    rcases hp' with rfl | hp' | rfl
    · exact key 0 0 0 (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) (by simp [← hS])
    · obtain ⟨j, hj, rfl⟩ := mem_place_ones k hk hp'
      refine key 1 1 j (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, by positivity, by exact_mod_cast hj⟩)))
        (Prod.ext rfl ?_)
      simp [← hS]
    · exact key 2 1 k (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))))
        (Prod.ext rfl (by simp [← hS]))
  · have hp' : p ∈ [((0 : Fin 3), S.β * x), (0, S.β * x + S.ℓ 0),
        (1, S.β * x + S.ℓ 0 + S.ℓ 0)] := by
      simpa [hS, substitution, LengthSubst.place] using hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · exact key 0 0 0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))))) (by simp)
    · exact key 0 1 0
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))))) (by simp)
    · exact key 1 2 0
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))))))
        (Prod.ext rfl (by push_cast; ring))

/-- The orbit of a lattice tile under the origin-tile map, in integer
coordinates, with the digit data of every step. -/
theorem orbit_data (a₀ : Fin 3) (z₀ z₁ z₂ : ℤ)
    (h₁ : -len k hk z₀ z₁ z₂ ≤ 0) (h₂ : 0 < -len k hk z₀ z₁ z₂ + (geometry k hk).ℓ a₀) :
    ∃ (A : ℕ → Fin 3) (V₀ W V₂ D E : ℕ → ℤ),
      (∀ i, (originChild (geometry k hk))^[i] (a₀, -len k hk z₀ z₁ z₂) =
        (A i, -len k hk (V₀ i) (W i) (V₂ i))) ∧
      (∀ i, -len k hk (V₀ i) (W i) (V₂ i) ≤ 0 ∧
        0 < -len k hk (V₀ i) (W i) (V₂ i) + (geometry k hk).ℓ (A i)) ∧
      (∀ i, Child k ((A i : ℕ) : ℤ) ((A (i + 1) : ℕ) : ℤ) (D (i + 1)) (E (i + 1))) ∧
      (∀ i, V₀ (i + 1) = W i + 2 * V₂ i - D (i + 1)) ∧
      (∀ i, W (i + 1) = V₀ i + k * W i + V₂ i - E (i + 1)) ∧
      (∀ i, V₂ (i + 1) = W i) := by
  let S := geometry k hk
  let V := {s : Fin 3 × ℤ × ℤ × ℤ // -len k hk s.2.1 s.2.2.1 s.2.2.2 ≤ 0 ∧
    0 < -len k hk s.2.1 s.2.2.1 s.2.2.2 + S.ℓ s.1}
  have step : ∀ s : V, ∃ (t : V) (d' e' : ℤ),
      Child k ((s.1.1 : ℕ) : ℤ) ((t.1.1 : ℕ) : ℤ) d' e' ∧
      originChild S (s.1.1, -len k hk s.1.2.1 s.1.2.2.1 s.1.2.2.2) =
        (t.1.1, -len k hk t.1.2.1 t.1.2.2.1 t.1.2.2.2) ∧
      t.1.2.1 = s.1.2.2.1 + 2 * s.1.2.2.2 - d' ∧
      t.1.2.2.1 = s.1.2.1 + k * s.1.2.2.1 + s.1.2.2.2 - e' ∧
      t.1.2.2.2 = s.1.2.2.1 := by
    intro s
    obtain ⟨a', d', e', hC, ho, g₁, g₂⟩ :=
      origin_step k hk s.1.1 s.1.2.1 s.1.2.2.1 s.1.2.2.2 s.2.1 s.2.2
    exact ⟨⟨(a', _, _, _), g₁, g₂⟩, d', e', hC, ho, rfl, rfl, rfl⟩
  choose nxt dd ee hCh hOr r₀ r₁ r₂ using step
  let s₀ : V := ⟨(a₀, z₀, z₁, z₂), h₁, h₂⟩
  have hsq : ∀ i, nxt^[i + 1] s₀ = nxt (nxt^[i] s₀) := fun i => iterate_succ_apply' nxt i s₀
  refine ⟨fun i => (nxt^[i] s₀).1.1, fun i => (nxt^[i] s₀).1.2.1,
    fun i => (nxt^[i] s₀).1.2.2.1, fun i => (nxt^[i] s₀).1.2.2.2,
    fun i => dd (nxt^[i - 1] s₀), fun i => ee (nxt^[i - 1] s₀), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iterate_succ_apply', ih]
      simp only
      rw [hsq i]
      exact hOr _
  · exact fun i => (nxt^[i] s₀).2
  · intro i
    simp only [Nat.add_sub_cancel]
    rw [hsq i]
    exact hCh _
  · intro i
    simp only [Nat.add_sub_cancel]
    rw [hsq i]
    exact r₀ _
  · intro i
    simp only [Nat.add_sub_cancel]
    rw [hsq i]
    exact r₁ _
  · intro i
    simp only
    rw [hsq i]
    exact r₂ _

/-- A tile starting at the origin has an origin child starting there. -/
theorem originChild_vertex (S : LengthSubst (Fin 3)) (a : Fin 3) :
    (originChild S (a, 0)).2 = 0 := by
  obtain ⟨b, u, hu⟩ := List.exists_cons_of_ne_nil (S.ne_nil a)
  have hp : (b, S.β * 0) ∈ S.place (S.σ ((a, (0 : ℝ)) : Fin 3 × ℝ).1)
      (S.β * ((a, (0 : ℝ)) : Fin 3 × ℝ).2) := by
    change (b, S.β * 0) ∈ S.place (S.σ a) (S.β * 0)
    rw [hu]
    simp [LengthSubst.place]
  have hz : (0 : ℝ) ∈ S.supp (b, S.β * 0) := by
    refine ⟨by simp, ?_⟩
    simpa using S.ℓ_pos b
  rw [originChild_eq hp hz]
  simp

theorem originChild_vertex_iterate (S : LengthSubst (Fin 3)) (q : Fin 3 × ℝ) (hq : q.2 = 0)
    (j : ℕ) : ((originChild S)^[j] q).2 = 0 := by
  induction j generalizing q with
  | zero => simpa using hq
  | succ j ih =>
    rw [iterate_succ_apply]
    apply ih
    obtain ⟨a, x⟩ := q
    simp only at hq
    subst hq
    exact originChild_vertex S a

theorem length_le_sq (a : Fin 3) : (geometry k hk).ℓ a ≤ expansion k hk ^ 2 := by
  have hb := two_lt_expansion k hk
  fin_cases a <;> simp [geometry] <;> nlinarith

variable (hk₂ : 2 ≤ k)

include hk₂

theorem contraction_coefficients :
    0 < (expansion k hk)⁻¹ ∧
      2 * (expansion k hk)⁻¹ + 2 * (expansion k hk)⁻¹ ^ 2 < 1 := by
  have hb := two_lt_expansion k hk
  have hc := expansion_equation k hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk₂
  have hpos : 0 < expansion k hk := by linarith
  refine ⟨inv_pos.mpr hpos, ?_⟩
  have hsq : 2 * expansion k hk + 2 < expansion k hk ^ 2 := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_le_mul_of_nonneg_left h hpos.le,
      mul_le_mul_of_nonneg_right hk' (sq_nonneg (expansion k hk))]
  have h2 : 2 * (expansion k hk)⁻¹ + 2 * (expansion k hk)⁻¹ ^ 2 =
      (2 * expansion k hk + 2) / expansion k hk ^ 2 := by
    field_simp
  rw [h2, div_lt_one (by positivity)]
  exact hsq

/-- **The arithmetic premise holds.** The only periodic interior lattice
tiles of the origin-tile map are the three phases. -/
theorem periodicLatticeOriginsClassified : PeriodicLatticeOriginsClassified k hk := by
  intro q n hn hper hneg hpos ⟨v, hv, hq⟩
  set S := geometry k hk with hS
  set β := expansion k hk with hβdef
  obtain ⟨z₀, hz₀⟩ := hv 0
  obtain ⟨z₁, hz₁⟩ := hv 1
  obtain ⟨z₂, hz₂⟩ := hv 2
  have hq2 : q.2 = -len k hk z₀ z₁ z₂ := by
    rw [hq]
    simp [dotProduct, Fin.sum_univ_three, hS, geometry, len, ← hz₀, ← hz₁, ← hz₂]
    ring
  have hqe : q = (q.1, -len k hk z₀ z₁ z₂) := Prod.ext rfl hq2
  obtain ⟨A, V₀, W, V₂, D, E, horb, hval, hCh, r₀, r₁, r₂⟩ :=
    orbit_data k hk q.1 z₀ z₁ z₂ (by rw [← hq2]; exact hneg.le) (by rw [← hq2]; exact hpos)
  rw [← hqe] at horb
  have hb2 : 2 < β := two_lt_expansion k hk
  have hβpos : 0 < β := by linarith
  have hperiod : ∀ m, (originChild S)^[n * m] q = q := by
    intro m
    rw [iterate_mul]
    exact iterate_fixed hper m
  -- every tile of the orbit is interior
  have hint : ∀ i, 0 < len k hk (V₀ i) (W i) (V₂ i) := by
    intro i
    have hle := (hval i).1
    rcases lt_or_eq_of_le (neg_nonpos.mp hle) with h | h
    · exact h
    · exfalso
      have hz : ((originChild S)^[i] q).2 = 0 := by rw [horb i]; simp [← h]
      have hj := originChild_vertex_iterate S _ hz (n * (i + 1) - i)
      rw [← iterate_add_apply, Nat.sub_add_cancel
        (by nlinarith [Nat.le_mul_of_pos_left (i + 1) hn] : i ≤ n * (i + 1)), hperiod] at hj
      linarith
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hD : Digits (k : ℤ) (fun i => ((A i : ℕ) : ℤ)) D E W := by
    refine ⟨hCh, fun i => ?_⟩
    have a1 := r₁ (i + 2)
    have a2 := r₀ (i + 1)
    have a3 := r₂ (i + 1)
    have a4 := r₂ i
    linarith
  obtain ⟨hα, hθ⟩ := contraction_coefficients k hk hk₂
  have hE : Bounded β⁻¹ W := by
    intro i
    have hb := child_bounds (hCh (i + 1)) hk0
    have hL := hint (i + 2)
    have hU := (hval (i + 2)).2
    have hle := length_le_sq k hk (A (i + 2))
    have e0 : V₀ (i + 2) = W (i + 1) + 2 * W i - D (i + 2) := by
      have a2 := r₀ (i + 1)
      have a4 := r₂ i
      linarith
    have e2 : V₂ (i + 2) = W (i + 1) := r₂ (i + 1)
    have key : (W (i + 2) : ℝ) + (2 * β⁻¹ + 2 * β⁻¹ ^ 2) * W (i + 1) + 2 * β⁻¹ * W i =
        (len k hk (V₀ (i + 2)) (W (i + 2)) (V₂ (i + 2)) + D (i + 2) * β) / β ^ 2 := by
      rw [eq_div_iff (by positivity), e0, e2]
      unfold len
      push_cast
      field_simp
      ring
    have hd0 : (0 : ℝ) ≤ D (i + 2) := by exact_mod_cast hb.1
    have hd2 : (D (i + 2) : ℝ) ≤ 2 := by exact_mod_cast hb.2.1
    rw [key]
    constructor
    · exact div_pos (add_pos_of_pos_of_nonneg hL (mul_nonneg hd0 hβpos.le)) (by positivity)
    · rw [div_lt_iff₀ (by positivity)]
      have h1 : (1 + 2 * β⁻¹) * β ^ 2 = β ^ 2 + 2 * β := by
        field_simp
      nlinarith
  obtain ⟨b, hb⟩ := eventually_cycle hα hθ (by exact_mod_cast hk₂) hE hD
  -- read the cycle off at a multiple of the period
  have hi : b + 3 ≤ n * (b + 3) := Nat.le_mul_of_pos_left _ hn
  obtain ⟨j, r, hr, hjr⟩ : ∃ j r, r < 3 ∧ n * (b + 3) = b + 3 * j + 3 + r :=
    ⟨(n * (b + 3) - b - 3) / 3, (n * (b + 3) - b - 3) % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  have hqi := (hperiod (b + 3)).symm
  rw [hjr] at hqi
  have P0 := hb j
  have P1 := hb (j + 1)
  rw [show b + 3 * (j + 1) = b + 3 * j + 3 by ring] at P1
  have P1' : W (b + 3 * j + 3) = 1 ∧ W (b + 3 * j + 4) = 0 ∧ W (b + 3 * j + 5) = 0 ∧
      ((A (b + 3 * j + 3) : ℕ) : ℤ) = 1 ∧ ((A (b + 3 * j + 4) : ℕ) : ℤ) = 1 ∧
      ((A (b + 3 * j + 5) : ℕ) : ℤ) = 1 ∧ D (b + 3 * j + 3) = 1 ∧ D (b + 3 * j + 4) = 1 ∧
      D (b + 3 * j + 5) = 1 := P1
  have hA : ∀ i, ((A i : ℕ) : ℤ) = 1 → A i = 1 := by
    intro i h
    apply Fin.ext
    have : (A i : ℕ) = 1 := by exact_mod_cast h
    simpa using this
  have s2 : V₂ (b + 3 * j + 2) = W (b + 3 * j + 1) := r₂ (b + 3 * j + 1)
  have s3 : V₂ (b + 3 * j + 3) = W (b + 3 * j + 2) := r₂ (b + 3 * j + 2)
  have s4 : V₂ (b + 3 * j + 4) = W (b + 3 * j + 3) := r₂ (b + 3 * j + 3)
  have s5 : V₂ (b + 3 * j + 5) = W (b + 3 * j + 4) := r₂ (b + 3 * j + 4)
  have t3 : V₀ (b + 3 * j + 3) = W (b + 3 * j + 2) + 2 * V₂ (b + 3 * j + 2) -
      D (b + 3 * j + 3) := r₀ (b + 3 * j + 2)
  have t4 : V₀ (b + 3 * j + 4) = W (b + 3 * j + 3) + 2 * V₂ (b + 3 * j + 3) -
      D (b + 3 * j + 4) := r₀ (b + 3 * j + 3)
  have t5 : V₀ (b + 3 * j + 5) = W (b + 3 * j + 4) + 2 * V₂ (b + 3 * j + 4) -
      D (b + 3 * j + 5) := r₀ (b + 3 * j + 4)
  have hℓ0 : S.ℓ 0 = β := rfl
  have hℓ1 : S.ℓ 1 = β ^ 2 := rfl
  have hℓ2 : S.ℓ 2 = β + 2 := rfl
  interval_cases r
  · right; left
    have hv0 : V₀ (b + 3 * j + 3) = -1 := by omega
    have hv2 : V₂ (b + 3 * j + 3) = 0 := by omega
    rw [hqi, horb (b + 3 * j + 3), hA _ P1'.2.2.2.1, hv0, P1'.1, hv2, hℓ0, hℓ1]
    refine Prod.ext rfl ?_
    simp only [len]
    push_cast
    ring
  · right; right
    have hv0 : V₀ (b + 3 * j + 4) = 0 := by omega
    have hv2 : V₂ (b + 3 * j + 4) = 1 := by omega
    rw [hqi, horb (b + 3 * j + 4), hA _ P1'.2.2.2.2.1, hv0, P1'.2.1, hv2, hℓ2]
    refine Prod.ext rfl ?_
    simp only [len]
    push_cast
    ring
  · left
    have hv0 : V₀ (b + 3 * j + 5) = 1 := by omega
    have hv2 : V₂ (b + 3 * j + 5) = 0 := by omega
    rw [hqi, horb (b + 3 * j + 5), hA _ P1'.2.2.2.2.2.1, hv0, P1'.2.2.1, hv2, hℓ0]
    refine Prod.ext rfl ?_
    simp only [len]
    push_cast
    ring

/-- **The anchor theorem.** For `k ≥ 2`, every tiling over the zero
solenoid history shares a labelled tile with the period-two seam anchor. -/
theorem anchor_common_tile {V U : (geometry k hk).Hull}
    (hV0 : (1, 0) ∈ V.1) (hV : inflateH^[2] V = V)
    (hzV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    (V.1 ∩ U.1).Nonempty :=
  anchor_common_tile_of_classified k hk hk₂ (periodicLatticeOriginsClassified k hk hk₂)
    hV0 hV hzV hzU

/-- Any two tilings over the zero history share a labelled tile. -/
theorem zero_fibre_common_tile (T U : (geometry k hk).Hull)
    (hzT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    (T.1 ∩ U.1).Nonempty :=
  (Psc.ParameterFamilyZeroFibreWitnesses.windowWitnesses_iff_common_tile k hk hk₂
      (by norm_num) hzT hzU).mp
    (all_pair_witnesses_of_classified k hk hk₂
      (periodicLatticeOriginsClassified k hk hk₂) T U hzT hzU)

/-- **All-pairs witnesses.** Any two tilings over the zero history have
the three exact radius-one agreements with one common translation. -/
theorem all_pair_witnesses (T U : (geometry k hk).Hull)
    (hzT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    Psc.PeriodicPartnerProximal.WindowWitnesses (geometry k hk) 1 T U :=
  all_pair_witnesses_of_classified k hk hk₂ (periodicLatticeOriginsClassified k hk hk₂)
    T U hzT hzU

/-- Any two tilings over the zero history agree exactly on arbitrarily
large windows after a common translation. -/
theorem zero_fibre_exactProximal (T U : (geometry k hk).Hull)
    (hzT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    Psc.PeriodicPartnerProximal.ExactProximal (geometry k hk) T U :=
  zero_fibre_exactProximal_of_classified k hk hk₂
    (periodicLatticeOriginsClassified k hk hk₂) T U hzT hzU

/-- A zero-fibre tiling has a vertex at the origin or its origin tile is
one of the three interior phases. -/
theorem zero_fibre_origin (U : (geometry k hk).Hull)
    (hzU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    (origin U).2 = 0 ∨ origin U = (1, -(geometry k hk).ℓ 0) ∨
      origin U = (1, (geometry k hk).ℓ 0 - (geometry k hk).ℓ 1) ∨
      origin U = (1, -(geometry k hk).ℓ 2) := by
  by_cases h : (origin U).2 = 0
  · exact Or.inl h
  · right
    obtain ⟨n, hn, hper⟩ := periodic_of_realize_zero k hk hzU
    obtain ⟨h1, h2⟩ := (tileAt_spec U 0).2
    exact periodicLatticeOriginsClassified k hk hk₂ (origin U) n hn
      (originChild_periodic_of_periodic hper) (lt_of_le_of_ne h1 h) h2
      (Psc.PeriodicPartnerPeriodicZero.lattice_origin_of_realize_zero _ _ hzU)

end Psc.ParameterFamilyOriginCycle
