/-
# The interior 4-cycle of `01/122/201`

`docs/c4-neutral-rank-seam-ceiling-2026-11-18.md`, the `+1` control.  The note uses one
interior `f`-cycle of period 4 for `σ = 01/122/201`.  This module proves, for every positive
left eigen-row `ℓ` of `M`, that

* `seam_address_classify`: the interior periodic addresses of `σ` at `k = 1, 2, 3, 4` are
  exactly the four of `Psc.NeutralRankSeam` (all at `k = 4`), decided by enumerating the
  occurrences of `e` in `σᵏ(e)` and the integrality of `adj(Mᵏ − I) p(P) / det(Mᵏ − I)`;
* `seam_periodic_iff`: the interior states `x` with `fᵏ x = x` for some `1 ≤ k ≤ 4` are
  exactly the four states `seamStates`, and only for `k = 4`;
* **`seam_single_cycle`**: these four states are `x₀, f x₀, f² x₀, f³ x₀` for
  `x₀ = (1; 0, 1, −1)`; they form a single `f`-cycle of exact period 4.

**Not proved here.**  That no interior periodic state of `σ` has a period other than 4
(periods `5, 6, …` are not enumerated); the Mojo search of the note certifies the complete list
in the certified box of the (F) note, which is not formalized.
-/
import PscVerif.NeutralRankSeam

namespace Psc.NeutralRankSeamCycle

open Matrix Psc.Binomial Psc.Incidence Psc.GeometricF Psc.GeometricFLemmas Psc.NeutralRankSeam

/-! ### Arithmetic of `σ` -/

theorem seam_inc : inc seamSubst = !![1, 0, 1; 1, 1, 1; 0, 2, 1] := by decide

/-- `χ_M = X³ − 3X² + X − 1`. -/
theorem seam_charpoly (K : Type*) [CommRing K] :
    ((inc seamSubst).map (Nat.cast : ℕ → K)).charpoly =
      Polynomial.X ^ 3 - 3 * Polynomial.X ^ 2 + Polynomial.X - 1 := by
  rw [Psc.Cyclicity.charpoly_fin_three, seam_inc]
  simp [Matrix.trace_fin_three, Matrix.det_fin_three, Psc.Cyclicity.wedge2,
    Psc.Cyclicity.pairFst, Psc.Cyclicity.pairSnd, map_ofNat]
  ring

theorem seam_irreducible : Irreducible ((inc seamSubst).map (Nat.cast : ℕ → ℚ)).charpoly := by
  rw [seam_charpoly]
  convert Psc.BPrimeCore.irreducible_cubic (-3) 1 (-1) (by decide) using 1
  simp only [Int.cast_neg, Int.cast_one, Int.cast_ofNat, map_neg, map_one, map_ofNat]
  ring

theorem seam_primitive : ∀ a c, 0 < (inc seamSubst ^ 3) a c := fun a c => by
  rw [seam_inc]; fin_cases a <;> fin_cases c <;> decide +kernel

theorem seam_prim : ∃ k ≥ 1, ∀ a c, 0 < (inc seamSubst ^ k) a c :=
  ⟨3, by norm_num, seam_primitive⟩

/-! ### Enumerating interior addresses -/

/-- `adj(Mᵏ − I)` and `det(Mᵏ − I)` for `k = 1, …, 4`. -/
def adjK : ℕ → Matrix (Fin 3) (Fin 3) ℤ
  | 1 => !![-2, 2, 0; 0, 0, 1; 2, 0, 0]
  | 2 => !![-8, 4, 2; 2, -4, 4; 4, 4, -4]
  | 3 => !![-16, 2, 8; 8, -14, 9; 2, 16, -14]
  | _ => !![-40, 8, 16; 16, -32, 20; 8, 32, -32]

def detK : ℕ → ℤ
  | 1 => 2
  | 2 => 12
  | 3 => 26
  | _ => 48

theorem adjK_mul : ∀ k ∈ [1, 2, 3, 4],
    adjK k * (incZ seamSubst ^ k - 1) = detK k • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by decide

/-- Positions `i` where `σᵏ(e)` has `e` with nonempty prefix and suffix and an integral
solution of `(Mᵏ − I) v = p(σᵏ(e)[0, i))`. -/
def goodIdx (k : ℕ) (e : Fin 3) : List ℕ :=
  (List.range (power seamSubst k e).length).filter fun i =>
    (power seamSubst k e)[i]? = some e ∧ 0 < i ∧ i + 1 < (power seamSubst k e).length ∧
      ∀ j, detK k ∣ (adjK k *ᵥ pvec ((power seamSubst k e).take i)) j

theorem goodIdx_eq :
    (∀ k ∈ [1, 2, 3], ∀ e, goodIdx k e = []) ∧
      goodIdx 4 0 = [] ∧ goodIdx 4 1 = [8, 22, 60] ∧ goodIdx 4 2 = [38] := by decide

/-- An interior address at `k` is an occurrence position in `goodIdx` and determines `v`. -/
theorem address_index {k : ℕ} (hk : k ∈ [1, 2, 3, 4]) {e : Fin 3} {P Q : List (Fin 3)}
    {v : Fin 3 → ℤ} (h : IsInteriorAddress seamSubst k e P Q v) :
    P.length ∈ goodIdx k e ∧ P = (power seamSubst k e).take P.length ∧
      detK k • v = adjK k *ᵥ pvec ((power seamSubst k e).take P.length) := by
  obtain ⟨hw, hP, hQ, hv⟩ := h
  have htake : (power seamSubst k e).take P.length = P := by rw [hw]; simp
  have hdv : detK k • v = adjK k *ᵥ pvec P := by
    rw [← hv, mulVec_mulVec, adjK_mul k hk, smul_mulVec, one_mulVec]
  refine ⟨?_, htake.symm, by rw [htake, hdv]⟩
  have hlen : (power seamSubst k e).length = P.length + 1 + Q.length := by
    rw [hw]; simp; omega
  simp only [goodIdx, List.mem_filter, List.mem_range, decide_eq_true_eq]
  refine ⟨by omega, ⟨by rw [hw]; simp, List.length_pos_of_ne_nil hP,
    by have := List.length_pos_of_ne_nil hQ; omega, fun j => ⟨v j, ?_⟩⟩⟩
  have := congrFun hdv j
  rw [htake]
  simpa [mul_comm] using this.symm

/-- The four interior states of period 4. -/
def seamStates : Finset (Fin 3 × (Fin 3 → ℤ)) :=
  {(1, ![0, 1, -1]), (1, ![-1, 0, 1]), (1, ![0, 0, 1]), (2, ![1, 0, 0])}

theorem v_of_index {k : ℕ} (hd : detK k ≠ 0) {v w : Fin 3 → ℤ} (h : detK k • v = w) :
    v = fun j => w j / detK k := by
  funext j
  have := congrFun h j
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [← this, Int.mul_ediv_cancel_left _ hd]

/-- **Every interior address at `k ≤ 4` is one of the four, at `k = 4`.** -/
theorem seam_address_classify {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {e : Fin 3}
    {P Q : List (Fin 3)} {v : Fin 3 → ℤ} (h : IsInteriorAddress seamSubst k e P Q v) :
    k = 4 ∧ (e, v) ∈ seamStates := by
  have hk : k ∈ [1, 2, 3, 4] := by simp; omega
  obtain ⟨hi, -, hv⟩ := address_index hk h
  have hd : detK k ≠ 0 := by interval_cases k <;> decide
  rw [v_of_index hd hv]
  obtain ⟨h123, h40, h41, h42⟩ := goodIdx_eq
  interval_cases k
  · rw [h123 1 (by simp)] at hi; simp at hi
  · rw [h123 2 (by simp)] at hi; simp at hi
  · rw [h123 3 (by simp)] at hi; simp at hi
  refine ⟨rfl, ?_⟩
  fin_cases e
  · change P.length ∈ goodIdx 4 0 at hi
    rw [h40] at hi; simp at hi
  · change P.length ∈ goodIdx 4 1 at hi
    rw [h41] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi <;> rw [hi] <;> decide
  · change P.length ∈ goodIdx 4 2 at hi
    rw [h42] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi]; decide

theorem seamStates_address : ∀ x ∈ seamStates,
    ∃ P Q, IsInteriorAddress seamSubst 4 x.1 P Q x.2 := by
  intro x hx
  simp only [seamStates, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨_, _, seam_isInteriorAddress_1⟩
  · exact ⟨_, _, seam_isInteriorAddress_2⟩
  · exact ⟨_, _, seam_isInteriorAddress_3⟩
  · exact ⟨_, _, seam_isInteriorAddress_4⟩

/-! ### Periodic states and the single cycle -/

section Periodic

variable {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
  (hℓM : ℓ ᵥ* (inc seamSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ)

include hℓ hℓM

theorem seam_lengthData : LengthData seamSubst (lenHom ℓ) β ∧ 1 < β := by
  have hβ := Psc.BPrimeCore.one_lt_perron seamSubst seam_prim hℓ hℓM
  exact ⟨lengthData_of_left_eigen (by linarith) hℓ hℓM, hβ⟩

/-- **Periodic interior states of period dividing `k ≤ 4`.** -/
theorem seam_periodic_iff {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : Fin 3 × (Fin 3 → ℤ)) :
    (IsState (lenHom ℓ) x ∧ x.2 ≠ 0 ∧ StepN seamSubst (lenHom ℓ) k x x) ↔
      k = 4 ∧ x ∈ seamStates := by
  obtain ⟨hL, hβ⟩ := seam_lengthData hℓ hℓM
  have hzero := lenHom_zero_kernel_of_pos seamSubst seam_irreducible hℓ hℓM
  obtain ⟨j, v⟩ := x
  rw [periodic_iff_isInteriorAddress hL hβ hzero hk1]
  constructor
  · rintro ⟨P, Q, h⟩
    exact seam_address_classify hk1 hk4 h
  · rintro ⟨rfl, hx⟩
    exact seamStates_address _ hx

/-- A vertex state maps to a vertex state. -/
theorem step_vertex {a : Fin 3} {y : Fin 3 × (Fin 3 → ℤ)}
    (h : Step seamSubst (lenHom ℓ) (a, 0) y) : y.2 = 0 := by
  obtain ⟨hL, -⟩ := seam_lengthData hℓ hℓM
  obtain ⟨P, S, -, hy, hs, -⟩ := h
  rw [hy, mulVec_zero, zero_sub] at hs ⊢
  by_cases hP : P = []
  · subst hP; funext i; simp
  · exfalso
    rw [map_neg] at hs
    linarith [L_pvec_pos hL.pos hP]

theorem stepN_vertex {a : Fin 3} :
    ∀ n {y : Fin 3 × (Fin 3 → ℤ)}, StepN seamSubst (lenHom ℓ) n (a, 0) y → y.2 = 0
  | 0, _, h => by rw [← h]
  | n + 1, y, ⟨z, hz, hy⟩ => by
    have := stepN_vertex n hz
    rw [show z = (z.1, 0) from Prod.ext rfl this] at hy
    exact step_vertex hℓ hℓM hy

omit hℓ hℓM in
theorem isState_of_stepN {x : Fin 3 × (Fin 3 → ℤ)} (hx : IsState (lenHom ℓ) x) :
    ∀ n {y}, StepN seamSubst (lenHom ℓ) n x y → IsState (lenHom ℓ) y
  | 0, _, h => h ▸ hx
  | _ + 1, _, ⟨_, _, ⟨_, _, _, _, hs⟩⟩ => hs

/-- The base state `x₀ = (1; 0, 1, −1)`. -/
def x0 : Fin 3 × (Fin 3 → ℤ) := (1, ![0, 1, -1])

/-- **The single cycle.**  The iterates `fʲ x₀`, `j = 0, 1, 2, 3`, are pairwise distinct and
are exactly `seamStates`; `f⁴ x₀ = x₀`. -/
theorem seam_single_cycle :
    ∃ y : Fin 4 → Fin 3 × (Fin 3 → ℤ),
      (∀ j : Fin 4, StepN seamSubst (lenHom ℓ) j x0 (y j)) ∧ Function.Injective y ∧
        Finset.univ.image y = seamStates ∧ StepN seamSubst (lenHom ℓ) 4 x0 x0 := by
  obtain ⟨hL, hβ⟩ := seam_lengthData hℓ hℓM
  have hpos := hL.pos
  have hx0 : x0 ∈ seamStates := by decide
  obtain ⟨hst, hv0, hper⟩ :=
    (seam_periodic_iff hℓ hℓM (k := 4) (by norm_num) le_rfl x0).2 ⟨rfl, hx0⟩
  choose y hy using fun j : Fin 4 => stepN_total hL hst (j : ℕ)
  -- `f^{4-j}` brings `y j` back to `x₀`
  have hback : ∀ j : Fin 4, StepN seamSubst (lenHom ℓ) (4 - j) (y j) x0 := by
    intro j
    obtain ⟨z, hz⟩ := stepN_total hL (isState_of_stepN hst _ (hy j)) (4 - j)
    have h4 := stepN_add (hy j) _ hz
    rw [show (j : ℕ) + (4 - j) = 4 by omega] at h4
    rwa [stepN_unique hpos 4 h4 hper] at hz
  have hmem : ∀ j : Fin 4, y j ∈ seamStates := by
    intro j
    have hs := isState_of_stepN hst _ (hy j)
    have hv : (y j).2 ≠ 0 := by
      intro h0
      have := stepN_vertex hℓ hℓM (a := (y j).1) (4 - j)
        (by rw [show ((y j).1, (0 : Fin 3 → ℤ)) = y j from Prod.ext rfl h0.symm]; exact hback j)
      exact hv0 this
    have hp := stepN_add (hback j) _ (hy j)
    rw [show 4 - (j : ℕ) + j = 4 by omega] at hp
    exact ((seam_periodic_iff hℓ hℓM (k := 4) (by norm_num) le_rfl _).1 ⟨hs, hv, hp⟩).2
  have hinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    wlog hlt : (i : ℕ) < j generalizing i j
    · exact this hij.symm (Ne.symm hne) (by have := Fin.val_ne_of_ne hne; omega)
    obtain ⟨z, hz⟩ := stepN_total hL (isState_of_stepN hst _ (hy i)) (j - i)
    have h := stepN_add (hy i) _ hz
    rw [show (i : ℕ) + (j - i) = j by omega] at h
    rw [stepN_unique hpos _ h (hy j), ← hij] at hz
    have hs := isState_of_stepN hst _ (hy i)
    have hv : (y i).2 ≠ 0 := by
      have := hmem i
      simp only [seamStates, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h <;> rw [h] <;> decide
    have := ((seam_periodic_iff hℓ hℓM (k := j - i) (by omega) (by omega) _).1 ⟨hs, hv, hz⟩).1
    omega
  refine ⟨y, hy, hinj, ?_, hper⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
    exact hmem j
  · rw [Finset.card_image_of_injective _ hinj]
    decide

end Periodic

end Psc.NeutralRankSeamCycle
