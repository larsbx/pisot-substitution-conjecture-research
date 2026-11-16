/-
# Theorem FC1 on a three-letter PIP3 specimen: property (F) for Tribonacci

`docs/c4-geometric-f-class-2026-11-16.md` §2 (states, the prototile state map `f`, property
(F), Lemma 3 (3), (4)) and §3 (Theorem FC1); `docs/c4-fc3-family-2026-11-16.md` §3–§5 (the
coordinate `Y`, identity (\*), the trapping argument of Lemma FM-T, and the reading of the
stable coordinates as a shift radix system).  `PscVerif.GeometricFPisot` proves Theorem FC1 on
the standing class with property (F) as the only hypothesis left (`fc1_pip3`) and records that
(F) is proved in Lean for no substitution on three letters: Tribonacci satisfied every
hypothesis of `fc1_pip3` except (F), and the complete instance was Fibonacci, on two letters.
This module proves (F) for Tribonacci, and so gives the first complete machine-checked
instance of Theorem FC1 on PIP3.

**Setting.**  `σ = Psc.Descendants.tribSubst`, `0 ↦ 01, 1 ↦ 02, 2 ↦ 0`, with incidence matrix
`[[1,1,1],[1,0,0],[0,1,0]]` (`Psc.BPrime.trib_inc`), `M v = (v₀ + v₁ + v₂, v₀, v₁)`
(`trib_mulVec`).  `ℓ` is any positive left eigen-row, `ℓ M = β ℓ`, and `θ = β⁻¹`.  States, the
state map and (F) are those of `PscVerif.GeometricFInclusion` (`IsState`, `Step`, `StepN`,
`PropertyF`) for the length functional `Psc.GeometricF.lenHom ℓ`.

**Definitions.**  `TribData β θ ℓ` (the Perron data and rational enclosures below); `tribY`
(`Y(v) = v₀ + (β − 1) v₁ + θ v₂`, so `ℓ·v = ℓ₀ Y(v)`); `tribH` (the centre
`h = 1/(2(β + θ))`); `tribQ` (the stable quadratic form
`Q(v) = u₁² + (β − 1) u₁ u₂ + θ u₂²`, `uᵢ = vᵢ − h`); `TribReach L b c` (every state with
`(v₁, v₂) = (b, c)` reaches a vertex state); `ctrlSubst` (the control `01/12/021`).

**The argument.**  The `ℓ¹` trap of Lemma FM-T does not apply: the coefficients `β − 1 ≈ 0.839`
and `θ ≈ 0.544` of the contracting factor `t² + (β − 1) t + θ` of `χ_M` sum to more than `1`.
A quadratic form, exact for that factor, replaces it.
1. *Perron data* (`trib_data`): `ℓ₁ = (β − 1) ℓ₀`, `ℓ₂ = θ ℓ₀`, `β³ = β² + β + 1`,
   `β ∈ (1.8392, 1.8393)`, `θ ∈ (0.54368, 0.54372)`.  Every tile is at most `ℓ₀`
   (`trib_le_len_zero`), so a state has `0 ≤ Y < 1` (`trib_state_Y`).
2. *Shape of a step* (`trib_step_coords`): every proper prefix of an image is `[]` or `0`, so
   `f(j; v) = (j'; v₀ + v₁ + v₂ − d, v₀, v₁)`, `d ∈ {0, 1}`.  With `v₀ = Y − (β − 1) v₁ − θ v₂`
   (`trib_forced`) the stable pair follows `(b, c) ↦ (−⌊(β − 1) b + θ c⌋, b)`, the shift radix
   system with parameter `(θ, β − 1)`.
3. *Lyapunov form* (`trib_lyap_real`, `tribQ_step`): with `δ = Y − 1/2`,
   `p = −((β − 1)/2) u₁ − θ u₂`, one step gives exactly `Q' = θ Q + 2 δ p + δ²`, and
   `θ Q − p² = (θ − (β − 1)²/4) u₁² ≥ 0` (`trib_kappa`: the gap is `> 0.3675`); with
   `2 δ p ≤ 3 δ² + p²/3` and `δ² ≤ 1/4`, `Q' ≤ (4/3) θ Q + 1`.
4. *Box* (`tribQ_stepN`, `tribQ_periodic`, `trib_box_real`, `trib_box`): on an `f`-cycle
   `Q (1 − (4/3) θ) ≤ 1`, so `Q < 3.636`, and then `v₁ ∈ [−2, 2]`, `v₂ ∈ [−2, 3]`.
5. *Finite check* (`trib_reach_zero`, `trib_reach_step`, `trib_reach_box`): from each of the 30
   pairs of the box the radix map reaches `(0, 0)` in at most 7 steps, through 32 nonzero pairs;
   each forced value is decided by `linarith` from the enclosures of `β` and `θ` (it is the
   floor of an irrational number, not a `decide` computation); a state with `v₁ = v₂ = 0` is a
   vertex state.
6. *(F)* (`trib_propertyF`): a periodic state reaches a vertex state, vertex states are forward
   invariant (`Psc.GeometricF.stepN_absorb`), so the state is a vertex state.

**Proved here, in full** (`propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no
`native_decide`):
* **`trib_propertyF`**: property (F) for Tribonacci, for every positive left eigen-row `ℓ`;
  `trib_reaches_vertex` (Lemma 3 (4): every state reaches a vertex state);
* **`trib_fc1_hypotheses_complete`**: every hypothesis of `Psc.GeometricFPisot.fc1_pip3` holds
  for Tribonacci (primitive, `χ_M` irreducible over `ℚ`, a positive left eigen-row `ℓ` with
  `ℓ M = β ℓ`, every other complex root of `χ_M` in the open unit disc, (F) for `ℓ`);
* **`trib_fc1`**: `fc1_pip3` instantiated, with no hypothesis left;
* **`trib_fc1_evaluated`**: both sides evaluated: explicit left strong-coincidence witnesses at
  level `1` on words (`trib_witness_01`, `trib_witness_02`, `trib_witness_12`), the
  `g`-periodic letters are exactly `{0}` (`trib_isPeriodicLetter_zero`,
  `trib_not_isPeriodicLetter`), and, through `trib_fc1`, no strict system; all three
  statements of the equivalence are false;
* **negative control** `ctrl_not_propertyF`, `ctrl_exists_not_propertyF`: on `01/12/021`
  (primitive, `ctrl_prim`) the state `(2; −1, 0, 1)` is `f`-fixed for every positive left
  eigen-row, so (F) fails.

**Hypotheses and where they enter.**  The spectral hypotheses are the theorems on main
(`Psc.BPrime.trib_prim`, `trib_irreducible`, `trib_isPisot`, `Psc.PerronExistence`).  Inside the
proof of (F): the Pisot property enters quantitatively, as `(4/3) θ < 1` and
`θ > (β − 1)²/4` (a complex pair of modulus `√θ < 1`), through the rational enclosures of `β`
derived from `β³ = β² + β + 1` and `ℓ > 0`; irreducibility is not used; the shape of the words
enters in step 1 (`ℓ_j ≤ ℓ₀`) and step 2 (only the letter `0` occurs in a proper prefix of an
image).

**Negative controls: where the argument stops.**  On `01/12/021`, which is PIP3 on paper
(`χ_M = t³ − 3t² + 2t − 1`; not proved in Lean here) and fails (F) (`ctrl_not_propertyF`;
also pinned in `kernel/tests/test_c4_geometric_f.mojo`), step 2 fails: `σ(1) = 12` and
`σ(2) = 021` have proper prefixes with letters other than `0`.  So (F) is not automatic on PIP3
and the proof is specific to Tribonacci.  On the strict controls of the brief the spectral input
is absent (reducible: `10/102/211`, its reversal, C-D1, C-D2, `1/012/101`, cf.
`Psc.GeometricFPisot.carrier_not_pisot_roots`; singular or not Pisot: Thue–Morse,
`012/120/201`, `01/2/120`, `1/012/1`; not primitive: `1/0/22`), and nothing here applies.

**Deviations and cross-checks.**  The box is in the two stable coordinates only (`v₀` is
forced).  The Mojo module `kernel/psc/c4_geometric_f.mojo` decides (F) for Tribonacci with the
certified radii `[2, 3, 4]` for `|v₀|, |v₁|, |v₂|` (`stable_radii`, pinned); the Lean box is a
different bound, and its ranges for `v₁`, `v₂` lie inside the radii `3`, `4`.  No novelty is
claimed for (F) on Tribonacci: the radix map is the shift radix system attached to `β`, and the
finiteness property of the Tribonacci number is classical (Frougny–Solomyak; see the stop/go
record of the family note); that identification is a remark and is neither imported nor
formalised.

**Not proved here.**  (F) for any other substitution on three letters, or for a family; that
`01/12/021` is PIP3.  Nothing new about Tribonacci's strict systems: "no strict system" is on
main without Theorem FC1 (`Psc.StrictSystem.trib_no_strictSystem`), and `trib_fc1_evaluated`
reaches it through the elementary direction of the equivalence; item (3) of Theorem FC1 (the
construction of a strict system) is not exercised, and since `0` is the only `g`-periodic letter
items (1), (2) are not instantiated.  Theorems FC2, P, FC3, N, Fork.  Universal C4 is open:
Theorem FC1 is an equivalence, and this instance excludes no strict system on any other
specimen.
-/
import PscVerif.GeometricFPisot

namespace Psc.GeometricFTriple

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.BPrimeBinding Psc.GeometricF
  Psc.GeometricFPisot
open Psc.StrictSystem (StrictSystem StrongCoincidenceWitness)
open Psc.Descendants (tribSubst)

/-! ### The Perron data of Tribonacci -/

/-- The incidence action of Tribonacci `0 ↦ 01, 1 ↦ 02, 2 ↦ 0`:
`M (v₀, v₁, v₂) = (v₀ + v₁ + v₂, v₀, v₁)`. -/
theorem trib_mulVec (v : Fin 3 → ℤ) :
    incZ tribSubst *ᵥ v = ![v 0 + v 1 + v 2, v 0, v 1] := by
  funext i
  rw [incZ, Psc.BPrime.trib_inc]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **The Perron data of Tribonacci**, for a positive left eigen-row `ℓ` with eigenvalue `β`
and `θ = β⁻¹`: `ℓ₁ = (β − 1) ℓ₀`, `ℓ₂ = θ ℓ₀`, `β³ = β² + β + 1`, and rational enclosures
`β ∈ (1.8392, 1.8393)`, `θ ∈ (0.54368, 0.54372)`; with the length data of `ℓ`. -/
structure TribData (β θ : ℝ) (ℓ : Fin 3 → ℝ) : Prop where
  len : LengthData tribSubst (lenHom ℓ) β
  pos0 : 0 < ℓ 0
  l1 : ℓ 1 = (β - 1) * ℓ 0
  l2 : ℓ 2 = θ * ℓ 0
  inv : β * θ = 1
  cubic : β ^ 3 = β ^ 2 + β + 1
  lo : 18392 / 10000 < β
  hi : β < 18393 / 10000
  tlo : 54368 / 100000 < θ
  thi : θ < 54372 / 100000

variable {β θ : ℝ} {ℓ : Fin 3 → ℝ}

/-- Every positive left eigen-row of the Tribonacci incidence matrix has the Perron data
`TribData β β⁻¹ ℓ`. -/
theorem trib_data (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) : TribData β β⁻¹ ℓ := by
  have h0 := congrFun hℓM 0
  have h1 := congrFun hℓM 1
  have h2 := congrFun hℓM 2
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Psc.BPrime.trib_inc] at h0 h1 h2
  have hl0 := hℓ 0
  have hl2 := hℓ 2
  have hβ0 : 0 < β := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hl2.le]
  have hcub : β ^ 3 = β ^ 2 + β + 1 := by
    have h : (β ^ 3 - β ^ 2 - β - 1) * ℓ 2 = 0 := by
      linear_combination (-β) * h0 - h1 - (β ^ 2 - β - 1) * h2
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · exact absurd h hl2.ne'
  have hlo : 18392 / 10000 < β := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sq_nonneg β), mul_nonneg (sub_nonneg.2 h) hβ0.le]
  have hhi : β < 18393 / 10000 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sq_nonneg β), mul_nonneg (sub_nonneg.2 h) hβ0.le]
  have hinv : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ0.ne'
  have hθ0 : 0 < β⁻¹ := inv_pos.2 hβ0
  refine ⟨lengthData_of_left_eigen hβ0 hℓ hℓM, hl0, by linear_combination h0, ?_, hinv, hcub,
    hlo, hhi, ?_, ?_⟩
  · rw [h2, ← mul_assoc, inv_mul_cancel₀ hβ0.ne', one_mul]
  · nlinarith [mul_pos (sub_pos.2 hhi) hθ0]
  · nlinarith [mul_pos (sub_pos.2 hlo) hθ0]

/-! ### Coordinates of a state and the shape of a step -/

/-- The length coordinate `ℓ·v / ℓ₀ = v₀ + (β − 1) v₁ + θ v₂`. -/
def tribY (β θ : ℝ) (v : Fin 3 → ℤ) : ℝ := v 0 + (β - 1) * v 1 + θ * v 2

theorem trib_lenHom_eq (D : TribData β θ ℓ) (v : Fin 3 → ℤ) :
    lenHom ℓ v = ℓ 0 * tribY β θ v := by
  rw [lenHom_apply, Fin.sum_univ_three, D.l1, D.l2, tribY]
  ring

/-- Every tile is at most as long as the tile `0`. -/
theorem trib_le_len_zero (D : TribData β θ ℓ) (j : Fin 3) : ℓ j ≤ ℓ 0 := by
  have := D.pos0
  fin_cases j
  · exact le_rfl
  · show ℓ 1 ≤ ℓ 0
    rw [D.l1]
    nlinarith [D.hi]
  · show ℓ 2 ≤ ℓ 0
    rw [D.l2]
    nlinarith [D.thi]

/-- A state `(j, v)` has `0 ≤ Y(v) < 1`. -/
theorem trib_state_Y (D : TribData β θ ℓ) {x : Fin 3 × (Fin 3 → ℤ)}
    (hx : IsState (lenHom ℓ) x) : 0 ≤ tribY β θ x.2 ∧ tribY β θ x.2 < 1 := by
  obtain ⟨h0, h1⟩ := hx
  rw [trib_lenHom_eq D] at h0 h1
  rw [lenHom_single] at h1
  have hle := trib_le_len_zero D x.1
  have hp := D.pos0
  constructor
  · by_contra h
    push Not at h
    nlinarith [mul_neg_of_pos_of_neg hp h]
  · by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hp.le]

/-- **The shape of a step**: every proper prefix of a Tribonacci image is `[]` or `0`, so
`f(j; v₀, v₁, v₂) = (j'; v₀ + v₁ + v₂ − d, v₀, v₁)` with `d ∈ {0, 1}`: the two stable
coordinates are shifted, `(v₁', v₂') = (v₀, v₁)`. -/
theorem trib_step_coords {L : (Fin 3 → ℤ) →+ ℝ} {x y : Fin 3 × (Fin 3 → ℤ)}
    (h : Step tribSubst L x y) : y.2 1 = x.2 0 ∧ y.2 2 = x.2 1 := by
  obtain ⟨P, S, hP, hy, -⟩ := h
  have hP0 : pvec P 1 = 0 ∧ pvec P 2 = 0 := by
    rcases x with ⟨j, v⟩
    rcases P with _ | ⟨p, _ | ⟨q, r⟩⟩
    · simp [pvec]
    · fin_cases j <;> simp [tribSubst] at hP <;> obtain ⟨rfl, -⟩ := hP <;> simp [pvec]
    · fin_cases j <;> simp [tribSubst] at hP
  rw [hy, trib_mulVec]
  simp [hP0.1, hP0.2]

/-! ### Lemma 3 (3) on Tribonacci: a quadratic Lyapunov form for the stable coordinates -/

/-- The centre `h = 1 / (2 (β + θ))` of the stable box: `(h, h)` is the fixed point of the
recursion `(v₁, v₂) ↦ (Y − (β − 1) v₁ − θ v₂, v₁)` at `Y = 1/2`. -/
noncomputable def tribH (β θ : ℝ) : ℝ := 1 / (2 * (β + θ))

theorem tribH_mul (D : TribData β θ ℓ) : tribH β θ * (β + θ) = 1 / 2 := by
  have : 0 < β + θ := by linarith [D.lo, D.tlo]
  unfold tribH
  field_simp

theorem tribH_bounds (D : TribData β θ ℓ) :
    2098 / 10000 < tribH β θ ∧ tribH β θ < 2099 / 10000 := by
  have hm := tribH_mul D
  have hpos : 0 < tribH β θ := div_pos one_pos (by linarith [D.lo, D.tlo])
  have := D.lo
  have := D.hi
  have := D.tlo
  have := D.thi
  constructor <;> nlinarith

/-- **The stable quadratic form** `Q(v) = u₁² + (β − 1) u₁ u₂ + θ u₂²`, `uᵢ = vᵢ − h`.  It is
`|u₁ − λ̄ u₂|²` for the complex root `λ` of the contracting factor `t² + (β − 1) t + θ` of
`χ_M = (t − β)(t² + (β − 1) t + θ)`, so `Q(A u) = θ Q(u)` for its companion matrix `A` (a
remark; the identity used is the one inside `trib_lyap_real`). -/
noncomputable def tribQ (β θ : ℝ) (v : Fin 3 → ℤ) : ℝ :=
  ((v 1 : ℝ) - tribH β θ) ^ 2 +
    (β - 1) * ((v 1 : ℝ) - tribH β θ) * ((v 2 : ℝ) - tribH β θ) +
    θ * ((v 2 : ℝ) - tribH β θ) ^ 2

/-- The discriminant gap `θ − (β − 1)²/4 > 0.3675` (the contracting factor has a complex pair):
`Q` is positive definite. -/
theorem trib_kappa (D : TribData β θ ℓ) : 3675 / 10000 < θ - (β - 1) ^ 2 / 4 := by
  have := D.lo
  have := D.hi
  have := D.tlo
  nlinarith

/-- The real inequality behind one step: with `a = Y − (β − 1) b − θ c`, `0 ≤ Y < 1`,
`Q(a, b) ≤ (4/3) θ Q(b, c) + 1`. -/
theorem trib_lyap_real {H a b c : ℝ} (hH : H * (β + θ) = 1 / 2) (hκ : 0 < θ - (β - 1) ^ 2 / 4)
    (hY0 : 0 ≤ a + (β - 1) * b + θ * c) (hY1 : a + (β - 1) * b + θ * c < 1) :
    (a - H) ^ 2 + (β - 1) * (a - H) * (b - H) + θ * (b - H) ^ 2 ≤
      4 / 3 * θ * ((b - H) ^ 2 + (β - 1) * (b - H) * (c - H) + θ * (c - H) ^ 2) + 1 := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = a + (β - 1) * b + θ * c - 1 / 2 := ⟨_, rfl⟩
  have ha : a - H = δ - (β - 1) * (b - H) - θ * (c - H) := by
    rw [hδ]
    linear_combination -hH
  have key : (a - H) ^ 2 + (β - 1) * (a - H) * (b - H) + θ * (b - H) ^ 2 =
      θ * ((b - H) ^ 2 + (β - 1) * (b - H) * (c - H) + θ * (c - H) ^ 2) +
        2 * δ * (-((β - 1) / 2) * (b - H) - θ * (c - H)) + δ ^ 2 := by
    rw [ha]
    ring
  have hpq : θ * ((b - H) ^ 2 + (β - 1) * (b - H) * (c - H) + θ * (c - H) ^ 2) -
      (-((β - 1) / 2) * (b - H) - θ * (c - H)) ^ 2 = (θ - (β - 1) ^ 2 / 4) * (b - H) ^ 2 := by
    ring
  have hp := mul_nonneg hκ.le (sq_nonneg (b - H))
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have h3 := sq_nonneg (3 * δ - (-((β - 1) / 2) * (b - H) - θ * (c - H)))
  rw [key]
  nlinarith

/-- **One step of `f` contracts `Q` up to a constant**: `Q(f x) ≤ (4/3) θ Q(x) + 1`. -/
theorem tribQ_step (D : TribData β θ ℓ) {x y : Fin 3 × (Fin 3 → ℤ)}
    (hx : IsState (lenHom ℓ) x) (h : Step tribSubst (lenHom ℓ) x y) :
    tribQ β θ y.2 ≤ 4 / 3 * θ * tribQ β θ x.2 + 1 := by
  obtain ⟨e1, e2⟩ := trib_step_coords h
  obtain ⟨hY0, hY1⟩ := trib_state_Y D hx
  unfold tribQ
  unfold tribY at hY0 hY1
  rw [e1, e2]
  exact trib_lyap_real (tribH_mul D) (by linarith [trib_kappa D]) hY0 hY1

/-- `R(fⁿ x) ≤ cⁿ R(x)` for `R = Q (1 − c) − 1`, `c = (4/3) θ`. -/
theorem tribQ_stepN (D : TribData β θ ℓ) {x : Fin 3 × (Fin 3 → ℤ)}
    (hx : IsState (lenHom ℓ) x) :
    ∀ (n : ℕ) {y : Fin 3 × (Fin 3 → ℤ)}, StepN tribSubst (lenHom ℓ) n x y →
      tribQ β θ y.2 * (1 - 4 / 3 * θ) - 1 ≤
        (4 / 3 * θ) ^ n * (tribQ β θ x.2 * (1 - 4 / 3 * θ) - 1)
  | 0, _, h => by rw [← h]; simp
  | n + 1, y, ⟨z, hz, hy⟩ => by
    have ih := tribQ_stepN D hx n hz
    have hs := tribQ_step D (stepN_isState hx n hz) hy
    have hc0 : 0 ≤ 4 / 3 * θ := by linarith [D.tlo]
    have hc1 : 0 ≤ 1 - 4 / 3 * θ := by linarith [D.thi]
    have h1 : tribQ β θ y.2 * (1 - 4 / 3 * θ) - 1 ≤
        4 / 3 * θ * (tribQ β θ z.2 * (1 - 4 / 3 * θ) - 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hs hc1]
    calc tribQ β θ y.2 * (1 - 4 / 3 * θ) - 1
        ≤ 4 / 3 * θ * (tribQ β θ z.2 * (1 - 4 / 3 * θ) - 1) := h1
      _ ≤ 4 / 3 * θ * ((4 / 3 * θ) ^ n * (tribQ β θ x.2 * (1 - 4 / 3 * θ) - 1)) :=
          mul_le_mul_of_nonneg_left ih hc0
      _ = (4 / 3 * θ) ^ (n + 1) * (tribQ β θ x.2 * (1 - 4 / 3 * θ) - 1) := by ring

/-- **Lemma 3 (3) on Tribonacci**: an `f`-periodic state has `Q(v) (1 − (4/3) θ) ≤ 1`. -/
theorem tribQ_periodic (D : TribData β θ ℓ) {x : Fin 3 × (Fin 3 → ℤ)}
    (hx : IsState (lenHom ℓ) x) {k : ℕ} (hk : 1 ≤ k) (h : StepN tribSubst (lenHom ℓ) k x x) :
    tribQ β θ x.2 * (1 - 4 / 3 * θ) ≤ 1 := by
  have hb := tribQ_stepN D hx k h
  have hc0 : 0 ≤ 4 / 3 * θ := by linarith [D.tlo]
  have hc1 : 4 / 3 * θ < 1 := by linarith [D.thi]
  have hp : (4 / 3 * θ) ^ k < 1 := pow_lt_one₀ hc0 hc1 (by omega)
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos (sub_pos.2 hp) (sub_pos.2 hcon)]

/-- The real box: `Q (1 − (4/3) θ) ≤ 1` forces `−3 < u₁ + h < 3` and `−3 < u₂ + h < 4`. -/
theorem trib_box_real (D : TribData β θ ℓ) {b c : ℝ}
    (h : ((b - tribH β θ) ^ 2 + (β - 1) * (b - tribH β θ) * (c - tribH β θ) +
      θ * (c - tribH β θ) ^ 2) * (1 - 4 / 3 * θ) ≤ 1) :
    (-3 < b ∧ b < 3) ∧ (-3 < c ∧ c < 4) := by
  have hκ := trib_kappa D
  obtain ⟨hH0, hH1⟩ := tribH_bounds D
  have tlo := D.tlo
  have thi := D.thi
  generalize tribH β θ = H at h hH0 hH1
  obtain ⟨q, hq⟩ : ∃ q : ℝ,
      q = (b - H) ^ 2 + (β - 1) * (b - H) * (c - H) + θ * (c - H) ^ 2 := ⟨_, rfl⟩
  rw [← hq] at h
  have hlb2 : (θ - (β - 1) ^ 2 / 4) * (c - H) ^ 2 ≤ q := by
    have e : q = (b - H + (β - 1) / 2 * (c - H)) ^ 2 +
        (θ - (β - 1) ^ 2 / 4) * (c - H) ^ 2 := by rw [hq]; ring
    rw [e]
    linarith [sq_nonneg (b - H + (β - 1) / 2 * (c - H))]
  have hlb1 : (θ - (β - 1) ^ 2 / 4) * (b - H) ^ 2 ≤ θ * q := by
    have e : θ * q = (θ * (c - H) + (β - 1) / 2 * (b - H)) ^ 2 +
        (θ - (β - 1) ^ 2 / 4) * (b - H) ^ 2 := by rw [hq]; ring
    rw [e]
    linarith [sq_nonneg (θ * (c - H) + (β - 1) / 2 * (b - H))]
  clear hq
  have hq0 : 0 ≤ q := le_trans (mul_nonneg (by linarith) (sq_nonneg _)) hlb2
  have hqb : q ≤ 36359 / 10000 := by
    have h1c : 27504 / 100000 ≤ 1 - 4 / 3 * θ := by linarith
    have := mul_le_mul_of_nonneg_left h1c hq0
    linarith
  have hθq : θ * q ≤ 19770 / 10000 := by
    have := mul_le_mul_of_nonneg_left hqb (by linarith : (0 : ℝ) ≤ θ)
    have := mul_le_mul_of_nonneg_right thi.le hq0
    linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · by_contra hb
    push Not at hb
    have hu0 : (32098 / 10000 : ℝ) ^ 2 ≤ (H - b) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hu : 103 / 10 ≤ (b - H) ^ 2 := by nlinarith
    have := mul_le_mul hκ.le hu (by norm_num) (by linarith)
    linarith
  · by_contra hb
    push Not at hb
    have hu0 : (27901 / 10000 : ℝ) ^ 2 ≤ (b - H) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hu : 7 ≤ (b - H) ^ 2 := by nlinarith
    have := mul_le_mul hκ.le hu (by norm_num) (by linarith)
    linarith
  · by_contra hc
    push Not at hc
    have hu0 : (32098 / 10000 : ℝ) ^ 2 ≤ (H - c) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hu : 103 / 10 ≤ (c - H) ^ 2 := by nlinarith
    have := mul_le_mul hκ.le hu (by norm_num) (by linarith)
    linarith
  · by_contra hc
    push Not at hc
    have hu0 : (37901 / 10000 : ℝ) ^ 2 ≤ (c - H) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hu : 14 ≤ (c - H) ^ 2 := by nlinarith
    have := mul_le_mul hκ.le hu (by norm_num) (by linarith)
    linarith

/-- **The box of the periodic states**: an `f`-periodic state of Tribonacci has
`v₁ ∈ [−2, 2]` and `v₂ ∈ [−2, 3]`. -/
theorem trib_box (D : TribData β θ ℓ) {v : Fin 3 → ℤ}
    (h : tribQ β θ v * (1 - 4 / 3 * θ) ≤ 1) :
    (-2 ≤ v 1 ∧ v 1 ≤ 2) ∧ (-2 ≤ v 2 ∧ v 2 ≤ 3) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := trib_box_real D h
  have e1 : (-3 : ℤ) < v 1 := by exact_mod_cast h1
  have e2 : v 1 < 3 := by exact_mod_cast h2
  have e3 : (-3 : ℤ) < v 2 := by exact_mod_cast h3
  have e4 : v 2 < 4 := by exact_mod_cast h4
  omega

/-! ### The trapped states reach a vertex state -/

/-- `TribReach L b c`: every state whose stable coordinates are `(v₁, v₂) = (b, c)` reaches a
vertex state under iteration of `f`. -/
def TribReach (L : (Fin 3 → ℤ) →+ ℝ) (b c : ℤ) : Prop :=
  ∀ x : Fin 3 × (Fin 3 → ℤ), IsState L x → x.2 1 = b → x.2 2 = c →
    ∃ n a, StepN tribSubst L n x (a, 0)

/-- **The forced coordinate**: on a state, `v₀ = Y − (β − 1) v₁ − θ v₂` with `0 ≤ Y < 1`, so
`v₀ = −⌊(β − 1) v₁ + θ v₂⌋`; here in the form "`v₀ = k` when `(β − 1) v₁ + θ v₂ ∈ [−k, 1 − k)`". -/
theorem trib_forced (D : TribData β θ ℓ) {x : Fin 3 × (Fin 3 → ℤ)} (hx : IsState (lenHom ℓ) x)
    {k : ℤ} (h1 : -(k : ℝ) ≤ (β - 1) * (x.2 1 : ℝ) + θ * (x.2 2 : ℝ))
    (h2 : (β - 1) * (x.2 1 : ℝ) + θ * (x.2 2 : ℝ) < 1 - k) : x.2 0 = k := by
  obtain ⟨hY0, hY1⟩ := trib_state_Y D hx
  unfold tribY at hY0 hY1
  have a1 : ((k - 1 : ℤ) : ℝ) < (x.2 0 : ℝ) := by push_cast; linarith
  have a2 : (x.2 0 : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
  have b1 : k - 1 < x.2 0 := by exact_mod_cast a1
  have b2 : x.2 0 < k + 1 := by exact_mod_cast a2
  omega

/-- A state with `v₁ = v₂ = 0` is a vertex state: `v₀ = Y ∈ [0, 1)`. -/
theorem trib_reach_zero (D : TribData β θ ℓ) : TribReach (lenHom ℓ) 0 0 := by
  intro x hx hb hc
  have ha : x.2 0 = 0 := trib_forced D hx (k := 0) (by rw [hb, hc]; simp) (by rw [hb, hc]; simp)
  refine ⟨0, x.1, ?_⟩
  show x = (x.1, 0)
  refine Prod.ext rfl ?_
  funext i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- **One step of the shift radix system** `(v₁, v₂) ↦ (−⌊(β − 1) v₁ + θ v₂⌋, v₁)`: if the
forced coordinate of `(b, c)` is `k` and every state with stable coordinates `(k, b)` reaches
a vertex state, so does every state with stable coordinates `(b, c)`. -/
theorem trib_reach_step (D : TribData β θ ℓ) (b c k : ℤ)
    (h1 : -(k : ℝ) ≤ (β - 1) * (b : ℝ) + θ * (c : ℝ))
    (h2 : (β - 1) * (b : ℝ) + θ * (c : ℝ) < 1 - k)
    (h : TribReach (lenHom ℓ) k b) : TribReach (lenHom ℓ) b c := by
  intro x hx hb hc
  have ha : x.2 0 = k := trib_forced D hx (by rw [hb, hc]; exact h1) (by rw [hb, hc]; exact h2)
  obtain ⟨y, hy⟩ := step_total D.len hx
  obtain ⟨e1, e2⟩ := trib_step_coords hy
  obtain ⟨n, a, hn⟩ := h y hy.isState (by rw [e1, ha]) (by rw [e2, hb])
  have h1 : StepN tribSubst (lenHom ℓ) 1 x y := ⟨x, rfl, hy⟩
  exact ⟨1 + n, a, stepN_add h1 n hn⟩

/-- **Every state in the box reaches a vertex state.**  The chain below lists the 32 nonzero
pairs `(b, c)` met by the shift radix system from the box `[−2, 2] × [−2, 3]` (three of them,
`(−3, 2)`, `(3, −2)`, `(2, −3)`, lie outside it), each with its forced coordinate `k` decided by
the enclosures of `β` and `θ`, in the order of their distance to `(0, 0)`: at most 7 radix
steps, i.e. at most 7 applications of `f` (the bound is read off the chain; it is not part of
the statement). -/
theorem trib_reach_box (D : TribData β θ ℓ) {b c : ℤ} (hb : -2 ≤ b ∧ b ≤ 2)
    (hc : -2 ≤ c ∧ c ≤ 3) : TribReach (lenHom ℓ) b c := by
  have lo := D.lo
  have hi := D.hi
  have tlo := D.tlo
  have thi := D.thi
  have r_0_0 := trib_reach_zero D
  have r_0_1 : TribReach (lenHom ℓ) 0 1 :=
    trib_reach_step D 0 1 0 (by push_cast; linarith) (by push_cast; linarith) r_0_0
  have r_1_m1 : TribReach (lenHom ℓ) 1 (-1) :=
    trib_reach_step D 1 (-1) 0 (by push_cast; linarith) (by push_cast; linarith) r_0_1
  have r_1_0 : TribReach (lenHom ℓ) 1 0 :=
    trib_reach_step D 1 0 0 (by push_cast; linarith) (by push_cast; linarith) r_0_1
  have r_m1_0 : TribReach (lenHom ℓ) (-1) 0 :=
    trib_reach_step D (-1) 0 1 (by push_cast; linarith) (by push_cast; linarith) r_1_m1
  have r_m1_1 : TribReach (lenHom ℓ) (-1) 1 :=
    trib_reach_step D (-1) 1 1 (by push_cast; linarith) (by push_cast; linarith) r_1_m1
  have r_0_m1 : TribReach (lenHom ℓ) 0 (-1) :=
    trib_reach_step D 0 (-1) 1 (by push_cast; linarith) (by push_cast; linarith) r_1_0
  have r_m1_2 : TribReach (lenHom ℓ) (-1) 2 :=
    trib_reach_step D (-1) 2 0 (by push_cast; linarith) (by push_cast; linarith) r_0_m1
  have r_m1_3 : TribReach (lenHom ℓ) (-1) 3 :=
    trib_reach_step D (-1) 3 0 (by push_cast; linarith) (by push_cast; linarith) r_0_m1
  have r_0_2 : TribReach (lenHom ℓ) 0 2 :=
    trib_reach_step D 0 2 (-1) (by push_cast; linarith) (by push_cast; linarith) r_m1_0
  have r_0_3 : TribReach (lenHom ℓ) 0 3 :=
    trib_reach_step D 0 3 (-1) (by push_cast; linarith) (by push_cast; linarith) r_m1_0
  have r_1_1 : TribReach (lenHom ℓ) 1 1 :=
    trib_reach_step D 1 1 (-1) (by push_cast; linarith) (by push_cast; linarith) r_m1_1
  have r_1_2 : TribReach (lenHom ℓ) 1 2 :=
    trib_reach_step D 1 2 (-1) (by push_cast; linarith) (by push_cast; linarith) r_m1_1
  have r_1_m2 : TribReach (lenHom ℓ) 1 (-2) :=
    trib_reach_step D 1 (-2) 1 (by push_cast; linarith) (by push_cast; linarith) r_1_1
  have r_2_m3 : TribReach (lenHom ℓ) 2 (-3) :=
    trib_reach_step D 2 (-3) 0 (by push_cast; linarith) (by push_cast; linarith) r_0_2
  have r_2_m2 : TribReach (lenHom ℓ) 2 (-2) :=
    trib_reach_step D 2 (-2) 0 (by push_cast; linarith) (by push_cast; linarith) r_0_2
  have r_2_m1 : TribReach (lenHom ℓ) 2 (-1) :=
    trib_reach_step D 2 (-1) (-1) (by push_cast; linarith) (by push_cast; linarith) r_m1_2
  have r_2_0 : TribReach (lenHom ℓ) 2 0 :=
    trib_reach_step D 2 0 (-1) (by push_cast; linarith) (by push_cast; linarith) r_m1_2
  have r_3_m2 : TribReach (lenHom ℓ) 3 (-2) :=
    trib_reach_step D 3 (-2) (-1) (by push_cast; linarith) (by push_cast; linarith) r_m1_3
  have r_m3_2 : TribReach (lenHom ℓ) (-3) 2 :=
    trib_reach_step D (-3) 2 2 (by push_cast; linarith) (by push_cast; linarith) r_2_m3
  have r_m2_m2 : TribReach (lenHom ℓ) (-2) (-2) :=
    trib_reach_step D (-2) (-2) 3 (by push_cast; linarith) (by push_cast; linarith) r_3_m2
  have r_m2_m1 : TribReach (lenHom ℓ) (-2) (-1) :=
    trib_reach_step D (-2) (-1) 3 (by push_cast; linarith) (by push_cast; linarith) r_3_m2
  have r_m2_0 : TribReach (lenHom ℓ) (-2) 0 :=
    trib_reach_step D (-2) 0 2 (by push_cast; linarith) (by push_cast; linarith) r_2_m2
  have r_m2_1 : TribReach (lenHom ℓ) (-2) 1 :=
    trib_reach_step D (-2) 1 2 (by push_cast; linarith) (by push_cast; linarith) r_2_m2
  have r_m2_2 : TribReach (lenHom ℓ) (-2) 2 :=
    trib_reach_step D (-2) 2 1 (by push_cast; linarith) (by push_cast; linarith) r_1_m2
  have r_m2_3 : TribReach (lenHom ℓ) (-2) 3 :=
    trib_reach_step D (-2) 3 1 (by push_cast; linarith) (by push_cast; linarith) r_1_m2
  have r_m1_m2 : TribReach (lenHom ℓ) (-1) (-2) :=
    trib_reach_step D (-1) (-2) 2 (by push_cast; linarith) (by push_cast; linarith) r_2_m1
  have r_m1_m1 : TribReach (lenHom ℓ) (-1) (-1) :=
    trib_reach_step D (-1) (-1) 2 (by push_cast; linarith) (by push_cast; linarith) r_2_m1
  have r_0_m2 : TribReach (lenHom ℓ) 0 (-2) :=
    trib_reach_step D 0 (-2) 2 (by push_cast; linarith) (by push_cast; linarith) r_2_0
  have r_1_3 : TribReach (lenHom ℓ) 1 3 :=
    trib_reach_step D 1 3 (-2) (by push_cast; linarith) (by push_cast; linarith) r_m2_1
  have r_2_1 : TribReach (lenHom ℓ) 2 1 :=
    trib_reach_step D 2 1 (-2) (by push_cast; linarith) (by push_cast; linarith) r_m2_2
  have r_2_2 : TribReach (lenHom ℓ) 2 2 :=
    trib_reach_step D 2 2 (-2) (by push_cast; linarith) (by push_cast; linarith) r_m2_2
  have r_2_3 : TribReach (lenHom ℓ) 2 3 :=
    trib_reach_step D 2 3 (-3) (by push_cast; linarith) (by push_cast; linarith) r_m3_2
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  interval_cases b <;> interval_cases c <;> assumption

/-! ### Property (F) for Tribonacci -/

/-- **Property (F) for Tribonacci**, for every positive left eigen-row `ℓ` of its incidence
matrix: an `f`-periodic state lies in the box `v₁ ∈ [−2, 2]`, `v₂ ∈ [−2, 3]`
(`tribQ_periodic`, `trib_box`), every state of the box reaches a vertex state
(`trib_reach_box`), and vertex states are forward invariant (`stepN_absorb`), so the cycle
through the state is made of vertex states. -/
theorem trib_propertyF {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    PropertyF tribSubst (lenHom ℓ) := by
  intro x hx k hk hper
  have D := trib_data hℓ hℓM
  obtain ⟨hb, hc⟩ := trib_box D (tribQ_periodic D hx hk hper)
  obtain ⟨n, a, hn⟩ := trib_reach_box D hb hc x hx rfl rfl
  have hmul : ∀ j, StepN tribSubst (lenHom ℓ) (k * j) x x := by
    intro j
    induction j with
    | zero => exact rfl
    | succ j ih => rw [Nat.mul_succ]; exact stepN_add ih k hper
  exact stepN_absorb D.len.pos hn (Nat.le_mul_of_pos_left n hk) (hmul n)

/-- **Lemma 3 (4) on Tribonacci**: every state reaches a vertex state
(`Psc.GeometricF.reaches_vertex_of_propertyF`, with the contraction data of
`Psc.GeometricFPisot.exists_contractionData_of_pisot`). -/
theorem trib_reaches_vertex {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) {x : Fin 3 × (Fin 3 → ℤ)}
    (hx : IsState (lenHom ℓ) x) : ∃ n a, StepN tribSubst (lenHom ℓ) n x (a, 0) := by
  have hroots := pisot_roots_of_isPisot tribSubst Psc.BPrime.trib_irreducible hℓ hℓM
    (Psc.BPrime.trib_isPisot hℓ hℓM)
  obtain ⟨ν, ρ, hc⟩ :=
    exists_contractionData_of_pisot tribSubst Psc.BPrime.trib_irreducible hℓ hℓM hroots
  exact reaches_vertex_of_propertyF (trib_data hℓ hℓM).len hc (trib_propertyF hℓ hℓM) hx

/-! ### Theorem FC1 on Tribonacci, every hypothesis discharged -/

/-- **Every hypothesis of `Psc.GeometricFPisot.fc1_pip3` holds for Tribonacci**
`0 ↦ 01, 1 ↦ 02, 2 ↦ 0`: primitive (`Psc.BPrime.trib_prim`, `M³ > 0`), `χ_M = X³ − X² − X − 1`
irreducible over `ℚ` (`Psc.BPrime.trib_irreducible`), a positive left eigen-row `ℓ` with
`ℓ M = β ℓ` (`Psc.PerronExistence.exists_pos_left_eigen_inc`), every complex root of `χ_M`
other than `β` in the open unit disc (`Psc.BPrime.trib_isPisot` through
`Psc.GeometricFPisot.pisot_roots_of_isPisot`), and property (F) for the tile lengths `ℓ`
(`trib_propertyF`). -/
theorem trib_fc1_hypotheses_complete : ∃ (β : ℝ) (ℓ : Fin 3 → ℝ),
    (∃ k ≥ 1, ∀ a c, 0 < (inc tribSubst ^ k) a c) ∧
      Irreducible ((inc tribSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (∀ a, 0 < ℓ a) ∧ ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ ∧
      (∀ z : ℂ, ((inc tribSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
        ‖z‖ < 1) ∧
      PropertyF tribSubst (lenHom ℓ) := by
  obtain ⟨β, -, ℓ, hℓ, hℓM⟩ :=
    Psc.PerronExistence.exists_pos_left_eigen_inc tribSubst Psc.BPrime.trib_prim
  exact ⟨β, ℓ, Psc.BPrime.trib_prim, Psc.BPrime.trib_irreducible, hℓ, hℓM,
    pisot_roots_of_isPisot tribSubst Psc.BPrime.trib_irreducible hℓ hℓM
      (Psc.BPrime.trib_isPisot hℓ hℓM),
    trib_propertyF hℓ hℓM⟩

/-- **Theorem FC1 on a PIP3 specimen, with no hypothesis left**: `Psc.GeometricFPisot.fc1_pip3`
instantiated at Tribonacci.  `σ` has a strict system iff some two distinct `g`-periodic letters
have no left strong-coincidence witness iff some two distinct letters have none. -/
theorem trib_fc1 :
    ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter tribSubst c ∧ IsPeriodicLetter tribSubst c' ∧
          ¬ StrongCoincidenceWitness tribSubst c c') ∧
      ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness tribSubst c c') := by
  obtain ⟨β, ℓ, hprim, hirr, hℓ, hℓM, hroots, hF⟩ := trib_fc1_hypotheses_complete
  exact fc1_pip3 hprim hirr hℓ hℓM hroots hF

/-! ### Evaluating both sides on words -/

/-- `σ(0) = 0·1` and `σ(1) = 0·2`: the common letter `0` after the empty prefixes. -/
theorem trib_witness_01 : StrongCoincidenceWitness tribSubst 0 1 :=
  ⟨1, [], [1], [], [2], 0, by decide, by decide, fun _ => rfl⟩

/-- `σ(0) = 0·1` and `σ(2) = 0`. -/
theorem trib_witness_02 : StrongCoincidenceWitness tribSubst 0 2 :=
  ⟨1, [], [1], [], [], 0, by decide, by decide, fun _ => rfl⟩

/-- `σ(1) = 0·2` and `σ(2) = 0`. -/
theorem trib_witness_12 : StrongCoincidenceWitness tribSubst 1 2 :=
  ⟨1, [], [2], [], [], 0, by decide, by decide, fun _ => rfl⟩

/-- `0` is a `g`-periodic letter (`σ(0)` begins with `0`). -/
theorem trib_isPeriodicLetter_zero : IsPeriodicLetter tribSubst 0 :=
  ⟨1, le_rfl, by decide⟩

/-- `1` and `2` are not `g`-periodic: every image begins with `0`, so the first-letter map is
constant `0` and `g^k(c) = 0` for `k ≥ 1`. -/
theorem trib_not_isPeriodicLetter {c : Fin 3} (hc : c ≠ 0) : ¬ IsPeriodicLetter tribSubst c := by
  have hs : ∀ a, tribSubst a ≠ [] := by decide
  rw [isPeriodicLetter_iff hs]
  rintro ⟨k, hk, hck⟩
  have hg : ∀ a, (tribSubst a).head (hs a) = 0 := by
    intro a
    fin_cases a <;> rfl
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm, Function.iterate_succ_apply', hg] at hck
  exact hc hck.symm

/-- **Both sides of the equivalence, evaluated.**  Every pair of distinct letters has a left
strong-coincidence witness at level `1` (`trib_witness_01`, `_02`, `_12`), so the right-hand
statement of the second equivalence is false; by `trib_fc1` there is no strict system, and no
pair of distinct `g`-periodic letters lacks a witness (there is only one `g`-periodic letter,
`trib_not_isPeriodicLetter`).  All three statements are false.  The direction of `trib_fc1`
used here (a strict system gives a pair without a witness) is the elementary one; the same
conclusion is proved on main without Theorem FC1 (`Psc.StrictSystem.trib_no_strictSystem`). -/
theorem trib_fc1_evaluated :
    (¬ ∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ∧
      (¬ ∃ c c', c ≠ c' ∧ IsPeriodicLetter tribSubst c ∧ IsPeriodicLetter tribSubst c' ∧
          ¬ StrongCoincidenceWitness tribSubst c c') ∧
      (∀ c c', c ≠ c' → StrongCoincidenceWitness tribSubst c c') ∧
      (∀ c, IsPeriodicLetter tribSubst c ↔ c = 0) := by
  have hall : ∀ c c' : Fin 3, c ≠ c' → StrongCoincidenceWitness tribSubst c c' :=
    Psc.StrictSystem.fin3_all_pairs trib_witness_01 trib_witness_02 trib_witness_12
  have h1 : ¬ ∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C :=
    fun h => trib_fc1.2.1 h hall
  refine ⟨h1, fun h => h1 (trib_fc1.1.2 h), hall, fun c => ⟨fun h => ?_, ?_⟩⟩
  · by_contra hc
    exact trib_not_isPeriodicLetter hc h
  · rintro rfl
    exact trib_isPeriodicLetter_zero

/-! ### Negative control: a PIP3 specimen without property (F) -/

/-- The productive control `01/12/021` (`0 ↦ 01, 1 ↦ 12, 2 ↦ 021`).  On paper it is PIP3:
`M² > 0`, `χ_M = t³ − 3t² + 2t − 1` (no rational root), roots `β ≈ 2.3247` and a complex pair
of modulus `≈ 0.656`; this module does not prove those facts in Lean. -/
def ctrlSubst : Fin 3 → List (Fin 3) := ![[0, 1], [1, 2], [0, 2, 1]]

/-- **(F) fails on `01/12/021`**, for every positive left eigen-row `ℓ`: the state
`(2; −1, 0, 1)` is `f`-fixed (`σ(2) = 0·2·1`, `(M − I) v = e₀ = p(0)`, and `ℓ₂ ≥ ℓ₀` makes it a
state).  Step 2 of the argument above stops here: `σ(1) = 12` and `σ(2) = 021` have proper
prefixes containing letters other than `0`, so the stable pair is not shifted. -/
theorem ctrl_not_propertyF {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc ctrlSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ¬ PropertyF ctrlSubst (lenHom ℓ) := by
  intro hF
  have h0 := congrFun hℓM 0
  have h2 := congrFun hℓM 2
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, inc, ctrlSubst] at h0 h2
  have hl0 := hℓ 0
  have hl1 := hℓ 1
  have hl2 := hℓ 2
  have hβ0 : 0 < β := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hl0.le]
  have hle : ℓ 0 ≤ ℓ 2 := by nlinarith [mul_pos hβ0 hl0]
  have hlen : lenHom ℓ ![-1, 0, 1] = ℓ 2 - ℓ 0 := by
    simp [lenHom_apply, Fin.sum_univ_three]
    ring
  have hx : IsState (lenHom ℓ) ((2 : Fin 3), (![-1, 0, 1] : Fin 3 → ℤ)) := by
    refine ⟨?_, ?_⟩
    · show 0 ≤ lenHom ℓ ![-1, 0, 1]
      rw [hlen]
      linarith
    · show lenHom ℓ ![-1, 0, 1] < lenHom ℓ (pvec [(2 : Fin 3)])
      rw [hlen, lenHom_single]
      linarith
  have hstep : Step ctrlSubst (lenHom ℓ) ((2 : Fin 3), (![-1, 0, 1] : Fin 3 → ℤ))
      ((2 : Fin 3), (![-1, 0, 1] : Fin 3 → ℤ)) := by
    refine ⟨[0], [1], rfl, ?_, hx⟩
    funext i
    fin_cases i <;> simp [incZ, Matrix.mulVec, dotProduct, Fin.sum_univ_three, inc, ctrlSubst,
      pvec]
  have h := congrFun (hF _ hx 1 le_rfl ⟨_, rfl, hstep⟩) 0
  simp at h

/-- The incidence matrix of `01/12/021`. -/
theorem ctrl_inc : inc ctrlSubst = Matrix.of ![![1, 0, 1], ![1, 1, 1], ![0, 1, 1]] := by
  decide

/-- `01/12/021` is primitive (`M² > 0`). -/
theorem ctrl_prim : ∃ k ≥ 1, ∀ a c, 0 < (inc ctrlSubst ^ k) a c :=
  ⟨2, by norm_num, fun a c => by rw [ctrl_inc]; fin_cases a <;> fin_cases c <;> decide +kernel⟩

/-- The control is not vacuous: `01/12/021` has a positive left eigen-row, and (F) fails for
it. -/
theorem ctrl_exists_not_propertyF : ∃ (β : ℝ) (ℓ : Fin 3 → ℝ), (∀ a, 0 < ℓ a) ∧
    ℓ ᵥ* (inc ctrlSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ ∧ ¬ PropertyF ctrlSubst (lenHom ℓ) := by
  obtain ⟨β, -, ℓ, hℓ, hℓM⟩ := Psc.PerronExistence.exists_pos_left_eigen_inc ctrlSubst ctrl_prim
  exact ⟨β, ℓ, hℓ, hℓM, ctrl_not_propertyF hℓ hℓM⟩

end Psc.GeometricFTriple
