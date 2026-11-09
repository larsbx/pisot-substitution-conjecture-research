import Mathlib
import PscVerif.WeightModulus

/-!
# Theorem A(ii): moving the largest exponent onto `β` by a Galois conjugation

`docs/c4-concentration-attack-2026-11-06.md`, §2.  The eigenvalues of `Φ` on `im Q₄` are
the roots of a rational polynomial `q` (a divisor of `χ_S`), and each is a weight
`β^a α^b γ^c`, where `β, α, γ` are the three roots of the irreducible rational cubic `χ_M`.
The proof uses: the Galois group acts transitively on `{β, α, γ}`, so some conjugate of a
root of `q` carries the largest exponent on `β`, and that conjugate is again a root of `q`.

## Setting

Everything lives in `ℂ`.  `f : ℚ[X]` is irreducible with `f.natDegree = 3`, and
`β α γ : ℂ` are pairwise distinct roots of `f` (`aeval _ f = 0`).  `q : ℚ[X]` is arbitrary;
the conclusion of `orbit_310_excluded` is informative only for `q ≠ 0` (in the application
`q = χ_{Φ|im Q₄}` is monic), and for `q = 0` the modulus hypotheses of items 3 and 4 fail.

The modulus steps of items 2 and 4 are `Psc.WeightModulus.weight_310` and `weight_220`,
applied at the real number `‖β‖`.  Item 3 keeps its own short argument because it is
stronger than `weight_211`: it needs no bound `1 < ‖β‖`.  The local tactic macros
`distinct_contra` and `perm_close` (hygiene off) refer to the hypothesis names `hβα`, `hβγ`,
`hαγ`, `hc`, `hm`, `hp` of the section; renaming those breaks them at compile time.

## What is proved

* `root_eq_of_three`: every complex root of `f` is `β`, `α` or `γ`.
* `exists_conj` (transitivity): for any two roots `ρ, ρ'` of `f` there is an ordering
  `(x, y, z)` of `(β, α, γ)` -- the images of `(β, α, γ)` under an automorphism `g` of the
  splitting field `ℚ(rootSet f ℂ) ⊆ ℂ` with `g ρ = ρ'` -- such that `q` vanishing at
  `β^a α^b γ^c` implies `q` vanishing at `x^a y^b z^c`, for every `q, a, b, c`.  The
  automorphism comes from `Normal.minpoly_eq_iff_mem_orbit`, using that every root of `f` has
  minimal polynomial `f / lc f` (`minpoly.eq_of_irreducible`).
* `orbit_exponent_on_beta` (task item 1): each of the exponents `b`, `c` can be moved onto
  `β`, the other two exponents landing on `α, γ` in one of the two orders.
* `orbit_310_excluded` (item 2): with `1 < ‖β‖`, `‖α‖ < 1`, `‖γ‖ < 1`, `1 ≤ ‖βαγ‖`, a root
  of `q` of shape `(3,1,0)` (any permutation) forces a root `z` of `q` with
  `‖β‖ < ‖z‖` and `‖β‖² < ‖z‖`.
* `orbit_211_root`: a root of shape `(2,1,1)` gives the root `β · βαγ`;
  `orbit_211_forces_unit` (item 3): with `1 ≤ ‖βαγ‖`, a root of shape `(2,1,1)` and every
  root of `q` of modulus at most `‖β‖`, one gets `‖βαγ‖ = 1`.
* `orbit_220_both`: a root of shape `(2,2,0)` gives that both `β²α²` and `β²γ²` are roots.
* `orbit_220_forces_complex_unit` (item 4): with `1 < ‖β‖`, `1 ≤ ‖βαγ‖`, a root of shape
  `(2,2,0)` and the modulus bound, `‖βαγ‖ = 1`, `‖α‖ = ‖γ‖`, `α.im ≠ 0` and `γ.im ≠ 0`.
  Non-reality (`im_ne_zero_of_norm_eq`): if `α` were real, complex conjugation (a root
  permutation) and `‖γ‖ = ‖α‖ < ‖β‖` force `γ` real, hence `γ = -α`; then `f(α) = f(-α) = 0`
  gives `α² = -c₁/c₃ ∈ ℚ`, so `α` has degree at most two, contradicting the cubic minimal
  polynomial.  `aeval_conj_eq_zero`: complex conjugation permutes the roots of a rational
  polynomial.
* **Pure powers.**  `mono111_ne_cube` (moduli `1 < ‖β‖`, `‖α‖, ‖γ‖ < 1`, `1 ≤ ‖βαγ‖` only):
  the `(1,1,1)` weight `βαγ` is none of `β³, α³, γ³`.  `mono211_ne_pow4_of_moduli`: seven of
  the nine equalities between a `(2,1,1)` weight and a fourth power of a root fail under the
  moduli alone; `moduli_211_control`: the eighth, `βα²γ = γ⁴`, is consistent with the moduli
  (`(β, α, γ) = (729/250, 1/2, 9/10)`), so they do not suffice; `mono211_ne_pow4_galois`: the
  remaining two fail for the roots of an irreducible rational cubic with a rational `βαγ`
  (the conjugation `β ↦ α`, resp. `β ↦ γ`, of `exists_conj` applied to the rational relation
  `β⁴α⁵ = (βαγ)³`); `mono211_ne_pow4`: all nine.

## What is not proved here

* Nothing about `Φ`, `Lie₄`, `Q₄`, `S` or `χ_S`: that the eigenvalues of `Φ|im Q₄` are the
  roots of a rational `q`, that they are the weights `β^a α^b γ^c` with `(a,b,c)` a
  permutation of `(3,1,0)`, `(2,2,0)` or `(2,1,1)` (Witt formula), and the modulus bound
  `ρ(S) ≤ β` (`prop:cocycle`) are all hypotheses supplied by the reader, here entering as
  `hq` and `hbound`.
* The Wielandt step that excludes the `(2,2,0)` sector in the remaining complex unit case,
  and the semisimplicity of `Φ`, are not formalized.
* `1 ≤ ‖βαγ‖` is assumed (in the application `βαγ = d = det M` is a nonzero integer); no
  integrality is used.  `mono211_ne_pow4_galois` assumes `βαγ` rational (`hr`); for
  `f = χ_M` that is `Psc.SectorBridge.det_eq_mul_roots`, used by the matrix form
  `Psc.SectorBridge.pure_power_excluded`.
* Non-vacuity is exhibited numerically, not formally.  For Tribonacci `f = X³ − X² − X − 1`
  (`|β| ≈ 1.8393`, `|α| = |γ| ≈ 0.7374`, `|βαγ| = 1`): `q = X³ + X² + 3X − 1` (roots
  `β²α², β²γ², α²γ²`, largest modulus `|β|`) satisfies every hypothesis of item 4; `q = f`
  those of item 3; and `q = X⁶ + 4X⁵ + 15X⁴ − 24X³ + 7X² + 1` (with roots `β³α`, `α³β`)
  those of item 2.
-/

namespace Psc.GaloisOrbit

open Polynomial

/-- A root of a degree-three polynomial is one of three given distinct roots. -/
theorem root_eq_of_three {f : ℚ[X]} (hf0 : f ≠ 0) (hdeg : f.natDegree = 3) {β α γ : ℂ}
    (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) {z : ℂ} (hz : aeval z f = 0) :
    z = β ∨ z = α ∨ z = γ := by
  classical
  by_contra h
  simp only [not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hsub : ({z, β, α, γ} : Finset ℂ) ⊆ (f.aroots ℂ).toFinset := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨hf0, ?_⟩
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({z, β, α, γ} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hαγ]
    · simp [hβα, hβγ]
    · simp [h1, h2, h3]
  have h4 := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
  have h5 := Polynomial.card_roots' (f.map (algebraMap ℚ ℂ))
  rw [natDegree_map, hdeg] at h5
  rw [aroots_def] at h4
  omega

/-- The six orderings of three pairwise distinct elements of `{β, α, γ}`. -/
def IsPerm3 (β α γ x y z : ℂ) : Prop :=
  (x = β ∧ y = α ∧ z = γ) ∨ (x = β ∧ y = γ ∧ z = α) ∨ (x = α ∧ y = β ∧ z = γ) ∨
    (x = α ∧ y = γ ∧ z = β) ∨ (x = γ ∧ y = β ∧ z = α) ∨ (x = γ ∧ y = α ∧ z = β)

/-- Three pairwise distinct elements of `{β, α, γ}` form one of its six orderings. -/
theorem isPerm3_of {β α γ x y z : ℂ}
    (hx : x = β ∨ x = α ∨ x = γ) (hy : y = β ∨ y = α ∨ y = γ) (hz : z = β ∨ z = α ∨ z = γ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : IsPerm3 β α γ x y z := by
  unfold IsPerm3
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;> simp_all

/-- **Transitivity of the Galois action on the roots.**  For roots `ρ, ρ'` of `f` there is an
ordering `(x, y, z)` of `(β, α, γ)` with `ρ ↦ ρ'` under which every rational relation
`q(β^a α^b γ^c) = 0` is transported to `q(x^a y^b z^c) = 0`. -/
theorem exists_conj {f : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3) {β α γ : ℂ}
    (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ) {ρ ρ' : ℂ} (hρ : aeval ρ f = 0)
    (hρ' : aeval ρ' f = 0) :
    ∃ x y z : ℂ, IsPerm3 β α γ x y z ∧ (ρ = β → x = ρ') ∧ (ρ = α → y = ρ') ∧ (ρ = γ → z = ρ') ∧
      ∀ (q : ℚ[X]) (a b c : ℕ), aeval (β ^ a * α ^ b * γ ^ c) q = 0 →
        aeval (x ^ a * y ^ b * z ^ c) q = 0 := by
  classical
  have hf0 := hf.ne_zero
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (f.rootSet ℂ) with hK
  have : IsSplittingField ℚ K f :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : Normal ℚ K := Normal.of_isSplittingField f
  have memK : ∀ w : ℂ, aeval w f = 0 → w ∈ K := fun w hw =>
    IntermediateField.subset_adjoin ℚ _ (mem_rootSet.2 ⟨hf0, hw⟩)
  let ι : K →+* ℂ := algebraMap K ℂ
  have hι : Function.Injective ι := (algebraMap K ℂ).injective
  -- the minimal polynomial of every root of `f` lying in `K`
  have hmin : ∀ w : K, aeval (ι w) f = 0 → minpoly ℚ w = f * C f.leadingCoeff⁻¹ := by
    intro w hw
    rw [← minpoly.algebraMap_eq hι]
    exact (minpoly.eq_of_irreducible hf hw).symm
  have hrootK : ∀ w : K, aeval (ι w) f = 0 → aeval w f = 0 := by
    intro w hw
    apply hι
    rw [map_zero, ← hw]
    exact (aeval_algebraMap_apply ℂ w f).symm
  let ρK : K := ⟨ρ, memK ρ hρ⟩
  let ρK' : K := ⟨ρ', memK ρ' hρ'⟩
  have hmeq : minpoly ℚ ρK' = minpoly ℚ ρK := by
    rw [hmin ρK hρ, hmin ρK' hρ']
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit K).1 hmeq
  -- `hg : g • ρK = ρK'`
  have hg' : g ρK = ρK' := hg
  have groot : ∀ w : K, aeval (ι w) f = 0 → aeval (ι (g w)) f = 0 := by
    intro w hw
    rw [aeval_algebraMap_apply ℂ (g w) f, aeval_algEquiv]
    simp [hrootK w hw]
  have three : ∀ w : K, aeval (ι w) f = 0 → ι (g w) = β ∨ ι (g w) = α ∨ ι (g w) = γ :=
    fun w hw => root_eq_of_three hf0 hdeg hβ hα hγ hβα hβγ hαγ (groot w hw)
  let βK : K := ⟨β, memK β hβ⟩
  let αK : K := ⟨α, memK α hα⟩
  let γK : K := ⟨γ, memK γ hγ⟩
  have ne : ∀ u v : K, ι u ≠ ι v → ι (g u) ≠ ι (g v) := by
    intro u v h h'
    exact h (congrArg ι (g.injective (hι h')))
  refine ⟨ι (g βK), ι (g αK), ι (g γK), ?_, ?_, ?_, ?_, ?_⟩
  · exact isPerm3_of (three βK hβ) (three αK hα) (three γK hγ) (ne βK αK hβα) (ne βK γK hβγ)
      (ne αK γK hαγ)
  · rintro rfl
    show ι (g ρK) = ρ'
    rw [hg']
    rfl
  · rintro rfl
    show ι (g ρK) = ρ'
    rw [hg']
    rfl
  · rintro rfl
    show ι (g ρK) = ρ'
    rw [hg']
    rfl
  · intro q a b c hq
    have h1 : aeval (βK ^ a * αK ^ b * γK ^ c) q = 0 := by
      apply hι
      rw [map_zero, ← aeval_algebraMap_apply ℂ _ q]
      simpa using hq
    have h2 : ι (g βK) ^ a * ι (g αK) ^ b * ι (g γK) ^ c = ι (g (βK ^ a * αK ^ b * γK ^ c)) := by
      simp
    rw [h2, aeval_algebraMap_apply ℂ _ q, aeval_algEquiv]
    simp [h1]

/-- Complex conjugation permutes the complex roots of a rational polynomial (moved here from
`Psc.Degree4Floor`, which keeps a deprecated alias). -/
theorem aeval_conj_eq_zero {f : ℚ[X]} {w : ℂ} (hw : aeval w f = 0) :
    aeval (starRingEnd ℂ w) f = 0 := by
  have := Polynomial.aeval_algHom_apply (Complex.conjAe.toAlgHom.restrictScalars ℚ) w f
  simp only [AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom, Complex.conjAe_coe, hw,
    map_zero] at this
  exact this


set_option hygiene false in
/-- Close a branch whose hypothesis `hc` equates two of the distinct roots. -/
local macro "distinct_contra" : tactic =>
  `(tactic| first
    | exact absurd hc hβα | exact absurd hc hβα.symm | exact absurd hc hβγ
    | exact absurd hc hβγ.symm | exact absurd hc hαγ | exact absurd hc hαγ.symm)

set_option hygiene false in
/-- Split the six orderings `hp` of the roots, rewrite `hm` and `hc`, and close each branch. -/
local macro "perm_close" : tactic =>
  `(tactic| (rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp only [h1, h2, h3] at hm hc <;>
      first
      | distinct_contra
      | exact of_eq (by ring1) hm))

/-- Transport a vanishing statement along an equality of evaluation points. -/
private theorem of_eq {q : ℚ[X]} {u v : ℂ} (h : u = v) (hu : aeval u q = 0) : aeval v q = 0 := h ▸ hu

section Orbit
variable {f : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3) {β α γ : ℂ}
    (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
include hf hdeg hβ hα hγ hβα hβγ hαγ

/-- **Moving an exponent onto `β`** (task item 1).  If `q(β^a α^b γ^c) = 0`, then `q` also
vanishes at `β^b x^a y^c` and at some `β^c x'^a y'^b`, where `(x, y)` and `(x', y')` are
`(α, γ)` or `(γ, α)`. -/
theorem orbit_exponent_on_beta (q : ℚ[X]) (a b c : ℕ)
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    (∃ x y : ℂ, ((x = α ∧ y = γ) ∨ (x = γ ∧ y = α)) ∧ aeval (β ^ b * x ^ a * y ^ c) q = 0) ∧
      (∃ x y : ℂ, ((x = α ∧ y = γ) ∨ (x = γ ∧ y = α)) ∧ aeval (β ^ c * x ^ a * y ^ b) q = 0) := by
  constructor
  · obtain ⟨x, y, z, hp, -, hc, -, ht⟩ := exists_conj hf hdeg hβ hα hγ hβα hβγ hαγ hα hβ
    have hc := hc rfl
    have hm := ht q a b c hq
    rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;> simp only [h1, h2, h3] at hm hc <;>
      first
      | distinct_contra
      | exact ⟨α, γ, Or.inl ⟨rfl, rfl⟩, of_eq (by ring1) hm⟩
      | exact ⟨γ, α, Or.inr ⟨rfl, rfl⟩, of_eq (by ring1) hm⟩
  · obtain ⟨x, y, z, hp, -, -, hc, ht⟩ := exists_conj hf hdeg hβ hα hγ hβα hβγ hαγ hγ hβ
    have hc := hc rfl
    have hm := ht q a b c hq
    rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;> simp only [h1, h2, h3] at hm hc <;>
      first
      | distinct_contra
      | exact ⟨α, γ, Or.inl ⟨rfl, rfl⟩, of_eq (by ring1) hm⟩
      | exact ⟨γ, α, Or.inr ⟨rfl, rfl⟩, of_eq (by ring1) hm⟩

/-- The `(2,2,0)` orbit: from any one monomial of shape `(2,2,0)` the polynomial `q` also
vanishes at `β²α²` and at `β²γ²`. -/
theorem orbit_220_both (q : ℚ[X]) (a b c : ℕ)
    (habc : (a, b, c) = (2, 2, 0) ∨ (a, b, c) = (2, 0, 2) ∨ (a, b, c) = (0, 2, 2))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    aeval (β ^ 2 * α ^ 2) q = 0 ∧ aeval (β ^ 2 * γ ^ 2) q = 0 := by
  rcases habc with h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h
  · refine ⟨of_eq (by ring1) hq, ?_⟩
    obtain ⟨x, y, z, hp, -, -, hc, ht⟩ := exists_conj hf hdeg hβ hα hγ hβα hβγ hαγ hγ hα
    have hc := hc rfl
    have hm := ht q 2 2 0 hq
    perm_close
  · refine ⟨?_, of_eq (by ring1) hq⟩
    obtain ⟨x, y, z, hp, -, hc, -, ht⟩ := exists_conj hf hdeg hβ hα hγ hβα hβγ hαγ hα hγ
    have hc := hc rfl
    have hm := ht q 2 0 2 hq
    perm_close
  · constructor
    · obtain ⟨x, y, z, hp, hc, -, -, ht⟩ := exists_conj hf hdeg hβ hα hγ hβα hβγ hαγ hβ hγ
      have hc := hc rfl
      have hm := ht q 0 2 2 hq
      perm_close
    · obtain ⟨x, y, z, hp, hc, -, -, ht⟩ := exists_conj hf hdeg hβ hα hγ hβα hβγ hαγ hβ hα
      have hc := hc rfl
      have hm := ht q 0 2 2 hq
      perm_close

/-- **The `(3,1,0)` orbit is excluded** (task item 2).  A root of `q` of shape `(3,1,0)`
forces a root of `q` of modulus larger than `‖β‖²` (hence than `‖β‖`). -/
theorem orbit_310_excluded (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1)
    (hdet : 1 ≤ ‖β * α * γ‖) (q : ℚ[X]) (a b c : ℕ)
    (habc : (a, b, c) = (3, 1, 0) ∨ (a, b, c) = (3, 0, 1) ∨ (a, b, c) = (1, 3, 0) ∨
      (a, b, c) = (0, 3, 1) ∨ (a, b, c) = (1, 0, 3) ∨ (a, b, c) = (0, 1, 3))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) :
    ∃ z : ℂ, aeval z q = 0 ∧ ‖β‖ < ‖z‖ ∧ ‖β‖ ^ 2 < ‖z‖ := by
  -- some `β³δ` with `δ ∈ {α, γ}` is a root of `q`
  have hex : ∃ δ : ℂ, (δ = α ∨ δ = γ) ∧ aeval (β ^ 3 * δ) q = 0 := by
    have h1 := orbit_exponent_on_beta hf hdeg hβ hα hγ hβα hβγ hαγ q a b c hq
    rcases habc with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h
    · exact ⟨α, Or.inl rfl, of_eq (by ring1) hq⟩
    · exact ⟨γ, Or.inr rfl, of_eq (by ring1) hq⟩
    · obtain ⟨x, y, hxy, hm⟩ := h1.1
      exact ⟨x, hxy.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1), of_eq (by ring1) hm⟩
    · obtain ⟨x, y, hxy, hm⟩ := h1.1
      exact ⟨y, hxy.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), of_eq (by ring1) hm⟩
    · obtain ⟨x, y, hxy, hm⟩ := h1.2
      exact ⟨x, hxy.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1), of_eq (by ring1) hm⟩
    · obtain ⟨x, y, hxy, hm⟩ := h1.2
      exact ⟨y, hxy.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), of_eq (by ring1) hm⟩
  obtain ⟨δ, hδ, hz⟩ := hex
  refine ⟨β ^ 3 * δ, hz, ?_⟩
  -- the inequality is `WeightModulus.weight_310` at the real number `‖β‖`
  have hdn : 1 ≤ ‖((‖β‖ : ℝ) : ℂ) * α * γ‖ := by simpa [norm_mul] using hdet
  obtain ⟨h1, h2, h3, h4⟩ := Psc.WeightModulus.weight_310 hβ1 hα1 hγ1 rfl hdn
  have e : ∀ x : ℂ, ‖((‖β‖ : ℝ) : ℂ) ^ 3 * x‖ = ‖β ^ 3 * x‖ := fun x => by
    simp [norm_pow]
  rcases hδ with h | h
  · rw [h, ← e]; exact ⟨h3, h1⟩
  · rw [h, ← e]; exact ⟨h4, h2⟩

/-- **The `(2,1,1)` orbit contains `d β`** (`d = β α γ`): from a root of `q` of shape
`(2,1,1)`, `orbit_exponent_on_beta` gives the root `β² α γ = β · d`.  (Moved here from
`Psc.Degree4Floor`, which keeps a deprecated alias; `orbit_211_forces_unit` uses it.) -/
theorem orbit_211_root (q : ℚ[X]) (a b c : ℕ)
    (habc : (a, b, c) = (2, 1, 1) ∨ (a, b, c) = (1, 2, 1) ∨ (a, b, c) = (1, 1, 2))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0) : aeval (β * (β * α * γ)) q = 0 := by
  have h1 := orbit_exponent_on_beta hf hdeg hβ hα hγ hβα hβγ hαγ q a b c hq
  rcases habc with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h
  · exact of_eq (by ring1) hq
  · obtain ⟨x, y, hxy, hm⟩ := h1.1
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] at hm <;> exact of_eq (by ring1) hm
  · obtain ⟨x, y, hxy, hm⟩ := h1.2
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] at hm <;> exact of_eq (by ring1) hm

/-- **The `(2,1,1)` orbit forces `|d| = 1`** (task item 3). -/
theorem orbit_211_forces_unit (hdet : 1 ≤ ‖β * α * γ‖) (q : ℚ[X]) (a b c : ℕ)
    (habc : (a, b, c) = (2, 1, 1) ∨ (a, b, c) = (1, 2, 1) ∨ (a, b, c) = (1, 1, 2))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0)
    (hbound : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ ‖β‖) :
    ‖β * α * γ‖ = 1 := by
  have hz := orbit_211_root hf hdeg hβ hα hγ hβα hβγ hαγ q a b c habc hq
  have h := hbound _ hz
  rw [norm_mul (β : ℂ) (β * α * γ)] at h
  have hB : 0 < ‖β‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0] at hdet
    simp at hdet
    linarith
  have : ‖β * α * γ‖ ≤ 1 := by
    by_contra hlt
    push Not at hlt
    nlinarith
  exact le_antisymm this hdet

/-- In the unit-determinant case with `‖α‖ = ‖γ‖`, the root `α` is not real. -/
theorem im_ne_zero_of_norm_eq (hβ1 : 1 < ‖β‖) (hunit : ‖β * α * γ‖ = 1) (hαγn : ‖α‖ = ‖γ‖) :
    α.im ≠ 0 := by
  intro hαr
  have hf0 := hf.ne_zero
  rw [norm_mul, norm_mul] at hunit
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hunit
  -- complex conjugation permutes the roots of the rational polynomial `f`
  have hconj : ∀ w : ℂ, aeval w f = 0 → aeval (starRingEnd ℂ w) f = 0 :=
    fun _ hw => aeval_conj_eq_zero hw
  -- step 1: `γ` is real
  have hγr : γ.im = 0 := by
    rcases root_eq_of_three hf0 hdeg hβ hα hγ hβα hβγ hαγ (hconj γ hγ) with h | h | h
    · exfalso
      have hn : ‖γ‖ = ‖β‖ := by rw [← h, Complex.norm_conj]
      rw [← hαγn] at hn
      rw [hn] at hunit
      nlinarith [hβ1]
    · exfalso
      have h' : γ = starRingEnd ℂ α := by rw [← h, Complex.conj_conj]
      rw [Complex.conj_eq_iff_im.2 hαr] at h'
      exact hαγ h'.symm
    · exact Complex.conj_eq_iff_im.1 h
  -- step 2: `γ = -α`
  have hγα : γ = -α := by
    have h1 : |α.re| = |γ.re| := by
      rw [Complex.abs_re_eq_norm.2 hαr, Complex.abs_re_eq_norm.2 hγr, hαγn]
    rcases abs_eq_abs.1 h1 with h | h
    · exact absurd (Complex.ext h (by rw [hαr, hγr])) hαγ
    · apply Complex.ext
      · simp [h]
      · simp [hαr, hγr]
  -- step 3: `α² = -c₁/c₃` is rational
  have hev : ∀ w : ℂ, aeval w f = (f.coeff 0 : ℂ) + (f.coeff 1 : ℂ) * w + (f.coeff 2 : ℂ) * w ^ 2
      + (f.coeff 3 : ℂ) * w ^ 3 := by
    intro w
    rw [aeval_eq_sum_range, hdeg]
    simp [Finset.sum_range_succ, Rat.smul_def]
  have hc3 : f.coeff 3 ≠ 0 := by
    have := leadingCoeff_ne_zero.2 hf0
    rwa [leadingCoeff, hdeg] at this
  have h1 := hev α
  have h2 := hev (-α)
  rw [hα] at h1
  have hγ' : aeval (-α) f = 0 := hγα ▸ hγ
  rw [hγ'] at h2
  have h3 : ((f.coeff 1 : ℂ) + (f.coeff 3 : ℂ) * α ^ 2) * (2 * α) = 0 := by
    linear_combination h2 - h1
  have h4 : (f.coeff 1 : ℂ) + (f.coeff 3 : ℂ) * α ^ 2 = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd (by linear_combination h / 2) hα0
  set r : ℚ := -f.coeff 1 / f.coeff 3 with hr
  have hsq : α ^ 2 = (r : ℂ) := by
    have hc3' : (f.coeff 3 : ℂ) ≠ 0 := by exact_mod_cast hc3
    rw [hr]
    push_cast
    field_simp
    linear_combination h4
  -- step 4: then `α` has degree at most two over `ℚ`, but its minimal polynomial is cubic
  have hp0 : (X ^ 2 - C r : ℚ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) r
  have hpα : aeval α (X ^ 2 - C r : ℚ[X]) = 0 := by
    simp [hsq]
  have hle := minpoly.degree_le_of_ne_zero ℚ α hp0 hpα
  rw [← minpoly.eq_of_irreducible hf hα, degree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hf0)),
    degree_X_pow_sub_C (by norm_num), degree_eq_natDegree hf0, hdeg] at hle
  exact absurd hle (by decide)

/-- **The `(2,2,0)` orbit forces a unit determinant and a complex pair** (task item 4). -/
theorem orbit_220_forces_complex_unit (hβ1 : 1 < ‖β‖) (hdet : 1 ≤ ‖β * α * γ‖) (q : ℚ[X])
    (a b c : ℕ) (habc : (a, b, c) = (2, 2, 0) ∨ (a, b, c) = (2, 0, 2) ∨ (a, b, c) = (0, 2, 2))
    (hq : aeval (β ^ a * α ^ b * γ ^ c) q = 0)
    (hbound : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ ‖β‖) :
    ‖β * α * γ‖ = 1 ∧ ‖α‖ = ‖γ‖ ∧ α.im ≠ 0 ∧ γ.im ≠ 0 := by
  obtain ⟨hA, hG⟩ := orbit_220_both hf hdeg hβ hα hγ hβα hβγ hαγ q a b c habc hq
  -- the modulus step is `WeightModulus.weight_220` at the real number `‖β‖`
  have e : ∀ x : ℂ, ‖((‖β‖ : ℝ) : ℂ) ^ 2 * x ^ 2‖ = ‖β ^ 2 * x ^ 2‖ := fun x => by
    simp [norm_pow]
  have hdn : 1 ≤ ‖((‖β‖ : ℝ) : ℂ) * α * γ‖ := by simpa [norm_mul] using hdet
  obtain ⟨hunit', hαγn, -⟩ := Psc.WeightModulus.weight_220 hβ1 rfl hdn
    (by rw [e]; exact hbound _ hA) (by rw [e]; exact hbound _ hG)
  have hunit : ‖β * α * γ‖ = 1 := by simpa [norm_mul] using hunit'
  refine ⟨hunit, hαγn, ?_, ?_⟩
  · exact im_ne_zero_of_norm_eq hf hdeg hβ hα hγ hβα hβγ hαγ hβ1 hunit hαγn
  · refine im_ne_zero_of_norm_eq hf hdeg hβ hγ hα hβγ hβα hαγ.symm hβ1 ?_ hαγn.symm
    rw [show β * γ * α = β * α * γ by ring]
    exact hunit

end Orbit

/-! ### Weights that are pure powers of a root

Under the Pisot moduli a weight of shape `(1,1,1)` or `(2,1,1)` is never numerically a pure
power `x³`, `x⁴` of a root `x ∈ {β, α, γ}`.  Without the moduli it can be: for the irreducible
`X³ − 2` every three distinct roots give `βαγ = β³`, `β²αγ = β⁴`
(`Psc.SectorBridge.mono_eq_pow_of_cube_eq`, `Psc.SectorBridge.cube_root_two_control`). -/

section PurePower

variable {β α γ : ℂ} (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1)
  (hdet : 1 ≤ ‖β * α * γ‖)

include hβ1 hα1 hγ1 hdet

/-- **The `(1,1,1)` weight is not a cube of a root** under the Pisot moduli and
`1 ≤ ‖βαγ‖`: `βαγ = β³` gives `‖α‖ ‖γ‖ = ‖β‖² > 1`, and `βαγ = α³` (resp. `γ³`) gives
`1 ≤ ‖βαγ‖ = ‖α‖³ < 1`. -/
theorem mono111_ne_cube :
    β * α * γ ≠ β ^ 3 ∧ β * α * γ ≠ α ^ 3 ∧ β * α * γ ≠ γ ^ 3 := by
  have ha := norm_nonneg α
  have hc := norm_nonneg γ
  have hb : 0 < ‖β‖ := by linarith
  rw [norm_mul, norm_mul] at hdet
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have e := congrArg norm h
    rw [norm_mul, norm_mul, norm_pow] at e
    have hac : ‖α‖ * ‖γ‖ = ‖β‖ ^ 2 := by
      have : ‖β‖ * (‖α‖ * ‖γ‖ - ‖β‖ ^ 2) = 0 := by linear_combination e
      linear_combination (mul_eq_zero.1 this).resolve_left hb.ne'
    nlinarith [mul_le_mul_of_nonneg_left hγ1.le ha]
  · have e := congrArg norm h
    rw [norm_mul, norm_mul, norm_pow] at e
    nlinarith [pow_lt_one₀ ha hα1 (by norm_num : (3 : ℕ) ≠ 0)]
  · have e := congrArg norm h
    rw [norm_mul, norm_mul, norm_pow] at e
    nlinarith [pow_lt_one₀ hc hγ1 (by norm_num : (3 : ℕ) ≠ 0)]

/-- **Seven of the nine `(2,1,1)`-versus-fourth-power equalities fail under the moduli
alone** (`1 < ‖β‖`, `‖α‖, ‖γ‖ < 1`, `1 ≤ ‖βαγ‖`, no Galois input).  With `b, a, c` the
moduli of `β, α, γ` and `D = bac ≥ 1`: `β²αγ = β⁴` gives `ac = b²`; `β²αγ = α⁴` (or `γ⁴`)
gives `bD = a⁴ < 1`; `βα²γ = β⁴` gives `a²c = b³`; `βα²γ = α⁴` gives `D = a³`; symmetrically
for `βαγ²`.  The two remaining equalities `βα²γ = γ⁴`, `βαγ² = α⁴` are consistent with the
moduli (`moduli_211_control`) and are excluded by the Galois step
(`mono211_ne_pow4_galois`). -/
theorem mono211_ne_pow4_of_moduli :
    β ^ 2 * α * γ ≠ β ^ 4 ∧ β ^ 2 * α * γ ≠ α ^ 4 ∧ β ^ 2 * α * γ ≠ γ ^ 4 ∧
      β * α ^ 2 * γ ≠ β ^ 4 ∧ β * α ^ 2 * γ ≠ α ^ 4 ∧
      β * α * γ ^ 2 ≠ β ^ 4 ∧ β * α * γ ^ 2 ≠ γ ^ 4 := by
  have ha := norm_nonneg α
  have hc := norm_nonneg γ
  have hb : 0 < ‖β‖ := by linarith
  rw [norm_mul, norm_mul] at hdet
  have ha4 := pow_lt_one₀ ha hα1 (by norm_num : (4 : ℕ) ≠ 0)
  have hc4 := pow_lt_one₀ hc hγ1 (by norm_num : (4 : ℕ) ≠ 0)
  have hac : ‖α‖ * ‖γ‖ < 1 := by nlinarith [mul_le_mul_of_nonneg_left hγ1.le ha]
  have ha0 : 0 < ‖α‖ := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · rw [← h] at hdet; simp at hdet; linarith
  have hc0 : 0 < ‖γ‖ := by
    rcases hc.lt_or_eq with h | h
    · exact h
    · rw [← h] at hdet; simp at hdet; linarith
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩ <;> have e := congrArg norm h <;>
    simp only [norm_mul, norm_pow] at e
  · -- `‖α‖ ‖γ‖ = ‖β‖²`
    have : ‖β‖ ^ 2 * (‖α‖ * ‖γ‖ - ‖β‖ ^ 2) = 0 := by linear_combination e
    have h2 := (mul_eq_zero.1 this).resolve_left (by positivity)
    nlinarith
  · nlinarith
  · nlinarith
  · -- `‖α‖² ‖γ‖ = ‖β‖³`
    have : ‖β‖ * (‖α‖ ^ 2 * ‖γ‖ - ‖β‖ ^ 3) = 0 := by linear_combination e
    have h2 := (mul_eq_zero.1 this).resolve_left hb.ne'
    have h3 : 1 < ‖β‖ ^ 3 := one_lt_pow₀ hβ1 (by norm_num)
    have h4 : ‖α‖ * (‖α‖ * ‖γ‖) < ‖α‖ * 1 := mul_lt_mul_of_pos_left hac ha0
    nlinarith
  · -- `‖βαγ‖ = ‖α‖³`
    have : ‖α‖ * (‖β‖ * ‖α‖ * ‖γ‖ - ‖α‖ ^ 3) = 0 := by linear_combination e
    have h2 := (mul_eq_zero.1 this).resolve_left ha0.ne'
    nlinarith [pow_lt_one₀ ha hα1 (by norm_num : (3 : ℕ) ≠ 0)]
  · have : ‖β‖ * (‖α‖ * ‖γ‖ ^ 2 - ‖β‖ ^ 3) = 0 := by linear_combination e
    have h2 := (mul_eq_zero.1 this).resolve_left hb.ne'
    have h3 : 1 < ‖β‖ ^ 3 := one_lt_pow₀ hβ1 (by norm_num)
    have h4 : ‖γ‖ * (‖α‖ * ‖γ‖) < ‖γ‖ * 1 := mul_lt_mul_of_pos_left hac hc0
    nlinarith
  · have : ‖γ‖ * (‖β‖ * ‖α‖ * ‖γ‖ - ‖γ‖ ^ 3) = 0 := by linear_combination e
    have h2 := (mul_eq_zero.1 this).resolve_left hc0.ne'
    nlinarith [pow_lt_one₀ hc hγ1 (by norm_num : (3 : ℕ) ≠ 0)]

end PurePower

/-- **The moduli alone do not exclude `βα²γ = γ⁴`** (counter-calibration of
`mono211_ne_pow4_of_moduli`): `(β, α, γ) = (729/250, 1/2, 9/10)` has `1 < β`, `α, γ < 1`,
`βαγ = 6561/5000 ≥ 1` and `βα²γ = γ⁴ = 6561/10000`.  So the Galois hypotheses of
`mono211_ne_pow4_galois` are not redundant. -/
theorem moduli_211_control :
    ∃ β α γ : ℂ, 1 < ‖β‖ ∧ ‖α‖ < 1 ∧ ‖γ‖ < 1 ∧ 1 ≤ ‖β * α * γ‖ ∧ β * α ^ 2 * γ = γ ^ 4 := by
  refine ⟨((729 / 250 : ℚ) : ℂ), ((1 / 2 : ℚ) : ℂ), ((9 / 10 : ℚ) : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Complex.norm_ratCast]; norm_num
  · rw [Complex.norm_ratCast]; norm_num
  · rw [Complex.norm_ratCast]; norm_num
  · rw [← Rat.cast_mul, ← Rat.cast_mul, Complex.norm_ratCast]; norm_num
  · push_cast; norm_num

section PureGalois
variable {f : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3) {β α γ : ℂ}
    (hβ : aeval β f = 0) (hα : aeval α f = 0) (hγ : aeval γ f = 0)
    (hβα : β ≠ α) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    (hβ1 : 1 < ‖β‖) (hα1 : ‖α‖ < 1) (hγ1 : ‖γ‖ < 1) (hdet : 1 ≤ ‖β * α * γ‖)
    (hr : ∃ r : ℚ, (r : ℂ) = β * α * γ)
include hf hdeg hβ hα hγ hβα hβγ hαγ hβ1 hα1 hγ1 hdet hr

/-- **The two `(2,1,1)` equalities the moduli leave open fail by the Galois step**, for the
roots `β, α, γ` of an irreducible rational cubic with the Pisot moduli and a rational
`d = βαγ` (in the application `d = det M`, `Psc.SectorBridge.det_eq_mul_roots`).  If
`βα²γ = γ⁴` then `βα² = γ³`, so `β⁴α⁵ = d³`: the monomial `β⁴α⁵` is a root of the rational
`X − d³`.  The conjugation `β ↦ α` of `exists_conj` transports this to `α⁴β⁵ = d³` or
`α⁴γ⁵ = d³`, i.e. `αβ² = γ³` (then `b · D = c⁴ < 1 < b · D`) or `αγ² = β³` (then
`ac² < 1 < b³`).  `βαγ² = α⁴` is the same with `β ↦ γ`. -/
theorem mono211_ne_pow4_galois :
    β * α ^ 2 * γ ≠ γ ^ 4 ∧ β * α * γ ^ 2 ≠ α ^ 4 := by
  obtain ⟨r, hr⟩ := hr
  have ha := norm_nonneg α
  have hc := norm_nonneg γ
  have hb : 0 < ‖β‖ := by linarith
  have hn : ‖β * α * γ‖ = ‖β‖ * ‖α‖ * ‖γ‖ := by rw [norm_mul, norm_mul]
  have hβ0 : β ≠ 0 := norm_pos_iff.1 hb
  have hα0 : α ≠ 0 := by rintro rfl; simp at hdet; linarith
  have hγ0 : γ ≠ 0 := by rintro rfl; simp at hdet; linarith
  have hb3 : 1 < ‖β‖ ^ 3 := one_lt_pow₀ hβ1 (by norm_num)
  have hac : ‖α‖ * ‖γ‖ < 1 := by nlinarith [mul_le_mul_of_nonneg_left hγ1.le ha]
  -- the relation `q(m) = 0` for the monomial `m` and `q = X - r³`
  have hq : ∀ m : ℂ, m = (β * α * γ) ^ 3 → aeval m (X - C (r ^ 3) : ℚ[X]) = 0 := by
    rintro m rfl
    simp [hr]
  constructor
  · intro h
    have h1 : β * α ^ 2 = γ ^ 3 := mul_right_cancel₀ hγ0 (by linear_combination h)
    have hm := hq (β ^ 4 * α ^ 5 * γ ^ 0) (by linear_combination (β ^ 3 * α ^ 3) * h1)
    obtain ⟨x, y, z, hp, hx, -, -, ht⟩ := exists_conj hf hdeg hβ hα hγ hβα hβγ hαγ hβ hα
    have hx := hx rfl
    have hm' := ht _ 4 5 0 hm
    simp only [aeval_sub, aeval_X, aeval_C, map_pow, eq_ratCast, hr, sub_eq_zero] at hm'
    rcases hp with ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ |
      ⟨h1', h2, h3⟩ <;> rw [h1'] at hx <;> rw [h1', h2, h3] at hm'
    · exact hβα hx
    · exact hβα hx
    · -- `α β² = γ³`
      have e1 : α * β ^ 2 = γ ^ 3 :=
        mul_left_cancel₀ (pow_ne_zero 3 (mul_ne_zero hα0 hβ0)) (by linear_combination hm')
      have e := congrArg norm e1
      simp only [norm_mul, norm_pow] at e
      have : ‖β‖ * (‖β‖ * ‖α‖ * ‖γ‖) = ‖γ‖ ^ 4 := by linear_combination ‖γ‖ * e
      nlinarith [pow_lt_one₀ hc hγ1 (by norm_num : (4 : ℕ) ≠ 0)]
    · -- `α γ² = β³`
      have e1 : α * γ ^ 2 = β ^ 3 :=
        mul_left_cancel₀ (pow_ne_zero 3 (mul_ne_zero hα0 hγ0)) (by linear_combination hm')
      have e := congrArg norm e1
      simp only [norm_mul, norm_pow] at e
      have h4 : ‖γ‖ * (‖α‖ * ‖γ‖) < ‖γ‖ * 1 := mul_lt_mul_of_pos_left hac (norm_pos_iff.2 hγ0)
      nlinarith
    · exact hαγ hx.symm
    · exact hαγ hx.symm
  · intro h
    have h1 : β * γ ^ 2 = α ^ 3 := mul_right_cancel₀ hα0 (by linear_combination h)
    have hm := hq (β ^ 4 * α ^ 0 * γ ^ 5) (by linear_combination (β ^ 3 * γ ^ 3) * h1)
    obtain ⟨x, y, z, hp, hx, -, -, ht⟩ := exists_conj hf hdeg hβ hα hγ hβα hβγ hαγ hβ hγ
    have hx := hx rfl
    have hm' := ht _ 4 0 5 hm
    simp only [aeval_sub, aeval_X, aeval_C, map_pow, eq_ratCast, hr, sub_eq_zero] at hm'
    rcases hp with ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ |
      ⟨h1', h2, h3⟩ <;> rw [h1'] at hx <;> rw [h1', h2, h3] at hm'
    · exact hβγ hx
    · exact hβγ hx
    · exact hαγ hx
    · exact hαγ hx
    · -- `γ α² = β³`
      have e1 : γ * α ^ 2 = β ^ 3 :=
        mul_left_cancel₀ (pow_ne_zero 3 (mul_ne_zero hγ0 hα0)) (by linear_combination hm')
      have e := congrArg norm e1
      simp only [norm_mul, norm_pow] at e
      have h4 : ‖α‖ * (‖α‖ * ‖γ‖) < ‖α‖ * 1 := mul_lt_mul_of_pos_left hac (norm_pos_iff.2 hα0)
      nlinarith
    · -- `γ β² = α³`
      have e1 : γ * β ^ 2 = α ^ 3 :=
        mul_left_cancel₀ (pow_ne_zero 3 (mul_ne_zero hγ0 hβ0)) (by linear_combination hm')
      have e := congrArg norm e1
      simp only [norm_mul, norm_pow] at e
      have : ‖β‖ * (‖β‖ * ‖α‖ * ‖γ‖) = ‖α‖ ^ 4 := by linear_combination ‖α‖ * e
      nlinarith [pow_lt_one₀ ha hα1 (by norm_num : (4 : ℕ) ≠ 0)]

/-- **No `(2,1,1)` weight is a fourth power of a root** (all nine equalities), for the roots of
an irreducible rational cubic with the Pisot moduli and a rational `βαγ`:
`mono211_ne_pow4_of_moduli` and `mono211_ne_pow4_galois`. -/
theorem mono211_ne_pow4 :
    ∀ w ∈ ({β ^ 2 * α * γ, β * α ^ 2 * γ, β * α * γ ^ 2} : Set ℂ),
      ∀ x ∈ ({β, α, γ} : Set ℂ), w ≠ x ^ 4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := mono211_ne_pow4_of_moduli hβ1 hα1 hγ1 hdet
  obtain ⟨h8, h9⟩ := mono211_ne_pow4_galois hf hdeg hβ hα hγ hβα hβγ hαγ hβ1 hα1 hγ1 hdet hr
  intro w hw x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw hx
  rcases hw with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> assumption

end PureGalois

end Psc.GaloisOrbit
