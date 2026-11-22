import PscVerif.PeriodicPartnerOrdinaryProximal
import Mathlib.Data.ENat.Lattice

/-!
# Rotation-factor descent and finite nonproximal fibre rank

Continuous equivariant maps preserve ordinary proximality. Group rotations
have only diagonal proximal pairs, so every continuous rotation-factor map
descends uniquely through a compact-to-Hausdorff factor with proximal fibres.

The rank defined here is attached to the specified map and its specified
fibre. No published maximal-factor identification or measure conclusion is
part of its definition or of the rank-one theorem.

Source decision: `docs/c4-rotation-factor-rank-stop-go-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerRotationFactor

open Function Set Topology
open Psc.PeriodicPartnerOrdinaryProximal

section ContinuousImages

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The common-orbit-closure definition of proximality is preserved by a
continuous map that intertwines the two actions. -/
theorem topologicallyProximal_map (act : ℝ → X → X) (act' : ℝ → Y → Y)
    (f : X → Y) (hf : Continuous f)
    (hequiv : ∀ t x, f (act t x) = act' t (f x))
    {x y : X} (h : TopologicallyProximal act x y) :
    TopologicallyProximal act' (f x) (f y) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨f z, ?_⟩
  let C := closure (range (fun t : ℝ => (act' t (f x), act' t (f y))))
  have hc : IsClosed {p : X × X | (f p.1, f p.2) ∈ C} :=
    isClosed_closure.preimage (hf.prodMap hf)
  apply hc.closure_subset_iff.mpr ?_ hz
  rintro _ ⟨t, rfl⟩
  change (f (act t x), f (act t y)) ∈ C
  rw [hequiv, hequiv]
  exact subset_closure (mem_range_self t)

end ContinuousImages

section Rotations

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [T2Space G]

/-- The relative group element is constant along a common left-translation
orbit and equals the identity at any diagonal limit. No compactness or
additional hypothesis on the translation parameter is needed. -/
@[to_additive eq_of_topologicallyProximal_add_rotation]
theorem eq_of_topologicallyProximal_rotation (ρ : ℝ → G) {x y : G}
    (h : TopologicallyProximal (fun t z => ρ t * z) x y) : x = y := by
  obtain ⟨z, hz⟩ := h
  have hc : IsClosed {p : G × G | p.1⁻¹ * p.2 = x⁻¹ * y} :=
    isClosed_eq (continuous_fst.inv.mul continuous_snd) continuous_const
  have he : z⁻¹ * z = x⁻¹ * y := by
    apply hc.closure_subset_iff.mpr ?_ hz
    rintro _ ⟨t, rfl⟩
    simp only [mem_ofPred_eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  exact inv_mul_eq_one.mp (by simpa using he.symm)

end Rotations

section Descent

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [CompactSpace X] [T2Space Y]

/-- Quotient descent through a compact-to-Hausdorff map with proximal
fibres. The other action need only have diagonal proximal pairs. -/
theorem existsUnique_continuous_equivariant_descent
    (act : ℝ → X → X) (actY : ℝ → Y → Y) (actZ : ℝ → Z → Z)
    (g : X → Y) (hg : Continuous g) (honto : Surjective g)
    (hg_equiv : ∀ t x, g (act t x) = actY t (g x))
    (hprox : ∀ x y, g x = g y → TopologicallyProximal act x y)
    (hdiag : ∀ z w, TopologicallyProximal actZ z w → z = w)
    (f : X → Z) (hf : Continuous f)
    (hf_equiv : ∀ t x, f (act t x) = actZ t (f x)) :
    ∃! d : Y → Z, Continuous d ∧ (∀ x, d (g x) = f x) ∧
      ∀ t y, d (actY t y) = actZ t (d y) := by
  classical
  have hconst (x y : X) (hxy : g x = g y) : f x = f y :=
    hdiag (f x) (f y)
      (topologicallyProximal_map act actZ f hf hf_equiv (hprox x y hxy))
  let d : Y → Z := fun y => f (surjInv honto y)
  have hd (x : X) : d (g x) = f x :=
    hconst (surjInv honto (g x)) x (surjInv_eq honto (g x))
  have hdcomp : d ∘ g = f := funext hd
  have hquot : IsQuotientMap g := .of_surjective_continuous honto hg
  have hdcont : Continuous d := hquot.continuous_iff.mpr (by rw [hdcomp]; exact hf)
  have hdequiv (t : ℝ) (y : Y) : d (actY t y) = actZ t (d y) := by
    obtain ⟨x, rfl⟩ := honto y
    rw [← hg_equiv, hd, hf_equiv, hd]
  refine ⟨d, ⟨hdcont, hd, hdequiv⟩, ?_⟩
  intro e he
  funext y
  obtain ⟨x, rfl⟩ := honto y
  exact (he.2.1 x).trans (hd x).symm

/-- Every continuous equivariant map to a Hausdorff group rotation descends
uniquely through a compact-to-Hausdorff factor with proximal fibres. This
is a universal property for the stated class of group-rotation factors. -/
@[to_additive existsUnique_add_rotation_descent]
theorem existsUnique_rotation_descent
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [T2Space G]
    (act : ℝ → X → X) (actY : ℝ → Y → Y)
    (g : X → Y) (hg : Continuous g) (honto : Surjective g)
    (hg_equiv : ∀ t x, g (act t x) = actY t (g x))
    (hprox : ∀ x y, g x = g y → TopologicallyProximal act x y)
    (ρ : ℝ → G) (f : X → G) (hf : Continuous f)
    (hf_equiv : ∀ t x, f (act t x) = ρ t * f x) :
    ∃! d : Y → G, Continuous d ∧ (∀ x, d (g x) = f x) ∧
      ∀ t y, d (actY t y) = ρ t * d y :=
  existsUnique_continuous_equivariant_descent act actY (fun t z => ρ t * z)
    g hg honto hg_equiv hprox
    (fun _ _ h => eq_of_topologicallyProximal_rotation ρ h) f hf hf_equiv

end Descent

section FiniteNonproximalRank

variable {X Y : Type*} [TopologicalSpace X]

/-- The supremum of cardinalities of finite pairwise nonproximal subsets
of a specified factor fibre. Extended naturals retain an unbounded rank.
This definition does not assert that the factor is maximal equicontinuous. -/
noncomputable def fibreNonproximalRank (act : ℝ → X → X) (g : X → Y) (z : Y) : ℕ∞ :=
  ⨆ (F : Finset X) (_ : ∀ x ∈ F, g x = z)
    (_ : (F : Set X).Pairwise (fun x y => ¬ TopologicallyProximal act x y)), (F.card : ℕ∞)

/-- A nonempty fibre whose pairs are all proximal has finite nonproximal
rank exactly one, even if the fibre contains several distinct points. -/
theorem fibreNonproximalRank_eq_one (act : ℝ → X → X) (g : X → Y) (z : Y)
    (hne : ∃ x, g x = z)
    (hprox : ∀ x y, g x = z → g y = z → TopologicallyProximal act x y) :
    fibreNonproximalRank act g z = 1 := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply iSup_le
    intro hpair
    have hcard : F.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      by_contra hne
      exact hpair hx hy hne (hprox x y (hF x hx) (hF y hy)))
    exact_mod_cast hcard
  · obtain ⟨x, hx⟩ := hne
    have hf : ∀ y ∈ ({x} : Finset X), g y = z := by simpa using hx
    have hp : (({x} : Finset X) : Set X).Pairwise
        (fun a b => ¬ TopologicallyProximal act a b) := by simp
    exact le_iSup_of_le ({x} : Finset X)
      (le_iSup_of_le hf (le_iSup_of_le hp (by simp)))

/-- Surjectivity supplies the singleton lower bound in every fibre. -/
theorem fibreNonproximalRank_eq_one_of_surjective
    (act : ℝ → X → X) (g : X → Y) (honto : Surjective g)
    (hprox : ∀ x y, g x = g y → TopologicallyProximal act x y) (z : Y) :
    fibreNonproximalRank act g z = 1 :=
  fibreNonproximalRank_eq_one act g z (honto z)
    (fun x y hx hy => hprox x y (hx.trans hy.symm))

end FiniteNonproximalRank

end Psc.PeriodicPartnerRotationFactor
