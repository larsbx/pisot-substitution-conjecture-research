/-
# The ordinary hull as a continuous ℝ-flow, and inflation as a homeomorphism

Two F2 items of `docs/c4-family-lean-dynamical-roadmap-2026-11-21.md`:

* **action laws**: `LocalHull S` carries an `AddAction ℝ` by `t +ᵥ T = translate t T` with
  `ContinuousVAdd`, and inflation intertwines it, `inflate (t +ᵥ T) = (β t) +ᵥ inflate T`;
* **recognizability, topological form**: with compactness (`localHull_compactSpace`) and
  Hausdorffness (`PeriodicPartnerLocalHausdorff`), bijective inflation is a homeomorphism of
  the ordinary hull.  The σₖ instance is in `C4ParameterFamilyFlow`.

The negative control of that roadmap is checked as well: for the one-letter doubling
substitution `a ↦ aa` the hull is nonempty, yet inflation is not injective.  Bijectivity is a
genuine hypothesis of `inflateHomeomorph`.

Source decision: `docs/c4-hull-flow-homeomorphism-stop-go-2026-11-22.md`.
-/
import PscVerif.PeriodicPartnerLocalHausdorff
import PscVerif.PeriodicPartnerHullLeft
import PscVerif.PeriodicPartnerRealizationOnto

namespace Psc.PeriodicPartnerLocalTopology

open Function Set Psc.PeriodicPartnerHull
open LengthSubst

variable {α : Type*} (S : LengthSubst α)

/-! ## The translation flow -/

/-- The ordinary hull is an `ℝ`-set under translation, `t +ᵥ T = T - t`. -/
instance : AddAction ℝ (LocalHull S) where
  vadd := translate S
  zero_vadd := translate_zero S
  add_vadd s t T := (translate_translate S s t T).symm

theorem vadd_eq_translate (t : ℝ) (T : LocalHull S) : t +ᵥ T = translate S t T := rfl

/-- The translation flow is jointly continuous. -/
instance : ContinuousVAdd ℝ (LocalHull S) := ⟨continuous_translate S⟩

/-- Inflation intertwines the flow with its `β`-rescaling. -/
theorem inflate_vadd [Nonempty α] (t : ℝ) (T : LocalHull S) :
    inflate S (t +ᵥ T) = (S.β * t) +ᵥ inflate S T :=
  LocalHull.ext (inflateH_translate t T.toHull)

/-! ## Inflation as a homeomorphism -/

theorem inflate_bijective [Nonempty α] (hR : Bijective (inflateH (S := S))) :
    Bijective (inflate S) := by
  refine ⟨fun T U h => LocalHull.ext (hR.1 (congrArg LocalHull.toHull h)), fun T => ?_⟩
  obtain ⟨U, hU⟩ := hR.2 T.toHull
  exact ⟨⟨U⟩, LocalHull.ext hU⟩

/-- On a finite alphabet, bijective inflation is a homeomorphism of the ordinary hull: a
continuous bijection from a compact space to a Hausdorff space. -/
noncomputable def inflateHomeomorph [Fintype α] [DecidableEq α] [Nonempty α]
    (hR : Bijective (inflateH (S := S))) : LocalHull S ≃ₜ LocalHull S :=
  letI : CompactSpace (LocalHull S) := Psc.PeriodicPartnerRealizationOnto.localHull_compactSpace
  (continuous_inflate S).homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (inflate_bijective S hR))

@[simp] theorem inflateHomeomorph_apply [Fintype α] [DecidableEq α] [Nonempty α]
    (hR : Bijective (inflateH (S := S))) (T : LocalHull S) :
    inflateHomeomorph S hR T = inflate S T := rfl

/-! ## Negative control: one-letter doubling -/

/-- `a ↦ aa` with unit tiles and `β = 2`.  Its legal tilings are the translates of `ℤ`. -/
def doubling : LengthSubst Unit where
  σ _ := [(), ()]
  ne_nil _ := by simp
  ℓ _ := 1
  ℓ_pos _ := one_pos
  β := 2
  eigen _ := by norm_num

/-- Every doubling tiling is invariant under translation by one tile. -/
theorem doubling_translate_one (V : doubling.Hull) : LengthSubst.translate 1 V = V := by
  apply Subtype.ext
  ext ⟨a, x⟩
  change (a, x + 1) ∈ V.1 ↔ (a, x) ∈ V.1
  constructor
  · intro h
    obtain ⟨c, hc⟩ := endsAt_of_startsAt (T := V) (y := x + 1) (b := a) h
    have : (c, x + 1 - doubling.ℓ c) = (a, x) := by
      refine Prod.ext (Subsingleton.elim _ _) ?_
      show x + 1 - 1 = x
      ring
    exact this ▸ hc
  · intro h
    obtain ⟨b, hb⟩ := startsAt_of_endsAt (T := V) (y := x + 1) (b := a)
      (by simpa [EndsAt, doubling] using h)
    exact (Subsingleton.elim b a) ▸ hb

/-- Recognizability fails for `a ↦ aa`, although its hull is nonempty. -/
theorem doubling_not_injective : ¬ Injective (inflateH (S := doubling)) := by
  intro hinj
  obtain ⟨T⟩ := doubling.hull_nonempty (by norm_num [doubling])
  have hsame : inflateH (LengthSubst.translate (1 / 2) T) = inflateH T := by
    rw [inflateH_translate, show doubling.β * (1 / 2) = 1 by norm_num [doubling],
      doubling_translate_one]
  have hT := hinj hsame
  -- a tile `(a, x)` and its half-shift `(a, x + 1/2)` would both lie in `T`
  obtain ⟨p, ⟨hp, _⟩, -⟩ := T.2.1 0
  have hp' : (p.1, p.2 + 1 / 2) ∈ T.1 := by
    have : p ∈ (LengthSubst.translate (1 / 2) T).1 := by rw [hT]; exact hp
    exact this
  have hz : p.2 + 1 / 2 ∈ doubling.supp p := ⟨by linarith, by
    simp only [doubling]; linarith⟩
  have hz' : p.2 + 1 / 2 ∈ doubling.supp (p.1, p.2 + 1 / 2) := ⟨le_rfl, by
    simp only [doubling]; linarith⟩
  have := (T.2.1 (p.2 + 1 / 2)).unique ⟨hp, hz⟩ ⟨hp', hz'⟩
  have h2 := congrArg Prod.snd this
  simp only at h2
  linarith

end Psc.PeriodicPartnerLocalTopology
