import PscVerif.PeriodicPartnerOrdinaryProximal
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Fibre distality and unique preimages

When ordinary proximality is exactly the fibre relation of a specified
map, a base point is fibre-distal exactly when its fibre is a subsingleton.
Surjectivity makes this a unique-preimage statement, also almost everywhere
for any explicitly supplied measure. No full-measure premise is proved here.

Source decision: `docs/c4-fibre-distal-measure-stop-go-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerFibreDistal

open Function Set Filter MeasureTheory
open Psc.PeriodicPartnerOrdinaryProximal

variable {X Y : Type*} [TopologicalSpace X]

/-- A distal point has no distinct ordinarily proximal partner anywhere
in the source space, not merely in its specified factor fibre. -/
def IsDistalPoint (act : ℝ → X → X) (x : X) : Prop :=
  ∀ y : X, TopologicallyProximal act x y → y = x

/-- A base point is fibre-distal when every preimage is a distal point.
This definition is vacuous on an empty fibre. -/
def IsFibreDistal (act : ℝ → X → X) (g : X → Y) (z : Y) : Prop :=
  ∀ x : X, g x = z → IsDistalPoint act x

variable (act : ℝ → X → X) (g : X → Y)

/-- Both implications between proximality and equality of factor images
are retained explicitly in this equivalence. -/
theorem fibreDistal_iff_subsingleton
    (hprox : ∀ x y, g x = g y ↔ TopologicallyProximal act x y) (z : Y) :
    IsFibreDistal act g z ↔ ({x : X | g x = z} : Set X).Subsingleton := by
  constructor
  · intro hd x hx y hy
    exact (hd x hx y ((hprox x y).mp (hx.trans hy.symm))).symm
  · intro hs x hx y hxy
    exact hs (((hprox x y).mpr hxy).symm.trans hx) hx

/-- Nonemptiness is necessary when replacing a subsingleton fibre by
the existence of exactly one preimage. -/
theorem fibreDistal_iff_existsUnique
    (hprox : ∀ x y, g x = g y ↔ TopologicallyProximal act x y)
    (z : Y) (hne : ∃ x, g x = z) :
    IsFibreDistal act g z ↔ ∃! x : X, g x = z := by
  rw [fibreDistal_iff_subsingleton act g hprox z]
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, fun y hy => hs hy hx⟩
  · rintro ⟨x, hx, huniq⟩ y hy w hw
    exact (huniq y hy).trans (huniq w hw).symm

/-- A distinct proximal pair in a fibre refutes fibre-distality at that
base point; this does not refute an almost-everywhere assertion. -/
theorem not_fibreDistal_of_distinct_proximal {z : Y} {x y : X}
    (hx : g x = z) (hxy : TopologicallyProximal act x y) (hne : x ≠ y) :
    ¬ IsFibreDistal act g z := by
  intro hd
  exact hne (hd x hx y hxy).symm

/-- The almost-everywhere geometric input is exactly the almost-everywhere
unique-preimage input. The supplied measure need not yet be identified
with Haar measure, and neither side is asserted by this equivalence. -/
theorem ae_fibreDistal_iff_ae_existsUnique [MeasurableSpace Y]
    (honto : Surjective g)
    (hprox : ∀ x y, g x = g y ↔ TopologicallyProximal act x y)
    (ν : Measure Y) :
    (∀ᵐ z ∂ν, IsFibreDistal act g z) ↔ (∀ᵐ z ∂ν, ∃! x : X, g x = z) := by
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall fun z =>
    fibreDistal_iff_existsUnique act g hprox z (honto z)

end Psc.PeriodicPartnerFibreDistal
