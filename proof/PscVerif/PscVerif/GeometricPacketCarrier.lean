import PscVerif.OccurrenceAdmissibility
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NormNum

/-!
# A finite geometric packet carrier from an actual chart enclosure

The two internal coordinates are bounded on every point of the actual
supplied tiles. Together with the physical interior strip, an exact full
chart reconstruction therefore bounds each integral residual coordinate.
The finite box is constructed and filtered by physical interior. Every
nonempty incoming ancestor of every admitted source is then represented,
so the existing literal history-cover theorem applies without an assumed
representation conclusion.

No topology, compactness, Pisot hypothesis, forward closure, or measure
statement is inferred. A smaller unchecked box or an exhausted executable
budget cannot replace the certified coordinate inequalities. All literal
incoming marks and histories remain in the cover index.

Pre-code gate: `docs/c4-geometric-packet-carrier-literature-2026-11-11.md`.
-/

namespace Psc.GeometricPacketCarrier

open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrencePiece
open Psc.OccurrenceCover Psc.OccurrenceNewborn Matrix
open scoped BigOperators

section Geometry

variable {G : Type*} [AddCommGroup G]

/-- Exact geometric inputs. `reconstruct` is the faithfulness statement on
integer translations; the two internal coordinates alone need not be
injective. `enclosed` concerns every actual tile point, not sampled points. -/
structure ChartEnclosure (star : (Fin 3 → ℤ) →+ G)
    (K : Fin 3 → Set G) (ℓ : Fin 3 → ℝ) where
  coordinate : Fin 2 → G →+ ℝ
  radius : Fin 2 → ℝ
  physicalBound : ℝ
  length_le : ∀ a, ℓ a ≤ physicalBound
  inverse : Fin 3 → Fin 3 → ℝ
  reconstruct : ∀ (z : Fin 3 → ℤ) (j : Fin 3),
    (z j : ℝ) = inverse j 0 * offset ℓ z +
      inverse j 1 * coordinate 0 (star z) + inverse j 2 * coordinate 1 (star z)
  enclosed : ∀ (a : Fin 3) (x : G), x ∈ K a →
    ∀ i : Fin 2, |coordinate i x| ≤ radius i

/-- The explicit inverse-chart coordinate estimate before integer rounding. -/
def ChartEnclosure.coordinateBound {star : (Fin 3 → ℤ) →+ G}
    {K : Fin 3 → Set G} {ℓ : Fin 3 → ℝ}
    (chart : ChartEnclosure star K ℓ) (j : Fin 3) : ℝ :=
  |chart.inverse j 0| * chart.physicalBound +
    |chart.inverse j 1| * (2 * chart.radius 0) +
    |chart.inverse j 2| * (2 * chart.radius 1)

/-- An actual intersection witness gives a difference of two enclosed
coordinates. Closed enclosure boundaries are retained. -/
theorem stable_difference_bound {star : (Fin 3 → ℤ) →+ G}
    {K : Fin 3 → Set G} {ℓ : Fin 3 → ℝ}
    (chart : ChartEnclosure star K ℓ) (p : Packet)
    (nonempty : (overlap star K p).Nonempty) (i : Fin 2) :
    |chart.coordinate i (star p.delta)| ≤ 2 * chart.radius i := by
  obtain ⟨x, htop, hbottom⟩ := nonempty
  have ht := chart.enclosed p.top x htop i
  have hb := chart.enclosed p.bottom (x - star p.delta) hbottom i
  have he : chart.coordinate i (star p.delta) =
      chart.coordinate i x - chart.coordinate i (x - star p.delta) := by
    rw [map_sub]
    abel
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

/-- Physical interior bounds the expanding coordinate. This does not
assert that arbitrary internal overlaps satisfy a physical strip. -/
theorem physical_offset_bound {star : (Fin 3 → ℤ) →+ G}
    {K : Fin 3 → Set G} {ℓ : Fin 3 → ℝ}
    (chart : ChartEnclosure star K ℓ) (positive : ∀ a, 0 < ℓ a)
    (p : Packet) (interior : p.Interior ℓ) :
    |offset ℓ p.delta| ≤ chart.physicalBound := by
  obtain ⟨hlo, hhi⟩ := (Packet.interior_iff_bounds ℓ positive p).mp interior
  apply abs_le.mpr
  constructor
  · linarith [chart.length_le p.top]
  · linarith [chart.length_le p.bottom]

/-- Reconstruction combines the physical and the two internal bounds to
control every integer coordinate. No finite carrier is assumed. -/
theorem integer_coordinate_bound {star : (Fin 3 → ℤ) →+ G}
    {K : Fin 3 → Set G} {ℓ : Fin 3 → ℝ}
    (chart : ChartEnclosure star K ℓ) (positive : ∀ a, 0 < ℓ a)
    (p : Packet) (interior : p.Interior ℓ)
    (nonempty : (overlap star K p).Nonempty) (j : Fin 3) :
    |(p.delta j : ℝ)| ≤ chart.coordinateBound j := by
  have hp := physical_offset_bound chart positive p interior
  have h0 := stable_difference_bound chart p nonempty 0
  have h1 := stable_difference_bound chart p nonempty 1
  rw [chart.reconstruct p.delta j]
  calc
    |chart.inverse j 0 * offset ℓ p.delta +
        chart.inverse j 1 * chart.coordinate 0 (star p.delta) +
        chart.inverse j 2 * chart.coordinate 1 (star p.delta)| ≤
        |chart.inverse j 0 * offset ℓ p.delta| +
        |chart.inverse j 1 * chart.coordinate 0 (star p.delta)| +
        |chart.inverse j 2 * chart.coordinate 1 (star p.delta)| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ chart.coordinateBound j := by
      simp only [abs_mul, ChartEnclosure.coordinateBound]
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h0 (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))

/-- Certified natural coordinate bounds always exist by Archimedeanness.
A particular executable box must still prove these same inequalities. -/
theorem exists_natural_bounds {star : (Fin 3 → ℤ) →+ G}
    {K : Fin 3 → Set G} {ℓ : Fin 3 → ℝ}
    (chart : ChartEnclosure star K ℓ) :
    ∃ N : Fin 3 → ℕ, ∀ j, chart.coordinateBound j ≤ (N j : ℝ) := by
  choose N hN using fun j : Fin 3 => exists_nat_ge (chart.coordinateBound j)
  exact ⟨N, hN⟩

end Geometry

/-! ## The actual finite box and its physically admitted packets -/

/-- All integral vectors inside the inclusive coordinate box. -/
def residualBox (N : Fin 3 → ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun j => Finset.Icc (-(N j : ℤ)) (N j : ℤ)

theorem mem_residualBox (N : Fin 3 → ℕ) (z : Fin 3 → ℤ) :
    z ∈ residualBox N ↔ ∀ j, |z j| ≤ (N j : ℤ) := by
  simp only [residualBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem residualBox_card (N : Fin 3 → ℕ) :
    (residualBox N).card = ∏ j, (2 * N j + 1) := by
  rw [residualBox, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j _
  rw [Int.card_Icc]
  omega

/-- Every letter pair over the complete residual box, before the physical
interior filter. Equal packets do not encode occurrence multiplicities. -/
noncomputable def boxPackets (N : Fin 3 → ℕ) : Finset Packet := by
  classical
  exact ((Finset.univ : Finset (Fin 3 × Fin 3)).product (residualBox N)).image
    (fun v => (⟨v.1.1, v.1.2, v.2⟩ : Packet))

theorem mem_boxPackets (N : Fin 3 → ℕ) (p : Packet) :
    p ∈ boxPackets N ↔ p.delta ∈ residualBox N := by
  classical
  constructor
  · intro hp
    obtain ⟨⟨⟨a, b⟩, z⟩, hz, he⟩ := Finset.mem_image.mp hp
    cases he
    exact (Finset.mem_product.mp hz).2
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨((p.top, p.bottom), p.delta),
      Finset.mem_product.mpr ⟨Finset.mem_univ _, hp⟩, ?_⟩
    cases p
    rfl

/-- The physical filter is essential: it supplies the premise needed to
propagate interiority to every actual incoming ancestor. -/
noncomputable def carrier (ℓ : Fin 3 → ℝ) (N : Fin 3 → ℕ) : Finset Packet := by
  classical
  exact (boxPackets N).filter (fun p => p.Interior ℓ)

theorem mem_carrier (ℓ : Fin 3 → ℝ) (N : Fin 3 → ℕ) (p : Packet) :
    p ∈ carrier ℓ N ↔ (∀ j, |p.delta j| ≤ (N j : ℤ)) ∧ p.Interior ℓ := by
  classical
  simp only [carrier, Finset.mem_filter, mem_boxPackets, mem_residualBox]

/-- An a priori packet budget independent of inverse-history depth. -/
theorem carrier_card_le (ℓ : Fin 3 → ℝ) (N : Fin 3 → ℕ) :
    (carrier ℓ N).card ≤ 9 * ∏ j, (2 * N j + 1) := by
  classical
  calc
    (carrier ℓ N).card ≤ (boxPackets N).card := Finset.card_filter_le _ _
    _ ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).product (residualBox N)).card :=
      Finset.card_image_le
    _ = 9 * ∏ j, (2 * N j + 1) := by
      simp [Finset.card_product, residualBox_card]

/-- The symmetric coordinate box and strict physical strip are swap closed. -/
theorem carrier_swap_closed (ℓ : Fin 3 → ℝ) (N : Fin 3 → ℕ)
    (p : Packet) (hp : p ∈ carrier ℓ N) : p.swap ∈ carrier ℓ N := by
  obtain ⟨hb, hi⟩ := (mem_carrier ℓ N p).mp hp
  apply (mem_carrier ℓ N p.swap).mpr
  refine ⟨?_, hi.swap⟩
  intro j
  simpa only [Packet.swap, Pi.neg_apply, abs_neg] using hb j

section Representation

variable {G : Type*} [AddCommGroup G]
variable {star : (Fin 3 → ℤ) →+ G} {K : Fin 3 → Set G} {ℓ : Fin 3 → ℝ}

/-- An actual nonempty overlap in the physical strip lies in the constructed
carrier whenever the chosen integer box dominates the proved chart bound. -/
theorem nonempty_overlap_mem_carrier (chart : ChartEnclosure star K ℓ)
    (positive : ∀ a, 0 < ℓ a) (N : Fin 3 → ℕ)
    (certified : ∀ j, chart.coordinateBound j ≤ (N j : ℝ))
    (p : Packet) (interior : p.Interior ℓ)
    (nonempty : (overlap star K p).Nonempty) : p ∈ carrier ℓ N := by
  apply (mem_carrier ℓ N p).mpr
  refine ⟨?_, interior⟩
  intro j
  have h := (integer_coordinate_bound chart positive p interior nonempty j).trans (certified j)
  exact_mod_cast h

/-- This is the previously supplied represented-ancestor premise, now
derived at every admitted source from the chart, actual enclosure and exact
physical scaling. No finite closure search or representation hypothesis is
used. Empty ancestor overlaps need not be represented. -/
theorem nonempty_inverse_ancestor_represented (s : Fin 3 → Word)
    (chart : ChartEnclosure star K ℓ) (positive : ∀ a, 0 < ℓ a)
    (β : ℝ) (positiveScale : 0 < β)
    (scale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (N : Fin 3 → ℕ) (certified : ∀ j, chart.coordinateBound j ≤ (N j : ℝ))
    (p : Packet) (hp : p ∈ carrier ℓ N) (u : Packet)
    (e : InverseOccurrence s p u) (nonempty : (overlap star K u).Nonempty) :
    u ∈ carrier ℓ N := by
  have hi := (mem_carrier ℓ N p).mp hp |>.2
  exact nonempty_overlap_mem_carrier chart positive N certified u
    (e.interior s ℓ β positive positiveScale scale hi) nonempty

/-- An omitted actual ancestor of an admitted source must have empty
overlap. This is a geometric exclusion, not a resource-cap verdict. -/
theorem outside_carrier_overlap_empty (s : Fin 3 → Word)
    (chart : ChartEnclosure star K ℓ) (positive : ∀ a, 0 < ℓ a)
    (β : ℝ) (positiveScale : 0 < β)
    (scale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (N : Fin 3 → ℕ) (certified : ∀ j, chart.coordinateBound j ≤ (N j : ℝ))
    (p : Packet) (hp : p ∈ carrier ℓ N) (u : Packet)
    (e : InverseOccurrence s p u) (outside : u ∉ carrier ℓ N) :
    overlap star K u = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hn
  exact outside (nonempty_inverse_ancestor_represented s chart positive β positiveScale
    scale N certified p hp u e hn)

/-- The constructed global finite carrier supports every prescribed
finite-history cover. Existing tile, action and range hypotheses are kept;
the nonempty-ancestor representation conclusion is proved above. Distinct
literal histories with equal endpoints remain separate indices. -/
theorem finite_carrier_history_cover (s : Fin 3 → Word)
    (A : G →+ G) (chart : ChartEnclosure star K ℓ)
    (positive : ∀ a, 0 < ℓ a) (β : ℝ) (positiveScale : 0 < β)
    (scale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (N : Fin 3 → ℕ) (certified : ∀ j, chart.coordinateBound j ≤ (N j : ℝ))
    (injective : Function.Injective A)
    (commute : ∀ z, A (star z) = star (incidenceZ s *ᵥ z))
    (tiles : TileEquation s A star K) (reflects : ReflectsIntegralRange s A star)
    (n : ℕ) (p : Packet) (hp : p ∈ carrier ℓ N) :
    Finite {h : History s n p // historyWithin s (carrier ℓ N) n p h} ∧
      overlap star K p =
        ⋃ h : {h : History s n p // historyWithin s (carrier ℓ N) n p h},
          historyPiece s A star K n p h.val := by
  refine ⟨Psc.OccurrenceAdmissibility.finite_restrictedHistory s (carrier ℓ N) n p, ?_⟩
  exact overlap_eq_iUnion_restrictedHistory A star K injective commute tiles reflects
    (carrier ℓ N)
    (nonempty_inverse_ancestor_represented s chart positive β positiveScale scale N certified)
    n p hp

end Representation

/-! ## Narrow controls for missing hypotheses and closed boundaries -/

/-- With both internal coordinates zero, the positive row `(1,1,1)` has
an invisible nonzero integer direction. No full reconstruction of the first
coordinate can then hold, regardless of the alleged inverse coefficients. -/
theorem missing_chart_control (a b c : ℝ) :
    ¬ ((1 : ℝ) = a * ((1 : ℝ) + (-1) + 0) + b * 0 + c * 0) := by
  norm_num

/-- Difference-box boundary contact can be a genuine intersection. The
bound is inclusive; rejecting equality would discard this actual point. -/
theorem enclosure_boundary_control :
    (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∧
      (1 : ℝ) - 2 ∈ Set.Icc (-1 : ℝ) 1 ∧
      |(2 : ℝ)| = 2 * 1 := by
  norm_num

/-- An undersized natural box cannot satisfy the required bound check. -/
theorem undersized_box_control : ¬ ((2 : ℝ) ≤ (1 : ℕ)) := by
  norm_num

end Psc.GeometricPacketCarrier
