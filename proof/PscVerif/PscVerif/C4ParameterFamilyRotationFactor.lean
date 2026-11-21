import PscVerif.C4ParameterFamilyOrdinaryProximal
import PscVerif.PeriodicPartnerRotationFactor

/-!
# Concrete factor rank and rotation-factor descent

The converse from ordinary proximality to equal concrete solenoid images is
unconditional. The remaining results retain the explicit zero-fibre anchor
premise from the earlier family interface. The rank is the finite nonproximal
rank of this specified factor; universality is stated for group rotations.
No invariant measure or almost-everywhere singleton-fibre theorem is asserted.

Source decision: `docs/c4-rotation-factor-rank-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyRotationFactor

open Function Set Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyRecognizability Psc.ParameterFamilyOrdinaryProximal
open Psc.PeriodicPartnerLocalTopology Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerOrdinaryProximal Psc.PeriodicPartnerRotationFactor

variable (k : ℕ) (hk : 1 ≤ k)

/-- The existing solenoid flow is translation by its value at zero. -/
theorem solenoid_flow_eq_add (t : ℝ) (z : Solenoid (geometry k hk)) :
    flow (pisotData k hk) t z = flow (pisotData k hk) t 0 + z := by
  unfold flow
  simp only [zero_add, add_comm]

/-- A common ordinary orbit-limit point forces equal concrete solenoid
images. This direction requires no zero-fibre witness assumption. -/
theorem solenoidRealize_eq_of_topologicallyProximal
    {T U : LocalHull (geometry k hk)}
    (h : TopologicallyProximal (translate (geometry k hk)) T U) :
    solenoidRealize k hk T = solenoidRealize k hk U := by
  let : T2Space (Solenoid (geometry k hk)) := solenoid_t2Space _
  apply eq_of_topologicallyProximal_add_rotation (fun t => flow (pisotData k hk) t 0)
  apply topologicallyProximal_map (translate (geometry k hk))
    (fun t z => flow (pisotData k hk) t 0 + z)
    (solenoidRealize k hk) (continuous_solenoidRealize k hk) ?_ h
  intro t T
  rw [solenoidRealize_translate, solenoid_flow_eq_add]

/-- The conditional anchor theorem identifies the full concrete fibre relation
with ordinary proximality. It does not supply the anchor premise. -/
theorem same_fibre_iff_proximal_of_zero_anchor_common_tile
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hanchor : ∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty)
    (T U : LocalHull (geometry k hk)) :
    solenoidRealize k hk T = solenoidRealize k hk U ↔
      TopologicallyProximal (translate (geometry k hk)) T U :=
  ⟨same_fibre_proximal_of_zero_anchor_common_tile k hk hV hanchor,
    solenoidRealize_eq_of_topologicallyProximal k hk⟩

/-- The finite pairwise-nonproximal cardinality quantity for this actual
solenoid map. This is not a definition imported from a published MEF. -/
noncomputable def concreteFibreRank (z : Solenoid (geometry k hk)) : ℕ∞ :=
  fibreNonproximalRank (translate (geometry k hk)) (solenoidRealize k hk) z

/-- Surjectivity and the conditional anchor transport make the concrete
factor's finite nonproximal rank one in every fibre, including exceptional
fibres containing more than one tiling. -/
theorem concreteFibreRank_eq_one_of_zero_anchor_common_tile
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hanchor : ∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty)
    (z : Solenoid (geometry k hk)) : concreteFibreRank k hk z = 1 :=
  fibreNonproximalRank_eq_one_of_surjective (translate (geometry k hk))
    (solenoidRealize k hk) (solenoidRealize_surjective k hk)
    (fun _ _ h => same_fibre_proximal_of_zero_anchor_common_tile k hk hV hanchor h) z

/-- Every continuous additive group-rotation map descends uniquely through
the concrete solenoid, conditional only on the stated common-tile anchor
obligation. The target group need not be commutative. -/
theorem rotation_descent_of_zero_anchor_common_tile
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hanchor : ∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty)
    {G : Type*} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [T2Space G]
    (ρ : ℝ → G) (f : LocalHull (geometry k hk) → G) (hf : Continuous f)
    (hf_equiv : ∀ t T, f (translate (geometry k hk) t T) = ρ t + f T) :
    ∃! d : Solenoid (geometry k hk) → G,
      Continuous d ∧ (∀ T, d (solenoidRealize k hk T) = f T) ∧
        ∀ t z, d (flow (pisotData k hk) t z) = ρ t + d z := by
  let : CompactSpace (LocalHull (geometry k hk)) :=
    Psc.PeriodicPartnerRealizationOnto.localHull_compactSpace
  let : T2Space (Solenoid (geometry k hk)) := solenoid_t2Space _
  exact existsUnique_add_rotation_descent (translate (geometry k hk))
    (flow (pisotData k hk)) (solenoidRealize k hk) (continuous_solenoidRealize k hk)
    (solenoidRealize_surjective k hk) (solenoidRealize_translate k hk)
    (fun _ _ h => same_fibre_proximal_of_zero_anchor_common_tile k hk hV hanchor h)
    ρ f hf hf_equiv

end Psc.ParameterFamilyRotationFactor
