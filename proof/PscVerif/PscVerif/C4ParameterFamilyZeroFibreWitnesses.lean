import PscVerif.C4ParameterFamilySolenoid
import PscVerif.PeriodicPartnerProximal
import PscVerif.PeriodicPartnerPeriodicZero

/-!
# Exact witness interfaces at the zero solenoid fibre

For the literal family at `k ≥ 2`, the three radius-one witnesses, the
published three closed-origin witnesses, a common tile, and arbitrary exact
common-translation windows are equivalent on a zero-fibre pair. These are
proved equivalences, not a proof that an arbitrary zero-fibre pair satisfies
one of them. The remaining existence assertion is reduced further to pairs
with one fixed zero-fibre anchor.

Source decision: `docs/c4-zero-fibre-witness-stop-go-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerProximal

open Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerLegalCoincidence (originPatch)

variable {α : Type*} (S : LengthSubst α)

/-- The exact three agreements, all using one common translation. -/
def WindowWitnesses (R : ℝ) (T U : S.Hull) : Prop :=
  ∃ (T' U' : S.Hull) (t : ℝ),
    Agree R T T' ∧ Agree R U U' ∧ Agree R (translate t T') (translate t U')

/-- The closed-origin interface consumed by the legal-patch transfer theorem. -/
def ClosedOriginWitnesses (T U : S.Hull) : Prop :=
  ∃ (T' U' : S.Hull) (t : ℝ),
    originPatch S T.1 = originPatch S T'.1 ∧
    originPatch S U.1 = originPatch S U'.1 ∧
    originPatch S (shift t T'.1) = originPatch S (shift t U'.1)

/-- Exact strong regional proximality in the repository's open-window convention. -/
def StronglyRegionallyProximal (T U : S.Hull) : Prop :=
  ∀ R : ℝ, 0 < R → WindowWitnesses S R T U

theorem closedOriginWitnesses_of_windowWitnesses {R : ℝ} (hR : 0 < R)
    {T U : S.Hull} (h : WindowWitnesses S R T U) : ClosedOriginWitnesses S T U := by
  obtain ⟨T', U', t, h₁, h₂, h₃⟩ := h
  exact ⟨T', U', t, originPatch_eq_of_agree S hR h₁,
    originPatch_eq_of_agree S hR h₂, originPatch_eq_of_agree S hR h₃⟩

/-- An exact proximal pair can use the original tilings as its regional witnesses. -/
theorem stronglyRegionallyProximal_of_exactProximal {T U : S.Hull}
    (h : ExactProximal S T U) : StronglyRegionallyProximal S T U := by
  intro R hR
  obtain ⟨t, ht⟩ := h R hR
  exact ⟨T, U, t, Agree.refl R T, Agree.refl R U, ht⟩

end Psc.PeriodicPartnerProximal

namespace Psc.ParameterFamilyZeroFibreWitnesses

open Function Set Psc.ParameterFamilyTiling Psc.ParameterFamilyPisot
open Psc.ParameterFamilyRecognizability Psc.ParameterFamilySolenoid
open Psc.PeriodicPartnerProximal Psc.PeriodicPartnerEventualCoincidence
open Psc.PeriodicPartnerHull.LengthSubst (inflateH Agree)
open Psc.PeriodicPartnerRealization (realize origin lattice)
open Psc.PeriodicPartnerPeriodicZero
open Matrix

variable (k : ℕ) (hk : 1 ≤ k)

/-- The concrete family's zero fibre is exactly its inflation-periodic
tilings with origin starts in the integer length lattice. Interior origins
are retained; this is an equivalence, not an origin-vertex restriction. -/
theorem realize_zero_iff_periodic_lattice_origin {T : (geometry k hk).Hull} :
    realize (pisotData k hk) (inflateH_bijective k hk) T = 0 ↔
      ∃ n > 0, inflateH^[n] T = T ∧
        ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧
          (origin T).2 = -((geometry k hk).ℓ ⬝ᵥ v) := by
  constructor
  · intro h
    obtain ⟨n, hn, hper⟩ := periodic_of_realize_zero k hk h
    exact ⟨n, hn, hper, lattice_origin_of_realize_zero _ _ h⟩
  · rintro ⟨n, hn, hper, v, hv, horigin⟩
    exact realize_zero_of_periodic_lattice_origin _ _ hn hper hv horigin

/-- The weaker published origin interface suffices, without adding a new
periodicity premise: both periods are derived from the zero history. -/
theorem common_tile_of_closedOriginWitnesses (hk₂ : 2 ≤ k)
    {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0)
    (h : ClosedOriginWitnesses (geometry k hk) T U) : (T.1 ∩ U.1).Nonempty := by
  obtain ⟨m, hm, hTm⟩ := periodic_of_realize_zero k hk hT
  obtain ⟨n, hn, hUn⟩ := periodic_of_realize_zero k hk hU
  obtain ⟨T', U', t, h₁, h₂, h₃⟩ := h
  exact periodic_common_tile_of_origin_witnesses k hk₂ hm hn hTm hUn h₁ h₂ h₃

/-- A shared tile is equivalent to arbitrarily large exact common-shift
windows for a pair over zero. This reuses the derived inflation periods. -/
theorem exactProximal_iff_common_tile
    {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    ExactProximal (geometry k hk) T U ↔ (T.1 ∩ U.1).Nonempty := by
  obtain ⟨m, hm, hTm⟩ := periodic_of_realize_zero k hk hT
  obtain ⟨n, hn, hUn⟩ := periodic_of_realize_zero k hk hU
  exact exactProximal_iff_common_tile_of_periodic _ (expansion_gt_one k hk) hm hn hTm hUn

/-- Any positive radius gives precisely the same unresolved common-tile
condition on a zero-fibre pair. Radius one is not an additional hypothesis. -/
theorem windowWitnesses_iff_common_tile (hk₂ : 2 ≤ k) {R : ℝ} (hR : 0 < R)
    {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    WindowWitnesses (geometry k hk) R T U ↔ (T.1 ∩ U.1).Nonempty := by
  constructor
  · intro h
    exact common_tile_of_closedOriginWitnesses k hk hk₂ hT hU
      (closedOriginWitnesses_of_windowWitnesses _ hR h)
  · intro h
    exact stronglyRegionallyProximal_of_exactProximal _
      ((exactProximal_iff_common_tile k hk hT hU).mpr h) R hR

theorem closedOriginWitnesses_iff_common_tile (hk₂ : 2 ≤ k)
    {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    ClosedOriginWitnesses (geometry k hk) T U ↔ (T.1 ∩ U.1).Nonempty := by
  refine ⟨common_tile_of_closedOriginWitnesses k hk hk₂ hT hU, fun h => ?_⟩
  exact closedOriginWitnesses_of_windowWitnesses _ (by norm_num : (0 : ℝ) < 1)
    ((windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hT hU).mpr h)

theorem stronglyRegionallyProximal_iff_common_tile (hk₂ : 2 ≤ k)
    {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    StronglyRegionallyProximal (geometry k hk) T U ↔ (T.1 ∩ U.1).Nonempty := by
  constructor
  · intro h
    exact (windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hT hU).mp (h 1 (by norm_num))
  · intro h
    exact stronglyRegionallyProximal_of_exactProximal _
      ((exactProximal_iff_common_tile k hk hT hU).mpr h)

/-- On the zero fibre, common-tile existence is transitive. The two common
tiles need not be the same tile or lie at the same position. Legal-patch
density and transitivity of eventual coincidence supply the bridge. -/
theorem common_tile_trans (hk₂ : 2 ≤ k)
    {T V U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0)
    (hTV : (T.1 ∩ V.1).Nonempty) (hVU : (V.1 ∩ U.1).Nonempty) :
    (T.1 ∩ U.1).Nonempty := by
  let S := geometry k hk
  have hd₁ : Dense (eventual S T.1 V.1) := hull_dense_eventual k hk₂ hTV
  have hd₂ : Dense (eventual S V.1 U.1) := hull_dense_eventual k hk₂ hVU
  obtain ⟨x, hx₁, hx₂⟩ :=
    (hd₁.inter_of_isOpen_left hd₂ (eventual_open S _ _)).nonempty
  have he : (eventual S T.1 U.1).Nonempty :=
    ⟨x, eventual_trans S V.2.1 hx₁ hx₂⟩
  obtain ⟨m, hm, hTm⟩ := periodic_of_realize_zero k hk hT
  obtain ⟨n, hn, hUn⟩ := periodic_of_realize_zero k hk hU
  have hTm' : inflateH^[m * n] T = T := by
    rw [iterate_mul]
    exact IsFixedPt.iterate hTm n
  have hUn' : inflateH^[m * n] U = U := by
    rw [Nat.mul_comm, iterate_mul]
    exact IsFixedPt.iterate hUn m
  apply Psc.PeriodicPartnerLegalCoincidence.common_tile_of_periodic_eventual S
    (Nat.mul_pos hm hn) ?_ ?_ he
  · simpa only [Psc.PeriodicPartnerEvenTails.hull_iterate_val] using congrArg Subtype.val hTm'
  · simpa only [Psc.PeriodicPartnerEvenTails.hull_iterate_val] using congrArg Subtype.val hUn'

/-- All pairwise radius-one witnesses reduce to witnesses between one
chosen zero-fibre tiling and every other zero-fibre member. Neither side
is asserted by this equivalence. -/
theorem all_pair_witnesses_iff_anchor (hk₂ : 2 ≤ k)
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0) :
    (∀ T U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
      WindowWitnesses (geometry k hk) 1 T U) ↔
    (∀ U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
      WindowWitnesses (geometry k hk) 1 V U) := by
  constructor
  · intro h U hU
    exact h V U hV hU
  · intro h T U hT hU
    have hVT := (windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hV hT).mp (h T hT)
    have hVU := (windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hV hU).mp (h U hU)
    have hTV : (T.1 ∩ V.1).Nonempty := by simpa only [inter_comm] using hVT
    exact (windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hT hU).mpr
      (common_tile_trans k hk hk₂ hT hU hTV hVU)

/-- An exact arithmetic-geometric form of the remaining obligation. It is
equivalent to the requested all-pairs witness statement, with no stronger
geometric premise inserted. The right side is still an existence target. -/
theorem all_pair_witnesses_iff_periodic_lattice_anchor (hk₂ : 2 ≤ k)
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0) :
    (∀ T U : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 →
      realize (pisotData k hk) (inflateH_bijective k hk) U = 0 →
      WindowWitnesses (geometry k hk) 1 T U) ↔
    (∀ U : (geometry k hk).Hull,
      (∃ n > 0, inflateH^[n] U = U ∧
        ∃ v : Fin 3 → ℝ, v ∈ lattice (Fin 3) ∧
          (origin U).2 = -((geometry k hk).ℓ ⬝ᵥ v)) →
      (V.1 ∩ U.1).Nonempty) := by
  rw [all_pair_witnesses_iff_anchor k hk hk₂ hV]
  constructor
  · intro h U hU
    have hz := (realize_zero_iff_periodic_lattice_origin k hk).mpr hU
    exact (windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hV hz).mp (h U hz)
  · intro h U hz
    exact (windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hV hz).mpr
      (h U ((realize_zero_iff_periodic_lattice_origin k hk).mp hz))

end Psc.ParameterFamilyZeroFibreWitnesses
