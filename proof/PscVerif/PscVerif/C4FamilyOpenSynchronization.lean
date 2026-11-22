import PscVerif.C4FamilyFiniteFibreSynchronization
import PscVerif.PeriodicPartnerOriginSeparation

/-!
# An open set of synchronized actual solenoid fibres

Finite simultaneous coincidence first produces one fibre sharing a tile.
Centering that tile puts the origin strictly inside it. In nearby local
patches the tile persists up to a small translation. The finite separation
of equal-torus origin displacements forces these small translations to agree
within each fibre. The complement of the closed image of the remaining
source tilings is then an open base neighborhood of synchronized fibres.

The closed-image step reuses the already proved compact ordinary hull and
continuous factor map. No new sequence-limit construction occurs. The result
supplies a nonempty open seed, not a Haar measure or ergodicity theorem.
Source decision: `docs/c4-finite-fibre-obligations-2026-11-21.md`.
-/

namespace Psc.C4FamilyOpenSynchronization

open Function Set
open Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyRecognizability
open Psc.C4FamilyFiniteFibreSynchronization Psc.PeriodicPartnerOriginSeparation
open Psc.PeriodicPartnerHull.LengthSubst (Agree translate)
open Psc.PeriodicPartnerLocalTopology (LocalHull patch isOpen_patch)
open Psc.PeriodicPartnerRealization (Solenoid origin tileAt_spec tileAt_eq flow solenoid_t2Space)

variable (k : ℕ) (hk : 1 ≤ k)

/-- Some actual fibre has one labelled tile centered at zero in every
preimage. Centering is a common translation of the entire fibre. -/
theorem exists_centered_tile_fibre (hk₂ : 2 ≤ k) :
    ∃ z : Solenoid (geometry k hk), ∃ a : Fin 3,
      ∀ T : LocalHull (geometry k hk), solenoidRealize k hk T = z →
        (a, -((geometry k hk).ℓ a / 2)) ∈ T.toHull.1 := by
  obtain ⟨z, ⟨T₀, hT₀⟩, hwindow⟩ := exists_fibre_common_window k hk hk₂
    (R := 1) (by norm_num)
  let q := origin T₀.toHull
  have hq (T : LocalHull (geometry k hk)) (hT : solenoidRealize k hk T = z) :
      q ∈ T.toHull.1 := by
    exact (hwindow T₀ T hT₀ hT q
      ⟨0, (tileAt_spec T₀.toHull 0).2, by constructor <;> norm_num⟩).mp
      (tileAt_spec T₀.toHull 0).1
  let c := q.2 + (geometry k hk).ℓ q.1 / 2
  refine ⟨flow (pisotData k hk) c z, q.1, fun T hT => ?_⟩
  let V := Psc.PeriodicPartnerLocalTopology.translate (geometry k hk) (-c) T
  have hVT : Psc.PeriodicPartnerLocalTopology.translate (geometry k hk) c V = T := by
    simp only [V, Psc.PeriodicPartnerLocalTopology.translate_translate, add_neg_cancel,
      Psc.PeriodicPartnerLocalTopology.translate_zero]
  have hVz : solenoidRealize k hk V = z := by
    have hbase : flow (pisotData k hk) c (solenoidRealize k hk V) =
        flow (pisotData k hk) c z := by
      rw [← solenoidRealize_translate k hk c V, hVT]
      exact hT
    exact add_right_cancel hbase
  have hcommon := hq V hVz
  change (q.1, q.2 + -c) ∈ T.toHull.1 at hcommon
  have hstart : q.2 + -c = -((geometry k hk).ℓ q.1 / 2) := by
    dsimp only [c]
    ring
  simpa only [hstart] using hcommon

/-- A sufficiently small ordinary patch neighborhood preserves a centered
tile, with its actual origin shifted by the patch's alignment parameter. -/
theorem origin_of_centered_patch (a : Fin 3) {δ : ℝ}
    (hδ : δ ≤ (geometry k hk).ℓ a / 4)
    {T U : LocalHull (geometry k hk)}
    (hq : (a, -((geometry k hk).ℓ a / 2)) ∈ T.toHull.1)
    (hU : U ∈ patch (geometry k hk) T δ 1) :
    ∃ s : ℝ, |s| < δ ∧
      origin U.toHull = (a, -((geometry k hk).ℓ a / 2) - s) := by
  obtain ⟨s, hs, hA⟩ := hU
  have hq₀ : (0 : ℝ) ∈ (geometry k hk).supp (a, -((geometry k hk).ℓ a / 2)) := by
    change -((geometry k hk).ℓ a / 2) ≤ 0 ∧
      0 < -((geometry k hk).ℓ a / 2) + (geometry k hk).ℓ a
    constructor <;> linarith [(geometry k hk).ℓ_pos a]
  have hqU : (a, -((geometry k hk).ℓ a / 2) - s) ∈ U.toHull.1 := by
    have h := (hA (a, -((geometry k hk).ℓ a / 2))
      ⟨0, hq₀, by constructor <;> norm_num⟩).mp hq
    exact h
  have hsupp : (0 : ℝ) ∈ (geometry k hk).supp
      (a, -((geometry k hk).ℓ a / 2) - s) := by
    change -((geometry k hk).ℓ a / 2) - s ≤ 0 ∧
      0 < -((geometry k hk).ℓ a / 2) - s + (geometry k hk).ℓ a
    constructor <;> linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2,
      (geometry k hk).ℓ_pos a]
  exact ⟨s, hs, tileAt_eq hqU hsupp⟩

/-- A fibre sharing a centered tile has an open base neighborhood whose
fibres all agree on one fixed positive window. The neighborhood comes from
the existing compact-to-Hausdorff factor map and the finite origin gap. -/
theorem open_common_window_of_centered_tile_fibre
    (z : Solenoid (geometry k hk)) (a : Fin 3)
    (hseed : ∀ T : LocalHull (geometry k hk), solenoidRealize k hk T = z →
      (a, -((geometry k hk).ℓ a / 2)) ∈ T.toHull.1) :
    ∃ W : Set (Solenoid (geometry k hk)), IsOpen W ∧ z ∈ W ∧
      ∀ w ∈ W, ∀ T U : LocalHull (geometry k hk),
        solenoidRealize k hk T = w → solenoidRealize k hk U = w →
        Agree ((geometry k hk).ℓ a / 4) T.toHull U.toHull := by
  let : CompactSpace (LocalHull (geometry k hk)) :=
    Psc.PeriodicPartnerRealizationOnto.localHull_compactSpace
  let : T2Space (Solenoid (geometry k hk)) := solenoid_t2Space _
  obtain ⟨ε, hε, hsep⟩ := exists_origin_separation (pisotData k hk) (inflateH_bijective k hk)
  let δ := min ((geometry k hk).ℓ a / 4) (ε / 4)
  have hδ : 0 < δ := lt_min
    (div_pos ((geometry k hk).ℓ_pos a) (by norm_num)) (div_pos hε (by norm_num))
  have hδℓ : δ ≤ (geometry k hk).ℓ a / 4 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  let O : Set (LocalHull (geometry k hk)) :=
    ⋃ T : LocalHull (geometry k hk), ⋃ (_hT : solenoidRealize k hk T = z),
      patch (geometry k hk) T δ 1
  have hO : IsOpen O := isOpen_iUnion fun T => isOpen_iUnion fun _ => isOpen_patch _ T δ 1
  have hsource (T : LocalHull (geometry k hk)) (hT : solenoidRealize k hk T = z) : T ∈ O := by
    refine mem_iUnion.mpr ⟨T, mem_iUnion.mpr ⟨hT, 0, by simpa using hδ, ?_⟩⟩
    simpa using (Psc.PeriodicPartnerHull.LengthSubst.Agree.refl 1 T.toHull)
  let W := (solenoidRealize k hk '' Oᶜ)ᶜ
  have hW : IsOpen W :=
    ((continuous_solenoidRealize k hk).isClosedMap _ hO.isClosed_compl).isOpen_compl
  have hzW : z ∈ W := by
    rintro ⟨T, hT, hz⟩
    exact hT (hsource T hz)
  refine ⟨W, hW, hzW, fun w hw T U hT hU => ?_⟩
  have hnear (V : LocalHull (geometry k hk)) (hV : solenoidRealize k hk V = w) : V ∈ O := by
    by_contra hn
    exact hw ⟨V, hn, hV⟩
  obtain ⟨T', hT'⟩ := mem_iUnion.mp (hnear T hT)
  obtain ⟨hzT', hpT'⟩ := mem_iUnion.mp hT'
  obtain ⟨U', hU'⟩ := mem_iUnion.mp (hnear U hU)
  obtain ⟨hzU', hpU'⟩ := mem_iUnion.mp hU'
  obtain ⟨s, hs, horiginT⟩ := origin_of_centered_patch k hk a hδℓ (hseed T' hzT') hpT'
  obtain ⟨t, ht, horiginU⟩ := origin_of_centered_patch k hk a hδℓ (hseed U' hzU') hpU'
  have htorus := congrArg (fun v : Solenoid (geometry k hk) => v.1 0) (hT.trans hU.symm)
  have hsmall : |(origin T.toHull).2 - (origin U.toHull).2| < ε := by
    rw [horiginT, horiginU]
    apply abs_lt.mpr
    constructor <;> dsimp only [Prod.snd] <;>
      linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2,
        (abs_lt.mp ht).1, (abs_lt.mp ht).2]
  have hstart := hsep T.toHull U.toHull htorus hsmall
  have hst : s = t := by
    rw [horiginT, horiginU] at hstart
    dsimp only [Prod.snd] at hstart
    linarith
  have hqT := (tileAt_spec T.toHull 0).1
  have hqU := (tileAt_spec U.toHull 0).1
  change origin T.toHull ∈ T.toHull.1 at hqT
  change origin U.toHull ∈ U.toHull.1 at hqU
  rw [horiginT] at hqT
  rw [horiginU, ← hst] at hqU
  rintro p ⟨x, hxp, hx⟩
  have hxq : x ∈ (geometry k hk).supp (a, -((geometry k hk).ℓ a / 2) - s) := by
    change -((geometry k hk).ℓ a / 2) - s ≤ x ∧
      x < -((geometry k hk).ℓ a / 2) - s + (geometry k hk).ℓ a
    constructor <;> linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2, hx.1, hx.2]
  constructor
  · intro hp
    have hpq := (T.toHull.2.1 x).unique ⟨hp, hxp⟩ ⟨hqT, hxq⟩
    exact hpq.symm ▸ hqU
  · intro hp
    have hpq := (U.toHull.2.1 x).unique ⟨hp, hxp⟩ ⟨hqU, hxq⟩
    exact hpq.symm ▸ hqT

/-- The actual solenoid has a nonempty open set on which every fibre
agrees on the same positive-radius window. No measure is assumed or proved. -/
theorem exists_open_common_window (hk₂ : 2 ≤ k) :
    ∃ r : ℝ, 0 < r ∧ ∃ W : Set (Solenoid (geometry k hk)),
      IsOpen W ∧ W.Nonempty ∧
      ∀ w ∈ W, ∀ T U : LocalHull (geometry k hk),
        solenoidRealize k hk T = w → solenoidRealize k hk U = w →
        Agree r T.toHull U.toHull := by
  obtain ⟨z, a, hseed⟩ := exists_centered_tile_fibre k hk hk₂
  obtain ⟨W, hW, hzW, hagree⟩ := open_common_window_of_centered_tile_fibre k hk z a hseed
  exact ⟨(geometry k hk).ℓ a / 4,
    div_pos ((geometry k hk).ℓ_pos a) (by norm_num), W, hW, ⟨z, hzW⟩, hagree⟩

end Psc.C4FamilyOpenSynchronization
