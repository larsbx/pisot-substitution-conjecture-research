import PscVerif.C4FamilyHaarErgodicity
import PscVerif.C4FamilyOpenSynchronization

/-! Open fibre synchronization and Haar ergodicity imply singleton fibres
almost everywhere for the actual ordinary family factor.

Source decision: `docs/c4-family-haar-spectrum-2026-11-21.md`. -/

namespace Psc.C4FamilyHaarSingletonFibres

open Function Filter MeasureTheory Set
open scoped Psc.PeriodicPartnerSolenoidHaar
open Psc.ParameterFamilyTiling (geometry expansion_gt_one)
open Psc.ParameterFamilyRecognizability (inflateH_bijective)
open Psc.ParameterFamilySolenoid (solenoidRealize solenoidRealize_surjective pisotData)
open Psc.PeriodicPartnerHull.LengthSubst
  (Agree agree_iff_window agree_mono agreementData inflateH window_injective)
open Psc.PeriodicPartnerLocalTopology (LocalHull ofExact)
open Psc.PeriodicPartnerRealization (Solenoid shiftS shiftS_bijective shiftHomeomorph
  realize realize_semiconj)
open Psc.PeriodicPartnerSolenoidHaar (haar)

variable (k : ℕ) (hk : 1 ≤ k)

local notation "G" => Solenoid (geometry k hk)
local notation "μₛ" => haar (geometry k hk)
local notation "σ" => shiftS (geometry k hk)
local notation "π" => solenoidRealize k hk

/-- The union of all forward images at depths at least `N`. -/
def forwardTail (W : Set G) (N : ℕ) : Set G := ⋃ n : ℕ, (σ^[N + n]) '' W

theorem isOpen_forwardTail {W : Set G} (hW : IsOpen W) (N : ℕ) :
    IsOpen (forwardTail k hk W N) := by
  have hopen (n : ℕ) : IsOpenMap (σ^[n]) := by
    induction n with
    | zero =>
      intro U hU
      simpa only [iterate_zero, image_id] using hU
    | succ n ih =>
      rw [iterate_succ']
      exact (shiftHomeomorph (geometry k hk)).isOpenMap.comp ih
  exact isOpen_iUnion fun n => hopen (N + n) W hW

/-- Forward tails of every nonempty open set are conull by inflation ergodicity.
One-sided forward invariance suffices for a measure-preserving map. -/
theorem ae_mem_forwardTail {W : Set G} (hW : IsOpen W) (hne : W.Nonempty) (N : ℕ) :
    ∀ᵐ z ∂μₛ, z ∈ forwardTail k hk W N := by
  let A := forwardTail k hk W N
  have hA : IsOpen A := isOpen_forwardTail k hk hW N
  have hpos : 0 < μₛ A := hA.measure_pos μₛ <| (hne.image (σ^[N + 0])).mono
    (subset_iUnion (fun n : ℕ => (σ^[N + n]) '' W) 0)
  have hinv : σ '' A ⊆ A := by
    rintro _ ⟨x, hx, rfl⟩
    rcases mem_iUnion.mp hx with ⟨n, w, hw, rfl⟩
    exact mem_iUnion.mpr ⟨n + 1, w, hw, by rw [Nat.add_succ, iterate_succ_apply']⟩
  have h := (C4FamilyHaarErgodicity.ergodic_shiftS k hk).ae_empty_or_univ_of_image_ae_le
    hA.measurableSet.nullMeasurableSet (Eventually.of_forall hinv)
  rcases h with hnull | hfull
  · exact False.elim (hpos.ne' ((measure_congr hnull).trans measure_empty))
  · filter_upwards [hfull] with z hz
    exact hz.mpr (mem_univ z)

private theorem fibre_agree_of_mem_image {r : ℝ} (hr : 0 < r) {W : Set G}
    (hW : ∀ w ∈ W, ∀ T U : LocalHull (geometry k hk),
      π T = w → π U = w → Agree r T.toHull U.toHull)
    {z : G} {n : ℕ} (hz : z ∈ (σ^[n]) '' W) (T U : LocalHull (geometry k hk))
    (hT : π T = z) (hU : π U = z) :
    Agree ((geometry k hk).β ^ n * r) T.toHull U.toHull := by
  obtain ⟨w, hw, hshift⟩ := hz
  have lift (V : LocalHull (geometry k hk)) (hV : π V = z) :
      ∃ V₀ : LocalHull (geometry k hk), π V₀ = w ∧ inflateH^[n] V₀.toHull = V.toHull := by
    obtain ⟨V₀, h₀⟩ := (inflateH_bijective k hk).2.iterate n V.toHull
    refine ⟨ofExact (geometry k hk) V₀, (shiftS_bijective (geometry k hk)).1.iterate n ?_, h₀⟩
    change σ^[n] (realize (pisotData k hk) (inflateH_bijective k hk) V₀) = σ^[n] w
    rw [hshift, ← (realize_semiconj (pisotData k hk) (inflateH_bijective k hk)).iterate_right n,
      h₀]
    exact hV
  obtain ⟨T₀, hT₀, heqT⟩ := lift T hT
  obtain ⟨U₀, hU₀, heqU⟩ := lift U hU
  have h := (agreementData (S := geometry k hk)).agreement_iterate (geometry k hk).β_pos hr
    (hW w hw T₀ U₀ hT₀ hU₀) n
  change Agree ((geometry k hk).β ^ n * r) (inflateH^[n] T₀.toHull) (inflateH^[n] U₀.toHull) at h
  rwa [heqT, heqU] at h

/-- A conull Gδ set of full-history solenoid points has exactly one ordinary
legal tiling above each point. The radius is expanded by actual inflation. -/
theorem exists_conull_singleton_fibres (hk₂ : 2 ≤ k) :
    ∃ A : Set G, IsGδ A ∧ (∀ᵐ z ∂μₛ, z ∈ A) ∧
      ∀ z ∈ A, ∃! T : LocalHull (geometry k hk), π T = z := by
  obtain ⟨r, hr, W, hWopen, hWne, hW⟩ :=
    C4FamilyOpenSynchronization.exists_open_common_window k hk hk₂
  refine ⟨⋂ N, forwardTail k hk W N, IsGδ.iInter_of_isOpen (isOpen_forwardTail k hk hWopen),
    ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr (ae_mem_forwardTail k hk hWopen hWne)] with z hz
    exact mem_iInter.mpr hz
  · intro z hz
    obtain ⟨T, hT⟩ := solenoidRealize_surjective k hk z
    refine ⟨T, hT, fun U hU => LocalHull.ext (window_injective (funext fun m => ?_))⟩
    have hβ := expansion_gt_one k hk
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((m : ℝ) / r) hβ
    rcases mem_iUnion.mp (mem_iInter.mp hz N) with ⟨n, hn⟩
    have hscale : (m : ℝ) ≤ (geometry k hk).β ^ (N + n) * r :=
      ((div_lt_iff₀ hr).mp (hN.trans_le (pow_le_pow_right₀ hβ.le (Nat.le_add_right N n)))).le
    exact agree_iff_window.mp (agree_mono (fibre_agree_of_mem_image k hk hr hW hn U T hU hT) hscale)

/-- Haar-almost every point of the actual solenoid has a singleton fibre. -/
theorem ae_singleton_fibre (hk₂ : 2 ≤ k) :
    ∀ᵐ z ∂μₛ, ∃! T : LocalHull (geometry k hk), π T = z := by
  obtain ⟨A, _, hA, hsingle⟩ := exists_conull_singleton_fibres k hk hk₂
  exact hA.mono hsingle

end Psc.C4FamilyHaarSingletonFibres
