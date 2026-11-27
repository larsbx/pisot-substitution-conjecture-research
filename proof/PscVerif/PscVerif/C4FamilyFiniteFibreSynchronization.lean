import PscVerif.C4FamilyFiniteZeroFibre
import PscVerif.PeriodicPartnerFiniteCoincidence

/-!
# Finite simultaneous synchronization of each actual family fibre

For every `k >= 2`, the actual full solenoid fibre is finite and every pair
in it is densely eventually coincident by finite automaton replay. The finite
coincidence lemma therefore provides one inflation depth and one labelled
tile shared by the whole fibre. For any prescribed positive radius, one depth
and one translation give exact agreement for every pair in that fibre.

These are finite witnesses for each fibre. The depth may depend on its base
point and on the radius. This module does not assert an open neighborhood of
synchronized fibres, Haar-almost-everywhere injectivity, or an uninflated
common tile in every original fibre.
Source decision: `docs/c4-finite-fibre-obligations-2026-11-21.md`.
-/

namespace Psc.C4FamilyFiniteFibreSynchronization

open Function Set
open Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyRecognizability
open Psc.C4FamilyFiniteZeroFibre Psc.PeriodicPartnerFiniteCoincidence
open Psc.PeriodicPartnerEventualCoincidence
open Psc.PeriodicPartnerHull.LengthSubst
  (inflateH Agree translate translate_translate translate_zero)
open Psc.PeriodicPartnerLocalTopology (LocalHull ofExact)
open Psc.PeriodicPartnerRealization
  (Solenoid realize flow shiftS shiftS_bijective realize_semiconj realize_translate)

variable (k : ℕ) (hk : 1 ≤ k)

/-- One common finite depth and one labelled tile serve every member of
the specified full solenoid fibre simultaneously. -/
theorem fibre_common_tile_after_inflation (hk₂ : 2 ≤ k)
    (z : Solenoid (geometry k hk)) :
    ∃ n : ℕ, ∃ q : Fin 3 × ℝ, ∀ T : LocalHull (geometry k hk),
      solenoidRealize k hk T = z → q ∈ (inflateH^[n] T.toHull).1 := by
  classical
  let F : Set (LocalHull (geometry k hk)) := {T | solenoidRealize k hk T = z}
  let : Fintype F := (solenoidRealize_finite_fibres k hk z).fintype
  obtain ⟨T₀, hT₀⟩ := solenoidRealize_surjective k hk z
  let i₀ : F := ⟨T₀, hT₀⟩
  have hd (i : F) :
      Dense (eventual (geometry k hk) i₀.1.toHull.1 i.1.toHull.1) :=
    same_fibre_dense_eventual k hk hk₂ (i₀.2.trans i.2.symm)
  obtain ⟨n, q, hq⟩ := common_tile_of_finite_dense_eventual (geometry k hk)
    (fun i : F => i.1.toHull) i₀ hd
  exact ⟨n, q, fun T hT => hq ⟨T, hT⟩⟩

/-- For a prescribed radius, a single finite inflation depth and common
translation synchronize the whole fibre. The witnesses precede both tiling
quantifiers; no pair-dependent depth or translation is substituted here. -/
theorem fibre_common_window_after_inflation (hk₂ : 2 ≤ k)
    (z : Solenoid (geometry k hk)) {R : ℝ} (hR : 0 < R) :
    ∃ n : ℕ, ∃ t : ℝ, ∀ T U : LocalHull (geometry k hk),
      solenoidRealize k hk T = z → solenoidRealize k hk U = z →
      Agree R (translate t (inflateH^[n] T.toHull))
        (translate t (inflateH^[n] U.toHull)) := by
  classical
  let F : Set (LocalHull (geometry k hk)) := {T | solenoidRealize k hk T = z}
  let : Fintype F := (solenoidRealize_finite_fibres k hk z).fintype
  obtain ⟨T₀, hT₀⟩ := solenoidRealize_surjective k hk z
  let i₀ : F := ⟨T₀, hT₀⟩
  have hd (i : F) :
      Dense (eventual (geometry k hk) i₀.1.toHull.1 i.1.toHull.1) :=
    same_fibre_dense_eventual k hk hk₂ (i₀.2.trans i.2.symm)
  obtain ⟨n, t, hwindow⟩ := common_window_of_finite_dense_eventual (geometry k hk)
    (expansion_gt_one k hk) (fun i : F => i.1.toHull) i₀ hd hR
  exact ⟨n, t, fun T U hT hU => hwindow ⟨T, hT⟩ ⟨U, hU⟩⟩

/-- Inflation and translation carry an entire fibre onto the entire fibre
over the transformed base point. Thus the shared window belongs to that
actual target fibre, not only to an unspecified subset of its preimages. -/
theorem fibre_common_window_at_shifted_base (hk₂ : 2 ≤ k)
    (z : Solenoid (geometry k hk)) {R : ℝ} (hR : 0 < R) :
    ∃ n : ℕ, ∃ t : ℝ, ∀ T U : LocalHull (geometry k hk),
      solenoidRealize k hk T = flow (pisotData k hk) t ((shiftS (geometry k hk))^[n] z) →
      solenoidRealize k hk U = flow (pisotData k hk) t ((shiftS (geometry k hk))^[n] z) →
      Agree R T.toHull U.toHull := by
  obtain ⟨n, t, hwindow⟩ := fibre_common_window_after_inflation k hk hk₂ z hR
  let z' := flow (pisotData k hk) t ((shiftS (geometry k hk))^[n] z)
  have hlift (T : LocalHull (geometry k hk)) (hT : solenoidRealize k hk T = z') :
      ∃ V : LocalHull (geometry k hk), solenoidRealize k hk V = z ∧
        translate t (inflateH^[n] V.toHull) = T.toHull := by
    obtain ⟨V, hV⟩ := (inflateH_bijective k hk).2.iterate n (translate (-t) T.toHull)
    have hVT : translate t (inflateH^[n] V) = T.toHull := by
      rw [hV, translate_translate, add_neg_cancel, translate_zero]
    have hbase : flow (pisotData k hk) t
        ((shiftS (geometry k hk))^[n]
          (realize (pisotData k hk) (inflateH_bijective k hk) V)) = z' := by
      rw [← (realize_semiconj (pisotData k hk) (inflateH_bijective k hk)).iterate_right n V,
        ← realize_translate (pisotData k hk) (inflateH_bijective k hk)
          (expansion_gt_one k hk), hVT]
      exact hT
    have hVz : realize (pisotData k hk) (inflateH_bijective k hk) V = z := by
      apply (shiftS_bijective (geometry k hk)).1.iterate n
      exact add_right_cancel hbase
    exact ⟨ofExact (geometry k hk) V, hVz, hVT⟩
  refine ⟨n, t, fun T U hT hU => ?_⟩
  obtain ⟨V, hV, hVT⟩ := hlift T hT
  obtain ⟨W, hW, hWU⟩ := hlift U hU
  simpa only [hVT, hWU] using hwindow V W hV hW

/-- Every prescribed positive radius is shared by all tilings in some
actual nonempty solenoid fibre. This does not assert one fibre for all radii
or an open neighborhood of such fibres. -/
theorem exists_fibre_common_window (hk₂ : 2 ≤ k) {R : ℝ} (hR : 0 < R) :
    ∃ z : Solenoid (geometry k hk),
      (∃ T : LocalHull (geometry k hk), solenoidRealize k hk T = z) ∧
      ∀ T U : LocalHull (geometry k hk),
        solenoidRealize k hk T = z → solenoidRealize k hk U = z →
        Agree R T.toHull U.toHull := by
  obtain ⟨n, t, hwindow⟩ := fibre_common_window_at_shifted_base k hk hk₂ 0 hR
  let z := flow (pisotData k hk) t ((shiftS (geometry k hk))^[n] 0)
  exact ⟨z, solenoidRealize_surjective k hk z, hwindow⟩

end Psc.C4FamilyFiniteFibreSynchronization
