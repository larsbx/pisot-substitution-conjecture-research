import PscVerif.C4ParameterFamilyRecognizability
import PscVerif.PeriodicPartnerRealizationFinite
import PscVerif.PeriodicPartnerRealizationOnto
import PscVerif.PeriodicPartnerSpectral

/-!
# Geometric realization of the literal σₖ tiling flow

The descent and the stable contraction are derived for the same substitution
and Perron-length ordinary hull used in the legal-patch coincidence theorem.
-/

namespace Psc.ParameterFamilySolenoid

open Function Matrix Polynomial Set Psc.ParameterFamilyTiling Psc.ParameterFamilyPisot
open Psc.ParameterFamilyRecognizability
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerSpectral
open Psc.PeriodicPartnerHull.LengthSubst (inflateH Agree shift)
open Psc.PeriodicPartnerLegalCoincidence (originPatch)
open Psc.PeriodicPartnerHull (LengthSubst)
open Psc.PeriodicPartnerLocalTopology Psc.PeriodicPartnerLocalRealization

variable (k : ℕ) (hk : 1 ≤ k)

theorem mat_eq : mat (geometry k hk) = (incidenceQ k).map (algebraMap ℚ ℝ) := by
  ext a b
  simp [mat, incidenceQ, Psc.Incidence.inc_apply, Matrix.map_apply]

theorem charpoly_map :
    (mat (geometry k hk)).charpoly = (incidenceQ k).charpoly.map (algebraMap ℚ ℝ) := by
  rw [mat_eq, Matrix.charpoly_map]

/-- The strict Pisot spectral input comes from the actual family's rational
incidence characteristic polynomial. -/
noncomputable def spectral : SpectralPisot (geometry k hk) :=
  SpectralPisot.ofIrreducible (incidenceQ k).charpoly (irreducible k hk) (charpoly_map k hk)
    fun z hz hne => by
      rw [charpoly_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ ℝ ℂ,
        Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hz
      exact (expansion_pisot k hk).2 z hz hne

/-- The derived stable-space contraction and normalized unstable eigenvector. -/
noncomputable def pisotData : PisotData (geometry k hk) :=
  (spectral k hk).toPisotData

/-- The ordinary legal hull's full compatible-history geometric realization. -/
noncomputable def solenoidRealize : LocalHull (geometry k hk) → Solenoid (geometry k hk) :=
  realizeLocal (pisotData k hk) (inflateH_bijective k hk)

theorem continuous_solenoidRealize : Continuous (solenoidRealize k hk) :=
  Psc.PeriodicPartnerRealizationContinuity.continuous_realizeLocal _ _ (expansion_gt_one k hk)

theorem solenoidRealize_inflate (T : LocalHull (geometry k hk)) :
    solenoidRealize k hk (inflate (geometry k hk) T) =
      shiftS (geometry k hk) (solenoidRealize k hk T) :=
  realizeLocal_inflate _ _ T

theorem solenoidRealize_translate (t : ℝ) (T : LocalHull (geometry k hk)) :
    solenoidRealize k hk (translate (geometry k hk) t T) =
      flow (pisotData k hk) t (solenoidRealize k hk T) :=
  realizeLocal_translate _ _ (expansion_gt_one k hk) t T

/-- The legal seam tiling constructs a preimage of the zero history. -/
theorem fixed_tiling_over_zero :
    ∃ T : (geometry k hk).Hull, inflateH^[2] T = T ∧
      realize (pisotData k hk) (inflateH_bijective k hk) T = 0 := by
  obtain ⟨T, hleft, _, hT⟩ := fixed_hull_tiling k hk
  refine ⟨T, hT, realize_r4 (pisotData k hk) (inflateH_bijective k hk) (b := 1) ?_ ?_⟩
  · exact ⟨2, by decide, hT⟩
  · exact (show (1, 0 - (geometry k hk).ℓ 1) ∈ T.1 by simpa using hleft)

theorem solenoidRealize_surjective : Surjective (solenoidRealize k hk) := by
  apply Psc.PeriodicPartnerRealizationOnto.realizeLocal_surjective _ (expansion_gt_one k hk)
  obtain ⟨T, _, hz⟩ := fixed_tiling_over_zero k hk
  exact ⟨ofExact (geometry k hk) T, hz⟩

theorem solenoidRealize_finite_fibres (z : Solenoid (geometry k hk)) :
    {T | solenoidRealize k hk T = z}.Finite :=
  Psc.PeriodicPartnerRealizationFinite.realizeLocal_finite_fibres _ _ (expansion_gt_one k hk) z

/-- Every tiling above the zero history is periodic under inflation. -/
theorem periodic_of_realize_zero {T : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0) :
    ∃ n > 0, inflateH^[n] T = T := by
  have hfinite := Psc.PeriodicPartnerRealizationFinite.realize_finite_fibres
    (pisotData k hk) (inflateH_bijective k hk) (expansion_gt_one k hk) 0
  obtain ⟨n, hn, _, hperiod⟩ := Psc.PeriodicPartner.periodic_lift_of_finite_fibre
    _ _ _ (inflateH_bijective k hk).1 (realize_semiconj _ _) hfinite (by decide : 0 < 1)
    (by simpa using shiftS_zero (geometry k hk)) hT
  exact ⟨n, hn, hperiod⟩

/-- Each ordinary legal tiling has a dense translation orbit. -/
theorem denseRange_translate (T : LocalHull (geometry k hk)) :
    DenseRange (fun t : ℝ => translate (geometry k hk) t T) := by
  let S := geometry k hk
  have hExact : DenseRange (fun t : ℝ => LengthSubst.translate t T.toHull) := by
    intro U
    rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨n, hn⟩ := (S.mem_nhds_iff_exists_agreement_subset U W).mp hW
    obtain ⟨t, ht⟩ :=
      S.window_occurs (expansion_gt_one k hk).le (every_letter_in_square k hk) T.toHull U n
    exact ⟨_, hn ht, mem_range_self t⟩
  have hOnto : Surjective (ofExact S) := fun U => ⟨U.toHull, by cases U; rfl⟩
  exact hOnto.denseRange.comp hExact (continuous_ofExact S)

/-- Any continuous realization into the same solenoid with the same time
normalization has exactly the fibres of the constructed map. -/
theorem solenoidRealize_fibres_eq_of_equivariant
    (g : LocalHull (geometry k hk) → Solenoid (geometry k hk)) (hg : Continuous g)
    (hflow : ∀ t T, g (translate (geometry k hk) t T) = flow (pisotData k hk) t (g T))
    (T U : LocalHull (geometry k hk)) :
    g T = g U ↔ solenoidRealize k hk T = solenoidRealize k hk U := by
  let : T2Space (Solenoid (geometry k hk)) := solenoid_t2Space _
  let d := g T - solenoidRealize k hk T
  have hc : IsClosed {V | g V = solenoidRealize k hk V + d} :=
    isClosed_eq hg ((continuous_solenoidRealize k hk).add continuous_const)
  have horbit (t : ℝ) : g (translate (geometry k hk) t T) =
      solenoidRealize k hk (translate (geometry k hk) t T) + d := by
    rw [hflow, solenoidRealize_translate]
    unfold flow
    dsimp [d]
    abel
  have hh (V : LocalHull (geometry k hk)) :
      g V = solenoidRealize k hk V + d :=
    hc.closure_subset_iff.mpr (by rintro _ ⟨t, rfl⟩; exact horbit t)
      (denseRange_translate k hk T V)
  rw [hh T, hh U, add_right_cancel_iff]

private theorem originPatch_eq_of_agree {S : LengthSubst (Fin 3)} {R : ℝ} (hR : 0 < R)
    {T U : S.Hull} (h : Agree R T U) : originPatch S T.1 = originPatch S U.1 := by
  ext p
  change (p ∈ T.1 ∧ 0 ∈ Icc p.2 (p.2 + S.ℓ p.1)) ↔
    (p ∈ U.1 ∧ 0 ∈ Icc p.2 (p.2 + S.ℓ p.1))
  apply and_congr_left
  intro hp
  exact h p ⟨max (-R / 2) p.2,
    ⟨le_max_right _ _, max_lt (by linarith [hp.2]) (lt_add_of_pos_right _ (S.ℓ_pos p.1))⟩,
    ⟨(by linarith : -R < -R / 2).trans_le (le_max_left _ _),
      max_lt (by linarith) (hp.1.trans_lt hR)⟩⟩

/-- Exact common-shift witnesses at one positive radius for a pair over zero
suffice for a common tile in that pair. -/
theorem common_tile_of_zero_fibre_witnesses (hk₂ : 2 ≤ k)
    {T U T' U' : (geometry k hk).Hull} {t : ℝ}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0)
    (h₁ : Agree 1 T T') (h₂ : Agree 1 U U')
    (h₃ : Agree 1 (LengthSubst.translate t T') (LengthSubst.translate t U')) :
    (T.1 ∩ U.1).Nonempty := by
  obtain ⟨m, hm, hTm⟩ := periodic_of_realize_zero k hk hT
  obtain ⟨n, hn, hUn⟩ := periodic_of_realize_zero k hk hU
  exact periodic_common_tile_of_origin_witnesses k hk₂ hm hn hTm hUn
    (originPatch_eq_of_agree (by norm_num) h₁)
    (originPatch_eq_of_agree (by norm_num) h₂)
    (originPatch_eq_of_agree (by norm_num) h₃)

end Psc.ParameterFamilySolenoid
