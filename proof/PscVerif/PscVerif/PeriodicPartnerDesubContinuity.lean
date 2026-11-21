/-
# Continuity of desubstitution in the exact hull

For a fixed origin tile in an inflated tiling, there are finitely many possible
parent origin tiles: their labels range over the finite alphabet and their
positions are obtained by subtracting the length of a substitution prefix and
dividing by the expansion factor.  The corresponding parent fibres are compact.

This proves that inflation has compact preimages of the open origin fibres.
Its images of closed sets are therefore closed locally on those fibres, hence
closed globally.  Under the existing bijectivity assumption, the existing
`desub` is consequently continuous.  No continuous-inverse or global hull
compactness premise is added, and recognizability itself is not proved here.

Source decision: `docs/c4-realization-continuity-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerHullCompact

namespace Psc.PeriodicPartnerDesubContinuity

open Function Filter Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerRealization Psc.PeriodicPartnerOriginContinuity
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α}

/-- A finite overapproximation of the possible parent origin tiles of `q`.
Including prefixes that do not actually precede `q` only enlarges this set. -/
noncomputable def parentOrigins (S : LengthSubst α) (q : α × ℝ) : Finset (α × ℝ) := by
  classical
  exact Finset.univ.biUnion fun a =>
    (S.σ a).inits.toFinset.image fun w => (a, (q.2 - (w.map S.ℓ).sum) / S.β)

/-- Every parent origin lies among the finitely many prefix-based candidates. -/
theorem origin_mem_parentOrigins (U : S.Hull) :
    origin U ∈ parentOrigins S (origin (inflateH U)) := by
  classical
  have hc : origin (inflateH U) ∈
      S.place (S.σ (origin U).1) (S.β * (origin U).2) := by
    simpa only [origin, zero_div] using tileAt_inflate U 0
  obtain ⟨w, hw, hpos⟩ := place_prefix hc
  apply Finset.mem_biUnion.mpr
  refine ⟨(origin U).1, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  refine ⟨w, by simpa using hw, ?_⟩
  apply Prod.ext
  · rfl
  · apply (div_eq_iff S.β_pos.ne').mpr
    nlinarith

/-- Preimages of exact origin fibres are compact, without recognizability. -/
theorem isCompact_inflate_preimage_origin_fibre (q : α × ℝ) :
    IsCompact {U : S.Hull | origin (inflateH U) = q} := by
  classical
  have hK : IsCompact (⋃ p ∈ parentOrigins S q, {U : S.Hull | origin U = p}) :=
    (parentOrigins S q).isCompact_biUnion fun p _ =>
      Psc.PeriodicPartnerHullCompact.isCompact_origin_fibre p
  apply hK.of_isClosed_subset ((isClosed_origin_fibre q).preimage continuous_inflateH)
  intro U hU
  change origin (inflateH U) = q at hU
  apply mem_iUnion.mpr
  refine ⟨origin U, mem_iUnion.mpr ⟨?_, rfl⟩⟩
  simpa only [hU] using origin_mem_parentOrigins U

/-- Inflation is closed in the exact topology, as can be checked on its open
origin fibres using their compact preimages. -/
theorem isClosedMap_inflateH : IsClosedMap (inflateH (S := S)) := by
  intro F hF
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro T hT
  let K : Set S.Hull := {U | origin (inflateH U) = origin T}
  have hK : IsCompact K := isCompact_inflate_preimage_origin_fibre (origin T)
  have hc : IsClosed (inflateH '' (K ∩ F)) :=
    ((hK.inter_right hF).image continuous_inflateH).isClosed
  have hn : {V : S.Hull | origin V = origin T} ∩
      (inflateH '' (K ∩ F))ᶜ ∈ 𝓝 T := by
    apply ((isOpen_origin_fibre (origin T)).inter hc.isOpen_compl).mem_nhds
    refine ⟨rfl, ?_⟩
    rintro ⟨U, hU, hUT⟩
    exact hT ⟨U, hU.2, hUT⟩
  apply Filter.mem_of_superset hn
  intro V hV
  rintro ⟨U, hU, hUV⟩
  apply hV.2
  refine ⟨U, ⟨?_, hU⟩, hUV⟩
  change origin (inflateH U) = origin T
  exact hUV ▸ hV.1

/-- The existing inverse of inflation is continuous from finite tile data and
bijectivity alone; continuous desubstitution is not a further hypothesis. -/
theorem continuous_desub (hR : Bijective (inflateH (S := S))) :
    Continuous (desub hR) := by
  rw [continuous_iff_isClosed]
  intro F hF
  have he : desub hR ⁻¹' F = inflateH '' F := by
    ext T
    constructor
    · intro hT
      exact ⟨desub hR T, hT, inflateH_desub hR T⟩
    · rintro ⟨U, hU, rfl⟩
      change desub hR (inflateH U) ∈ F
      simpa only [desub_inflateH] using hU
  rw [he]
  exact isClosedMap_inflateH F hF

end Psc.PeriodicPartnerDesubContinuity
