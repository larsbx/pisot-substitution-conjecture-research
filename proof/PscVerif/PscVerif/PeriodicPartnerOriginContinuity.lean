/-
# Locally constant origin data on the exact hull

Exact agreement on any window containing zero identifies the tile containing
zero.  The origin tile of the inflation is then determined by the placed image
of that parent tile.  Hence the existing chosen prefix count `offset` also
depends only on the origin tile.  Equality of its choice predicates, together
with proof irrelevance, handles the choice in the existing definition; no new
selector or injectivity of the length functional is assumed.

All local-constancy statements concern the exact-agreement hull.  Origin data
need not be continuous for the ordinary translation-tolerant hull topology.
Source decision: `docs/c4-realization-continuity-stop-go-2026-11-19.md`.
-/
import PscVerif.PeriodicPartnerHullContinuity
import PscVerif.PeriodicPartnerRealization
import Mathlib.Topology.LocallyConstant.Basic

namespace Psc.PeriodicPartnerOriginContinuity

open Function Filter Set Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerRealization
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {S : LengthSubst α}

/-- A radius-one agreement window identifies the tile containing zero. -/
theorem origin_eq_of_agree_one {T U : S.Hull} (h : Agree 1 T U) :
    origin T = origin U := by
  have hp := tileAt_spec T 0
  have hm : origin T ∈ U.1 :=
    (h (origin T) ⟨0, hp.2, by constructor <;> norm_num⟩).mp hp.1
  exact (tileAt_eq hm hp.2).symm

/-- The origin tile is locally constant in the exact-agreement topology. -/
theorem isLocallyConstant_origin : IsLocallyConstant (origin (S := S)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro T
  filter_upwards [agreement_mem_nhds T 1] with U hU
  apply Eq.symm
  apply origin_eq_of_agree_one
  simpa using hU

theorem isOpen_origin_fibre (p : α × ℝ) : IsOpen {T : S.Hull | origin T = p} :=
  (isLocallyConstant_origin (S := S)).isOpen_fiber p

theorem isClosed_origin_fibre (p : α × ℝ) : IsClosed {T : S.Hull | origin T = p} :=
  (isLocallyConstant_origin (S := S)).isClosed_fiber p

variable [Nonempty α]

/-- The parent origin tile determines the child origin tile: both candidates
lie in one placed word and cover zero, so placement uniqueness applies. -/
theorem origin_inflate_eq_of_origin_eq {U V : S.Hull} (h : origin U = origin V) :
    origin (inflateH U) = origin (inflateH V) := by
  have hu := tileAt_inflate U 0
  have hv := tileAt_inflate V 0
  simp only [zero_div] at hu hv
  change origin (inflateH U) ∈
    S.place (S.σ (origin U).1) (S.β * (origin U).2) at hu
  rw [h] at hu
  exact S.place_unique hu hv (tileAt_spec (inflateH U) 0).2
    (tileAt_spec (inflateH V) 0).2

/-- The existing chosen prefix count depends only on the origin tile.  Equal
origin data give the same existential choice predicate and proof irrelevance
identifies its proofs.  No uniqueness premise for integer counts is used. -/
theorem offset_eq_of_origin_eq {U V : S.Hull} (h : origin U = origin V) :
    offset U = offset V := by
  have hp : tileAt U 0 = tileAt V 0 := h
  have hc : tileAt (inflateH U) 0 = tileAt (inflateH V) 0 :=
    origin_inflate_eq_of_origin_eq h
  unfold offset
  simp only [hp, hc]

/-- The prefix-count selection is locally constant on the exact hull. -/
theorem isLocallyConstant_offset : IsLocallyConstant (offset (S := S)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro T
  filter_upwards [(isLocallyConstant_origin (S := S)).eventually_eq T] with U hU
  exact offset_eq_of_origin_eq hU

omit [Nonempty α] in
theorem continuous_origin_start : Continuous (fun T : S.Hull => (origin T).2) :=
  ((isLocallyConstant_origin (S := S)).comp Prod.snd).continuous

theorem continuous_offset : Continuous (offset (S := S)) :=
  (isLocallyConstant_offset (S := S)).continuous

end Psc.PeriodicPartnerOriginContinuity
