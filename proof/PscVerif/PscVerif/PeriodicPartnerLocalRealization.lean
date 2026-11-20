/-
# The concrete realization on the ordinary local hull

The carrier map is unchanged. Its proved flow equivariance and continuous
target flow identify its ordinary-hull continuity obligation exactly with
continuity from the existing exact-agreement hull. This does not assert that
the latter obligation, recognizability, or finite fibres have been discharged.
-/
import PscVerif.PeriodicPartnerLocalTopology
import PscVerif.PeriodicPartnerRealization

namespace Psc.PeriodicPartnerLocalRealization

open Function Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst
open Psc.PeriodicPartnerLocalTopology Psc.PeriodicPartnerRealization

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {S : LengthSubst α} (P : PisotData S) (hR : Bijective (inflateH (S := S)))

/-- The already constructed realization, on the ordinary topological presentation. -/
noncomputable def realizeLocal (T : LocalHull S) : Solenoid S := realize P hR T.toHull

theorem realizeLocal_inflate (T : LocalHull S) :
    realizeLocal P hR (PeriodicPartnerLocalTopology.inflate S T) =
      shiftS S (realizeLocal P hR T) :=
  realize_inflate P hR T.toHull

theorem realizeLocal_translate (hβ : 1 < S.β) (t : ℝ) (T : LocalHull S) :
    realizeLocal P hR (PeriodicPartnerLocalTopology.translate S t T) =
      flow P t (realizeLocal P hR T) :=
  realize_translate P hR hβ t T.toHull

/-- Precisely the remaining continuity obligation for the concrete map.
Both directions are proved; neither side is supplied as an unconditional fact. -/
theorem continuous_realizeLocal_iff (hβ : 1 < S.β) :
    Continuous (realizeLocal P hR) ↔ Continuous (realize P hR) :=
  continuous_iff_exact_of_equivariant S (realizeLocal P hR) (flow P)
    (continuous_flow S P) (realizeLocal_translate P hR hβ)

end Psc.PeriodicPartnerLocalRealization
