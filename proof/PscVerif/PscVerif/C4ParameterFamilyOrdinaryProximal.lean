import PscVerif.C4ParameterFamilyZeroFibreWitnesses
import PscVerif.PeriodicPartnerOrdinaryProximal

/-!
# Conditional ordinary proximality of concrete solenoid fibres

The ordinary hull's compactness, minimality, factor continuity and
equivariance are already proved. The only geometric input retained here
is the explicit universal zero-fibre anchor obligation. The wrappers
accept the exact-window and common-tile interfaces already in use.

Source decision: `docs/c4-ordinary-proximal-transport-stop-go-2026-11-21.md`.
-/

namespace Psc.ParameterFamilyOrdinaryProximal

open Function Set Psc.ParameterFamilyTiling Psc.ParameterFamilySolenoid
open Psc.ParameterFamilyRecognizability Psc.ParameterFamilyZeroFibreWitnesses
open Psc.PeriodicPartnerLocalTopology Psc.PeriodicPartnerRealization
open Psc.PeriodicPartnerProximal Psc.PeriodicPartnerOrdinaryProximal

variable (k : ℕ) (hk : 1 ≤ k)

/-- The explicit exact-proximal anchor obligation suffices for every concrete
factor fibre. Compactness and the ordinary translation dynamics are supplied
by existing family theorems, not added as unresolved hypotheses. -/
theorem same_fibre_proximal_of_zero_anchor
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hanchor : ∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      ExactProximal (geometry k hk) V W)
    {T U : LocalHull (geometry k hk)}
    (hTU : solenoidRealize k hk T = solenoidRealize k hk U) :
    TopologicallyProximal (translate (geometry k hk)) T U := by
  let S := geometry k hk
  let : CompactSpace (LocalHull S) :=
    Psc.PeriodicPartnerRealizationOnto.localHull_compactSpace
  let : T2Space (Solenoid S) := solenoid_t2Space S
  apply topologicallyProximal_of_anchor (translate S)
    (fun t => (translateHomeomorph S t).continuous_toFun)
    (translate_translate S) (denseRange_translate k hk)
    (solenoidRealize k hk) (continuous_solenoidRealize k hk)
    (fun t A B hAB => by rw [solenoidRealize_translate, solenoidRealize_translate, hAB])
    (ofExact S V) ?_ hTU
  intro W hW
  have hz : realize (pisotData k hk) (inflateH_bijective k hk) W.toHull = 0 :=
    hW.trans hV
  exact topologicallyProximal_of_exactProximal S (hanchor W.toHull hz)

/-- Sharing one tile with each zero-fibre member is the sufficient geometric
anchor input. Inflation periods come from zero realization as before. -/
theorem same_fibre_proximal_of_zero_anchor_common_tile
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hanchor : ∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      (V.1 ∩ W.1).Nonempty)
    {T U : LocalHull (geometry k hk)}
    (hTU : solenoidRealize k hk T = solenoidRealize k hk U) :
    TopologicallyProximal (translate (geometry k hk)) T U := by
  apply same_fibre_proximal_of_zero_anchor k hk hV ?_ hTU
  intro W hW
  exact (exactProximal_iff_common_tile k hk hV hW).mpr (hanchor W hW)

/-- The same radius-one triple already consumed by PR #643 is enough at one
anchor. No stronger witness radius or direct origin agreement is assumed. -/
theorem same_fibre_proximal_of_zero_anchor_witnesses (hk₂ : 2 ≤ k)
    {V : (geometry k hk).Hull}
    (hV : realize (pisotData k hk) (inflateH_bijective k hk) V = 0)
    (hanchor : ∀ W : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) W = 0 →
      WindowWitnesses (geometry k hk) 1 V W)
    {T U : LocalHull (geometry k hk)}
    (hTU : solenoidRealize k hk T = solenoidRealize k hk U) :
    TopologicallyProximal (translate (geometry k hk)) T U := by
  apply same_fibre_proximal_of_zero_anchor_common_tile k hk hV ?_ hTU
  intro W hW
  exact (windowWitnesses_iff_common_tile k hk hk₂ (by norm_num) hV hW).mp (hanchor W hW)

/-- A conditional endpoint using precisely the universal zero-fibre witness
obligation. The existing seam theorem supplies a zero anchor automatically. -/
theorem same_fibre_proximal_of_zero_fibre_witnesses (hk₂ : 2 ≤ k)
    (hw : ∀ A B : (geometry k hk).Hull,
      realize (pisotData k hk) (inflateH_bijective k hk) A = 0 →
      realize (pisotData k hk) (inflateH_bijective k hk) B = 0 →
      WindowWitnesses (geometry k hk) 1 A B)
    {T U : LocalHull (geometry k hk)}
    (hTU : solenoidRealize k hk T = solenoidRealize k hk U) :
    TopologicallyProximal (translate (geometry k hk)) T U := by
  obtain ⟨V, _, hV⟩ := fixed_tiling_over_zero k hk
  exact same_fibre_proximal_of_zero_anchor_witnesses k hk hk₂ hV
    (fun W hW => hw V W hV hW) hTU

end Psc.ParameterFamilyOrdinaryProximal
