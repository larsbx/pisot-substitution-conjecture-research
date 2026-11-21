import PscVerif.C4FamilyTileAutomatonHull
import PscVerif.C4ParameterFamilyZeroFibreWitnesses

/-!
# Finite automaton certificates for all literal zero-fibre pairs

Each signed edge is realized in an actual legal hull member.  Finite walk
induction joins those members through shared labelled tiles and uses the
already proved legal-patch coincidence transfer.  Intermediate hull members
need neither zero realization nor inflation periodicity.  Periodicity is
used only at the original two zero-fibre endpoints.

The new reduction introduces no sequence limit or new compactness step.
Source decision: `docs/c4-finite-hull-witnesses-2026-11-21.md`.
-/

namespace Psc.PeriodicPartnerEventualCoincidence

open Set Psc.PeriodicPartnerHull

/-- Dense eventual coincidence composes through a genuine middle tiling.
This uses a finite intersection of open dense sets, not transitivity of
an arbitrary proximality relation. -/
theorem dense_eventual_trans {α : Type*} [Nonempty α] (S : LengthSubst α)
    {P Q R : Set (α × ℝ)} (hQ : S.IsTiling Q)
    (hPQ : Dense (eventual S P Q)) (hQR : Dense (eventual S Q R)) :
    Dense (eventual S P R) := by
  apply (hPQ.inter_of_isOpen_left hQR (eventual_open S P Q)).mono
  intro x hx
  exact eventual_trans S hQ hx.1 hx.2

end Psc.PeriodicPartnerEventualCoincidence

namespace Psc.C4FamilyFiniteZeroFibre

open Function Set Matrix
open Psc.C4FiniteTileAutomaton Psc.C4FamilyTileAutomatonHull
open Psc.ParameterFamilyTiling Psc.ParameterFamilyRecognizability
open Psc.ParameterFamilySolenoid Psc.ParameterFamilyZeroFibreWitnesses
open Psc.PeriodicPartnerEventualCoincidence Psc.PeriodicPartnerProximal
open Psc.PeriodicPartnerHull.LengthSubst (inflateH)
open Psc.PeriodicPartnerRealization (realize realVec torusRealize Solenoid origin tileAt_spec lattice)
open Psc.PeriodicPartnerRealizationFinite (dot_realVec)
open Psc.PeriodicPartnerPeriodicZero

variable (k : ℕ) (hk : 1 ≤ k)

/-- A replayable finite walk transfers coincidence between any two actual
hull members carrying its endpoint tiles at the specified displacement. -/
theorem dense_eventual_of_walk (hk₂ : 2 ≤ k) {a b : Label} {w : List Edge} {v : Vector}
    (hwalk : Walk a w b v) {T U : (geometry k hk).Hull} (x : ℝ)
    (hT : (a, x) ∈ T.1)
    (hU : (b, x + lengthOutput (geometry k hk) v) ∈ U.1) :
    Dense (eventual (geometry k hk) T.1 U.1) := by
  induction hwalk generalizing T U x with
  | nil a =>
      exact hull_dense_eventual k hk₂ ⟨(a, x), hT, by simpa using hU⟩
  | @cons e es b v rest ih =>
      obtain ⟨H, hH₀, hH₁⟩ := signed_edge_hull_bridge k hk hk₂ e x
      have hTH : Dense (eventual (geometry k hk) T.1 H.1) :=
        hull_dense_eventual k hk₂ ⟨(source e, x), hT, hH₀⟩
      have hU' : (b, (x + lengthOutput (geometry k hk) (edgeOutput e)) +
          lengthOutput (geometry k hk) v) ∈ U.1 := by
        simpa only [lengthOutput_add, add_assoc] using hU
      exact dense_eventual_trans (geometry k hk) H.2.1 hTH
        (ih (x + lengthOutput (geometry k hk) (edgeOutput e)) hH₁ hU')

/-- The semantic transfer accepts the exact replay endpoint, preserving
the checked edge word, label and signed integer output. -/
theorem dense_eventual_of_replay (hk₂ : 2 ≤ k) {a b : Label} {w : List Edge} {v : Vector}
    (h : replay a w = some (b, v)) {T U : (geometry k hk).Hull} (x : ℝ)
    (hT : (a, x) ∈ T.1)
    (hU : (b, x + lengthOutput (geometry k hk) v) ∈ U.1) :
    Dense (eventual (geometry k hk) T.1 U.1) :=
  dense_eventual_of_walk k hk hk₂ (replay_walk h) x hT hU

/-- The constructed certificate handles arbitrary start and terminal
labels: reverse the zero-output terminal word to reach control 1, then
use the existing integer-output certificate. -/
theorem dense_eventual_of_integer_displacement (hk₂ : 2 ≤ k) {a b : Label} (v : Vector)
    {T U : (geometry k hk).Hull} (x : ℝ)
    (hT : (a, x) ∈ T.1)
    (hU : (b, x + lengthOutput (geometry k hk) v) ∈ U.1) :
    Dense (eventual (geometry k hk) T.1 U.1) := by
  have hw : Walk a (reverseWord (terminalWord a) ++ certificate v b) b v := by
    simpa using (terminalWord_walk a).reverse.append (certificate_walk v b)
  exact dense_eventual_of_walk k hk hk₂ hw x hT hU

/-- Equal actual zeroth torus coordinates already give the integer
displacement needed by the finite certificate. The endpoints need not be
periodic, so the conclusion remains dense eventual coincidence. -/
theorem dense_eventual_of_torusRealize_eq (hk₂ : 2 ≤ k)
    {T U : (geometry k hk).Hull}
    (h : torusRealize (pisotData k hk) (inflateH_bijective k hk) T =
      torusRealize (pisotData k hk) (inflateH_bijective k hk) U) :
    Dense (eventual (geometry k hk) T.1 U.1) := by
  let d := realVec (pisotData k hk) (inflateH_bijective k hk) T -
    realVec (pisotData k hk) (inflateH_bijective k hk) U
  have hd : d ∈ lattice (Fin 3) := QuotientAddGroup.eq_iff_sub_mem.mp h
  change ∀ i, ∃ z : ℤ, (z : ℝ) = d i at hd
  choose z hz using hd
  have hlen : lengthOutput (geometry k hk) z = (geometry k hk).ℓ ⬝ᵥ d := by
    simp only [lengthOutput, dotProduct, hz]
  have hpos : (origin T).2 + lengthOutput (geometry k hk) z = (origin U).2 := by
    rw [hlen]
    simp only [d, dotProduct_sub, dot_realVec]
    ring
  apply dense_eventual_of_integer_displacement k hk hk₂
    (a := (origin T).1) (b := (origin U).1) z (origin T).2
  · exact (tileAt_spec T 0).1
  · rw [hpos]
    exact (tileAt_spec U 0).1

/-- Every pair in any fibre of the actual full compatible-history map is
densely eventually coincident. No common tile or proximality conclusion
for nonperiodic endpoints is inserted here. -/
theorem same_fibre_dense_eventual (hk₂ : 2 ≤ k)
    {T U : (geometry k hk).Hull}
    (h : realize (pisotData k hk) (inflateH_bijective k hk) T =
      realize (pisotData k hk) (inflateH_bijective k hk) U) :
    Dense (eventual (geometry k hk) T.1 U.1) := by
  apply dense_eventual_of_torusRealize_eq k hk hk₂
  exact congrArg (fun z : Solenoid (geometry k hk) => z.1 0) h

/-- Zero realization supplies actual integer coordinates for the selected
origin tile. The coordinates remain unbounded; no finite box is asserted
to enumerate all zero-fibre members. -/
theorem integer_origin_of_zero {T : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0) :
    ∃ z : Vector, (origin T).2 = -lengthOutput (geometry k hk) z := by
  obtain ⟨v, hv, hx⟩ := lattice_origin_of_realize_zero
    (pisotData k hk) (inflateH_bijective k hk) hT
  change ∀ i, ∃ z : ℤ, (z : ℝ) = v i at hv
  choose z hz using hv
  refine ⟨z, ?_⟩
  simpa only [lengthOutput, dotProduct, hz] using hx

/-- All pairs whose selected origin tiles have integer length coordinates
are densely eventually coincident.  This arithmetic premise is explicit
and is not inferred for arbitrary hull members. -/
theorem dense_eventual_of_integer_origins (hk₂ : 2 ≤ k) {T U : (geometry k hk).Hull}
    (hT : ∃ z : Vector, (origin T).2 = -lengthOutput (geometry k hk) z)
    (hU : ∃ z : Vector, (origin U).2 = -lengthOutput (geometry k hk) z) :
    Dense (eventual (geometry k hk) T.1 U.1) := by
  obtain ⟨zT, hzT⟩ := hT
  obtain ⟨zU, hzU⟩ := hU
  have hpos : (origin T).2 + lengthOutput (geometry k hk) (zT + -zU) =
      (origin U).2 := by
    rw [hzT, hzU, lengthOutput_add, lengthOutput_neg]
    ring
  apply dense_eventual_of_integer_displacement k hk hk₂
    (a := (origin T).1) (b := (origin U).1) (zT + -zU) (origin T).2
  · exact (tileAt_spec T 0).1
  · rw [hpos]
    exact (tileAt_spec U 0).1

/-- The finite integer certificate and its actual hull interpretation
give dense eventual coincidence for every pair over the full zero history. -/
theorem zero_fibre_dense_eventual (hk₂ : 2 ≤ k) {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    Dense (eventual (geometry k hk) T.1 U.1) :=
  dense_eventual_of_integer_origins k hk hk₂
    (integer_origin_of_zero k hk hT) (integer_origin_of_zero k hk hU)

/-- Every pair in the literal family's full zero solenoid fibre shares a
labelled tile. Only the original endpoints require inflation periods. -/
theorem zero_fibre_common_tile (hk₂ : 2 ≤ k) {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    (T.1 ∩ U.1).Nonempty := by
  obtain ⟨m, hm, hTm⟩ := periodic_of_realize_zero k hk hT
  obtain ⟨n, hn, hUn⟩ := periodic_of_realize_zero k hk hU
  have hTm' : inflateH^[m * n] T = T := by
    rw [iterate_mul]
    exact IsFixedPt.iterate hTm n
  have hUn' : inflateH^[m * n] U = U := by
    rw [Nat.mul_comm, iterate_mul]
    exact IsFixedPt.iterate hUn m
  apply Psc.PeriodicPartnerLegalCoincidence.common_tile_of_periodic_eventual
    (geometry k hk) (Nat.mul_pos hm hn) ?_ ?_
    (zero_fibre_dense_eventual k hk hk₂ hT hU).nonempty
  · simpa only [Psc.PeriodicPartnerEvenTails.hull_iterate_val]
      using congrArg Subtype.val hTm'
  · simpa only [Psc.PeriodicPartnerEvenTails.hull_iterate_val]
      using congrArg Subtype.val hUn'

/-- Arbitrarily large exact common-translation windows for every pair
over zero, derived from the now established common tile. -/
theorem zero_fibre_exactProximal (hk₂ : 2 ≤ k) {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    ExactProximal (geometry k hk) T U :=
  (exactProximal_iff_common_tile k hk hT hU).mpr
    (zero_fibre_common_tile k hk hk₂ hT hU)

/-- The three exact common-shift agreements consumed by the zero-fibre
interface now exist for every positive radius and every zero-fibre pair. -/
theorem zero_fibre_windowWitnesses (hk₂ : 2 ≤ k) {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0)
    {R : ℝ} (hR : 0 < R) : WindowWitnesses (geometry k hk) R T U :=
  (windowWitnesses_iff_common_tile k hk hk₂ hR hT hU).mpr
    (zero_fibre_common_tile k hk hk₂ hT hU)

/-- The published closed-origin witnesses, without requiring the two
original origin patches to agree. -/
theorem zero_fibre_closedOriginWitnesses (hk₂ : 2 ≤ k) {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    ClosedOriginWitnesses (geometry k hk) T U :=
  (closedOriginWitnesses_iff_common_tile k hk hk₂ hT hU).mpr
    (zero_fibre_common_tile k hk hk₂ hT hU)

/-- Exact strong regional proximality on the complete zero fibre. -/
theorem zero_fibre_stronglyRegionallyProximal (hk₂ : 2 ≤ k) {T U : (geometry k hk).Hull}
    (hT : realize (pisotData k hk) (inflateH_bijective k hk) T = 0)
    (hU : realize (pisotData k hk) (inflateH_bijective k hk) U = 0) :
    StronglyRegionallyProximal (geometry k hk) T U :=
  stronglyRegionallyProximal_of_exactProximal (geometry k hk)
    (zero_fibre_exactProximal k hk hk₂ hT hU)

end Psc.C4FamilyFiniteZeroFibre
