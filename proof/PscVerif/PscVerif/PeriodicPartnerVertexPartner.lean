/-
# A vertex-type common partner forces a permutation

Origin case (A) of Theorem S: the two asymptotic leaves end different tiles `b ≠ c` at the
origin, and the triple is inflation-periodic.  If the common partner also has a vertex at
the origin, ending a tile `x`, then (Z2) at level zero gives `x ≠ b` and `x ≠ c`.
Periodicity makes all three letters periodic for the last-letter map, and three periodic
letters on three letters force a permutation.  So that side lies in the injective regime of
round-4 Lemma A.  No determinant hypothesis enters.  Nothing is excluded here.
-/
import PscVerif.PeriodicPartnerHull
import PscVerif.PeriodicPartnerSelection

namespace Psc.PeriodicPartnerVertexPartner

open Function Psc.PeriodicPartnerDynamics Psc.PeriodicPartnerSelection
  Psc.PeriodicPartnerHull Psc.PeriodicPartnerHull.LengthSubst

section Abstract

variable {X α : Type*} {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → α → Prop}

/-- The letter ending a tile at the origin of a periodic tiling is periodic for `g`. -/
theorem periodic_letter (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    {T : X} {x : α} (hT : T ∈ periodicPts f) (hx : EndsAt T 0 x) : x ∈ periodicPts g := by
  obtain ⟨n, hn, hTn⟩ := hT
  refine ⟨n, hn, ?_⟩
  have h := laws.endpoint_iterate n hx
  rw [mul_zero, hTn.eq] at h
  exact laws.endpoint_unique h hx

end Abstract

/-- Three distinct periodic letters make a ternary map injective. -/
theorem injective_of_three_periodic :
    ∀ (g : Fin 3 → Fin 3) (x b c : Fin 3), x ≠ b → x ≠ c → b ≠ c →
      g^[6] x = x → g^[6] b = b → g^[6] c = c → Injective g := by
  decide

/-- Two periodic letters alone do not suffice: `(0,1,1)` is the control. -/
theorem two_periodic_not_injective :
    TwoPeriodicLetters ![0, 1, 1] ∧ ¬ Injective (![0, 1, 1] : Fin 3 → Fin 3) :=
  ⟨collapsed_pair_example.1, fun h => absurd (h collapsed_pair_example.2) (by decide)⟩

section AbstractTernary

variable {X : Type*} {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt : X → ℝ → Fin 3 → Prop}

/-- **Lemma VP.**  Three periodic tilings ending pairwise different tiles at the origin
force the last-letter map to be a permutation. -/
theorem injective_of_vertex_partner (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    {T S U : X} {x b c : Fin 3}
    (hT : T ∈ periodicPts f) (hS : S ∈ periodicPts f) (hU : U ∈ periodicPts f)
    (hx : EndsAt T 0 x) (hb : EndsAt S 0 b) (hc : EndsAt U 0 c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hbc : b ≠ c) : Injective g :=
  injective_of_three_periodic g x b c hxb hxc hbc
    (six_of_mem_periodicPts (periodic_letter laws hT hx))
    (six_of_mem_periodicPts (periodic_letter laws hS hb))
    (six_of_mem_periodicPts (periodic_letter laws hU hc))

end AbstractTernary

section Hull

variable {L : LengthSubst (Fin 3)}

/-- Two hull tilings share no tile at level zero: the level-zero part of (Z2). -/
def NoCommonTile (T U : L.Hull) : Prop := ∀ p, p ∈ T.1 → p ∉ U.1

/-- **Lemma VP on the hull.**  If the leaves branch at the origin and the common partner
also has a vertex there, sharing no tile with either leaf, the last-letter map is a
permutation. -/
theorem hull_lastLetter_injective_of_vertex_partner
    {T S U : L.Hull} {x b c : Fin 3}
    (hT : T ∈ periodicPts inflateH) (hS : S ∈ periodicPts inflateH)
    (hU : U ∈ periodicPts inflateH) (hbranch : BranchAt AgreeRight EndsAt S U 0 b c)
    (hx : EndsAt T 0 x) (hTS : NoCommonTile T S) (hTU : NoCommonTile T U) :
    Injective L.lastLetter := by
  obtain ⟨-, hb, hc, hbc⟩ := hbranch
  refine injective_of_vertex_partner rightBranchLaws hT hS hU hx hb hc ?_ ?_ hbc
  · rintro rfl; exact hTS _ hx hb
  · rintro rfl; exact hTU _ hx hc

end Hull

end Psc.PeriodicPartnerVertexPartner
