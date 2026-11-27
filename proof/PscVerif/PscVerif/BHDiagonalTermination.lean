import PscVerif.BHDiagonalOuter
import PscVerif.BHDiagonalProgress
import PscVerif.BHDiagonalParameters

/-!
# Finite energy termination for full diagonal run-window packets

Energy is measured on the last two integer coordinates, but the reachable
set retains a witness full packet and a path of actual strict occurrence
steps. A minimum reachable energy suffices: every nonterminal progress
block would produce a strictly smaller member of the same finite set.
-/

namespace Psc.BHDiagonalTermination

open Psc.OccurrenceTransport Psc.BHNearDiagonalLiteral
open Psc.BHNearDiagonalDescent Psc.BHDiagonalProgress

/-- A real energy bound cuts out only finitely many integral pairs. -/
theorem finite_energy_sublevel {r β} (h : BHDiagonalLiteral.Family r β) (L : ℝ) :
    {u : ℤ × ℤ | energy (β-r) (r/β) u.1 u.2 ≤ L}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2*L+1)
  apply ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod
    (Set.finite_Icc (-(N : ℤ)) (N : ℤ))).subset
  rintro ⟨z, y⟩ he
  change energy (β-r) (r/β) z y ≤ L at he
  have hb := BHDiagonalOuter.energy_ge_half h (z : ℝ) (y : ℝ)
  have hz : -(N : ℝ) ≤ z ∧ (z : ℝ) ≤ N := by
    constructor <;> nlinarith only [hb, he, hN, sq_nonneg (y : ℝ),
      sq_nonneg ((z : ℝ)+1/2), sq_nonneg ((z : ℝ)-1/2)]
  have hy : -(N : ℝ) ≤ y ∧ (y : ℝ) ≤ N := by
    constructor <;> nlinarith only [hb, he, hN, sq_nonneg (z : ℝ),
      sq_nonneg ((y : ℝ)+1/2), sq_nonneg ((y : ℝ)-1/2)]
  exact ⟨⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2⟩,
    ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩⟩

/-- Reusable finite-energy argument. The final family theorem below
supplies this progress premise from its outer and residual proofs. -/
theorem central_exit_of_progress {r β} (h : BHDiagonalLiteral.Family r β)
    (hprogress : ∀ q : Packet, Central r r β q → Progress r β q)
    {p : Packet} (hp : Central r r β p) : LabelledExit r β p := by
  let E (u : ℤ × ℤ) := energy (β-r) (r/β) u.1 u.2
  let u₀ := (p.delta 2, p.delta 1)
  let C : Set (ℤ × ℤ) := {u | E u ≤ E u₀ ∧ ∃ q : Packet,
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β)) p q ∧
      Central r r β q ∧ (q.delta 2, q.delta 1) = u}
  have hc0 : u₀ ∈ C := ⟨le_rfl, p, .refl, hp, rfl⟩
  have hfin : C.Finite := (finite_energy_sublevel h (E u₀)).subset (by
    intro u hu
    exact hu.1)
  obtain ⟨u, hu, hmin⟩ := Set.exists_min_image C E hfin ⟨u₀, hc0⟩
  obtain ⟨hEU, q, hpath, hq, rfl⟩ := hu
  rcases hprogress q hq with ⟨q', hfinal, hlabel, hzero⟩ | ⟨q', hnext, hc', he⟩
  · exact ⟨q', hpath.trans hfinal, hlabel, hzero⟩
  · have hm : (q'.delta 2, q'.delta 1) ∈ C :=
      ⟨he.le.trans hEU, q', hpath.trans hnext, hc', rfl⟩
    exact (not_lt_of_ge (hmin _ hm) he).elim

/-- Outer descent expressed at an arbitrary central packet, without
forgetting its retained first coordinate or its actual occurrence path. -/
theorem outer_progress {r β} (h : BHDiagonalLiteral.Family r β)
    {p : Packet} (hc : Central r r β p)
    (hbig : BHDiagonalOuter.cutoff r β <
      energy (β-r) (r/β) (p.delta 2) (p.delta 1)) : Progress r β p := by
  let x := p.delta 0
  let y := p.delta 1
  let z := p.delta 2
  have hpack : p = runPacket x y z := packet_from_central hc
  have hc' : Central r r β (runPacket x y z) := hpack ▸ hc
  obtain ⟨t, hs, ht, he⟩ := BHDiagonalOuter.outer_step h x y z hc' hbig
  refine Or.inr ⟨runPacket (y+(r : ℤ)*z) t y,
    .single (hpack.symm ▸ hs), ht, ?_⟩
  exact he

/-- Every run-window packet either already has a labelled exit or admits
an actual strict path to a central packet with strictly smaller energy. -/
theorem central_progress {r β} (h : BHDiagonalLiteral.Family r β)
    {p : Packet} (hc : Central r r β p) : Progress r β p := by
  by_cases hbig : BHDiagonalOuter.cutoff r β <
      energy (β-r) (r/β) (p.delta 2) (p.delta 1)
  · exact outer_progress h hc hbig
  · exact residual_progress h hc
      (BHDiagonalOuter.cutoff_implies_disk h (p.delta 2) (p.delta 1)
        (le_of_not_gt hbig))

/-- Uniform run-window termination for the literal diagonal family.
The conclusion retains actual strict occurrence edges, equal terminal
letters, and the full integral zero vector. No classification, finite
certificate, progress, or zero-hitting premise remains. -/
theorem central_hits_labelled_zero {r β} (h : BHDiagonalLiteral.Family r β)
    {p : Packet} (hp : Central r r β p) : LabelledExit r β p :=
  central_exit_of_progress h (fun _ hc => central_progress h hc) hp

/-- Every integer parameter at least twelve has its bracketed root and a
uniform labelled exit for every full packet in its run window. -/
theorem run_window_exit_for_all_parameters (r : ℕ) (hr : 12 ≤ r) :
    ∃ β : ℝ, BHDiagonalLiteral.Family r β ∧
      ∀ p : Packet, Central r r β p → LabelledExit r β p := by
  obtain ⟨β, h⟩ := BHDiagonalParameters.family_root_exists r hr
  exact ⟨β, h, fun _ hp => central_hits_labelled_zero h hp⟩

end Psc.BHDiagonalTermination
