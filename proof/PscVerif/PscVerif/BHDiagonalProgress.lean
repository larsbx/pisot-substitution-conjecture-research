import PscVerif.BHDiagonalAxis
import PscVerif.BHDiagonalDescent
import PscVerif.BHDiagonalClassificationFull

/-!
# Full signed packet progress for the diagonal family

The sign involution exchanges the two physical tracks and negates all three
integral displacement coordinates.  The endpoint predicate retains equal
letters and full integral zero.  The energy comparison is only at the end
of a block; intermediate strict packets need not decrease energy.

Literature and written derivation:
`docs/bh-diagonal-residual-stop-go-2026-11-27.md` and
`docs/bh-diagonal-residual-exit-2026-11-27.md`.
-/

namespace Psc.BHDiagonalProgress

open Psc.OccurrenceTransport Psc.BHNearDiagonalLiteral
open Psc.BHNearDiagonalDescent

def LabelledExit (r : ℕ) (β : ℝ) (p : Packet) : Prop :=
  ∃ q : Packet,
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β)) p q ∧
    q.top = q.bottom ∧ q.delta = 0

def Progress (r : ℕ) (β : ℝ) (p : Packet) : Prop :=
  LabelledExit r β p ∨
  ∃ q : Packet,
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β)) p q ∧
    Central r r β q ∧
    energy (β-r) (r/β) (q.delta 2) (q.delta 1) <
      energy (β-r) (r/β) (p.delta 2) (p.delta 1)

@[simp] theorem packet_swap_swap (p : Packet) : p.swap.swap = p := by
  cases p
  simp [Packet.swap]

@[simp] theorem runPacket_swap (x y z : ℤ) :
    (runPacket x y z).swap = runPacket (-x) (-y) (-z) := by
  unfold Packet.swap runPacket
  congr 1
  funext i
  fin_cases i <;> rfl

theorem path_swap {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} {p q : Packet}
    (hp : Relation.ReflTransGen (InteriorStep s ℓ) p q) :
    Relation.ReflTransGen (InteriorStep s ℓ) p.swap q.swap := by
  induction hp with
  | refl => exact .refl
  | @tail b c hpath hedge ih => exact ih.tail ⟨hedge.1.swap, hedge.2.swap⟩

theorem central_swap {r k β} {p : Packet} (hp : Central r k β p) :
    Central r k β p.swap := by
  refine ⟨hp.2.1, hp.1, ?_⟩
  simpa only [Packet.swap, offset_neg, abs_neg] using hp.2.2

theorem energy_swap (a b : ℝ) (p : Packet) :
    energy a b (p.swap.delta 2) (p.swap.delta 1) =
      energy a b (p.delta 2) (p.delta 1) := by
  simp only [Packet.swap, Pi.neg_apply, Int.cast_neg, energy]
  ring

theorem LabelledExit.swap {r β} {p : Packet} (hp : LabelledExit r β p) :
    LabelledExit r β p.swap := by
  obtain ⟨q, hpath, hlabel, hzero⟩ := hp
  refine ⟨q.swap, path_swap hpath, hlabel.symm, ?_⟩
  simp only [Packet.swap, hzero, neg_zero]

theorem Progress.swap {r β} {p : Packet} (hp : Progress r β p) :
    Progress r β p.swap := by
  rcases hp with hzero | ⟨q, hpath, hc, he⟩
  · exact Or.inl hzero.swap
  · exact Or.inr ⟨q.swap, path_swap hpath, central_swap hc,
      by simpa only [energy_swap] using he⟩

theorem packet_from_central {r k β} {p : Packet} (hp : Central r k β p) :
    p = runPacket (p.delta 0) (p.delta 1) (p.delta 2) := by
  obtain ⟨a, b, v⟩ := p
  obtain ⟨ha, hb, _⟩ := hp
  change a = 1 at ha
  change b = 1 at hb
  subst a
  subst b
  congr 1
  funext i
  fin_cases i <;> rfl

theorem zero_pair_exit {r β} (h : BHDiagonalLiteral.Family r β) (x : ℤ)
    (hc : Central r r β (runPacket x 0 0)) :
    LabelledExit r β (runPacket x 0 0) := by
  refine ⟨runPacket 0 0 0,
    .single (BHDiagonalLiteral.central_zero_pair_step h x hc), rfl, ?_⟩
  funext i
  fin_cases i <;> rfl

theorem positive_axis_progress {r β} (h : BHDiagonalLiteral.Family r β)
    (x z : ℤ) (hc : Central r r β (runPacket x 0 z))
    (hz : 1 ≤ z) (hzr : z < (r : ℤ)) :
    Progress r β (runPacket x 0 z) := by
  rcases BHDiagonalAxis.positive_axis_progress h x z hc hz hzr with hp | hp
  · exact Or.inl ⟨BHDiagonalLiteral.zero00, hp, rfl, rfl⟩
  · obtain ⟨q, hpath, hcentral, he⟩ := hp
    refine Or.inr ⟨q, hpath, hcentral, ?_⟩
    simpa [runPacket] using he

/-- Both signs of the entire residual axis are covered, including full
zero-pair cleanup and the strict unit excursion. -/
theorem axis_progress {r β} (h : BHDiagonalLiteral.Family r β) (x z : ℤ)
    (hc : Central r r β (runPacket x 0 z))
    (hdisk : (z : ℝ)^2 < (r : ℝ)^2) :
    Progress r β (runPacket x 0 z) := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hzr : z < (r : ℤ) := by
    have hzreal : (z : ℝ) < r := by nlinarith
    exact_mod_cast hzreal
  have hnzr : -z < (r : ℤ) := by
    have hzreal : -(z : ℝ) < r := by nlinarith
    exact_mod_cast hzreal
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have hc' : Central r r β (runPacket (-x) 0 (-z)) := by
      simpa only [runPacket_swap, neg_zero] using central_swap hc
    have hp := (positive_axis_progress h (-x) (-z) hc' (by omega) hnzr).swap
    simpa only [runPacket_swap, neg_neg, neg_zero] using hp
  · exact Or.inl (zero_pair_exit h x hc)
  · exact positive_axis_progress h x z hc (by omega) hzr

theorem one_step_progress {r β} (h : BHDiagonalLiteral.Family r β)
    (x y z t : ℤ) (hc : Central r r β (runPacket x y z))
    (ht : |(t : ℝ)+((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β)
    (he : energy (β-r) (r/β) y t < energy (β-r) (r/β) z y) :
    Progress r β (runPacket x y z) := by
  obtain ⟨hs, hc'⟩ := BHDiagonalLiteral.literal_rounding_step h x y z t hc ht
  exact Or.inr ⟨_, .single hs, hc', he⟩

theorem first_pair_progress {N : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family (3*N) β) (x : ℤ)
    (hc : Central (3*N) (3*N) β (runPacket x N ((N : ℤ)-1))) :
    Progress (3*N) β (runPacket x N ((N : ℤ)-1)) := by
  obtain ⟨hp, hc'⟩ := BHDiagonalDescent.first_pair_literal_path h x hc
  refine Or.inr ⟨_, hp, hc', ?_⟩
  simpa [runPacket] using
    BHDiagonalDescent.first_pair_decreases (BHDiagonalDescent.family_block_parameters h)

theorem second_pair_progress {N : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family (3*N) β) (x : ℤ)
    (hc : Central (3*N) (3*N) β (runPacket x (-(N : ℤ)) ((N : ℤ)+2))) :
    Progress (3*N) β (runPacket x (-(N : ℤ)) ((N : ℤ)+2)) := by
  obtain ⟨hp, hc'⟩ := BHDiagonalDescent.second_pair_literal_path h x hc
  refine Or.inr ⟨_, hp, hc', ?_⟩
  simpa [runPacket] using
    BHDiagonalDescent.second_pair_decreases (BHDiagonalDescent.family_block_parameters h)

theorem neg_first_pair_progress {N : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family (3*N) β) (x : ℤ)
    (hc : Central (3*N) (3*N) β
      (runPacket x (-(N : ℤ)) (-((N : ℤ)-1)))) :
    Progress (3*N) β (runPacket x (-(N : ℤ)) (-((N : ℤ)-1))) := by
  have hc' : Central (3*N) (3*N) β (runPacket (-x) N ((N : ℤ)-1)) := by
    simpa only [runPacket_swap, neg_neg] using central_swap hc
  have hp := (first_pair_progress h (-x) hc').swap
  simpa only [runPacket_swap, neg_neg] using hp

theorem neg_second_pair_progress {N : ℕ} {β : ℝ}
    (h : BHDiagonalLiteral.Family (3*N) β) (x : ℤ)
    (hc : Central (3*N) (3*N) β (runPacket x N (-((N : ℤ)+2)))) :
    Progress (3*N) β (runPacket x N (-((N : ℤ)+2))) := by
  have hc' : Central (3*N) (3*N) β
      (runPacket (-x) (-(N : ℤ)) ((N : ℤ)+2)) := by
    simpa only [runPacket_swap, neg_neg] using central_swap hc
  have hp := (second_pair_progress h (-x) hc').swap
  simpa only [runPacket_swap, neg_neg] using hp

/-- The actual arithmetic classification and the literal signed blocks
jointly cover every full run packet in the residual disk. -/
theorem run_packet_residual_progress {r β} (h : BHDiagonalLiteral.Family r β)
    (x y z : ℤ) (hc : Central r r β (runPacket x y z))
    (hdisk : (z : ℝ)^2+(y : ℝ)^2 < (r : ℝ)^2) :
    Progress r β (runPacket x y z) := by
  rcases BHDiagonalClassificationFull.residual_classification h z y hdisk with
    ⟨t, ht, he⟩ | hy | ⟨N, hr, hshape⟩
  · exact one_step_progress h x y z t hc ht he
  · subst y
    exact axis_progress h x z hc (by simpa using hdisk)
  · subst r
    rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact first_pair_progress h x hc
    · exact second_pair_progress h x hc
    · have hc' : Central (3*N) (3*N) β
          (runPacket x (-(N : ℤ)) (-((N : ℤ)-1))) := by
        simpa only [neg_sub] using hc
      simpa only [neg_sub] using neg_first_pair_progress h x hc'
    · have heq : -(N : ℤ)-2 = -((N : ℤ)+2) := by ring
      rw [heq] at hc ⊢
      exact neg_second_pair_progress h x hc

/-- Full residual progress, with no certificate or classification premise. -/
theorem residual_progress {r β} (h : BHDiagonalLiteral.Family r β) {p : Packet}
    (hc : Central r r β p)
    (hdisk : (p.delta 2 : ℝ)^2+(p.delta 1 : ℝ)^2 < (r : ℝ)^2) :
    Progress r β p := by
  have hp := packet_from_central hc
  have hc' : Central r r β (runPacket (p.delta 0) (p.delta 1) (p.delta 2)) := by
    rw [← hp]
    exact hc
  have result := run_packet_residual_progress h (p.delta 0) (p.delta 1) (p.delta 2)
    hc' hdisk
  rwa [← hp] at result

end Psc.BHDiagonalProgress
