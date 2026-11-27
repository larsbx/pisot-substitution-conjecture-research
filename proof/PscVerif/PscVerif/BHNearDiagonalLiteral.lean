import PscVerif.BHNearDiagonalDescent
import PscVerif.OccurrenceMass

/-!
# Actual run children in the two near-diagonal determinant bands

Each admissible integer update is realized by two original marks in the
long runs of the image of 1. Both types and all three coordinates are
retained. The general boundary entry is a separate geometric obligation.
-/

namespace Psc.BHNearDiagonalLiteral

open Psc.Binomial Psc.Incidence Psc.OccurrenceTransport Psc.OccurrenceSuccessor
open Psc.OccurrenceNewborn Psc.BHNearDiagonalDescent Matrix
open scoped BigOperators

def sigma (r k : ℕ) : Fin 3 → Word :=
  ![[1], 0 :: (List.replicate k 1 ++ [2]), List.replicate r 0 ++ [1]]

noncomputable def lengths (r : ℕ) (β : ℝ) : Fin 3 → ℝ := ![1, β, 1 + r / β]

structure Family (r k : ℕ) (β : ℝ) : Prop where
  large : 12 ≤ r
  above : r + 1 ≤ k
  below : k ≤ r + 2
  lower : (k : ℝ) < β
  upper : β < (k : ℝ) + 1
  cubic : β ^ 3 = (k : ℝ) * β ^ 2 + 2 * β + r

theorem beta_gt_thirteen {r k β} (h : Family r k β) : 13 < β := by
  have hk : 13 ≤ k := by have := h.large; have := h.above; omega
  exact (by exact_mod_cast hk : (13 : ℝ) ≤ k).trans_lt h.lower

theorem quadratic_eq {r k β} (h : Family r k β) : β ^ 2 = k * β + 2 + r / β := by
  have hb : β ≠ 0 := ne_of_gt (by linarith [beta_gt_thirteen h] : 0 < β)
  apply mul_right_cancel₀ hb
  calc
    β ^ 2 * β = β ^ 3 := by ring
    _ = (k : ℝ) * β ^ 2 + 2 * β + r := h.cubic
    _ = (k * β + 2 + r / β) * β := by rw [add_mul, div_mul_cancel₀ _ hb]; ring

theorem family_window {r k β} (h : Family r k β) :
    Window (β-k) (r/β) (((k : ℝ)-1)/β) := by
  have h13 := beta_gt_thirteen h
  have hβ : 0 < β := by linarith
  have hgap1 : (r : ℝ) + 1 ≤ k := by exact_mod_cast h.above
  have hgap2 : (k : ℝ) ≤ r + 2 := by exact_mod_cast h.below
  have hr : (12 : ℝ) ≤ r := by exact_mod_cast h.large
  have hb1 : (r : ℝ)/β < 1 := (div_lt_one hβ).mpr (by linarith [h.lower])
  have hb4 : 4/5 < (r : ℝ)/β := (lt_div_iff₀ hβ).mpr (by linarith [h.upper])
  have ha : (β-(k : ℝ))*β = 2 + r/β := by nlinarith only [quadratic_eq h]
  have ha1 : β-(k : ℝ) < 1/4 := by
    apply lt_of_mul_lt_mul_right _ hβ.le
    rw [ha]
    linarith
  have hmul : ((r : ℝ)/β)*β = r := div_mul_cancel₀ _ hβ.ne'
  refine ⟨sub_nonneg.mpr h.lower.le, ha1, hb4, hb1, ?_, ?_, ?_, ?_⟩
  · apply (le_of_mul_le_mul_right _ hβ)
    rw [add_mul, ha, hmul, one_mul]
    linarith
  · apply (le_of_mul_le_mul_right _ hβ)
    calc
      (β-(k : ℝ))*β = 2+r/β := ha
      _ ≤ 3*(β-r) := by linarith [h.lower]
      _ = 3*(1-r/β)*β := by nlinarith only [hmul]
  · exact div_le_div_of_nonneg_right (by linarith) hβ.le
  · exact (div_lt_one hβ).mpr (by linarith [h.lower])

private theorem physical_replicate (ℓ : Fin 3 → ℝ) (n : ℕ) (a : Fin 3) :
    physicalLength ℓ (List.replicate n a) = n * ℓ a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.cast_succ, add_mul, add_comm]

theorem lengths_ge_one {r k β} (h : Family r k β) (a : Fin 3) :
    1 ≤ lengths r β a := by
  have hwin := family_window h
  fin_cases a <;> simp [lengths] <;> linarith [beta_gt_thirteen h, hwin.b_large]

theorem lengths_scale {r k β} (h : Family r k β) (a : Fin 3) :
    physicalLength (lengths r β) (sigma r k a) = β * lengths r β a := by
  have hβ : β ≠ 0 := ne_of_gt (by linarith [beta_gt_thirteen h] : 0 < β)
  have hb : (r : ℝ)/β * β = r := div_mul_cancel₀ _ hβ
  fin_cases a
  · simp [sigma, lengths]
  · simp [sigma, lengths, physical_replicate]
    nlinarith only [quadratic_eq h]
  · simp [sigma, lengths, physical_replicate]
    nlinarith only [hb]

def runPacket (x y z : ℤ) : Packet := ⟨1, 1, ![x, y, z]⟩

def Central (r k : ℕ) (β : ℝ) (p : Packet) : Prop :=
  p.top = 1 ∧ p.bottom = 1 ∧ |offset (lengths r β) p.delta| ≤ (k : ℝ) - 1

theorem offset_run (r : ℕ) (β : ℝ) (x y z : ℤ) :
    offset (lengths r β) (runPacket x y z).delta =
      (x : ℝ) + β*y + (1+r/β)*z := by
  simp [offset, dotProduct, Fin.sum_univ_three, lengths, runPacket]

private def runMark (r k i : ℕ) (hi : i < k) : Mark (sigma r k 1) where
  before := 0 :: List.replicate i 1
  letter := 1
  after := List.replicate (k-i-1) 1 ++ [2]
  split := by
    have hk : i + ((k-i-1)+1) = k := by omega
    have hr : List.replicate k (1 : Fin 3) =
        List.replicate i 1 ++ 1 :: List.replicate (k-i-1) 1 := by
      rw [← List.replicate_succ, ← List.replicate_add, hk]
    simp only [sigma, Matrix.cons_val_one, Matrix.cons_val_zero, List.cons_append]
    rw [hr]
    simp [List.append_assoc]

private theorem ordinals_of_difference {k : ℕ} (hk : 0 < k) (d : ℤ)
    (hleft : -(k : ℤ) < d) (hright : d < (k : ℤ)) :
    ∃ i j : ℕ, i < k ∧ j < k ∧ (i : ℤ) - (j : ℤ) = d := by
  by_cases hd : 0 ≤ d
  · exact ⟨d.toNat, 0, by omega, hk, by omega⟩
  · exact ⟨0, (-d).toNat, hk, by omega, by omega⟩

private theorem incidence_run (r k : ℕ) (x y z : ℤ) :
    incidenceZ (sigma r k) *ᵥ (runPacket x y z).delta =
      ![y + (r : ℤ)*z, x+(k : ℤ)*y+z, y] := by
  funext i
  fin_cases i <;> simp [incidenceZ, inc, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    sigma, List.count_replicate, runPacket, add_assoc]

private theorem run_residual (r k i j : ℕ) (hi : i < k) (hj : j < k) :
    residual (runMark r k i hi).before (runMark r k j hj).before =
      ![0, (i : ℤ)-(j : ℤ), 0] := by
  funext a
  fin_cases a <;> simp [runMark, OccurrenceTransport.residual, parikhZ, List.count_replicate]

/-- Each chosen integer update inside the window is a strict ordered child
at genuine positions of the two copies of the image of 1. -/
theorem literal_rounding_step {r k β} (h : Family r k β) (x y z t : ℤ)
    (hsource : Central r k β (runPacket x y z))
    (ht : |(t : ℝ) + ((β-k)*y+(r/β)*z)| ≤ ((k : ℝ)-1)/β) :
    InteriorStep (sigma r k) (lengths r β) (runPacket x y z)
      (runPacket (y+(r : ℤ)*z) t y) ∧ Central r k β (runPacket (y+(r : ℤ)*z) t y) := by
  have hβ : 0 < β := by linarith [beta_gt_thirteen h]
  have hwidth : ((k : ℝ)-1)/β < 1 := (family_window h).window_lt_one
  let d := t - (x+(k : ℤ)*y+z)
  have hsh : (d : ℝ) = (t : ℝ) + ((β-k)*y+(r/β)*z) -
      offset (lengths r β) (runPacket x y z).delta := by
    rw [offset_run]
    push_cast [d]
    ring
  have hlo : -(k : ℤ) < d := by
    have hh : -(k : ℝ) < (d : ℝ) := by
      rw [hsh]
      linarith [(abs_le.mp ht).1, (abs_le.mp hsource.2.2).2]
    exact_mod_cast hh
  have hhi : d < (k : ℤ) := by
    have hh : (d : ℝ) < (k : ℝ) := by
      rw [hsh]
      linarith [(abs_le.mp ht).2, (abs_le.mp hsource.2.2).1]
    exact_mod_cast hh
  have hk : 0 < k := by have := h.above; omega
  obtain ⟨i, j, hi, hj, hd⟩ := ordinals_of_difference hk d hlo hhi
  have hscale_shift :
      offset (lengths r β) (runPacket (y+(r : ℤ)*z) t y).delta =
        β*((t : ℝ) + ((β-k)*y+(r/β)*z)) := by
    rw [offset_run]
    push_cast
    have ha : (β-(k : ℝ))*β = 2+r/β := by nlinarith only [quadratic_eq h]
    have hb : (r : ℝ)/β*β = r := div_mul_cancel₀ _ hβ.ne'
    have h₁ := congrArg (fun s : ℝ => s * (y : ℝ)) ha
    have h₂ := congrArg (fun s : ℝ => s * (z : ℝ)) hb
    nlinarith only [h₁, h₂]
  have hdst : |offset (lengths r β) (runPacket (y+(r : ℤ)*z) t y).delta| ≤ (k : ℝ)-1 := by
    rw [hscale_shift, abs_mul, abs_of_pos hβ, mul_comm]
    exact (le_div_iff₀ hβ).mp ht
  refine ⟨⟨?_, ?_⟩, rfl, rfl, hdst⟩
  · refine ⟨runMark r k i hi, runMark r k j hj, ?_⟩
    change runPacket (y+(r : ℤ)*z) t y =
      ⟨1, 1, incidenceZ (sigma r k) *ᵥ (runPacket x y z).delta +
        residual (runMark r k i hi).before (runMark r k j hj).before⟩
    rw [incidence_run, run_residual, hd]
    apply congrArg (fun d => (⟨1, 1, d⟩ : Packet))
    funext a
    fin_cases a <;> simp [d]
  · apply (Packet.interior_iff_bounds (lengths r β)
      (fun a => zero_lt_one.trans_le (lengths_ge_one h a)) _).mpr
    change -β < offset (lengths r β) (runPacket (y+(r : ℤ)*z) t y).delta ∧
      offset (lengths r β) (runPacket (y+(r : ℤ)*z) t y).delta < β
    constructor <;> linarith only [(abs_le.mp hdst).1, (abs_le.mp hdst).2, h.lower]

private theorem packet_from_central {r k β p} (hp : Central r k β p) :
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

/-- Every full integral packet in the central window has a path to the
typed zero using literal run children. -/
theorem central_hits_zero {r k β} (h : Family r k β) {p : Packet}
    (hp : Central r k β p) :
    Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β)) p (runPacket 0 0 0) := by
  let E (u : ℤ × ℤ) := energy (β-k) (r/β) u.1 u.2
  let u₀ := (p.delta 2, p.delta 1)
  let C : Set (ℤ × ℤ) := {u | E u ≤ E u₀ ∧ ∃ q,
    Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β)) p q ∧
      Central r k β q ∧ (q.delta 2, q.delta 1) = u}
  have hc0 : u₀ ∈ C := ⟨le_rfl, p, .refl, hp, rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2*E u₀+1)
  have hfin : C.Finite := by
    apply ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod
      (Set.finite_Icc (-(N : ℤ)) (N : ℤ))).subset
    rintro ⟨z, y⟩ hu
    have he : energy (β-k) (r/β) z y ≤ E u₀ := hu.1
    have hb := energy_ge_half (family_window h) (z : ℝ) (y : ℝ)
    have hz : -(N : ℝ) ≤ z ∧ (z : ℝ) ≤ N := by
      constructor <;> nlinarith only [hb, he, hN, sq_nonneg (y : ℝ),
        sq_nonneg ((z : ℝ) + 1/2), sq_nonneg ((z : ℝ) - 1/2)]
    have hy : -(N : ℝ) ≤ y ∧ (y : ℝ) ≤ N := by
      constructor <;> nlinarith only [hb, he, hN, sq_nonneg (z : ℝ),
        sq_nonneg ((y : ℝ) + 1/2), sq_nonneg ((y : ℝ) - 1/2)]
    exact ⟨⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2⟩,
      ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩⟩
  obtain ⟨u, hu, hmin⟩ := Set.exists_min_image C E hfin ⟨u₀, hc0⟩
  obtain ⟨hEU, q, hpath, hq, rfl⟩ := hu
  let x := q.delta 0
  let y := q.delta 1
  let z := q.delta 2
  have hpack : q = runPacket x y z := packet_from_central hq
  have hqc : Central r k β (runPacket x y z) := hpack ▸ hq
  by_cases hn : z ≠ 0 ∨ y ≠ 0
  · obtain ⟨t, ht, hless⟩ := choose_rounding (family_window h) z y hn
    obtain ⟨hstep, hcentral⟩ := literal_rounding_step h x y z t hqc ht
    have hm : (y, t) ∈ C := ⟨hless.le.trans hEU, _, hpath.tail (hpack.symm ▸ hstep),
      hcentral, rfl⟩
    exact (not_lt_of_ge (hmin _ hm) hless).elim
  · have hy : y = 0 := by tauto
    have hz : z = 0 := by tauto
    have ht : |((0 : ℤ) : ℝ) + ((β-k)*(y : ℝ)+(r/β)*(z : ℝ))| ≤ ((k : ℝ)-1)/β := by
      simp [hy, hz]
      linarith [(family_window h).b_large, (family_window h).b_le_window]
    have hs := (literal_rounding_step h x y z 0 hqc ht).1
    have he : InteriorStep (sigma r k) (lengths r β) q (runPacket 0 0 0) := by
      rw [hpack]
      simpa [hy, hz] using hs
    exact hpath.tail he

end Psc.BHNearDiagonalLiteral
