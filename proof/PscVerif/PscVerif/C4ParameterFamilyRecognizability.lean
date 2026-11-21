import PscVerif.C4ParameterFamilyTiling
import PscVerif.PeriodicPartnerDesubContinuity

/-!
# Recognizability of the literal parameter family

A tile labelled 2 identifies a parent of type 1. The word 00 identifies a
parent of type 2. Removing these leaves the one-child parents of type 0.
-/

namespace Psc.ParameterFamilyRecognizability

open Function Set Psc.ParameterFamilyTiling Psc.PeriodicPartnerHull
open Psc.PeriodicPartnerHull.LengthSubst
open Psc.ParameterFamilyRows (substitution)
open Psc.ParameterFamilyWords (ones)
open Psc.PeriodicPartnerEvenTails (place_append)
open scoped Topology

variable {k : ℕ} {hk : 1 ≤ k}

local notation "G" => geometry k hk

private theorem place_zero (x : ℝ) : (G).place (substitution k 0) x = [(1, x)] := by
  simp [substitution, LengthSubst.place]

private theorem place_one (x : ℝ) :
    (G).place (substitution k 1) x =
      (0, x) :: ((G).place (ones k) (x + (G).ℓ 0) ++ [(2, x + (G).ℓ 0 + (k : ℝ) * (G).ℓ 1)]) := by
  simp [substitution, LengthSubst.place, place_append, ones, nsmul_eq_mul]

private theorem place_two (x : ℝ) :
    (G).place (substitution k 2) x = [(0, x), (0, x + (G).ℓ 0), (1, x + (G).ℓ 0 + (G).ℓ 0)] := by
  simp [substitution, LengthSubst.place]

private theorem place_ones_label {m : ℕ} {x : ℝ} {q : Fin 3 × ℝ}
    (hq : q ∈ (G).place (ones m) x) : q.1 = 1 := by
  induction m generalizing x with
  | zero => simp [ones, LengthSubst.place] at hq
  | succ m ih =>
    simp only [ones, List.replicate_succ, LengthSubst.place, List.mem_cons] at hq
    rcases hq with rfl | hq
    · rfl
    · exact ih hq

private theorem place_one_second (x : ℝ) :
    (1, x + (G).ℓ 0) ∈ (G).place (substitution k 1) x := by
  rw [place_one]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [ones, List.replicate_succ, LengthSubst.place]

private theorem parent_of_two {T : Set (Fin 3 × ℝ)} {x : ℝ}
    (h : (2, x + (G).ℓ 0 + (k : ℝ) * (G).ℓ 1) ∈ (G).inflate T) :
    (1, x / (G).β) ∈ T := by
  obtain ⟨⟨a, y⟩, hT, hp⟩ := h
  change (2, _) ∈ (G).place ((G).σ a) ((G).β * y) at hp
  fin_cases a
  · exfalso
    change _ ∈ (G).place (substitution k 0) _ at hp
    simp [place_zero] at hp
  · change _ ∈ (G).place (substitution k 1) _ at hp
    rw [place_one] at hp
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with h | h | ⟨_, h⟩
    · exact ((by decide : (2 : Fin 3) ≠ 0) h.1).elim
    · exact ((by decide : (2 : Fin 3) ≠ 1) (place_ones_label h)).elim
    have hy : y = x / (G).β := (eq_div_iff (G).β_pos.ne').mpr (by linarith)
    simpa [hy] using hT
  · exfalso
    change _ ∈ (G).place (substitution k 2) _ at hp
    simp [place_two] at hp

private theorem parent_of_zeros {T : Set (Fin 3 × ℝ)} (hT : (G).IsTiling T) {x : ℝ}
    (h₀ : (0, x) ∈ (G).inflate T) (h₁ : (0, x + (G).ℓ 0) ∈ (G).inflate T) :
    (2, x / (G).β) ∈ T := by
  have conflict (h : (1, x + (G).ℓ 0) ∈ (G).inflate T) : False := by
    have he := ((G).isTiling_inflate hT (x + (G).ℓ 0)).unique
      ⟨h₁, le_rfl, lt_add_of_pos_right _ ((G).ℓ_pos 0)⟩
      ⟨h, le_rfl, lt_add_of_pos_right _ ((G).ℓ_pos 1)⟩
    exact (by decide : (0 : Fin 3) ≠ 1) (congrArg Prod.fst he)
  obtain ⟨⟨a, y⟩, hy, hp⟩ := h₀
  change (0, x) ∈ (G).place ((G).σ a) ((G).β * y) at hp
  fin_cases a
  · exfalso
    change _ ∈ (G).place (substitution k 0) _ at hp
    simp [place_zero] at hp
  · change _ ∈ (G).place (substitution k 1) _ at hp
    have hx : x = (G).β * y := by
      rw [place_one] at hp
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with h | h | h
      · exact h.2
      · exact ((by decide : (0 : Fin 3) ≠ 1) (place_ones_label h)).elim
      · exact ((by decide : (0 : Fin 3) ≠ 2) h.1).elim
    subst x
    exact (conflict ⟨(1, y), hy, place_one_second ((G).β * y)⟩).elim
  · change _ ∈ (G).place (substitution k 2) _ at hp
    have h : x = (G).β * y ∨ x = (G).β * y + (G).ℓ 0 := by
      simpa [place_two] using hp
    rcases h with hx | hx
    · have hxy : y = x / (G).β := (eq_div_iff (G).β_pos.ne').mpr (by linarith)
      simpa [hxy] using hy
    · apply (conflict ⟨(2, y), hy, ?_⟩).elim
      simp [place_two, hx]

private theorem larger_parents {T U : Set (Fin 3 × ℝ)} (hU : (G).IsTiling U)
    (h : (G).inflate T = (G).inflate U) {a : Fin 3} {x : ℝ}
    (ha : a ≠ 0) (hx : (a, x) ∈ T) : (a, x) ∈ U := by
  fin_cases a
  · exact (ha rfl).elim
  · have hc : (2, (G).β * x + (G).ℓ 0 + (k : ℝ) * (G).ℓ 1) ∈ (G).inflate T :=
      ⟨(1, x), hx, by simp [place_one]⟩
    rw [h] at hc
    simpa [mul_comm (G).β x, (G).β_pos.ne'] using parent_of_two hc
  · have h₀ : (0, (G).β * x) ∈ (G).inflate T := ⟨(2, x), hx, by simp [place_two]⟩
    have h₁ : (0, (G).β * x + (G).ℓ 0) ∈ (G).inflate T := ⟨(2, x), hx, by simp [place_two]⟩
    rw [h] at h₀ h₁
    simpa [mul_comm (G).β x, (G).β_pos.ne'] using parent_of_zeros hU h₀ h₁

private theorem parent_subset {T U : Set (Fin 3 × ℝ)} (hT : (G).IsTiling T) (hU : (G).IsTiling U)
    (h : (G).inflate T = (G).inflate U) : T ⊆ U := by
  rintro ⟨a, x⟩ hp
  by_cases ha : a = 0
  · subst a
    have hc : (1, (G).β * x) ∈ (G).inflate T := ⟨(0, x), hp, by simp [place_zero]⟩
    rw [h] at hc
    obtain ⟨q, hq, hchild⟩ := hc
    have hq0 : q.1 = 0 := by
      by_contra hn
      have hqT := larger_parents hT h.symm hn (show (q.1, q.2) ∈ U from hq)
      have hsupport := (G).mem_supp_parent hchild
        (show (G).β * x ∈ (G).supp (1, (G).β * x) from
          ⟨le_rfl, lt_add_of_pos_right _ ((G).ℓ_pos 1)⟩)
      have hqcover : x ∈ (G).supp q := by
        simpa [mul_comm (G).β x, (G).β_pos.ne'] using hsupport
      exact hn (congrArg Prod.fst ((hT x).unique ⟨hqT, hqcover⟩
          ⟨hp, le_rfl, lt_add_of_pos_right _ ((G).ℓ_pos 0)⟩))
    have he : (G).β * x = (G).β * q.2 := by
      simpa only [hq0, geometry_image, place_zero, List.mem_singleton, Prod.mk.injEq,
        true_and] using hchild
    have hx : x = q.2 := mul_left_cancel₀ (G).β_pos.ne' he
    have heq : (0, x) = q := Prod.ext hq0.symm hx
    simpa only [heq] using hq
  · exact larger_parents hU h ha hp

/-- Two full-line tilings with equal inflated tile sets have the same parents. -/
theorem inflate_injective_on_tilings {T U : Set (Fin 3 × ℝ)}
    (hT : (G).IsTiling T) (hU : (G).IsTiling U) (h : (G).inflate T = (G).inflate U) : T = U :=
  subset_antisymm (parent_subset hT hU h) (parent_subset hU hT h.symm)

/-- Each legal tiling has at most one legal desubstitution. -/
theorem inflateH_injective (k : ℕ) (hk : 1 ≤ k) : Injective (inflateH (S := geometry k hk)) := by
  intro T U h
  exact Subtype.ext (inflate_injective_on_tilings T.2.1 U.2.1 (congrArg Subtype.val h))

/-- Recurrence and closedness give a legal desubstitution of every hull tiling. -/
theorem inflateH_surjective (k : ℕ) (hk : 1 ≤ k) : Surjective (inflateH (S := geometry k hk)) := by
  obtain ⟨V, -, -, -⟩ := fixed_hull_tiling k hk
  have hc : IsClosed (range (inflateH (S := geometry k hk))) := by
    simpa only [Set.image_univ] using
      (Psc.PeriodicPartnerDesubContinuity.isClosedMap_inflateH (S := geometry k hk) _ isClosed_univ)
  intro T
  apply (show closure (range (inflateH (S := geometry k hk))) ⊆ range (inflateH (S := geometry k hk))
    from hc.closure_subset_iff.mpr subset_rfl)
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨n, hn⟩ := ((geometry k hk).mem_nhds_iff_exists_agreement_subset T W).mp hW
  obtain ⟨t, ht⟩ :=
    (geometry k hk).window_occurs (expansion_gt_one k hk).le (every_letter_in_square k hk) (inflateH V) T n
  have hm : inflateH (translate (t / (geometry k hk).β) V) = translate t (inflateH V) := by
    rw [inflateH_translate, mul_div_cancel₀ t (geometry k hk).β_pos.ne']
  exact ⟨translate t (inflateH V), hn ht, ⟨translate (t / (geometry k hk).β) V, hm⟩⟩

/-- Inflation on the actual legal hull is bijective for all k ≥ 1. -/
theorem inflateH_bijective (k : ℕ) (hk : 1 ≤ k) : Bijective (inflateH (S := geometry k hk)) :=
  ⟨inflateH_injective k hk, inflateH_surjective k hk⟩

end Psc.ParameterFamilyRecognizability
