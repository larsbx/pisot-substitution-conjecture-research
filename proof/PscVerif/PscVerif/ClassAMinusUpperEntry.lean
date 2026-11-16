/-
# Literal central entry on the minus-Class-A complement

Bind the existing all-source boundary escape and the indexed central RUN
child to the same positive bracketed root. Original ordinals and strictness
are retained. Scope: docs/bh-class-a-minus-upper-entry-stopgo-2026-11-16.md.
-/
import PscVerif.ClassABoundaryEscape
import PscVerif.ClassAMinusCentralBridge

namespace Psc.ClassAMinusUpperEntry

open Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusLiteralArithmetic
open Psc.ClassAMinusPrefixAssembly Psc.ClassAMinusCentralBridge

structure UpperRoot (n d : ℕ) (β : ℝ) : Prop where
  cubic_eq_zero : cubic n d β = 0
  lower : (n : ℝ)+2 < β
  upper : β < (n : ℝ)+3

theorem complement_parameters (k t : ℕ) (ht : 6 ≤ t) :
    k+t+3+8 ≤ k+2*t+5 ∧ k+2*t+5 < 2*(k+t+3) := by omega

theorem upper_root_exists (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n) :
    ∃ β : ℝ, UpperRoot n d β := by
  have hn : (9 : ℝ) ≤ n := by exact_mod_cast (show 9 ≤ n by omega)
  have hd' : (n : ℝ)+8 ≤ d := by exact_mod_cast hd
  have hnd' : (d : ℝ)+1 ≤ 2*(n : ℝ) := by
    exact_mod_cast (show d+1 ≤ 2*n by omega)
  have hlo : cubic n d ((n : ℝ)+2) < 0 := by
    unfold cubic
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ d-n-8 by linarith)
      (show (0 : ℝ) ≤ n+2 by linarith)]
  have hhi : 0 < cubic n d ((n : ℝ)+3) := by
    unfold cubic
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2*n-d-1 by linarith)
      (show (0 : ℝ) ≤ n+3 by linarith)]
  have hcont : Continuous (cubic n d) := by unfold cubic; fun_prop
  obtain ⟨β, hβ, hc⟩ := intermediate_value_Ioo
    (show (n : ℝ)+2 ≤ (n : ℝ)+3 by linarith) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (cubic n d ((n : ℝ)+2))
      (cubic n d ((n : ℝ)+3)) from ⟨hlo, hhi⟩)
  exact ⟨β, hc, hβ.1, hβ.2⟩

theorem lengths_upper (n d : ℕ) (hd : n+8 ≤ d) (hnd : d < 2*n)
    (β : ℝ) (hroot : UpperRoot n d β) :
    ∀ a, 0 < lengths n β a := by
  have hn : (9 : ℝ) ≤ n := by exact_mod_cast (show 9 ≤ n by omega)
  have hβ1 : 1 < β := by linarith [hroot.lower]
  have hp : 0 < β := by linarith
  have hinv : 0 < β⁻¹ := inv_pos.mpr hp
  have hinv1 : β⁻¹ < 1 := by
    rw [← one_div, div_lt_iff₀ hp]
    simpa using hβ1
  intro a
  fin_cases a <;> simp [lengths] <;> linarith [hroot.lower]

/-- The three scaling equations follow from the cubic without a lower
bracket assumption. -/
theorem scaling_upper (n d : ℕ) (hn : 1 ≤ n)
    (β : ℝ) (hβ : β ≠ 0) (hc : cubic n d β = 0) :
    ∀ a, physicalLength (lengths n β) (sigma n d a) = β*lengths n β a := by
  unfold cubic at hc
  intro a
  fin_cases a <;>
    simp [sigma, first, last, runLength, physicalLength_replicate, lengths,
      Nat.cast_sub hn, Nat.cast_add]
  · field_simp
    nlinarith [hc]
  · field_simp
    ring
  · ring

theorem lengths_agree (n : ℕ) (β : ℝ) :
    ClassARunDescent.lengths (β-((n : ℝ)+2)) (1/β) = lengths n β := by
  funext a
  fin_cases a <;> simp [ClassARunDescent.lengths, lengths] <;> ring

theorem upper_central_entry (k t : ℕ) (ht : 6 ≤ t)
    (β : ℝ) (hroot : UpperRoot (k+t+3) (k+2*t+5) β)
    (p : Packet) (hp : p.Interior (lengths (k+t+3) β)) :
    ∃ (q : IntegralState) (xs : List (ℕ × ℕ)),
      OrderedInteriorPath (sigma (k+t+3) (k+2*t+5)) (lengths (k+t+3) β) p xs q.toPacket ∧
      |shift (k+t+3) β q| ≤ 1/2 := by
  let n := k+t+3
  let d := k+2*t+5
  let α := β-((n : ℝ)+2)
  let h := 1/β
  let ℓ := ClassARunDescent.lengths α h
  have hlen : ℓ = lengths n β := lengths_agree n β
  obtain ⟨hd, hnd⟩ := complement_parameters k t ht
  have hβ : 0 < β := by linarith [hroot.lower, Nat.cast_nonneg (α := ℝ) n]
  have hpos : ∀ a, 0 < ℓ a := by
    rw [hlen]
    exact lengths_upper n d hd hnd β hroot
  have hscale : ∀ a, physicalLength ℓ (sigma n d a) = β*ℓ a := by
    rw [hlen]
    exact scaling_upper n d (by dsimp [n]; omega) β hβ.ne' hroot.cubic_eq_zero
  have hp' : p.Interior ℓ := by rwa [hlen]
  have hn : 7 ≤ n := by dsimp [n]; omega
  obtain ⟨q, hpath, hg⟩ :=
    ClassABoundaryEscape.minus_class_a_strict_enters_run_gap k t hn α h β hpos hβ hscale p hp'
  obtain ⟨u,v,w, hnear, i,j, _,_,_,_, he⟩ :=
    ClassARunDescent.enters_central_run n d (by omega) α h β hpos hscale q hg.1 hg.2
  let z : IntegralState := ⟨u,w,v-2*u-w⟩
  have hnear' : |shift n β z| ≤ 1/2 := by
    have hs : shift n β z = ClassARunDescent.shift α h u v w := by
      dsimp [shift, z, ClassARunDescent.shift, α, h]
      push_cast
      ring
    rwa [hs]
  have hforget : InteriorStep (sigma n d) ℓ ≤ DigitStep (sigma n d) :=
    fun _ _ step => step.1
  have hdigit := Relation.ReflTransGen.mono hforget p q hpath
  obtain ⟨xs, hxs⟩ := digit_path_has_ordered_path hdigit
  have he' : IndexedInteriorStep (sigma n d) ℓ q i j z.toPacket := he
  have hfinal := ordered_path_indexed_interior (sigma n d) ℓ β hpos hβ hscale
    (OrderedPath.snoc hxs i j he'.1) he'.2
  rw [hlen] at hfinal
  exact ⟨z, xs ++ [(i,j)], hfinal, hnear'⟩

/-- A single positive normalized root supplies central entry uniformly
for every strict source of the literal member. -/
theorem complement_central_entry (k t : ℕ) (ht : 6 ≤ t) :
    ∃ β : ℝ, UpperRoot (k+t+3) (k+2*t+5) β ∧
      ∀ p : Packet, p.Interior (lengths (k+t+3) β) →
        ∃ (q : IntegralState) (xs : List (ℕ × ℕ)),
          OrderedInteriorPath (sigma (k+t+3) (k+2*t+5)) (lengths (k+t+3) β) p xs q.toPacket ∧
          |shift (k+t+3) β q| ≤ 1/2 := by
  obtain ⟨hd, hnd⟩ := complement_parameters k t ht
  obtain ⟨β, hroot⟩ := upper_root_exists _ _ hd hnd
  exact ⟨β, hroot, fun p => upper_central_entry k t ht β hroot p⟩

end Psc.ClassAMinusUpperEntry
