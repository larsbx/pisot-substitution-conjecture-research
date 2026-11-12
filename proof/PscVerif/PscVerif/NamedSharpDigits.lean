import PscVerif.NamedPrefixCompact

/-!
# Complete sharp digit bounds for the original named substitutions

Signed integer prefix summaries compose over the actual literal substitution
words. The kernel checks the complete block-twelve summaries, with no sampled
prefixes, floating point, external digit table or native-reduction axiom.
The mathematical bound applies to every full literal mark, including repeated
letters. This file supplies digit bounds, not a finite graph/domain identity.

Pre-code gate: `docs/c4-archived-graph-refinement-literature-2026-11-11.md`.
-/

namespace Psc.NamedSharpDigits

open Psc.Binomial Psc.Incidence Psc.OccurrenceTransport Psc.OccurrenceInverse
open Psc.NamedStableChart Psc.NamedStableContraction Psc.NamedPrefixCompact

/-- A signed sum and enclosing bounds for every prefix, including both
endpoints. Including the final prefix only strengthens the digit contract. -/
structure PrefixSummary where
  total : ℤ
  lower : ℤ
  upper : ℤ
  deriving DecidableEq

def prefixScore (weight : Fin 3 → ℤ) (w : Word) : ℤ := (w.map weight).sum

theorem prefixScore_append (weight : Fin 3 → ℤ) (u v : Word) :
    prefixScore weight (u ++ v) = prefixScore weight u + prefixScore weight v := by
  simp [prefixScore]

def PrefixSummary.Covers (r : PrefixSummary) (weight : Fin 3 → ℤ) (w : Word) : Prop :=
  r.total = prefixScore weight w ∧
    ∀ u, u <+: w → r.lower ≤ prefixScore weight u ∧ prefixScore weight u ≤ r.upper

def emptySummary : PrefixSummary := ⟨0, 0, 0⟩

def singletonSummary (z : ℤ) : PrefixSummary := ⟨z, min 0 z, max 0 z⟩

def appendSummary (r t : PrefixSummary) : PrefixSummary :=
  ⟨r.total + t.total, min r.lower (r.total + t.lower),
    max r.upper (r.total + t.upper)⟩

theorem emptySummary_covers (weight : Fin 3 → ℤ) :
    emptySummary.Covers weight [] := by
  constructor
  · rfl
  · intro u hu
    have he : u = [] := List.prefix_nil.mp hu
    subst u
    exact ⟨le_refl _, le_refl _⟩

theorem singletonSummary_covers (weight : Fin 3 → ℤ) (a : Fin 3) :
    (singletonSummary (weight a)).Covers weight [a] := by
  constructor
  · simp [singletonSummary, prefixScore]
  · intro u hu
    rcases List.prefix_cons_iff.mp hu with rfl | ⟨v, rfl, hv⟩
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · have he : v = [] := List.prefix_nil.mp hv
      subst v
      simpa [singletonSummary, prefixScore] using
        And.intro (min_le_right (0 : ℤ) (weight a)) (le_max_right (0 : ℤ) (weight a))

/-- Prefixes of a concatenation are either prefixes of its first word or
the first word followed by a prefix of its second. -/
theorem appendSummary_covers (weight : Fin 3 → ℤ) (u v : Word)
    (r t : PrefixSummary) (hr : r.Covers weight u) (ht : t.Covers weight v) :
    (appendSummary r t).Covers weight (u ++ v) := by
  constructor
  · simpa [appendSummary, prefixScore_append] using congrArg₂ (· + ·) hr.1 ht.1
  · intro p hp
    rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append u v) with hpu | hup
    · obtain ⟨hl, hh⟩ := hr.2 p hpu
      exact ⟨(min_le_left _ _).trans hl, hh.trans (le_max_left _ _)⟩
    · obtain ⟨q, rfl⟩ := hup
      have hq : q <+: v := (List.prefix_append_right_inj u).mp hp
      obtain ⟨hl, hh⟩ := ht.2 q hq
      rw [prefixScore_append]
      constructor
      · calc
          _ ≤ r.total + t.lower := min_le_right _ _
          _ ≤ _ := by rw [hr.1]; exact add_le_add (le_refl _) hl
      · calc
          _ ≤ r.total + t.upper := by rw [hr.1]; exact add_le_add (le_refl _) hh
          _ ≤ _ := le_max_right _ _

/-- Compose summaries in literal word order. Repeated letters are visited
once per position, as required by the source word. -/
def wordSummary (r : Fin 3 → PrefixSummary) : Word → PrefixSummary
  | [] => emptySummary
  | a :: w => appendSummary (r a) (wordSummary r w)

theorem wordSummary_covers (weight : Fin 3 → ℤ) (s : Fin 3 → Word)
    (r : Fin 3 → PrefixSummary) (hr : ∀ a, (r a).Covers weight (s a))
    (w : Word) : (wordSummary r w).Covers weight (subst s w) := by
  induction w with
  | nil => exact emptySummary_covers weight
  | cons a w ih =>
      simpa only [wordSummary, subst_cons] using
        appendSummary_covers weight (s a) (subst s w) (r a) (wordSummary r w) (hr a) ih

/-- Dynamic composition over actual images, rather than enumerating all
long prefixes independently. The soundness theorem binds it to `iterateImages`. -/
def blockSummary (s : Fin 3 → Word) (weight : Fin 3 → ℤ) : ℕ → Fin 3 → PrefixSummary
  | 0 => fun a => singletonSummary (weight a)
  | k + 1 => fun a => wordSummary (blockSummary s weight k) (s a)

theorem blockSummary_covers (s : Fin 3 → Word) (weight : Fin 3 → ℤ)
    (k : ℕ) (a : Fin 3) :
    (blockSummary s weight k a).Covers weight (iterateImages s k a) := by
  induction k generalizing a with
  | zero => exact singletonSummary_covers weight a
  | succ k ih =>
      have hc := wordSummary_covers weight (iterateImages s k)
        (blockSummary s weight k) ih (s a)
      have he : subst (iterateImages s k) (s a) = iterateImages s (k + 1) a := by
        change subst (power s k) (s a) = (subst s)^[k + 1] [a]
        rw [subst_power, Function.iterate_succ_apply]
        simp [subst]
      simpa only [he, blockSummary] using hc

/-- The four rational endpoints bound the exact named real chart. -/
def endpointWeight (j : Fin 4) : Fin 3 → ℤ :=
  ![![1000000, -828911, 0], ![1000000, -828912, 0],
    ![0, -440619, 1000000], ![0, -440620, 1000000]] j

def endpointLimit (j : Fin 4) : ℤ := ![4600000, 4600000, 2800000, 2800000] j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Complete source-bound finite arithmetic. Each of the two literal
substitutions and all three block words are checked at every chart endpoint. -/
theorem endpoints_authenticated (fixture : Fin 2) (j : Fin 4) (a : Fin 3) :
    -(endpointLimit j) ≤ (blockSummary (substitution fixture) (endpointWeight j) 12 a).lower ∧
      (blockSummary (substitution fixture) (endpointWeight j) 12 a).upper ≤ endpointLimit j := by
  fin_cases fixture <;> fin_cases j <;> fin_cases a <;> decide +kernel

/-- Every literal mark inherits the complete prefix summary bound. -/
theorem mark_endpoint_bounds (fixture : Fin 2) (j : Fin 4) (a : Fin 3)
    (d : Mark (iterateImages (substitution fixture) 12 a)) :
    -(endpointLimit j) ≤ prefixScore (endpointWeight j) d.before ∧
      prefixScore (endpointWeight j) d.before ≤ endpointLimit j := by
  have hp : d.before <+: iterateImages (substitution fixture) 12 a :=
    ⟨d.letter :: d.after, d.split.symm⟩
  have hb := (blockSummary_covers (substitution fixture) (endpointWeight j) 12 a).2 d.before hp
  have he := endpoints_authenticated fixture j a
  exact ⟨he.1.trans hb.1, hb.2.trans he.2⟩

theorem prefixScore_counts (weight : Fin 3 → ℤ) (w : Word) :
    prefixScore weight w = weight 0 * parikhZ w 0 + weight 1 * parikhZ w 1 +
      weight 2 * parikhZ w 2 := by
  induction w with
  | nil => simp [prefixScore, parikhZ]
  | cons a w ih =>
      simp only [prefixScore, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      fin_cases a <;> simp [parikhZ, List.count_cons, mul_add] <;> ring

/-- Convert a complete signed endpoint enclosure to the actual chart value.
The nonnegative middle count is essential to the interval comparison. -/
theorem real_bound_of_integer_endpoints (x y : ℤ) (lo hi bound : ℤ) (t : ℝ)
    (hy : 0 ≤ y) (htlo : (lo : ℝ) / 1000000 ≤ t)
    (hthi : t ≤ (hi : ℝ) / 1000000)
    (hl : -bound ≤ 1000000 * x - hi * y)
    (hu : 1000000 * x - lo * y ≤ bound) :
    |(x : ℝ) - t * y| ≤ (bound : ℝ) / 1000000 := by
  have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hlR : -(bound : ℝ) ≤ 1000000 * (x : ℝ) - hi * (y : ℝ) := by exact_mod_cast hl
  have huR : 1000000 * (x : ℝ) - lo * (y : ℝ) ≤ bound := by exact_mod_cast hu
  have hmulL := mul_le_mul_of_nonneg_right htlo hyR
  have hmulU := mul_le_mul_of_nonneg_right hthi hyR
  rw [abs_le]
  constructor <;> nlinarith

/-- Complete sharp coordinate digit bounds for every original block-twelve
mark. No numerical premise or selected occurrence set remains. -/
theorem mark_coordinate_bound (fixture : Fin 2) (letter : Fin 3)
    (d : Mark (iterateImages (substitution fixture) 12 letter)) :
    |piZ (parikhZ d.before) 0| ≤ (23 : ℝ) / 5 ∧
      |piZ (parikhZ d.before) 1| ≤ (14 : ℝ) / 5 := by
  have h0 := mark_endpoint_bounds fixture 0 letter d
  have h1 := mark_endpoint_bounds fixture 1 letter d
  have h2 := mark_endpoint_bounds fixture 2 letter d
  have h3 := mark_endpoint_bounds fixture 3 letter d
  simp only [prefixScore_counts] at h0 h1 h2 h3
  norm_num [endpointWeight, endpointLimit] at h0 h1 h2 h3
  have hy : 0 ≤ parikhZ d.before 1 := Int.natCast_nonneg _
  obtain ⟨⟨hal, hau⟩, ⟨hbl, hbu⟩⟩ := chart_coarse_bounds
  have ha := real_bound_of_integer_endpoints (parikhZ d.before 0) (parikhZ d.before 1)
    828911 828912 4600000 a hy (by linarith) (by linarith) (by linarith [h1.1]) (by linarith [h0.2])
  have hb := real_bound_of_integer_endpoints (parikhZ d.before 2) (parikhZ d.before 1)
    440619 440620 2800000 b hy (by linarith) (by linarith) (by linarith [h3.1]) (by linarith [h2.2])
  simp only [piZ_apply, W_mulVec]
  norm_num [castZ] at ha hb ⊢
  exact ⟨ha, hb⟩

end Psc.NamedSharpDigits
