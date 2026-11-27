import PscVerif.BHDiagonalProgress
import PscVerif.ClassAMinusPrefixAssembly
import PscVerif.StrictSystemCore
import PscVerif.BHDiagonalAllSources

/-!
# Literal prefix coincidence consequences of the diagonal exit theorem

The source packet for letters `a,b` has full integral displacement zero.
An actual path to equal-letter zero therefore supplies original marks at
one common substitution depth with equal prefix Parikh vectors. This is
the existing left strong-coincidence predicate, with its literal word
decompositions retained. No finite balanced-pair carrier or spectral
conclusion is inferred here.
-/

namespace Psc.BHDiagonalConsequences

open Psc.Binomial Psc.OccurrenceTransport Psc.ClassAMinusPrefixAssembly
open Psc.BHNearDiagonalLiteral Psc.BHDiagonalProgress Matrix

/-- An ordered exit from zero displacement retains actual same-depth
marks, equal terminal letters, and equality of the complete prefix vectors. -/
theorem equal_prefix_marks_of_ordered_exit {s : Fin 3 → Word} (a b : Fin 3)
    {q : Packet} {xs : List (ℕ × ℕ)}
    (hpath : OrderedPath s (⟨a, b, 0⟩ : Packet) xs q)
    (hlabel : q.top = q.bottom) (hzero : q.delta = 0) :
    ∃ (top : Mark (image s xs.length a)) (bottom : Mark (image s xs.length b)),
      top.letter = bottom.letter ∧ parikhZ top.before = parikhZ bottom.before := by
  obtain ⟨top, bottom, ht, hb, he⟩ := ordered_path_original_prefixes hpath
  have hpre : parikhZ top.before = parikhZ bottom.before := by
    have hz : (0 : Fin 3 → ℤ) = parikhZ top.before-parikhZ bottom.before := by
      simpa only [hzero, Matrix.mulVec_zero, zero_add] using he
    exact sub_eq_zero.mp hz.symm
  exact ⟨top, bottom, ht.trans (hlabel.trans hb.symm), hpre⟩

/-- The original-prefix identity, specialized to labelled zero, supplies
the established strong-coincidence predicate without a realization premise. -/
theorem strong_coincidence_of_ordered_exit {s : Fin 3 → Word} (a b : Fin 3)
    {q : Packet} {xs : List (ℕ × ℕ)}
    (hpath : OrderedPath s (⟨a, b, 0⟩ : Packet) xs q)
    (hlabel : q.top = q.bottom) (hzero : q.delta = 0) :
    Psc.StrictSystem.StrongCoincidenceWitness s a b := by
  obtain ⟨top, bottom, hletter, hpre⟩ :=
    equal_prefix_marks_of_ordered_exit a b hpath hlabel hzero
  refine ⟨xs.length, top.before, top.after, bottom.before, bottom.after,
    top.letter, top.split, ?_, equiv1_of_parikhZ_eq hpre⟩
  simpa only [image, hletter] using bottom.split

/-- A diagonal labelled exit of the zero-displacement letter packet gives
actual equal-prefix marks. The path is unpacked into its genuine ordinals. -/
theorem equal_prefix_marks_of_labelled_exit {r β} (a b : Fin 3)
    (hexit : LabelledExit r β (⟨a, b, 0⟩ : Packet)) :
    ∃ (n : ℕ) (top : Mark (image (sigma r r) n a))
      (bottom : Mark (image (sigma r r) n b)),
      top.letter = bottom.letter ∧ parikhZ top.before = parikhZ bottom.before := by
  obtain ⟨q, hpath, hlabel, hzero⟩ := hexit
  have hdigit : Relation.ReflTransGen (DigitStep (sigma r r)) (⟨a, b, 0⟩ : Packet) q := by
    clear hlabel hzero
    induction hpath with
    | refl => exact .refl
    | tail _ he ih => exact ih.tail he.1
  obtain ⟨xs, hordered⟩ := digit_path_has_ordered_path hdigit
  obtain ⟨top, bottom, ht, hp⟩ :=
    equal_prefix_marks_of_ordered_exit a b hordered hlabel hzero
  exact ⟨xs.length, top, bottom, ht, hp⟩

theorem strong_coincidence_of_labelled_exit {r β} (a b : Fin 3)
    (hexit : LabelledExit r β (⟨a, b, 0⟩ : Packet)) :
    Psc.StrictSystem.StrongCoincidenceWitness (sigma r r) a b := by
  obtain ⟨n, top, bottom, hletter, hpre⟩ := equal_prefix_marks_of_labelled_exit a b hexit
  refine ⟨n, top.before, top.after, bottom.before, bottom.after,
    top.letter, top.split, ?_, equiv1_of_parikhZ_eq hpre⟩
  simpa only [image, hletter] using bottom.split

/-- The same bridge applies to any actual strict packet path whose
source has zero displacement and whose terminal packet is labelled zero. -/
theorem strong_coincidence_of_interior_exit (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (a b : Fin 3) {q : Packet}
    (hpath : Relation.ReflTransGen (InteriorStep s ℓ) (⟨a, b, 0⟩ : Packet) q)
    (hlabel : q.top = q.bottom) (hzero : q.delta = 0) :
    Psc.StrictSystem.StrongCoincidenceWitness s a b := by
  have hforget : InteriorStep s ℓ ≤ DigitStep s := fun _ _ he => he.1
  obtain ⟨xs, hordered⟩ := digit_path_has_ordered_path
    (Relation.ReflTransGen.mono hforget _ _ hpath)
  exact strong_coincidence_of_ordered_exit a b hordered hlabel hzero

theorem zero_source_interior {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (a b : Fin 3) : (⟨a, b, 0⟩ : Packet).Interior (lengths r β) := by
  have hpos : ∀ c, 0 < lengths r β c :=
    fun c => zero_lt_one.trans_le (h.lengths_ge_one c)
  apply (Packet.interior_iff_bounds _ hpos _).mpr
  change -lengths r β a < offset (lengths r β) 0 ∧
    offset (lengths r β) 0 < lengths r β b
  simpa [offset] using And.intro (neg_lt_zero.mpr (hpos a)) (hpos b)

/-- Actual same-depth original marks with equal prefix Parikh vectors
exist for every pair of source letters in the diagonal family. -/
theorem all_pairs_equal_prefix_marks {r β} (h : BHDiagonalLiteral.Family r β)
    (a b : Fin 3) :
    ∃ (n : ℕ) (top : Mark (image (sigma r r) n a))
      (bottom : Mark (image (sigma r r) n b)),
      top.letter = bottom.letter ∧ parikhZ top.before = parikhZ bottom.before :=
  equal_prefix_marks_of_labelled_exit a b
    (BHDiagonalAllSources.all_source_exit h (⟨a, b, 0⟩ : Packet)
      (zero_source_interior h.toRunFamily a b))

/-- The completed actual source exit entails left strong coincidence for
all letter pairs; equal letters are included. -/
theorem all_pairs_strong_coincidence {r β} (h : BHDiagonalLiteral.Family r β)
    (a b : Fin 3) : Psc.StrictSystem.StrongCoincidenceWitness (sigma r r) a b :=
  strong_coincidence_of_labelled_exit a b
    (BHDiagonalAllSources.all_source_exit h (⟨a, b, 0⟩ : Packet)
      (zero_source_interior h.toRunFamily a b))

/-- The root is constructed internally: only the integer parameter bound
is required for the literal word-level strong-coincidence conclusion. -/
theorem all_pairs_strong_coincidence_for_all_parameters (r : ℕ) (hr : 12 ≤ r)
    (a b : Fin 3) : Psc.StrictSystem.StrongCoincidenceWitness (sigma r r) a b := by
  obtain ⟨β, h⟩ := BHDiagonalParameters.family_root_exists r hr
  exact all_pairs_strong_coincidence h a b

/-- This excludes every finite nonempty closed system of noncoincident
irreducible balanced pairs. It supplies no finiteness hypothesis for an
arbitrary balanced-pair orbit. -/
theorem no_strict_system {r β} (h : BHDiagonalLiteral.Family r β)
    (C : Finset WordPair) : ¬ Psc.StrictSystem.StrictSystem (sigma r r) C :=
  Psc.StrictSystem.no_strictSystem_of_strongCoincidence
    (fun a b _ => all_pairs_strong_coincidence h a b) C

theorem no_strict_system_for_all_parameters (r : ℕ) (hr : 12 ≤ r)
    (C : Finset WordPair) : ¬ Psc.StrictSystem.StrictSystem (sigma r r) C :=
  Psc.StrictSystem.no_strictSystem_of_strongCoincidence
    (fun a b _ => all_pairs_strong_coincidence_for_all_parameters r hr a b) C

/-- The generic prefix bridge also applies to the two adjacent bands,
using their independently assembled actual source exit. -/
theorem three_band_strong_coincidence (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r ≤ k) (hkhi : k ≤ r+2) (a b : Fin 3) :
    Psc.StrictSystem.StrongCoincidenceWitness (sigma r k) a b := by
  obtain ⟨β, hlo, _, hc, hexit⟩ :=
    BHDiagonalAllSources.three_band_all_source_exit r k hr hklo hkhi
  have hrun : RunFamily r k β := ⟨by omega, hlo, hc⟩
  obtain ⟨q, hpath, hlabel, hzero⟩ :=
    hexit (⟨a, b, 0⟩ : Packet) (zero_source_interior hrun a b)
  exact strong_coincidence_of_interior_exit (sigma r k) (lengths r β) a b
    hpath hlabel hzero

/-- Family-specific strict-system exclusion across all three bands;
neither finite BPA nor a spectral theorem is assumed or concluded. -/
theorem three_band_no_strict_system (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r ≤ k) (hkhi : k ≤ r+2) (C : Finset WordPair) :
    ¬ Psc.StrictSystem.StrictSystem (sigma r k) C :=
  Psc.StrictSystem.no_strictSystem_of_strongCoincidence
    (fun a b _ => three_band_strong_coincidence r k hr hklo hkhi a b) C

end Psc.BHDiagonalConsequences
