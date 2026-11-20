/-
# The census in Lean: the PIP3 members on three letters, and their contraction

The census surveys the substitutions on `{0, 1, 2}` with every image of length one to three,
`39³ = 59 319` specimens in the order of `pip_corpus` (`reference/psc_research/pip_screen.py`,
letters shifted by one).  Here the specimens are enumerated in Lean and filtered by the
certificate `check` of `PeriodicPartnerSpectralCertificate`:

* `mem_specimens`: every substitution with image lengths in `[1, 3]` is a specimen;
* `corpus_length`: exactly `4 554` specimens pass `check`, by kernel evaluation
  (`decide +kernel`, no `native_decide`), one declaration per first image;
* `corpus_sound`: every member of `corpus` underlies a `LengthSubst (Fin 3)` in PIP3 carrying
  the derived `PisotData`;
* `decided_of_mem`: every specimen is rejected by `refute` or accepted by `check` (kernel);
* `census`: with `refute_spec`, a substitution underlies a PIP3 length substitution iff it is
  in `corpus`.

So the `4 554` census members are exactly the PIP3 members of this class, and each carries the
contraction; the count agrees with the exact Sturm screen of `kernel/psc/pisot.mojo` and its
Python oracle, which Lean does not import.
-/
import PscVerif.PeriodicPartnerSpectralCertificate

namespace Psc.PeriodicPartnerSpectralCensus

open Psc.PeriodicPartnerHull Psc.PeriodicPartnerRealization Psc.PeriodicPartnerSpectralCertificate

/-- The `39` words of length one to three, by length, then lexicographically. -/
def words : List (List (Fin 3)) :=
  [[0], [1], [2],
   [0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2],
   [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 0], [0, 2, 1],
   [0, 2, 2], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 1, 0], [1, 1, 1], [1, 1, 2], [1, 2, 0],
   [1, 2, 1], [1, 2, 2], [2, 0, 0], [2, 0, 1], [2, 0, 2], [2, 1, 0], [2, 1, 1], [2, 1, 2],
   [2, 2, 0], [2, 2, 1], [2, 2, 2]]

theorem mem_words {w : List (Fin 3)} (h1 : 1 ≤ w.length) (h3 : w.length ≤ 3) : w ∈ words := by
  match w, h1, h3 with
  | [a], _, _ => fin_cases a <;> decide
  | [a, b], _, _ => fin_cases a <;> fin_cases b <;> decide
  | [a, b, c], _, _ => fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

/-- The specimens with first image `a`. -/
def row (a : List (Fin 3)) : List Sub3 := words.flatMap fun b => words.map fun c => (a, b, c)

/-- All `39³` specimens. -/
def specimens : List Sub3 := words.flatMap row

theorem mem_specimens {s : Sub3} (h : ∀ a, 1 ≤ (s.σ a).length ∧ (s.σ a).length ≤ 3) :
    s ∈ specimens := by
  obtain ⟨x, y, z⟩ := s
  have mx := mem_words (h 0).1 (h 0).2
  have my := mem_words (h 1).1 (h 1).2
  have mz := mem_words (h 2).1 (h 2).2
  simp only [Sub3.σ] at mx my mz
  simp only [specimens, row, List.mem_flatMap, List.mem_map]
  exact ⟨x, mx, y, my, z, mz, rfl⟩

/-- The certified specimens with first image `a`. -/
def chunk (a : List (Fin 3)) : List Sub3 := (row a).filter check

/-- The certified corpus, in census order. -/
def corpus : List Sub3 := specimens.filter check

theorem corpus_eq : corpus = words.flatMap chunk := by
  simp only [corpus, specimens, List.filter_flatMap]; rfl

/-! ### Row counts

One kernel evaluation per first image: a single evaluation of all `59 319` specimens exceeds
the memory of a 16 GB runner, and the kernel's caches are per declaration. -/

theorem row_0 : (chunk [0]).length = 0 := by decide +kernel
theorem row_1 : (chunk [1]).length = 238 := by decide +kernel
theorem row_2 : (chunk [2]).length = 238 := by decide +kernel
theorem row_00 : (chunk [0, 0]).length = 0 := by decide +kernel
theorem row_01 : (chunk [0, 1]).length = 229 := by decide +kernel
theorem row_02 : (chunk [0, 2]).length = 229 := by decide +kernel
theorem row_10 : (chunk [1, 0]).length = 229 := by decide +kernel
theorem row_11 : (chunk [1, 1]).length = 126 := by decide +kernel
theorem row_12 : (chunk [1, 2]).length = 222 := by decide +kernel
theorem row_20 : (chunk [2, 0]).length = 229 := by decide +kernel
theorem row_21 : (chunk [2, 1]).length = 222 := by decide +kernel
theorem row_22 : (chunk [2, 2]).length = 126 := by decide +kernel
theorem row_000 : (chunk [0, 0, 0]).length = 0 := by decide +kernel
theorem row_001 : (chunk [0, 0, 1]).length = 92 := by decide +kernel
theorem row_002 : (chunk [0, 0, 2]).length = 92 := by decide +kernel
theorem row_010 : (chunk [0, 1, 0]).length = 92 := by decide +kernel
theorem row_011 : (chunk [0, 1, 1]).length = 94 := by decide +kernel
theorem row_012 : (chunk [0, 1, 2]).length = 148 := by decide +kernel
theorem row_020 : (chunk [0, 2, 0]).length = 92 := by decide +kernel
theorem row_021 : (chunk [0, 2, 1]).length = 148 := by decide +kernel
theorem row_022 : (chunk [0, 2, 2]).length = 94 := by decide +kernel
theorem row_100 : (chunk [1, 0, 0]).length = 92 := by decide +kernel
theorem row_101 : (chunk [1, 0, 1]).length = 94 := by decide +kernel
theorem row_102 : (chunk [1, 0, 2]).length = 148 := by decide +kernel
theorem row_110 : (chunk [1, 1, 0]).length = 94 := by decide +kernel
theorem row_111 : (chunk [1, 1, 1]).length = 0 := by decide +kernel
theorem row_112 : (chunk [1, 1, 2]).length = 77 := by decide +kernel
theorem row_120 : (chunk [1, 2, 0]).length = 148 := by decide +kernel
theorem row_121 : (chunk [1, 2, 1]).length = 77 := by decide +kernel
theorem row_122 : (chunk [1, 2, 2]).length = 77 := by decide +kernel
theorem row_200 : (chunk [2, 0, 0]).length = 92 := by decide +kernel
theorem row_201 : (chunk [2, 0, 1]).length = 148 := by decide +kernel
theorem row_202 : (chunk [2, 0, 2]).length = 94 := by decide +kernel
theorem row_210 : (chunk [2, 1, 0]).length = 148 := by decide +kernel
theorem row_211 : (chunk [2, 1, 1]).length = 77 := by decide +kernel
theorem row_212 : (chunk [2, 1, 2]).length = 77 := by decide +kernel
theorem row_220 : (chunk [2, 2, 0]).length = 94 := by decide +kernel
theorem row_221 : (chunk [2, 2, 1]).length = 77 := by decide +kernel
theorem row_222 : (chunk [2, 2, 2]).length = 0 := by decide +kernel

/-- **The census count.** -/
theorem corpus_length : corpus.length = 4554 := by
  rw [corpus_eq, List.length_flatMap]
  simp only [words, List.map_cons, List.map_nil, row_0, row_1, row_2, row_00, row_01, row_02, row_10, row_11, row_12, row_20, row_21, row_22, row_000, row_001, row_002, row_010, row_011, row_012, row_020, row_021, row_022, row_100, row_101, row_102, row_110, row_111, row_112, row_120, row_121, row_122, row_200, row_201, row_202, row_210, row_211, row_212, row_220, row_221, row_222]
  rfl

/-- **Every certified census member is in PIP3 and carries the derived contraction.** -/
theorem corpus_sound {s : Sub3} (hs : s ∈ corpus) :
    ∃ S : LengthSubst (Fin 3), S.σ = s.σ ∧ PIP3 S ∧ Nonempty (PisotData S) :=
  sound (List.mem_filter.mp hs).2

/-! ### Completeness

Every specimen is decided: rejected by `refute` or accepted by `check`.  `refute` is cheap and
fails on only the `4 554` members, so this costs little beyond the row counts. -/

/-- A specimen is rejected by a necessary condition or accepted by the certificate. -/
def decided (s : Sub3) : Bool := refute s || check s

theorem decided_0 : (row [0]).all decided = true := by decide +kernel
theorem decided_1 : (row [1]).all decided = true := by decide +kernel
theorem decided_2 : (row [2]).all decided = true := by decide +kernel
theorem decided_00 : (row [0, 0]).all decided = true := by decide +kernel
theorem decided_01 : (row [0, 1]).all decided = true := by decide +kernel
theorem decided_02 : (row [0, 2]).all decided = true := by decide +kernel
theorem decided_10 : (row [1, 0]).all decided = true := by decide +kernel
theorem decided_11 : (row [1, 1]).all decided = true := by decide +kernel
theorem decided_12 : (row [1, 2]).all decided = true := by decide +kernel
theorem decided_20 : (row [2, 0]).all decided = true := by decide +kernel
theorem decided_21 : (row [2, 1]).all decided = true := by decide +kernel
theorem decided_22 : (row [2, 2]).all decided = true := by decide +kernel
theorem decided_000 : (row [0, 0, 0]).all decided = true := by decide +kernel
theorem decided_001 : (row [0, 0, 1]).all decided = true := by decide +kernel
theorem decided_002 : (row [0, 0, 2]).all decided = true := by decide +kernel
theorem decided_010 : (row [0, 1, 0]).all decided = true := by decide +kernel
theorem decided_011 : (row [0, 1, 1]).all decided = true := by decide +kernel
theorem decided_012 : (row [0, 1, 2]).all decided = true := by decide +kernel
theorem decided_020 : (row [0, 2, 0]).all decided = true := by decide +kernel
theorem decided_021 : (row [0, 2, 1]).all decided = true := by decide +kernel
theorem decided_022 : (row [0, 2, 2]).all decided = true := by decide +kernel
theorem decided_100 : (row [1, 0, 0]).all decided = true := by decide +kernel
theorem decided_101 : (row [1, 0, 1]).all decided = true := by decide +kernel
theorem decided_102 : (row [1, 0, 2]).all decided = true := by decide +kernel
theorem decided_110 : (row [1, 1, 0]).all decided = true := by decide +kernel
theorem decided_111 : (row [1, 1, 1]).all decided = true := by decide +kernel
theorem decided_112 : (row [1, 1, 2]).all decided = true := by decide +kernel
theorem decided_120 : (row [1, 2, 0]).all decided = true := by decide +kernel
theorem decided_121 : (row [1, 2, 1]).all decided = true := by decide +kernel
theorem decided_122 : (row [1, 2, 2]).all decided = true := by decide +kernel
theorem decided_200 : (row [2, 0, 0]).all decided = true := by decide +kernel
theorem decided_201 : (row [2, 0, 1]).all decided = true := by decide +kernel
theorem decided_202 : (row [2, 0, 2]).all decided = true := by decide +kernel
theorem decided_210 : (row [2, 1, 0]).all decided = true := by decide +kernel
theorem decided_211 : (row [2, 1, 1]).all decided = true := by decide +kernel
theorem decided_212 : (row [2, 1, 2]).all decided = true := by decide +kernel
theorem decided_220 : (row [2, 2, 0]).all decided = true := by decide +kernel
theorem decided_221 : (row [2, 2, 1]).all decided = true := by decide +kernel
theorem decided_222 : (row [2, 2, 2]).all decided = true := by decide +kernel

theorem decided_of_mem {s : Sub3} (hs : s ∈ specimens) : decided s = true := by
  have hrows : ∀ a ∈ words, (row a).all decided = true := by
    simp only [words, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨decided_0, decided_1, decided_2, decided_00, decided_01, decided_02, decided_10,
      decided_11, decided_12, decided_20, decided_21, decided_22, decided_000, decided_001,
      decided_002, decided_010, decided_011, decided_012, decided_020, decided_021,
      decided_022, decided_100, decided_101, decided_102, decided_110, decided_111,
      decided_112, decided_120, decided_121, decided_122, decided_200, decided_201,
      decided_202, decided_210, decided_211, decided_212, decided_220, decided_221,
      decided_222⟩
  obtain ⟨a, ha, hs⟩ := List.mem_flatMap.mp hs
  exact List.all_eq_true.mp (hrows a ha) s hs

/-- **Completeness.** A specimen that is the image map of a PIP3 member is in `corpus`. -/
theorem mem_corpus_of_PIP3 {s : Sub3} (hs : s ∈ specimens) {S : LengthSubst (Fin 3)}
    (hS : S.σ = s.σ) (hP : PIP3 S) : s ∈ corpus := by
  have h := decided_of_mem hs
  rw [decided, refute_spec hS hP, Bool.false_or] at h
  exact List.mem_filter.mpr ⟨hs, h⟩

/-- **The census in Lean.** For a substitution on three letters with images of length one to
three: it underlies a PIP3 length substitution iff it is one of the `4 554` members of
`corpus`; and every member carries the derived `PisotData`. -/
theorem census (σ : Fin 3 → List (Fin 3)) (hlen : ∀ a, 1 ≤ (σ a).length ∧ (σ a).length ≤ 3) :
    ((∃ S : LengthSubst (Fin 3), S.σ = σ ∧ PIP3 S) ↔ (σ 0, σ 1, σ 2) ∈ corpus) ∧
      ((σ 0, σ 1, σ 2) ∈ corpus →
        ∃ S : LengthSubst (Fin 3), S.σ = σ ∧ PIP3 S ∧ Nonempty (PisotData S)) := by
  have he : Sub3.σ (σ 0, σ 1, σ 2) = σ := by funext a; fin_cases a <;> rfl
  have hs : (σ 0, σ 1, σ 2) ∈ specimens := mem_specimens (by rw [he]; exact hlen)
  have hsound : (σ 0, σ 1, σ 2) ∈ corpus →
      ∃ S : LengthSubst (Fin 3), S.σ = σ ∧ PIP3 S ∧ Nonempty (PisotData S) := fun hc => by
    obtain ⟨S, hS, h⟩ := corpus_sound hc
    exact ⟨S, hS.trans he, h⟩
  refine ⟨⟨fun ⟨S, hS, hP⟩ => mem_corpus_of_PIP3 hs (hS.trans he.symm) hP, fun hc => ?_⟩, hsound⟩
  obtain ⟨S, hS, hP, -⟩ := hsound hc
  exact ⟨S, hS, hP⟩

/-- Tribonacci is a census member. -/
theorem tribonacci_mem_corpus : (([0, 1], [0, 2], [0]) : Sub3) ∈ corpus :=
  List.mem_filter.mpr ⟨mem_specimens (by decide), check_tribonacci⟩

end Psc.PeriodicPartnerSpectralCensus
