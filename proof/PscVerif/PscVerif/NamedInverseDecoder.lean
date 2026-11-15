import PscVerif.NamedFiniteCarrier

/-!
# Exact integer inverse decoder for the original named block-two action

The adjugate divisibility test is equivalent to the full `M^2` lattice
condition. Its divided vector is unique. This authenticates the historical
residue exclusion in the original matrix-adic factor, without replacing it
by coordinatewise reduction or changing the substitution period.

Pre-code gate: `docs/c4-archived-graph-refinement-literature-2026-11-11.md`.
-/

namespace Psc.NamedInverseDecoder

open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrencePiece
open Psc.OccurrenceResidue Psc.NamedStableChart Psc.NamedPrefixCompact
open Psc.NamedFiniteCarrier Matrix

/-- Half-adjugate numerator; the actual adjugate numerator is twice this. -/
def numerator (z : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![3 * z 2 - z 1, z 0 - z 2, z 1 - z 0]

def inverse (z : Fin 3 → ℤ) : Fin 3 → ℤ := fun i => numerator z i / 2

/-- All three exact divisibility checks; no coordinate is silently dropped. -/
def ResidueValid (z : Fin 3 → ℤ) : Prop := ∀ i, numerator z i % 2 = 0

instance (z : Fin 3 → ℤ) : Decidable (ResidueValid z) := by
  unfold ResidueValid
  infer_instance

def check (z : Fin 3 → ℤ) : Bool := decide (ResidueValid z)

theorem check_iff (z : Fin 3 → ℤ) : check z = true ↔ ResidueValid z := by
  simp [check]

/-- The native adjugate numerator divided by four is exactly this decoder. -/
theorem adjugate_eq : (MZ ^ 2).adjugate =
    !![0, -2, 6; 2, 0, -2; -2, 2, 0] := by
  rw [MZ_pow_two]
  decide +kernel

/-- Integer modulo-four checks on the actual adjugate are equivalent to
all three modulo-two checks, including negative inputs. -/
theorem adjugate_divisibility_iff (z : Fin 3 → ℤ) :
    (∀ i, ((MZ ^ 2).adjugate *ᵥ z) i % 4 = 0) ↔ ResidueValid z := by
  rw [adjugate_eq]
  simp only [ResidueValid]
  constructor <;> intro h i
  · have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    fin_cases i <;> simp [numerator, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at * <;> omega
  · have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    fin_cases i <;> simp [numerator, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at * <;> omega

/-- An accepted exact residue decodes to a genuine integral inverse. -/
theorem inverse_equation (z : Fin 3 → ℤ) (h : ResidueValid z) :
    MZ ^ 2 *ᵥ inverse z = z := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rw [MZ_pow_two]
  ext i
  fin_cases i <;>
    simp [inverse, numerator, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at * <;> omega

/-- The residue condition is necessary for every integral inverse, with
its complete three-coordinate equation. -/
theorem residueValid_of_equation (z u : Fin 3 → ℤ) (h : MZ ^ 2 *ᵥ u = z) :
    ResidueValid z := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rw [MZ_pow_two] at h0 h1 h2
  intro i
  fin_cases i <;>
    simp [numerator, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at * <;> omega

/-- Complete lattice reflection, not just a sufficient divisibility filter. -/
theorem residueValid_iff_range (z : Fin 3 → ℤ) :
    ResidueValid z ↔ ∃ u : Fin 3 → ℤ, MZ ^ 2 *ᵥ u = z :=
  ⟨fun h => ⟨inverse z, inverse_equation z h⟩,
    fun ⟨u, h⟩ => residueValid_of_equation z u h⟩

/-- There is one and only one integral inverse offset. -/
theorem inverse_unique (z u : Fin 3 → ℤ) (h : MZ ^ 2 *ᵥ u = z) : u = inverse z := by
  have hi : Function.Injective (fun x : Fin 3 → ℤ => MZ ^ 2 *ᵥ x) :=
    Matrix.mulVec_injective_of_det_ne_zero (by rw [Matrix.det_pow, MZ_det]; norm_num)
  exact hi (h.trans (inverse_equation z (residueValid_of_equation z u h)).symm)

/-- The same exact range is used for each original literal block substitution. -/
theorem named_check_iff_range (fixture : Fin 2) (z : Fin 3 → ℤ) :
    check z = true ↔ ∃ u : Fin 3 → ℤ,
      incidenceZ (iterateImages (substitution fixture) 2) *ᵥ u = z := by
  rw [check_iff, incidenceZ_iterateImages, incidence_eq]
  exact residueValid_iff_range z

/-- Literal inverse occurrences decode to that unique offset. The full
parent words and both marks remain in the source-bound equation. -/
theorem occurrence_offset (fixture : Fin 2) {p u : Packet}
    (e : InverseOccurrence (iterateImages (substitution fixture) 2) p u) :
    check (p.delta + residual e.bottomMark.before e.topMark.before) = true ∧
      u.delta = inverse (p.delta + residual e.bottomMark.before e.topMark.before) := by
  have h := e.iterate_equation (substitution fixture) 2
  rw [incidence_eq] at h
  exact ⟨(check_iff _).mpr (residueValid_of_equation _ _ h), inverse_unique _ _ h⟩

/-- Rejection removes an empty original paired cylinder through the proved
matrix-adic range detector. Integer division alone is not the reason for emptiness. -/
theorem pairedPiece_empty_of_check_false (fixture : Fin 2) (p : Packet)
    {a b : Fin 3} (dt : Mark (iterateImages (substitution fixture) 2 a))
    (db : Mark (iterateImages (substitution fixture) 2 b))
    (rejected : check (p.delta + residual db.before dt.before) = false) :
    pairedPiece (ambientAction (substitution fixture) B ^ 2)
      (ambientStar (substitution fixture) piZ) (tiles fixture) p dt db = ∅ := by
  apply pairedPiece_empty_of_nonintegral _ _ _ (block_reflectsIntegralRange fixture 2)
  intro hex
  have ht := (named_check_iff_range fixture _).mpr hex
  rw [rejected] at ht
  contradiction

/-- The lattice contains odd vectors; coordinatewise evenness is an invalid substitute. -/
theorem odd_vector_is_integral :
    check (![1, 1, 1] : Fin 3 → ℤ) = true ∧
      inverse (![1, 1, 1] : Fin 3 → ℤ) = ![1, 0, 0] := by
  constructor <;> decide +kernel

/-- A unit vector outside the image cannot be admitted by ignoring a residue coordinate. -/
theorem nonintegral_vector_refused :
    check (![1, 0, 0] : Fin 3 → ℤ) = false := by decide +kernel

end Psc.NamedInverseDecoder
