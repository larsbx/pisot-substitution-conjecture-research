/-
# Descendant-span witnesses in a supplied strict carrier

This is the actual-closure specialization of `Psc.DescendantSpan`. A supplied
strict system contains every complete descendant of its members. The fixed-row
detecting witness therefore lies in that carrier and is noncoincident, with its
actual depth and list ordinal unchanged.

No strict carrier is constructed here; no geometric, legality, productivity or
common-row-existence conclusion is added. See
`docs/c4-descendant-span-dual-2026-11-10.md`.
-/
import PscVerif.DescendantSpan
import PscVerif.StrictSystem

namespace Psc.DescendantSpanStrict

open Matrix Psc.Descendants Psc.DescendantSpan Psc.StrictSystem

/-- Actual complete descendants remain in a supplied strict carrier. -/
theorem mem_of_descR {α : Type*} [DecidableEq α]
    {s : α → List α} {C : Finset (List α × List α)}
    (hC : StrictSystem s C) {T U : List α × List α} (hT : T ∈ C)
    {n : ℕ} (hU : U ∈ descR s n T) : U ∈ C :=
  hC.reflTransGen_mem hT ((reflTransGen_iff_mem_descR s).2 ⟨n, hU⟩)

/-- The local detecting occurrence retains its depth and ordinal in the
complete list and lies in the supplied coincidence-free carrier. -/
theorem exists_detecting_occurrence
    {s : Fin 3 → List (Fin 3)} {C : Finset (List (Fin 3) × List (Fin 3))}
    (hC : StrictSystem s C) (hM : Irreducible (incidenceQ s).charpoly) (n : ℕ)
    {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ C)
    (f : Fin 3 → ℚ) (hf : f ≠ 0) :
    ∃ (k j : ℕ) (U : List (Fin 3) × List (Fin 3)),
      n ≤ k ∧ k ≤ n + 2 ∧ (descR s k T)[j]? = some U ∧
      U ∈ C ∧ U.1 ≠ U.2 ∧ dotProduct f (mass U) ≠ 0 := by
  obtain ⟨k, j, U, hk, hk', hj, hrow⟩ :=
    Psc.DescendantSpan.exists_detecting_occurrence s hM n
      (hC.isBlock T hT).2.1 (hC.isBlock T hT).1 f hf
  have hU : U ∈ C := mem_of_descR hC hT (List.mem_iff_getElem?.2 ⟨j, hj⟩)
  exact ⟨k, j, U, hk, hk', hj, hU, hC.noncoincident U hU, hrow⟩

/-- A fixed rational row vanishing on a supplied strict carrier is zero under
rational irreducibility. This does not construct such a row. -/
theorem row_eq_zero_of_carrier
    {s : Fin 3 → List (Fin 3)} {C : Finset (List (Fin 3) × List (Fin 3))}
    (hC : StrictSystem s C) (hM : Irreducible (incidenceQ s).charpoly)
    (f : Fin 3 → ℚ) (hf : ∀ U ∈ C, dotProduct f (mass U) = 0) : f = 0 := by
  obtain ⟨T, hT⟩ := hC.nonempty
  apply row_eq_zero_of_window s hM 0 (hC.isBlock T hT).2.1 (hC.isBlock T hT).1 f
  intro k _ _ U hU
  exact hf U (mem_of_descR hC hT hU)

end Psc.DescendantSpanStrict
