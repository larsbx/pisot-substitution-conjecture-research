/-
# Actual descendant masses and fixed-row escape

`docs/c4-descendant-span-dual-2026-11-10.md`; the pre-code decision is in
`docs/c4-finite-carrier-dual-literature-2026-11-10.md`.

The complete ordered `Psc.Descendants.descR` list retains every occurrence,
including repeated factors and children of coincidences. Its rational Parikh
mass sums to the corresponding incidence iterate. For a nonempty balanced
ternary pair and rationally irreducible incidence, the masses in every three
consecutive levels span the whole rational space. Every nonzero fixed row
therefore detects an actual occurrence, with its depth and list ordinal.

No finite carrier, primitivity, Pisot, legality, nonerasure or unimodularity
hypothesis is used. This does not construct a common row from phase-flatness,
prove a productive route, or close C4. The span theorem concerns complete
descendants, not the graph with terminal or omitted coincidence blocks.
-/
import PscVerif.Descendants
import PscVerif.Cyclicity
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace Psc.DescendantSpan

open Matrix Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants
open Psc.ParikhIntertwiner

/-! ### The ordered mass identity, over any finite alphabet -/

section Mass

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The canonical natural Parikh vector, cast to the rationals. -/
def parikhQ (w : List α) : α → ℚ := fun a => parikh w a

/-- Rational top-track mass of an actual word pair. -/
def mass (T : List α × List α) : α → ℚ := parikhQ T.1

/-- The canonical incidence matrix, cast entrywise to the rationals. -/
def incidenceQ (s : α → List α) : Matrix α α ℚ :=
  (inc s).map (Nat.cast : ℕ → ℚ)

omit [Fintype α] in
theorem parikhQ_nil : parikhQ ([] : List α) = 0 := by
  funext a
  simp [parikhQ, parikh]

omit [Fintype α] in
theorem parikhQ_append (u v : List α) :
    parikhQ (u ++ v) = parikhQ u + parikhQ v := by
  funext a
  simp [parikhQ, parikh]

omit [Fintype α] in
theorem parikhQ_flatten (ws : List (List α)) :
    parikhQ ws.flatten = (ws.map parikhQ).sum := by
  induction ws with
  | nil => simp [parikhQ_nil]
  | cons w ws ih => simp [List.flatten_cons, parikhQ_append, ih]

theorem parikhQ_subst (s : α → List α) (w : List α) :
    parikhQ (subst s w) = incidenceQ s *ᵥ parikhQ w := by
  funext a
  change ((parikh (subst s w) a : ℕ) : ℚ) = _
  rw [parikh_subst]
  exact RingHom.map_mulVec (Nat.castRingHom ℚ) (inc s) (parikh w) a

theorem parikhQ_iterate_subst (s : α → List α) (n : ℕ) (w : List α) :
    parikhQ ((subst s)^[n] w) = incidenceQ s ^ n *ᵥ parikhQ w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', parikhQ_subst, ih, pow_succ',
      ← mulVec_mulVec]

omit [Fintype α] in
theorem parikhQ_ne_zero {w : List α} (hw : w ≠ []) : parikhQ w ≠ 0 := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  have hp : 0 < parikhQ (a :: w) a := by
    change (0 : ℚ) < (((a :: w).count a : ℕ) : ℚ)
    exact_mod_cast (show 0 < (a :: w).count a by simp)
  intro h
  exact (ne_of_gt hp) (congrFun h a)

/-- The sum is a list sum: repeated equal descendants contribute repeatedly.
The balanced source need not be an irreducible block; at depth zero its
single complete mass is retained. Erasing substitutions are allowed. -/
theorem mass_sum_descR (s : α → List α) (n : ℕ)
    {T : List α × List α} (hT : Equiv1 T.1 T.2) :
    ((descR s n T).map mass).sum = incidenceQ s ^ n *ᵥ mass T := by
  cases n with
  | zero => simp [descR]
  | succ n =>
    rw [descR_succ s n hT]
    calc
      ((red ((subst s)^[n + 1] T.1) ((subst s)^[n + 1] T.2)).map mass).sum =
          parikhQ (((red ((subst s)^[n + 1] T.1)
            ((subst s)^[n + 1] T.2)).map Prod.fst).flatten) := by
        rw [parikhQ_flatten, List.map_map]
        rfl
      _ = parikhQ ((subst s)^[n + 1] T.1) := by
        rw [red_top (equiv1_iterate_subst s (n + 1) hT).length_eq]
      _ = incidenceQ s ^ (n + 1) *ᵥ mass T :=
        parikhQ_iterate_subst s (n + 1) T.1

omit [Fintype α] in
/-- The empty source has no descendant at positive depth. -/
theorem descR_empty_succ (s : α → List α) (n : ℕ) :
    descR s (n + 1) ([], []) = [] := by
  simp [descR, subst, red, redAux]

end Mass

/-! ### Consecutive three-level windows -/

/-- Actual masses in levels `n`, `n+1`, `n+2`. A set suffices for the span;
the mass identity supplying its vectors remains an ordered list sum. -/
def windowMasses (s : Fin 3 → List (Fin 3)) (n : ℕ)
    (T : List (Fin 3) × List (Fin 3)) : Set (Fin 3 → ℚ) :=
  {p | ∃ k U, n ≤ k ∧ k ≤ n + 2 ∧ U ∈ descR s k T ∧ mass U = p}

def windowSpan (s : Fin 3 → List (Fin 3)) (n : ℕ)
    (T : List (Fin 3) × List (Fin 3)) : Submodule ℚ (Fin 3 → ℚ) :=
  Submodule.span ℚ (windowMasses s n T)

theorem mass_mem_windowSpan (s : Fin 3 → List (Fin 3)) (n : ℕ)
    {T U : List (Fin 3) × List (Fin 3)} {k : ℕ}
    (hk : n ≤ k) (hk' : k ≤ n + 2) (hU : U ∈ descR s k T) :
    mass U ∈ windowSpan s n T :=
  Submodule.subset_span ⟨k, U, hk, hk', hU, rfl⟩

theorem iterate_mass_mem_windowSpan (s : Fin 3 → List (Fin 3)) (n : ℕ)
    {T : List (Fin 3) × List (Fin 3)} (hT : Equiv1 T.1 T.2)
    {k : ℕ} (hk : n ≤ k) (hk' : k ≤ n + 2) :
    incidenceQ s ^ k *ᵥ mass T ∈ windowSpan s n T := by
  rw [← mass_sum_descR s k hT]
  apply list_sum_mem
  intro p hp
  obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hp
  exact mass_mem_windowSpan s n hk hk' hU

/-- Every consecutive three levels of complete descendants span `ℚ³`.
No finite carrier or dynamical hypothesis is used. -/
theorem windowSpan_eq_top (s : Fin 3 → List (Fin 3))
    (hM : Irreducible (incidenceQ s).charpoly) (n : ℕ)
    {T : List (Fin 3) × List (Fin 3)}
    (hT : Equiv1 T.1 T.2) (hne : T.1 ≠ []) :
    windowSpan s n T = ⊤ := by
  let M := incidenceQ s
  let w := M ^ n *ᵥ mass T
  have hdet : (M ^ n).det ≠ 0 := by
    rw [det_pow]
    exact pow_ne_zero n (Psc.Cyclicity.det_ne_zero_of_irreducible M hM)
  have hw : w ≠ 0 := by
    intro hw
    exact parikhQ_ne_zero hne (Matrix.eq_zero_of_mulVec_eq_zero hdet hw)
  have h0 : w ∈ windowSpan s n T :=
    iterate_mass_mem_windowSpan s n hT (by omega) (by omega)
  have h1 : M *ᵥ w ∈ windowSpan s n T := by
    simpa only [w, M, pow_succ', ← mulVec_mulVec] using
      iterate_mass_mem_windowSpan s n hT (k := n + 1) (by omega) (by omega)
  have h2 : M *ᵥ (M *ᵥ w) ∈ windowSpan s n T := by
    simpa only [w, M, show n + 2 = (n + 1) + 1 by omega,
      pow_succ', ← mulVec_mulVec] using
      iterate_mass_mem_windowSpan s n hT (k := n + 2) (by omega) (by omega)
  have hli := Psc.Cyclicity.cyclic_of_irreducible M hM w hw
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- A single rational row vanishing on the whole window must be zero. -/
theorem row_eq_zero_of_window (s : Fin 3 → List (Fin 3))
    (hM : Irreducible (incidenceQ s).charpoly) (n : ℕ)
    {T : List (Fin 3) × List (Fin 3)}
    (hT : Equiv1 T.1 T.2) (hne : T.1 ≠ []) (f : Fin 3 → ℚ)
    (hf : ∀ k, n ≤ k → k ≤ n + 2 →
      ∀ U ∈ descR s k T, dotProduct f (mass U) = 0) : f = 0 := by
  let L : (Fin 3 → ℚ) →ₗ[ℚ] ℚ := dotProductBilin ℚ ℚ f
  have hspan : windowSpan s n T ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro p ⟨k, U, hk, hk', hU, rfl⟩
    exact hf k hk hk' U hU
  rw [windowSpan_eq_top s hM n hT hne] at hspan
  have hself : dotProduct f f = 0 := hspan (Submodule.mem_top)
  exact dotProduct_self_eq_zero.mp hself

/-- A nonzero fixed row detects a literal descendant in the next three levels.
`j` is its ordinal in the complete ordered list at the returned depth `k`. -/
theorem exists_detecting_occurrence (s : Fin 3 → List (Fin 3))
    (hM : Irreducible (incidenceQ s).charpoly) (n : ℕ)
    {T : List (Fin 3) × List (Fin 3)}
    (hT : Equiv1 T.1 T.2) (hne : T.1 ≠ [])
    (f : Fin 3 → ℚ) (hf : f ≠ 0) :
    ∃ (k j : ℕ) (U : List (Fin 3) × List (Fin 3)), n ≤ k ∧ k ≤ n + 2 ∧
      (descR s k T)[j]? = some U ∧ dotProduct f (mass U) ≠ 0 := by
  classical
  by_contra h
  apply hf
  apply row_eq_zero_of_window s hM n hT hne f
  intro k hk hk' U hU
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hU
  by_contra hne
  exact h ⟨k, j, U, hk, hk', hj, hne⟩

/-- The local depth-at-most-two specialization. -/
theorem exists_detecting_occurrence_le_two (s : Fin 3 → List (Fin 3))
    (hM : Irreducible (incidenceQ s).charpoly)
    {T : List (Fin 3) × List (Fin 3)}
    (hT : Equiv1 T.1 T.2) (hne : T.1 ≠ [])
    (f : Fin 3 → ℚ) (hf : f ≠ 0) :
    ∃ (k j : ℕ) (U : List (Fin 3) × List (Fin 3)),
      k ≤ 2 ∧ (descR s k T)[j]? = some U ∧
      dotProduct f (mass U) ≠ 0 := by
  obtain ⟨k, j, U, _, hk, hj, hU⟩ := exists_detecting_occurrence s hM 0 hT hne f hf
  exact ⟨k, j, U, hk, hj, hU⟩

/-! ### Literal controls -/

namespace Controls

def sharpSubst : Fin 3 → List (Fin 3) := ![[1], [0, 2], [2, 0, 2]]
def sharpPair : List (Fin 3) × List (Fin 3) := ([0, 1], [1, 0])
def sharpRow : Fin 3 → ℚ := ![1, -1, 0]

theorem sharp_depth_one :
    descR sharpSubst 1 sharpPair = [([1, 0, 2], [0, 2, 1])] := by
  decide

theorem sharp_depth_two :
    descR sharpSubst 2 sharpPair =
      [([0, 2, 1], [1, 2, 0]), ([2], [2]), ([0], [0]), ([2], [2])] := by
  decide

theorem sharp_first_two_levels_vanish :
    ∀ U ∈ descR sharpSubst 0 sharpPair ++ descR sharpSubst 1 sharpPair,
      dotProduct sharpRow (mass U) = 0 := by
  rw [show descR sharpSubst 0 sharpPair = [sharpPair] from rfl, sharp_depth_one]
  norm_num [sharpPair, sharpRow, mass, parikhQ, parikh, dotProduct, Fin.sum_univ_three]

theorem sharp_depth_two_ordinal_two :
    (descR sharpSubst 2 sharpPair)[2]? = some ([0], [0]) ∧
      dotProduct sharpRow (mass ([0], [0])) = 1 := by
  rw [sharp_depth_two]
  norm_num [sharpRow, mass, parikhQ, parikh, dotProduct, Fin.sum_univ_three]

/-- Pruning diagonal factors removes every detected occurrence in this level. -/
theorem sharp_pruned_level_vanishes :
    ∀ U ∈ (descR sharpSubst 2 sharpPair).filter (fun U => U.1 != U.2),
      dotProduct sharpRow (mass U) = 0 := by
  rw [sharp_depth_two]
  norm_num [sharpRow, mass, parikhQ, parikh, dotProduct, Fin.sum_univ_three]

/-- The repeated `2/2` factor contributes twice to the true mass. -/
theorem sharp_multiplicity_matters :
    ((descR sharpSubst 2 sharpPair).map mass).sum = ![2, 1, 3] ∧
      (((descR sharpSubst 2 sharpPair).dedup).map mass).sum = ![2, 1, 2] := by
  have hd : (descR sharpSubst 2 sharpPair).dedup =
      [([0, 2, 1], [1, 2, 0]), ([0], [0]), ([2], [2])] := by decide
  rw [hd, sharp_depth_two]
  constructor <;> ext a <;> fin_cases a <;>
    norm_num [mass, parikhQ, parikh]

def reducibleSubst : Fin 3 → List (Fin 3) := ![[1, 0], [1, 0, 2], [2, 1, 1]]
def reduciblePair : List (Fin 3) × List (Fin 3) := ([1, 0, 2], [2, 1, 0])
def reducibleRow : Fin 3 → ℚ := ![1, 0, -1]

theorem reducible_depth_one :
    descR reducibleSubst 1 reduciblePair =
      [([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0])] := by
  decide

theorem reducible_depth_two :
    descR reducibleSubst 2 reduciblePair =
      [([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]),
        ([1, 0, 2], [2, 1, 0]), ([1, 0, 2], [2, 1, 0]),
        ([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]), ([1, 0, 2], [2, 1, 0])] := by
  decide

/-- The known reducible strict-carrier calibration retains a nonzero row. -/
theorem reducible_three_levels_vanish :
    reducibleRow ≠ 0 ∧
      ∀ U ∈ descR reducibleSubst 0 reduciblePair ++
        descR reducibleSubst 1 reduciblePair ++ descR reducibleSubst 2 reduciblePair,
        dotProduct reducibleRow (mass U) = 0 := by
  rw [show descR reducibleSubst 0 reduciblePair = [reduciblePair] from rfl,
    reducible_depth_one, reducible_depth_two]
  norm_num [reduciblePair, reducibleRow,
    mass, parikhQ, parikh, dotProduct, Fin.sum_univ_three, funext_iff, Fin.forall_fin_succ]

/-- Nonemptiness cannot be omitted even at depth zero. -/
theorem empty_window_vanishes (s : Fin 3 → List (Fin 3)) (f : Fin 3 → ℚ) :
    ∀ k U, U ∈ descR s k ([], []) → dotProduct f (mass U) = 0 := by
  intro k U hU
  cases k with
  | zero =>
    simp only [descR, List.mem_singleton] at hU
    subst U
    simp [mass, parikhQ_nil]
  | succ n => simp [descR_empty_succ] at hU

end Controls

end Psc.DescendantSpan
