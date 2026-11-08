import R2OrderedOccurrences

namespace PscRoutes.R2LinearScores

open PscRoutes.R2C PscRoutes.R2OrderedOccurrences

abbrev Vector3 := ℤ × ℤ × ℤ
abbrev Functional := ℚ × ℚ × ℚ

structure VectorEdge where
  source : ℕ
  target : ℕ
  weight : Vector3
  deriving DecidableEq

def vectors (images : Images) : List VectorEdge :=
  let (states, rows) := packet images
  rows.map fun row =>
    let (u, v) := states[row[0]!.toNat]!
    let coordinate (a : ℕ) : ℤ :=
      let x := Int.ofNat ((u.take row[5]!.toNat).count a) -
        Int.ofNat ((v.take row[7]!.toNat).count a)
      (row[9]! - 1) * x
    ⟨row[0]!.toNat, row[1]!.toNat, (coordinate 0, coordinate 1, coordinate 2)⟩

def dot (q : Functional) (w : Vector3) : ℚ :=
  q.1 * w.1 + q.2.1 * w.2.1 + q.2.2 * w.2.2

def project {n : ℕ} (hn : 0 < n) (q : Functional) (e : VectorEdge) :
    WeightedEdge n :=
  ⟨⟨e.source % n, Nat.mod_lt _ hn⟩, ⟨e.target % n, Nat.mod_lt _ hn⟩, dot q e.weight⟩

def admitsPotential {n : ℕ} (hn : 0 < n) (q : Functional) (edges : List VectorEdge) : Prop :=
  ∃ potential : Fin n → ℚ, SatisfiesEdges (edges.map (project hn q)) potential

theorem fixed_vector_support :
    (vectors tribonacci).all (fun e => e.source < 11 && e.target < 11 &&
      (e.weight == (0, 0, 0) || e.weight == (0, 0, 2))) = true ∧
    (vectors control).all (fun e => e.source < 4 && e.target < 4 &&
      (e.weight == (0, 0, 0) || e.weight == (2, 0, 0) || e.weight == (0, 0, 2))) = true := by
  decide

theorem zero_residuals_admit_potential {n : ℕ} (hn : 0 < n)
    (q : Functional) (edges : List VectorEdge)
    (h : ∀ e ∈ edges, dot q e.weight = 0) : admitsPotential hn q edges := by
  refine ⟨fun _ => 0, ?_⟩
  intro e he
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
  simpa [project] using h v hv

theorem tribonacci_linear_iff (q : Functional) :
    admitsPotential (n := 11) (by decide) q (vectors tribonacci) ↔ q.2.2 = 0 := by
  constructor
  · rintro ⟨H, h⟩
    have edge (v : VectorEdge) (hv : v ∈ vectors tribonacci) :=
      h (project (n := 11) (by decide) q v) (List.mem_map.mpr ⟨v, hv, rfl⟩)
    have h24 : dot q (0, 0, 2) = H 4 - H 2 := edge ⟨2, 4, (0, 0, 2)⟩ (by decide)
    have h40 : dot q (0, 0, 0) = H 0 - H 4 := edge ⟨4, 0, (0, 0, 0)⟩ (by decide)
    have h02 : dot q (0, 0, 0) = H 2 - H 0 := edge ⟨0, 2, (0, 0, 0)⟩ (by decide)
    simp [dot] at h24 h40 h02
    linarith
  · intro hq
    apply zero_residuals_admit_potential
    intro e he
    have hs := List.all_eq_true.mp fixed_vector_support.1 e he
    have hw : e.weight = (0, 0, 0) ∨ e.weight = (0, 0, 2) := by
      simp only [Bool.and_eq_true_iff, Bool.or_eq_true, beq_iff_eq] at hs
      exact hs.2
    rcases hw with hw | hw <;> simp [hw, dot, hq]

theorem control_linear_iff (q : Functional) :
    admitsPotential (n := 4) (by decide) q (vectors control) ↔ q.1 = 0 ∧ q.2.2 = 0 := by
  constructor
  · rintro ⟨H, h⟩
    have edge (v : VectorEdge) (hv : v ∈ vectors control) :=
      h (project (n := 4) (by decide) q v) (List.mem_map.mpr ⟨v, hv, rfl⟩)
    have h13 : dot q (2, 0, 0) = H 3 - H 1 := edge ⟨1, 3, (2, 0, 0)⟩ (by decide)
    have h31 : dot q (0, 0, 0) = H 1 - H 3 := edge ⟨3, 1, (0, 0, 0)⟩ (by decide)
    have h23 : dot q (0, 0, 2) = H 3 - H 2 := edge ⟨2, 3, (0, 0, 2)⟩ (by decide)
    have h32 : dot q (0, 0, 0) = H 2 - H 3 := edge ⟨3, 2, (0, 0, 0)⟩ (by decide)
    simp [dot] at h13 h31 h23 h32
    constructor <;> linarith
  · rintro ⟨h0, h2⟩
    apply zero_residuals_admit_potential
    intro e he
    have hs := List.all_eq_true.mp fixed_vector_support.2 e he
    have hw : (e.weight = (0, 0, 0) ∨ e.weight = (2, 0, 0)) ∨ e.weight = (0, 0, 2) := by
      simp only [Bool.and_eq_true_iff, Bool.or_eq_true, beq_iff_eq] at hs
      exact hs.2
    rcases hw with (hw | hw) | hw <;> simp [hw, dot, h0, h2]

def emitVectors (tag : String) (images : Images) : IO Unit := do
  for e in vectors images do
    IO.println (String.intercalate "," [tag, toString e.source, toString e.target,
      toString e.weight.1, toString e.weight.2.1, toString e.weight.2.2])

#eval emitVectors "R2_TRIB_VECTOR" tribonacci
#eval emitVectors "R2_CONTROL_VECTOR" control

end PscRoutes.R2LinearScores

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R2LinearScores.fixed_vector_support,
      `PscRoutes.R2LinearScores.zero_residuals_admit_potential,
      `PscRoutes.R2LinearScores.tribonacci_linear_iff,
      `PscRoutes.R2LinearScores.control_linear_iff] do
    for ax in ← collectAxioms name do
      if !allowed.contains ax then
        throwError "Nonstandard axiom {ax} in {name}"
    liftIO <| IO.println s!"PSC_LINEAR_SCORE_AXIOMS_OK {name}"
