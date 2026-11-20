import PscVerif.OccurrenceTransport

/-!
# Literal coincidence on residual A1′ tail families

The first two families have actual sixth-iterate prefix coincidences.
All witnesses are constructed with `Mark.inflate`; no spectral, overlap,
finite-graph, or affine-realizability premise is supplied.

Pre-code review: `docs/p1a-minimal-z3-tail-stop-go-2026-11-14.md`.
-/

namespace Psc.A1PrimeTailCoincidence

open Psc.Binomial Psc.Incidence Psc.OccurrenceTransport Matrix

attribute [local simp] Matrix.vecHead Matrix.vecTail

abbrev Word := List (Fin 3)

/-- The exact integer consequence of the necessary Pisot inequality after
the existing crossing/factor reductions have supplied `Z>=3` and `j>=1`.
Those reductions are not hypotheses silently discharged by this lemma. -/
theorem residual_parameter_cases (e Z j : ℤ)
    (he : 2 ≤ e) (hZ : 3 ≤ Z) (hj : 1 ≤ j)
    (h : (Z - 3) * e + (Z - 1) * (j - 1) ≤ 3) :
    (Z = 3 ∧ (j = 1 ∨ j = 2)) ∨
      (Z = 4 ∧ j = 1 ∧ (e = 2 ∨ e = 3)) := by
  have hprod : 0 ≤ (Z - 1) * (j - 1) :=
    mul_nonneg (by omega) (by omega)
  have hupper : Z ≤ 4 := by
    by_contra hn
    have hlarge : 5 ≤ Z := by omega
    have hmul : 0 ≤ (Z - 5) * e := mul_nonneg (by omega) (by omega)
    nlinarith
  have hcases : Z = 3 ∨ Z = 4 := by omega
  rcases hcases with rfl | rfl
  · left
    constructor
    · rfl
    · have hjupper : j ≤ 2 := by nlinarith
      omega
  · right
    have hjone : j = 1 := by nlinarith
    subst j
    refine ⟨rfl, rfl, ?_⟩
    have heupper : e ≤ 3 := by nlinarith
    omega

/-- Ordered literal images with arbitrary counted middles. -/
def substitution (v w : Word) : Fin 3 → Word
  | 0 => [1]
  | 1 => [0, 2, 2, 2, 1] ++ v ++ [1, 1, 0]
  | 2 => [0, 2, 1, 1] ++ w ++ [0]

theorem incidenceZ_eq (e : ℕ) (v w : Word)
    (hv : parikhZ v = ![0, 2 * (e : ℤ) - 2, 1])
    (hw : parikhZ w = ![0, (e : ℤ) - 2, 2]) :
    incidenceZ (substitution v w) =
      !![0, 2, 2; 1, 2 * (e : ℤ) + 1, (e : ℤ); 0, 4, 3] := by
  ext i j
  change parikhZ (substitution v w j) i = _
  fin_cases j <;> simp only [substitution, parikhZ_append, hv, hw]
  all_goals fin_cases i <;> norm_num [parikhZ] <;> ring

private def singletonMark (a : Fin 3) : Mark ([a] : Word) :=
  ⟨[], a, [], rfl⟩

private def onlyY (v w : Word) : Mark (substitution v w 0) :=
  ⟨[], 1, [], rfl⟩

private def firstO (v w : Word) : Mark (substitution v w 1) where
  before := []
  letter := 0
  after := [2, 2, 2, 1] ++ v ++ [1, 1, 0]
  split := by simp [substitution]

private def firstZ (v w : Word) : Mark (substitution v w 1) where
  before := [0]
  letter := 2
  after := [2, 2, 1] ++ v ++ [1, 1, 0]
  split := by simp [substitution]

private def firstY (v w : Word) : Mark (substitution v w 1) where
  before := [0, 2, 2, 2]
  letter := 1
  after := v ++ [1, 1, 0]
  split := by simp [substitution]

private def lastY (v w : Word) : Mark (substitution v w 1) where
  before := [0, 2, 2, 2, 1] ++ v ++ [1]
  letter := 1
  after := [0]
  split := by simp [substitution, List.append_assoc]

private def penultimateY (v w : Word) : Mark (substitution v w 1) where
  before := [0, 2, 2, 2, 1] ++ v
  letter := 1
  after := [1, 0]
  split := by simp [substitution, List.append_assoc]

private def secondZ (v w : Word) : Mark (substitution v w 1) where
  before := [0, 2]
  letter := 2
  after := [2, 1] ++ v ++ [1, 1, 0]
  split := by simp [substitution]

private def finalYO (v w : Word) : Mark (substitution v w 1) where
  before := [0, 2, 2, 2, 1] ++ v ++ [1, 1]
  letter := 0
  after := []
  split := by simp [substitution, List.append_assoc]

private def secondZY (v w : Word) : Mark (substitution v w 2) where
  before := [0, 2, 1]
  letter := 1
  after := w ++ [0]
  split := by simp [substitution]

private def finalZO (v w : Word) : Mark (substitution v w 2) where
  before := [0, 2, 1, 1] ++ w
  letter := 0
  after := []
  split := by simp [substitution, List.append_assoc]

private def stage0 : MarkedPair :=
  ⟨([0], [1]), singletonMark 0, singletonMark 1⟩

private theorem marked_counts {m : MarkedPair} {a b : Fin 3}
    (h : m.packet = ⟨a, b, 0⟩) : Equiv1 m.top.before m.bottom.before := by
  apply equiv1_of_parikhZ_eq
  apply sub_eq_zero.mp
  exact congrArg Packet.delta h

private theorem marked_prefixes (m : MarkedPair) (x y : Word) (a : Fin 3)
    (hwords : m.words = (x, y)) (hp : m.packet = ⟨a, a, 0⟩) :
    ∃ p q u t : Word, x = p ++ a :: u ∧ y = q ++ a :: t ∧ Equiv1 p q := by
  have ht : m.top.letter = a := congrArg Packet.top hp
  have hb : m.bottom.letter = a := congrArg Packet.bottom hp
  refine ⟨m.top.before, m.bottom.before, m.top.after, m.bottom.after, ?_, ?_, marked_counts hp⟩
  · rw [← congrArg Prod.fst hwords]
    simpa only [ht] using m.top.split
  · rw [← congrArg Prod.snd hwords]
    simpa only [hb] using m.bottom.split

private def stage1 (v w : Word) : MarkedPair :=
  stage0.inflate (substitution v w) (onlyY v w) (firstZ v w)

private def stage2 (v w : Word) : MarkedPair :=
  (stage1 v w).inflate (substitution v w) (firstY v w) (secondZY v w)

private def stage3 (v w : Word) : MarkedPair :=
  (stage2 v w).inflate (substitution v w) (lastY v w) (firstO v w)

private def stage4 (v w : Word) : MarkedPair :=
  (stage3 v w).inflate (substitution v w) (penultimateY v w) (onlyY v w)

private def stage5 (v w : Word) : MarkedPair :=
  (stage4 v w).inflate (substitution v w) (lastY v w) (secondZ v w)

private def stage6 (v w : Word) : MarkedPair :=
  (stage5 v w).inflate (substitution v w) (finalYO v w) (finalZO v w)

private theorem final_packet (e : ℕ) (v w : Word)
    (hv : parikhZ v = ![0, 2 * (e : ℤ) - 2, 1])
    (hw : parikhZ w = ![0, (e : ℤ) - 2, 2]) :
    (stage6 v w).packet = ⟨0, 0, 0⟩ := by
  have hm := incidenceZ_eq e v w hv hw
  have h0 : stage0.packet = ⟨0, 1, 0⟩ := rfl
  have h1 : (stage1 v w).packet = ⟨1, 2, ![-1, 0, 0]⟩ := by
    erw [stage1, MarkedPair.inflate_packet, h0, hm]
    congr 1
    ext i
    fin_cases i <;> norm_num [onlyY, firstZ, Psc.OccurrenceTransport.residual, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h2 : (stage2 v w).packet = ⟨1, 1, ![0, -2, 2]⟩ := by
    erw [stage2, MarkedPair.inflate_packet, h1, hm]
    congr 1
    ext i
    fin_cases i <;> norm_num [firstY, secondZY, Psc.OccurrenceTransport.residual, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hvlast : parikhZ (lastY v w).before = ![1, 2 * (e : ℤ), 4] := by
    simp only [lastY, parikhZ_append, hv]
    ext i
    fin_cases i <;> norm_num [parikhZ] <;> ring
  have hvpen : parikhZ (penultimateY v w).before = ![1, 2 * (e : ℤ) - 1, 4] := by
    simp only [penultimateY, parikhZ_append, hv]
    ext i
    fin_cases i <;> norm_num [parikhZ] <;> ring
  have hvfinal : parikhZ (finalYO v w).before = ![1, 2 * (e : ℤ) + 1, 4] := by
    simp only [finalYO, parikhZ_append, hv]
    ext i
    fin_cases i <;> norm_num [parikhZ] <;> ring
  have hwfinal : parikhZ (finalZO v w).before = ![1, (e : ℤ), 3] := by
    simp only [finalZO, parikhZ_append, hw]
    ext i
    fin_cases i <;> norm_num [parikhZ] <;> ring
  have h3 : (stage3 v w).packet = ⟨1, 0, ![1, -2, 2]⟩ := by
    erw [stage3, MarkedPair.inflate_packet, h2, hm]
    congr 1
    simp only [Psc.OccurrenceTransport.residual, hvlast]
    ext i
    fin_cases i <;> norm_num [firstO, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have h4 : (stage4 v w).packet = ⟨1, 1, ![1, -2, 2]⟩ := by
    erw [stage4, MarkedPair.inflate_packet, h3, hm]
    congr 1
    simp only [Psc.OccurrenceTransport.residual, hvpen]
    ext i
    fin_cases i <;> norm_num [onlyY, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have h5 : (stage5 v w).packet = ⟨1, 2, ![0, -1, 1]⟩ := by
    erw [stage5, MarkedPair.inflate_packet, h4, hm]
    congr 1
    simp only [Psc.OccurrenceTransport.residual, hvlast]
    ext i
    fin_cases i <;> norm_num [secondZ, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  erw [stage6, MarkedPair.inflate_packet, h5, hm]
  congr 1
  simp only [Psc.OccurrenceTransport.residual, hvfinal, hwfinal]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- Actual sixth iterates have equal-Parikh prefixes followed by `o`. -/
theorem six_level_coincidence (e : ℕ) (v w : Word)
    (hv : parikhZ v = ![0, 2 * (e : ℤ) - 2, 1])
    (hw : parikhZ w = ![0, (e : ℤ) - 2, 2]) :
    ∃ p q u t : Word,
      power (substitution v w) 6 0 = p ++ 0 :: u ∧
      power (substitution v w) 6 1 = q ++ 0 :: t ∧ Equiv1 p q := by
  have hp := final_packet e v w hv hw
  refine ⟨(stage6 v w).top.before, (stage6 v w).bottom.before,
    (stage6 v w).top.after, (stage6 v w).bottom.after, ?_, ?_, ?_⟩
  · exact (stage6 v w).top.split
  · exact (stage6 v w).bottom.split
  · exact marked_counts hp

def boundaryMiddleV (b d : ℕ) : Word :=
  List.replicate b 1 ++ [2] ++ List.replicate (b + 2 * d + 2) 1

def boundaryMiddleW (b d : ℕ) : Word :=
  List.replicate (b + d) 1 ++ [2, 2]

def boundarySubstitution (b d : ℕ) : Fin 3 → Word :=
  substitution (boundaryMiddleV b d) (boundaryMiddleW b d)

theorem boundary_middle_counts (b d : ℕ) :
    parikhZ (boundaryMiddleV b d) =
      ![0, 2 * ((b + d + 2 : ℕ) : ℤ) - 2, 1] ∧
    parikhZ (boundaryMiddleW b d) = ![0, ((b + d + 2 : ℕ) : ℤ) - 2, 2] := by
  constructor <;> ext a
  all_goals
    fin_cases a <;>
      norm_num [boundaryMiddleV, boundaryMiddleW, parikhZ,
        List.count_append, List.count_replicate] <;> omega

theorem boundary_layer_six_level (b d : ℕ) :
    ∃ p q u t : Word,
      power (boundarySubstitution b d) 6 0 = p ++ 0 :: u ∧
      power (boundarySubstitution b d) 6 1 = q ++ 0 :: t ∧ Equiv1 p q := by
  obtain ⟨hv, hw⟩ := boundary_middle_counts b d
  exact six_level_coincidence (b + d + 2)
    (boundaryMiddleV b d) (boundaryMiddleW b d) hv hw

/-! ## The second boundary layer -/

def secondPrefix (b d : ℕ) : Word :=
  [0, 2, 2, 2, 1] ++ List.replicate b 1 ++ [2] ++ List.replicate (d + 1) 1

def secondSubstitution (b d : ℕ) (w : Word) : Fin 3 → Word
  | 0 => [1]
  | 1 => secondPrefix b d ++ [1, 1] ++ List.replicate (b + d) 1 ++ [1, 1, 0]
  | 2 => [0] ++ w ++ [0]

theorem second_prefix_counts (b d : ℕ) :
    parikhZ (secondPrefix b d) = ![1, ((b + d + 2 : ℕ) : ℤ), 4] := by
  ext a
  fin_cases a <;> norm_num [secondPrefix, parikhZ,
    List.count_append, List.count_replicate] <;> omega

theorem second_incidenceZ_eq (b d : ℕ) (w : Word)
    (hw : parikhZ w = ![0, ((b + d + 2 : ℕ) : ℤ), 3]) :
    incidenceZ (secondSubstitution b d w) =
      !![0, 2, 2; 1, 2 * ((b + d + 2 : ℕ) : ℤ) + 2,
        ((b + d + 2 : ℕ) : ℤ); 0, 4, 3] := by
  have hp := second_prefix_counts b d
  ext i j
  change parikhZ (secondSubstitution b d w j) i = _
  fin_cases j <;> simp only [secondSubstitution, parikhZ_append, hp, hw]
  all_goals fin_cases i <;>
    norm_num [parikhZ, List.count_replicate] <;> omega

private def secondInitialZ (b d : ℕ) (w : Word) :
    Mark (secondSubstitution b d w 1) where
  before := [0, 2]
  letter := 2
  after := [2, 1] ++ List.replicate b 1 ++ [2] ++ List.replicate (d + 1) 1 ++
    [1, 1] ++ List.replicate (b + d) 1 ++ [1, 1, 0]
  split := by simp [secondSubstitution, secondPrefix, List.append_assoc]

private def secondFirstY (b d : ℕ) (w : Word) :
    Mark (secondSubstitution b d w 1) where
  before := [0, 2, 2, 2]
  letter := 1
  after := List.replicate b 1 ++ [2] ++ List.replicate (d + 1) 1 ++
    [1, 1] ++ List.replicate (b + d) 1 ++ [1, 1, 0]
  split := by simp [secondSubstitution, secondPrefix, List.append_assoc]

private def secondMiddleFirst (b d : ℕ) (w : Word) :
    Mark (secondSubstitution b d w 1) where
  before := secondPrefix b d
  letter := 1
  after := [1] ++ List.replicate (b + d) 1 ++ [1, 1, 0]
  split := by simp [secondSubstitution, List.append_assoc]

private def secondMiddleNext (b d : ℕ) (w : Word) :
    Mark (secondSubstitution b d w 1) where
  before := secondPrefix b d ++ [1]
  letter := 1
  after := List.replicate (b + d) 1 ++ [1, 1, 0]
  split := by simp [secondSubstitution, List.append_assoc]

private def secondLastY (b d : ℕ) (w : Word) :
    Mark (secondSubstitution b d w 1) where
  before := secondPrefix b d ++ [1, 1] ++ List.replicate (b + d) 1 ++ [1]
  letter := 1
  after := [0]
  split := by simp [secondSubstitution, List.append_assoc]

private def secondFinalYO (b d : ℕ) (w : Word) :
    Mark (secondSubstitution b d w 1) where
  before := secondPrefix b d ++ [1, 1] ++ List.replicate (b + d) 1 ++ [1, 1]
  letter := 0
  after := []
  split := by simp [secondSubstitution, List.append_assoc]

private def secondFirstZO (b d : ℕ) (w : Word) :
    Mark (secondSubstitution b d w 2) where
  before := []
  letter := 0
  after := w ++ [0]
  split := by simp [secondSubstitution]

private def secondFinalZO (b d : ℕ) (w : Word) :
    Mark (secondSubstitution b d w 2) where
  before := [0] ++ w
  letter := 0
  after := []
  split := by simp [secondSubstitution]

private def secondStage1 (b d : ℕ) (w : Word) : MarkedPair :=
  stage0.inflate (secondSubstitution b d w) (singletonMark 1) (secondInitialZ b d w)

private def secondStage2 (b d : ℕ) (w : Word) : MarkedPair :=
  (secondStage1 b d w).inflate (secondSubstitution b d w)
    (secondMiddleFirst b d w) (secondFirstZO b d w)

private def secondStage3 (b d : ℕ) (w : Word) : MarkedPair :=
  (secondStage2 b d w).inflate (secondSubstitution b d w)
    (secondMiddleNext b d w) (singletonMark 1)

private def secondStage4 (b d : ℕ) (w : Word) : MarkedPair :=
  (secondStage3 b d w).inflate (secondSubstitution b d w)
    (secondMiddleNext b d w) (secondFirstY b d w)

private def secondStage5 (b d : ℕ) (w : Word) : MarkedPair :=
  (secondStage4 b d w).inflate (secondSubstitution b d w)
    (secondLastY b d w) (secondInitialZ b d w)

private def secondStage6 (b d : ℕ) (w : Word) : MarkedPair :=
  (secondStage5 b d w).inflate (secondSubstitution b d w)
    (secondFinalYO b d w) (secondFinalZO b d w)

private theorem secondStage6_words (b d : ℕ) (w : Word) :
    (secondStage6 b d w).words =
      (power (secondSubstitution b d w) 6 0, power (secondSubstitution b d w) 6 1) := by
  simp only [secondStage6, secondStage5, secondStage4, secondStage3, secondStage2,
    secondStage1, stage0, MarkedPair.inflate, power,
    Function.iterate_succ_apply, Function.iterate_zero_apply]

private theorem second_final_packet (b d : ℕ) (w : Word)
    (hw : parikhZ w = ![0, ((b + d + 2 : ℕ) : ℤ), 3]) :
    (secondStage6 b d w).packet = ⟨0, 0, 0⟩ := by
  have hm := second_incidenceZ_eq b d w hw
  have hp := second_prefix_counts b d
  have h0 : stage0.packet = ⟨0, 1, 0⟩ := rfl
  have h1 : (secondStage1 b d w).packet = ⟨1, 2, ![-1, 0, -1]⟩ := by
    erw [secondStage1, MarkedPair.inflate_packet, h0, hm]
    congr 1
    ext i
    fin_cases i <;> norm_num [singletonMark, secondInitialZ, Psc.OccurrenceTransport.residual, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hmiddle : parikhZ (secondMiddleNext b d w).before =
      ![1, ((b + d + 2 : ℕ) : ℤ) + 1, 4] := by
    simp only [secondMiddleNext, parikhZ_append, hp]
    ext i
    fin_cases i <;> norm_num [parikhZ]
  have hlast : parikhZ (secondLastY b d w).before =
      ![1, 2 * ((b + d + 2 : ℕ) : ℤ) + 1, 4] := by
    simp only [secondLastY, parikhZ_append, hp]
    ext i
    fin_cases i <;> norm_num [parikhZ, List.count_replicate] <;> omega
  have hyfinal : parikhZ (secondFinalYO b d w).before =
      ![1, 2 * ((b + d + 2 : ℕ) : ℤ) + 2, 4] := by
    simp only [secondFinalYO, parikhZ_append, hp]
    ext i
    fin_cases i <;> norm_num [parikhZ, List.count_replicate] <;> omega
  have hzfinal : parikhZ (secondFinalZO b d w).before =
      ![1, ((b + d + 2 : ℕ) : ℤ), 3] := by
    simp only [secondFinalZO, parikhZ_append, hw]
    ext i
    fin_cases i <;> norm_num [parikhZ]
  have h2 : (secondStage2 b d w).packet = ⟨1, 0, ![-1, -1, 1]⟩ := by
    erw [secondStage2, MarkedPair.inflate_packet, h1, hm]
    congr 1
    simp only [Psc.OccurrenceTransport.residual, secondMiddleFirst, hp]
    ext i
    fin_cases i <;> norm_num [secondFirstZO, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have h3 : (secondStage3 b d w).packet = ⟨1, 1, ![1, -2, 3]⟩ := by
    erw [secondStage3, MarkedPair.inflate_packet, h2, hm]
    congr 1
    simp only [Psc.OccurrenceTransport.residual, hmiddle]
    ext i
    fin_cases i <;> norm_num [singletonMark, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have h4 : (secondStage4 b d w).packet = ⟨1, 1, ![2, -2, 2]⟩ := by
    erw [secondStage4, MarkedPair.inflate_packet, h3, hm]
    congr 1
    simp only [Psc.OccurrenceTransport.residual, hmiddle]
    ext i
    fin_cases i <;> norm_num [secondFirstY, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have h5 : (secondStage5 b d w).packet = ⟨1, 2, ![0, -1, 1]⟩ := by
    erw [secondStage5, MarkedPair.inflate_packet, h4, hm]
    congr 1
    simp only [Psc.OccurrenceTransport.residual, hlast]
    ext i
    fin_cases i <;> norm_num [secondInitialZ, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  erw [secondStage6, MarkedPair.inflate_packet, h5, hm]
  congr 1
  simp only [Psc.OccurrenceTransport.residual, hyfinal, hzfinal]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem second_layer_six_level (b d : ℕ) (w : Word)
    (hw : parikhZ w = ![0, ((b + d + 2 : ℕ) : ℤ), 3]) :
    ∃ p q u t : Word,
      power (secondSubstitution b d w) 6 0 = p ++ 0 :: u ∧
      power (secondSubstitution b d w) 6 1 = q ++ 0 :: t ∧ Equiv1 p q := by
  have hp := second_final_packet b d w hw
  exact marked_prefixes (secondStage6 b d w) _ _ 0 (secondStage6_words b d w) hp

/-! ## Uniform three-level witnesses for all three residual Z=4 run splits -/

private theorem tail_split (head tail : Word) (m n : ℕ) :
    head ++ List.replicate (m + 1 + n) 1 ++ tail =
      (head ++ List.replicate m 1) ++ 1 :: (List.replicate n 1 ++ tail) := by
  rw [Nat.add_assoc, List.replicate_add]
  simp [Nat.add_comm 1 n, List.replicate_succ, List.append_assoc]

/-- The three entries have `(a,c,r,t)` equal to `(3,2,1,3)`,
`(4,1,1,3)`, and `(4,1,2,2)`, respectively. The positive y-run
parameters are `b+1` and `d+1`. -/
def z4Head (shape : Fin 3) (b : ℕ) : Word :=
  match shape with
  | 0 => [0, 2, 2, 2] ++ List.replicate (b + 1) 1 ++ [2, 2]
  | 1 => [0, 2, 2, 2, 2] ++ List.replicate (b + 1) 1 ++ [2]
  | 2 => [0, 2, 2, 2, 2] ++ List.replicate (b + 1) 1 ++ [2]

def z4ZHead (shape : Fin 3) : Word :=
  if shape = 2 then [0, 2, 2] else [0, 2]

def z4ZTail (shape : Fin 3) : Word :=
  if shape = 2 then [2, 2, 0] else [2, 2, 2, 0]

def z4Substitution (shape : Fin 3) (b d : ℕ) : Fin 3 → Word
  | 0 => [1]
  | 1 => z4Head shape b ++ List.replicate (b + 2 * d + 4) 1 ++ [0]
  | 2 => z4ZHead shape ++ [1] ++ List.replicate (b + d + 1) 1 ++ z4ZTail shape

private def z4Extra (shape : Fin 3) : ℕ := if shape = 2 then 1 else 0

private theorem z4_head_counts (shape : Fin 3) (b : ℕ) :
    parikhZ (z4Head shape b) = ![1, (b : ℤ) + 1, 5] := by
  fin_cases shape <;> ext i
  all_goals fin_cases i <;> norm_num [z4Head, parikhZ,
    List.count_append, List.count_replicate] <;> omega

theorem z4_incidenceZ_eq (shape : Fin 3) (b d : ℕ) :
    incidenceZ (z4Substitution shape b d) =
      !![0, 2, 2; 1, 2 * ((b + d + 2 : ℕ) : ℤ) + 1,
        ((b + d + 2 : ℕ) : ℤ); 0, 5, 4] := by
  have hp := z4_head_counts shape b
  ext i j
  change parikhZ (z4Substitution shape b d j) i = _
  fin_cases j <;> simp only [z4Substitution, parikhZ_append, hp]
  all_goals fin_cases shape <;> fin_cases i <;>
    norm_num [z4ZHead, z4ZTail, parikhZ, List.count_replicate] <;> omega

private def z4InitialZ (shape : Fin 3) (b d : ℕ) :
    Mark (z4Substitution shape b d 1) where
  before := [0, 2]
  letter := 2
  after := (z4Head shape b).drop 3 ++ List.replicate (b + 2 * d + 4) 1 ++ [0]
  split := by fin_cases shape <;> simp [z4Substitution, z4Head, List.append_assoc]

private def z4Middle (shape : Fin 3) (b d : ℕ) :
    Mark (z4Substitution shape b d 1) where
  before := z4Head shape b ++ List.replicate (d + 2 + z4Extra shape) 1
  letter := 1
  after := List.replicate (if shape = 2 then b + d else b + d + 1) 1 ++ [0]
  split := by
    have ht : b + 2 * d + 4 =
        (d + 2 + z4Extra shape) + 1 + (if shape = 2 then b + d else b + d + 1) := by
      fin_cases shape <;> simp [z4Extra] <;> omega
    change z4Head shape b ++ List.replicate (b + 2 * d + 4) 1 ++ [0] = _
    rw [ht]
    exact tail_split (z4Head shape b) [0] _ _

private def z4FirstZY (shape : Fin 3) (b d : ℕ) :
    Mark (z4Substitution shape b d 2) where
  before := z4ZHead shape
  letter := 1
  after := List.replicate (b + d + 1) 1 ++ z4ZTail shape
  split := by simp [z4Substitution, List.append_assoc]

private def z4FinalTop (shape : Fin 3) (b d : ℕ) :
    Mark (z4Substitution shape b d 1) where
  before := if shape = 2 then [0, 2, 2, 2, 2] else z4Head shape b ++ [1, 1]
  letter := 1
  after := if shape = 2 then
      List.replicate b 1 ++ [2] ++ List.replicate (b + 2 * d + 4) 1 ++ [0]
    else List.replicate (b + 2 * d + 1) 1 ++ [0]
  split := by
    have ht : b + 2 * d + 4 = 2 + 1 + (b + 2 * d + 1) := by omega
    fin_cases shape
    · simpa [z4Substitution, z4Head, ht, List.append_assoc] using
        tail_split (z4Head 0 b) [0] 2 (b + 2 * d + 1)
    · simpa [z4Substitution, z4Head, ht, List.append_assoc] using
        tail_split (z4Head 1 b) [0] 2 (b + 2 * d + 1)
    · simp [z4Substitution, z4Head, List.replicate_succ, List.append_assoc]

private def z4FinalBottom (shape : Fin 3) (b d : ℕ) :
    Mark (z4Substitution shape b d 1) where
  before := if shape = 2 then z4Head shape b ++ List.replicate d 1 else z4Head shape b
  letter := 1
  after := List.replicate
    (if shape = 2 then b + d + 3 else b + 2 * d + 3) 1 ++ [0]
  split := by
    have ht0 : b + 2 * d + 4 = 0 + 1 + (b + 2 * d + 3) := by omega
    have ht2 : b + 2 * d + 4 = d + 1 + (b + d + 3) := by omega
    fin_cases shape
    · simpa [z4Substitution, z4Head, ht0, List.append_assoc] using
        tail_split (z4Head 0 b) [0] 0 (b + 2 * d + 3)
    · simpa [z4Substitution, z4Head, ht0, List.append_assoc] using
        tail_split (z4Head 1 b) [0] 0 (b + 2 * d + 3)
    · simpa [z4Substitution, z4Head, ht2, List.append_assoc] using
        tail_split (z4Head 2 b) [0] d (b + d + 3)

private def z4Stage1 (shape : Fin 3) (b d : ℕ) : MarkedPair :=
  stage0.inflate (z4Substitution shape b d) (singletonMark 1) (z4InitialZ shape b d)

private def z4Stage2 (shape : Fin 3) (b d : ℕ) : MarkedPair :=
  (z4Stage1 shape b d).inflate (z4Substitution shape b d)
    (z4Middle shape b d) (z4FirstZY shape b d)

private def z4Stage3 (shape : Fin 3) (b d : ℕ) : MarkedPair :=
  (z4Stage2 shape b d).inflate (z4Substitution shape b d)
    (z4FinalTop shape b d) (z4FinalBottom shape b d)

private theorem z4_final_packet (shape : Fin 3) (b d : ℕ) :
    (z4Stage3 shape b d).packet = ⟨1, 1, 0⟩ := by
  have hm := z4_incidenceZ_eq shape b d
  have hp := z4_head_counts shape b
  have h0 : stage0.packet = ⟨0, 1, 0⟩ := rfl
  have h1 : (z4Stage1 shape b d).packet = ⟨1, 2, ![-1, 0, -1]⟩ := by
    erw [z4Stage1, MarkedPair.inflate_packet, h0, hm]
    congr 1
    ext i
    fin_cases i <;> norm_num [singletonMark, z4InitialZ, Psc.OccurrenceTransport.residual, parikhZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h2 : (z4Stage2 shape b d).packet =
      ⟨1, 1, ![-2, (z4Extra shape : ℤ), -(z4Extra shape : ℤ)]⟩ := by
    erw [z4Stage2, MarkedPair.inflate_packet, h1, hm]
    congr 1
    simp only [Psc.OccurrenceTransport.residual, z4Middle, z4FirstZY, parikhZ_append, hp]
    fin_cases shape <;> ext i
    all_goals fin_cases i <;>
      norm_num [z4Extra, z4ZHead, parikhZ, List.count_replicate,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> omega
  erw [z4Stage3, MarkedPair.inflate_packet, h2, hm]
  congr 1
  simp only [Psc.OccurrenceTransport.residual, z4FinalTop, z4FinalBottom]
  fin_cases shape <;> ext i
  all_goals fin_cases i <;>
    norm_num [z4Extra, z4Head, parikhZ, List.count_append, List.count_replicate,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> omega

/-- Each residual Z=4 run split has an actual third-iterate coincidence
for every positive pair of y-run lengths. No Pisot assertion is made for
the expanded word family. -/
theorem z4_three_level (shape : Fin 3) (b d : ℕ) :
    ∃ p q u t : Word,
      power (z4Substitution shape b d) 3 0 = p ++ 1 :: u ∧
      power (z4Substitution shape b d) 3 1 = q ++ 1 :: t ∧ Equiv1 p q := by
  have hp := z4_final_packet shape b d
  refine ⟨(z4Stage3 shape b d).top.before, (z4Stage3 shape b d).bottom.before,
    (z4Stage3 shape b d).top.after, (z4Stage3 shape b d).bottom.after, ?_, ?_, ?_⟩
  · exact (z4Stage3 shape b d).top.split
  · exact (z4Stage3 shape b d).bottom.split
  · exact marked_counts hp

end Psc.A1PrimeTailCoincidence
