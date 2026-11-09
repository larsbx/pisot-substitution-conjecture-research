import R1Smith

namespace PscRoutes.R1OrderedAncestry

open PscRoutes.R1Smith

abbrev Word := List Nat
abbrev Vec := Fin 3 → ℤ

def image (a : Nat) : Word := ([[0, 1], [0, 2], [0]] : List Word)[a]!
def inflate (word : Word) : Word := word.flatMap image
def tracks (word : Word) (level : Nat) : Word := (inflate^[level]) word

def parikh (u v : Word) : Vec :=
  fun a => Int.ofNat (u.count a.val) - Int.ofNat (v.count a.val)

def incidence : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => Int.ofNat ((image j.val).count i.val)

def addr (word : Word) (cut : Nat) : Nat × Nat :=
  (word.zipIdx.flatMap fun (a, i) => (image a).zipIdx.map fun (_, j) => (i, j))[cut]!

structure Step where
  top : Nat
  bottom : Nat
  topOffset : Nat
  bottomOffset : Nat
  topLetter : Nat
  bottomLetter : Nat
  defect : Vec
  digit : Vec
  deriving Inhabited

def lineage (depth cut : Nat) : List Step := Id.run do
  let mut t := cut
  let mut b := cut
  let mut steps := []
  for level in (List.range depth).reverse do
    let u := tracks [0, 1] level
    let v := tracks [1, 0] level
    let (i, r) := addr u t
    let (j, s) := addr v b
    let a := u[i]!
    let c := v[j]!
    steps := ⟨i, j, r, s, a, c, parikh (u.take i) (v.take j),
      parikh ((image a).take r) ((image c).take s)⟩ :: steps
    t := i
    b := j
  return steps

def zeroReturns (depth : Nat) : List Nat :=
  let u := tracks [0, 1] depth
  let v := tracks [1, 0] depth
  ((List.range u.length).drop 1).filter fun k =>
    decide (parikh (u.take k) (v.take k) = 0)

def loops (depth : Nat) : List (Nat × Nat × Nat × List Step) :=
  (zeroReturns depth).flatMap fun cut =>
    let path := lineage depth cut
    path.zipIdx.flatMap fun (a, first) =>
      (path.zipIdx.drop (first + 1)).filterMap fun (b, last) =>
        if a.topLetter = b.topLetter ∧ a.bottomLetter = b.bottomLetter ∧
          a.defect = b.defect ∧ a.defect ≠ 0 then
          some (cut, first, last, (path.drop first).take (last - first))
        else none

def entries (v : Vec) : List Int := List.ofFn v

def rhs (steps : List Step) : Vec :=
  steps.foldl (fun b s => incidence.mulVec b + s.digit) 0

def operator (period : Nat) : Matrix (Fin 3) (Fin 3) ℤ := 1 - incidence ^ period

def row (c : Nat × Nat × Nat × List Step) : List Int :=
  let (cut, first, last, steps) := c
  [cut, first, last].map Int.ofNat ++ entries (steps[0]!.defect) ++
    (List.ofFn fun i => entries (operator (last - first) i)).flatten ++ entries (rhs steps) ++
    steps.flatMap fun s => [s.top, s.bottom, s.topOffset, s.bottomOffset, s.topLetter, s.bottomLetter].map Int.ofNat ++ entries s.digit


/-- Exact literal words after one inflation of the swap seed.
The parental swap seed is **productive**: it already has matching
letters on both tracks at positions zero and two. All nine
depth-six ancestry cycles sampled by `loops 6` descend from
this productive seed; they cannot serve as a strict child-closed
nonproductive BPA counterexample. -/
theorem tribonacci_swap_seed_image :
    inflate [0, 1] = [0, 1, 0, 2] ∧
    inflate [1, 0] = [0, 2, 0, 1] := by decide

/-- Independent source-word diagonal coincidence witness at the
first inflation, without invoking Parikh-only comparison. -/
theorem swap_seed_has_diagonal_coincidence :
    ∃ i : Nat,
      i < (inflate [0, 1]).length ∧
      i < (inflate [1, 0]).length ∧
      (inflate [0, 1])[i]? = (inflate [1, 0])[i]? := by
  refine ⟨0, by decide, by decide, by decide⟩

theorem bounded_candidate_absent :
    ((List.range 6).map fun i => (loops (i + 1)).length) = [0, 0, 0, 0, 0, 9] ∧
    (loops 6).all (fun (_, _, _, steps) => !(decide (steps.map Step.defect =
      ([![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] : List Vec)))) = true := by decide

def witness := (lineage 6 51).take 3

theorem witness_source_equation :
    51 ∈ zeroReturns 6 ∧
    (51, 0, 3) ∈ (loops 6).map (fun (cut, first, last, _) => (cut, first, last)) ∧
    rhs witness = ![0, -1, 0] ∧ (operator 3).mulVec ![1, -1, 0] = rhs witness := by decide

def U : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, -1; 0, 1, -2; -1, 0, 3]
def Uinv : Matrix (Fin 3) (Fin 3) ℤ := !![-3, 0, -1; -2, 1, 0; -1, 0, 0]
def V : Matrix (Fin 3) (Fin 3) ℤ := !![1, -1, -1; 0, 1, 1; 0, 0, 1]
def Vinv : Matrix (Fin 3) (Fin 3) ℤ := !![1, 1, 0; 0, 1, -1; 0, 0, 1]
def diagonal : Vec := ![1, 1, 2]

theorem period_three_smith (b : Vec) :
    (∃ x : Vec, (operator 3).mulVec x = b) ↔
      ∀ i : Fin 3, diagonal i ∣ U.mulVec b i :=
  matrix_smith_certificate_complete (operator 3) U Uinv V Vinv diagonal b
    (by decide) (by decide) (by decide)

theorem witness_passes_smith : ∀ i : Fin 3, diagonal i ∣ U.mulVec (rhs witness) i :=
  (period_three_smith (rhs witness)).mp ⟨![1, -1, 0], witness_source_equation.2.2.2⟩

def emit (tag : String) (values : List Int) : IO Unit :=
  IO.println (String.intercalate "," (tag :: values.map toString))

#eval do
  for depth in (List.range 6).map (· + 1) do
    let found := loops depth
    emit "R1_SCAN" [depth, (zeroReturns depth).length, found.length]
    for c in found do
      emit "R1_CYCLE" (row c)

#print axioms tribonacci_swap_seed_image
#print axioms swap_seed_has_diagonal_coincidence
#print axioms bounded_candidate_absent
#print axioms witness_source_equation
#print axioms period_three_smith
#print axioms witness_passes_smith

end PscRoutes.R1OrderedAncestry

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R1OrderedAncestry.tribonacci_swap_seed_image,
      `PscRoutes.R1OrderedAncestry.swap_seed_has_diagonal_coincidence,
      `PscRoutes.R1OrderedAncestry.bounded_candidate_absent,
      `PscRoutes.R1OrderedAncestry.witness_source_equation,
      `PscRoutes.R1OrderedAncestry.period_three_smith,
      `PscRoutes.R1OrderedAncestry.witness_passes_smith] do
    for ax in ← collectAxioms name do
      if !allowed.contains ax then
        throwError "Nonstandard axiom {ax} in {name}"
    liftIO <| IO.println s!"PSC_OCCURRENCE_AXIOMS_OK {name}"
