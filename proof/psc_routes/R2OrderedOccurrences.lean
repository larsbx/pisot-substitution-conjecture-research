import R2EdgeCertificate

namespace PscRoutes.R2OrderedOccurrences

open PscRoutes.R2C

abbrev Word := List Nat
abbrev Pair := Word × Word
abbrev Images := List Word

def tribonacci : Images := [[0, 1], [0, 2], [0]]
def control : Images := [[1], [0, 1, 2], [1]]
def seed : Pair := ([0, 1], [1, 0])

structure Address where
  letter : Nat
  parent : Nat
  offset : Nat
  deriving Inhabited

def expand (images : Images) (word : Word) : List Address :=
  word.zipIdx.flatMap fun (a, i) =>
    images[a]!.zipIdx.map fun (b, j) => ⟨b, i, j⟩

def balanced (u v : Word) : Bool :=
  [0, 1, 2].all fun a => u.count a == v.count a

def children (images : Images) (pair : Pair) : List (Pair × List Int) := Id.run do
  let u := expand images pair.1
  let v := expand images pair.2
  let top := u.map Address.letter
  let bottom := v.map Address.letter
  let cuts := (List.range (top.length + 1)).filter
    fun k => balanced (top.take k) (bottom.take k)
  let mut result := []
  for ((lo, hi), ordinal) in (cuts.zip (cuts.drop 1)).zipIdx do
    let child := ((top.drop lo).take (hi - lo), (bottom.drop lo).take (hi - lo))
    let sign : Int := if compare child.1 child.2 == .gt then -1 else 1
    let a := u[lo]!
    let b := v[lo]!
    result := result ++ [(child, [ordinal, lo, hi, a.parent, a.offset, b.parent, b.offset].map Int.ofNat ++ [sign])]
  return result

def packet (images : Images) : List Pair × List (List Int) := Id.run do
  let mut states := [seed]
  let mut edges := []
  for src in List.range 32 do
    if let some pair := states[src]? then
      for (child, address) in children images pair do
        if !states.contains child then
          states := states ++ [child]
        edges := edges ++ [(Int.ofNat src) :: (Int.ofNat (states.idxOf child)) :: address]
  return (states, edges)

def complete (images : Images) : Bool :=
  let (states, rows) := packet images
  states.length ≤ 32 &&
  states.zipIdx.all (fun (pair, src) =>
    let expected := (children images pair).map fun (child, address) =>
      (Int.ofNat src) :: (Int.ofNat (states.idxOf child)) :: address
    (children images pair).all (fun (child, _) => states.contains child) &&
    rows.filter (fun row => row[0]! == Int.ofNat src) == expected)

theorem fixed_domains_complete :
    complete tribonacci = true ∧ complete control = true ∧
    (packet tribonacci).1.length = 11 ∧ (packet tribonacci).2.length = 25 ∧
    (packet control).1.length = 4 ∧ (packet control).2.length = 8 := by decide

def residual (states : List Pair) (row : List Int) : Int :=
  let (u, v) := states[row[0]!.toNat]!
  let ordinary : Int :=
    Int.ofNat ((u.take row[5]!.toNat).count 2) - Int.ofNat ((v.take row[7]!.toNat).count 2)
  (row[9]! - 1) * ordinary

def vertex (n : Nat) : Fin 11 :=
  ⟨n % 11, Nat.mod_lt _ (by decide)⟩

def weighted (states : List Pair) (rows : List (List Int)) : List (WeightedEdge 11) :=
  rows.map fun row => ⟨vertex row[0]!.toNat, vertex row[1]!.toNat, residual states row⟩

def boundedRows (rows : List (List Int)) : Bool :=
  rows.all fun r => decide (0 ≤ r[0]! ∧ r[0]! < 11 ∧ 0 ≤ r[1]! ∧ r[1]! < 11)

def tribonacciEdges : List (WeightedEdge 11) :=
  let (states, rows) := packet tribonacci
  weighted states rows

theorem literal_cycle_residuals :
    boundedRows (packet tribonacci).2 = true ∧
    (packet tribonacci).2[5]!.take 2 = [2, 4] ∧
    (packet tribonacci).2[9]!.take 2 = [4, 0] ∧
    (packet tribonacci).2[1]!.take 2 = [0, 2] ∧
    let (states, rows) := packet tribonacci
    [residual states rows[5]!, residual states rows[9]!, residual states rows[1]!] =
      [2, 0, 0] := by decide

theorem literal_cycle_refuses_potential (h : Fin 11 → ℚ) :
    checkPotential tribonacciEdges h = false := by
  cases hc : checkPotential tribonacciEdges h with
  | false => rfl
  | true =>
    have hs := checkPotential_sound tribonacciEdges h hc
    have h1 := hs ⟨2, 4, 2⟩ (by decide)
    have h2 := hs ⟨4, 0, 0⟩ (by decide)
    have h3 := hs ⟨0, 2, 0⟩ (by decide)
    change (2 : ℚ) = h 4 - h 2 at h1
    change (0 : ℚ) = h 0 - h 4 at h2
    change (0 : ℚ) = h 2 - h 0 at h3
    linarith

/-- A fixed-domain gate. Check occurrence equality before applying any weights. -/
def checkTribonacciPacket (supplied : List Pair × List (List Int)) (h : Fin 11 → ℚ) : Bool :=
  if (complete tribonacci && boundedRows supplied.2) && supplied == packet tribonacci then
    checkPotential (weighted supplied.1 supplied.2) h
  else false

theorem packet_gate_sound (supplied : List Pair × List (List Int)) (h : Fin 11 → ℚ)
    (accepted : checkTribonacciPacket supplied h = true) :
    supplied = packet tribonacci ∧ SatisfiesEdges tribonacciEdges h := by
  unfold checkTribonacciPacket at accepted
  split at accepted
  next guard =>
    have hpacket : supplied = packet tribonacci := by
      exact eq_of_beq (Bool.and_eq_true_iff.mp guard).2
    subst supplied
    exact ⟨rfl, checkPotential_sound tribonacciEdges h accepted⟩
  next => simp at accepted

def emit (tag : String) (images : Images) : IO Unit := do
  let (states, rows) := packet images
  for (u, v) in states do
    for word in [u, v] do
      IO.println (String.intercalate "," ((tag ++ "_STATE") :: word.map toString))
  for row in rows do
    IO.println (String.intercalate "," ((tag ++ "_EDGE") :: row.map toString))

#eval emit "R2_TRIB" tribonacci
#eval emit "R2_CONTROL" control
#print axioms fixed_domains_complete
#print axioms literal_cycle_residuals
#print axioms literal_cycle_refuses_potential
#print axioms packet_gate_sound

end PscRoutes.R2OrderedOccurrences

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R2OrderedOccurrences.fixed_domains_complete,
      `PscRoutes.R2OrderedOccurrences.literal_cycle_residuals,
      `PscRoutes.R2OrderedOccurrences.literal_cycle_refuses_potential,
      `PscRoutes.R2OrderedOccurrences.packet_gate_sound] do
    for ax in ← collectAxioms name do
      if !allowed.contains ax then
        throwError "Nonstandard axiom {ax} in {name}"
    liftIO <| IO.println s!"PSC_OCCURRENCE_AXIOMS_OK {name}"
