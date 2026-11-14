/- Replay after compiling both A1′ tail modules. Every endpoint is bound to
independently declared literal words and its complete semantic type. -/
import PscVerif.A1PrimeTailPisot
import Lean.Util.CollectAxioms

namespace Psc.A1PrimeTailAudit

open Psc.Binomial (subst Equiv1)
open Psc.Incidence (inc)

def literalParikhZ (w : List (Fin 3)) : Fin 3 → ℤ := fun a => w.count a

def literalSubstitution (v w : List (Fin 3)) : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [0, 2, 2, 2, 1] ++ v ++ [1, 1, 0]
  | 2 => [0, 2, 1, 1] ++ w ++ [0]

def literalSecondPrefix (b d : Nat) : List (Fin 3) :=
  [0, 2, 2, 2, 1] ++ List.replicate b 1 ++ [2] ++ List.replicate (d + 1) 1

def literalSecondSubstitution (b d : Nat) (w : List (Fin 3)) : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => literalSecondPrefix b d ++ [1, 1] ++ List.replicate (b + d) 1 ++ [1, 1, 0]
  | 2 => [0] ++ w ++ [0]

def literalZ4Head (shape : Fin 3) (b : Nat) : List (Fin 3) :=
  match shape with
  | 0 => [0, 2, 2, 2] ++ List.replicate (b + 1) 1 ++ [2, 2]
  | 1 => [0, 2, 2, 2, 2] ++ List.replicate (b + 1) 1 ++ [2]
  | 2 => [0, 2, 2, 2, 2] ++ List.replicate (b + 1) 1 ++ [2]

def literalZ4ZHead (shape : Fin 3) : List (Fin 3) :=
  if shape = 2 then [0, 2, 2] else [0, 2]

def literalZ4ZTail (shape : Fin 3) : List (Fin 3) :=
  if shape = 2 then [2, 2, 0] else [2, 2, 2, 0]

def literalZ4Substitution (shape : Fin 3) (b d : Nat) : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => literalZ4Head shape b ++ List.replicate (b + 2 * d + 4) 1 ++ [0]
  | 2 => literalZ4ZHead shape ++ [1] ++ List.replicate (b + d + 1) 1 ++
      literalZ4ZTail shape

def literalThirdMatrix (e : Nat) : Matrix (Fin 3) (Fin 3) Nat :=
  !![0, 2, 2; 1, 2 * e + 3, e; 0, 4, 3]

def FirstCoincidenceType : Prop :=
  ∀ (e : Nat) (v w : List (Fin 3)),
    literalParikhZ v = ![0, 2 * (e : Int) - 2, 1] →
    literalParikhZ w = ![0, (e : Int) - 2, 2] →
    ∃ p q u t : List (Fin 3),
      (subst (literalSubstitution v w))^[6] [0] = p ++ 0 :: u ∧
      (subst (literalSubstitution v w))^[6] [1] = q ++ 0 :: t ∧ Equiv1 p q

def FirstPrimitiveType : Prop :=
  ∀ (e : Nat) (v w : List (Fin 3)),
    literalParikhZ v = ![0, 2 * (e : Int) - 2, 1] →
    literalParikhZ w = ![0, (e : Int) - 2, 2] →
    ∃ n ≥ 1, ∀ a c, 0 < (inc (literalSubstitution v w) ^ n) a c

def FirstIrreducibleType : Prop :=
  ∀ (e : Nat) (v w : List (Fin 3)),
    literalParikhZ v = ![0, 2 * (e : Int) - 2, 1] →
    literalParikhZ w = ![0, (e : Int) - 2, 2] →
    Irreducible ((inc (literalSubstitution v w)).map (Nat.cast : Nat → Rat)).charpoly

def FirstPisotType : Prop :=
  ∀ (e : Nat) (v w : List (Fin 3)),
    literalParikhZ v = ![0, 2 * (e : Int) - 2, 1] →
    literalParikhZ w = ![0, (e : Int) - 2, 2] →
    ∃ b : Real, 2 * (e : Real) + 3 < b ∧ b < 2 * (e : Real) + 4 ∧
      Polynomial.aeval (b : Complex)
        ((inc (literalSubstitution v w)).map (Nat.cast : Nat → Rat)).charpoly = 0 ∧
      ∀ z : Complex,
        Polynomial.aeval z
          ((inc (literalSubstitution v w)).map (Nat.cast : Nat → Rat)).charpoly = 0 →
        z ≠ b → ‖z‖ < 1

def SecondCoincidenceType : Prop :=
  ∀ (b d : Nat) (w : List (Fin 3)),
    literalParikhZ w = ![0, ((b + d + 2 : Nat) : Int), 3] →
    ∃ p q u t : List (Fin 3),
      (subst (literalSecondSubstitution b d w))^[6] [0] = p ++ 0 :: u ∧
      (subst (literalSecondSubstitution b d w))^[6] [1] = q ++ 0 :: t ∧ Equiv1 p q

def SecondPrimitiveType : Prop :=
  ∀ (b d : Nat) (w : List (Fin 3)),
    literalParikhZ w = ![0, ((b + d + 2 : Nat) : Int), 3] →
    ∃ n ≥ 1, ∀ a c, 0 < (inc (literalSecondSubstitution b d w) ^ n) a c

def SecondIrreducibleType : Prop :=
  ∀ (b d : Nat) (w : List (Fin 3)),
    literalParikhZ w = ![0, ((b + d + 2 : Nat) : Int), 3] →
    Irreducible ((inc (literalSecondSubstitution b d w)).map
      (Nat.cast : Nat → Rat)).charpoly

def SecondPisotType : Prop :=
  ∀ (b d : Nat) (w : List (Fin 3)),
    literalParikhZ w = ![0, ((b + d + 2 : Nat) : Int), 3] →
    ∃ β : Real, 2 * ((b + d + 2 : Nat) : Real) + 4 < β ∧
      β < 2 * ((b + d + 2 : Nat) : Real) + 5 ∧
      Polynomial.aeval (β : Complex)
        ((inc (literalSecondSubstitution b d w)).map (Nat.cast : Nat → Rat)).charpoly = 0 ∧
      ∀ z : Complex,
        Polynomial.aeval z
          ((inc (literalSecondSubstitution b d w)).map (Nat.cast : Nat → Rat)).charpoly = 0 →
        z ≠ β → ‖z‖ < 1

def Z4CoincidenceType : Prop :=
  ∀ (shape : Fin 3) (b d : Nat), ∃ p q u t : List (Fin 3),
    (subst (literalZ4Substitution shape b d))^[3] [0] = p ++ 1 :: u ∧
    (subst (literalZ4Substitution shape b d))^[3] [1] = q ++ 1 :: t ∧ Equiv1 p q

def ThirdLayerUnitRootType : Prop :=
  ∀ e : Nat, Polynomial.aeval (1 : Complex)
    ((literalThirdMatrix e).map (Nat.cast : Nat → Rat)).charpoly = 0

def ResidualParameterType : Prop :=
  ∀ e Z j : Int, 2 ≤ e → 3 ≤ Z → 1 ≤ j →
    (Z - 3) * e + (Z - 1) * (j - 1) ≤ 3 →
    (Z = 3 ∧ (j = 1 ∨ j = 2)) ∨
      (Z = 4 ∧ j = 1 ∧ (e = 2 ∨ e = 3))

def ResidualRunSplitType : Prop :=
  ∀ a c r t e j : Int, 1 ≤ c → 1 ≤ r → 2 ≤ e → 1 ≤ j →
    a + c = r + t + 1 → r + 2 ≤ a →
    (r + t - 3) * e + (r + t - 1) * (j - 1) ≤ 3 →
    (a = 3 ∧ c = 1 ∧ r = 1 ∧ t = 2 ∧ (j = 1 ∨ j = 2)) ∨
      (j = 1 ∧ (e = 2 ∨ e = 3) ∧
        ((a = 3 ∧ c = 2 ∧ r = 1 ∧ t = 3) ∨
         (a = 4 ∧ c = 1 ∧ r = 1 ∧ t = 3) ∨
         (a = 4 ∧ c = 1 ∧ r = 2 ∧ t = 2)))

def FirstSimultaneousType : Prop :=
  ∀ (e : Nat) (v w : List (Fin 3)),
    literalParikhZ v = ![0, 2 * (e : Int) - 2, 1] →
    literalParikhZ w = ![0, (e : Int) - 2, 2] →
    ∃ p r : Fin 3 → List (Fin 3),
      (∀ a, (subst (literalSubstitution v w))^[7] [a] = p a ++ 0 :: r a) ∧
      (∀ a b, Equiv1 (p a) (p b))

def SecondSimultaneousType : Prop :=
  ∀ (b d : Nat) (w : List (Fin 3)),
    literalParikhZ w = ![0, ((b + d + 2 : Nat) : Int), 3] →
    ∃ p r : Fin 3 → List (Fin 3),
      (∀ a, (subst (literalSecondSubstitution b d w))^[7] [a] = p a ++ 0 :: r a) ∧
      (∀ a b, Equiv1 (p a) (p b))

def Z4SimultaneousType : Prop :=
  ∀ (shape : Fin 3) (b d : Nat),
    ∃ p r : Fin 3 → List (Fin 3),
      (∀ a, (subst (literalZ4Substitution shape b d))^[4] [a] = p a ++ 1 :: r a) ∧
      (∀ a b, Equiv1 (p a) (p b))

-- Whole declaration assignments reject added premises, changed source words,
-- alternate parameter ranges, weaker root bounds, or a wrong common letter.
example : FirstCoincidenceType := Psc.A1PrimeTailCoincidence.six_level_coincidence
example : FirstPrimitiveType := Psc.A1PrimeTailPisot.primitive
example : FirstIrreducibleType := Psc.A1PrimeTailPisot.irreducible
example : FirstPisotType := Psc.A1PrimeTailPisot.pisot
example : SecondCoincidenceType := Psc.A1PrimeTailCoincidence.second_layer_six_level
example : SecondPrimitiveType := Psc.A1PrimeTailPisot.second_primitive
example : SecondIrreducibleType := Psc.A1PrimeTailPisot.second_irreducible
example : SecondPisotType := Psc.A1PrimeTailPisot.second_pisot
example : Z4CoincidenceType := Psc.A1PrimeTailCoincidence.z4_three_level
example : ThirdLayerUnitRootType := Psc.A1PrimeTailPisot.third_layer_unit_root
example : ResidualParameterType := Psc.A1PrimeTailCoincidence.residual_parameter_cases
example : ResidualRunSplitType := Psc.A1PrimeTailPisot.residual_run_split
example : FirstSimultaneousType := Psc.A1PrimeTailCoincidence.first_layer_simultaneous
example : SecondSimultaneousType := Psc.A1PrimeTailCoincidence.second_layer_simultaneous
example : Z4SimultaneousType := Psc.A1PrimeTailCoincidence.z4_simultaneous

theorem wrongTypeControl : True := True.intro

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``Psc.A1PrimeTailCoincidence.six_level_coincidence, ``FirstCoincidenceType,
        `PscVerif.A1PrimeTailCoincidence),
      (``Psc.A1PrimeTailPisot.primitive, ``FirstPrimitiveType,
        `PscVerif.A1PrimeTailPisot),
      (``Psc.A1PrimeTailPisot.irreducible, ``FirstIrreducibleType,
        `PscVerif.A1PrimeTailPisot),
      (``Psc.A1PrimeTailPisot.pisot, ``FirstPisotType,
        `PscVerif.A1PrimeTailPisot),
      (``Psc.A1PrimeTailCoincidence.second_layer_six_level, ``SecondCoincidenceType,
        `PscVerif.A1PrimeTailCoincidence),
      (``Psc.A1PrimeTailPisot.second_primitive, ``SecondPrimitiveType,
        `PscVerif.A1PrimeTailPisot),
      (``Psc.A1PrimeTailPisot.second_irreducible, ``SecondIrreducibleType,
        `PscVerif.A1PrimeTailPisot),
      (``Psc.A1PrimeTailPisot.second_pisot, ``SecondPisotType,
        `PscVerif.A1PrimeTailPisot),
      (``Psc.A1PrimeTailCoincidence.z4_three_level, ``Z4CoincidenceType,
        `PscVerif.A1PrimeTailCoincidence),
      (``Psc.A1PrimeTailPisot.third_layer_unit_root, ``ThirdLayerUnitRootType,
        `PscVerif.A1PrimeTailPisot),
      (``Psc.A1PrimeTailCoincidence.residual_parameter_cases, ``ResidualParameterType,
        `PscVerif.A1PrimeTailCoincidence),
      (``Psc.A1PrimeTailPisot.residual_run_split, ``ResidualRunSplitType,
        `PscVerif.A1PrimeTailPisot),
      (``Psc.A1PrimeTailCoincidence.first_layer_simultaneous, ``FirstSimultaneousType,
        `PscVerif.A1PrimeTailCoincidence),
      (``Psc.A1PrimeTailCoincidence.second_layer_simultaneous, ``SecondSimultaneousType,
        `PscVerif.A1PrimeTailCoincidence),
      (``Psc.A1PrimeTailCoincidence.z4_simultaneous, ``Z4SimultaneousType,
        `PscVerif.A1PrimeTailCoincidence)]
    let env ← getEnv
    let matchesType (name expected : Name) : Term.TermElabM Bool := do
      let some info := env.find? name | return false
      if !info.isTheorem then return false
      let some expectedInfo := env.find? expected | return false
      if info.levelParams.length != expectedInfo.levelParams.length then return false
      withNewMCtxDepth do
        let declaration ← mkConstWithFreshMVarLevels name
        let declarationType ← inferType declaration
        -- Expected universe parameters remain rigid; compare complete types.
        let expectedType := mkConst expected (expectedInfo.levelParams.map Level.param)
        withTransparency .all <| isDefEq declarationType expectedType
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let modules := #[`PscVerif.A1PrimeTailCoincidence, `PscVerif.A1PrimeTailPisot]
    let mut declarations := 0
    let mut proofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled family module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut owned := 0
      let mut ownedProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local family axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard family axiom in {info.name}: {ax}"
        owned := owned + 1
        if info.isTheorem then ownedProofs := ownedProofs + 1
      if owned == 0 then throwError "Empty compiled family module: {mod}"
      declarations := declarations + owned
      proofs := proofs + ownedProofs
      Lean.Core.liftIOCore <| IO.println s!"PSC_A1_TAIL_MODULE\t{mod}\t{owned}\t{ownedProofs}"
    Lean.Core.liftIOCore <| IO.println s!"PSC_A1_TAIL_DECLARATIONS\t2\t{declarations}\t{proofs}"
    for (name, expected, expectedOwner) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed family endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Family endpoint has no imported owner: {name}"
      unless env.header.moduleNames[owner.toNat]! == expectedOwner do
        throwError "Wrong family endpoint owner: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard family endpoint axiom in {name}: {ax}"
      let names := String.intercalate "," (axioms.toList.map toString)
      Lean.Core.liftIOCore <| IO.println s!"PSC_A1_TAIL_ENDPOINT\t{name}\t{names}"
    -- Exercise the same recognizer independently of the successful endpoints.
    -- Missing declarations and harmless True proofs both must be refused.
    if (env.find? `Psc.A1PrimeTailAudit.absentEndpoint).isSome then
      throwError "Missing-declaration control name collision"
    for (_, expected, _) in endpoints do
      let wrong := ``wrongTypeControl
      if ← matchesType wrong expected then
        throwError "Family endpoint audit accepted a wrong-type theorem"
      if ← matchesType `Psc.A1PrimeTailAudit.absentEndpoint expected then
        throwError "Family endpoint audit accepted a missing declaration"
    Lean.Core.liftIOCore <| IO.println "PSC_A1_TAIL_AUDIT_COMPLETE\t15\t30"

end Psc.A1PrimeTailAudit
