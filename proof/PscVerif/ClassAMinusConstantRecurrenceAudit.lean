/- Exact semantic acceptance for the minus-Class-A constant recurrence.
The expected types independently spell the coefficient inequalities,
strict rounding, quantifiers, literal images, original occurrence ordinals,
integral signs and composable strict path. No arbitrary-overlap central
entry, Perron-root identification or nested-prefix assembly is audited. -/
import PscVerif.ClassAMinusConstantRecurrence
import Lean.Util.CollectAxioms

namespace Psc.ClassAMinusConstantRecurrenceAudit

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Matrix

def ForwardBoundType : Prop :=
  ∀ A B : ℝ, 0 ≤ A → A < 1/2 → 0 < B → A+B < 1 →
    ∀ u : ℕ → ℤ,
      (∀ n, |(u (n+2) : ℝ)-(A*(u n : ℝ)+B*(u (n+1) : ℝ))| < 1/2) →
      ∃ C : ℕ, ∀ n, |u n| ≤ (C : ℤ)

def TwoSidedType : Prop :=
  ∀ A B : ℝ, 0 ≤ A → A < 1/2 → 0 < B → A+B < 1 →
    ∀ u : ℤ → ℤ,
      (∀ z, |(u (z+2) : ℝ)-(A*(u z : ℝ)+B*(u (z+1) : ℝ))| < 1/2) →
      (∃ C : ℤ, ∀ z, |u z| ≤ C) →
      ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ z, u z = H

def PeriodicType : Prop :=
  ∀ A B : ℝ, 0 ≤ A → A < 1/2 → 0 < B → A+B < 1 →
    ∀ (u : ℤ → ℤ) (T : ℤ), 0 < T → (∀ z, u (z+T) = u z) →
      (∀ z, |(u (z+2) : ℝ)-(A*(u z : ℝ)+B*(u (z+1) : ℝ))| < 1/2) →
      ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ z, u z = H

def EventualTailType : Prop :=
  ∀ A B : ℝ, 0 ≤ A → A < 1/2 → 0 < B → A+B < 1 →
    ∀ u : ℕ → ℤ,
      (∀ n, |(u (n+2) : ℝ)-(A*(u n : ℝ)+B*(u (n+1) : ℝ))| < 1/2) →
      ∃ N : ℕ, ∃ H : ℤ, |(1-A-B)*(H : ℝ)| < 1/2 ∧ ∀ m, u (N+m) = H

def AmplitudeType : Prop :=
  ∀ (A B : ℝ) (H : ℤ),
    (|(H : ℝ)-(A*(H : ℝ)+B*(H : ℝ))| < 1/2) ↔
      |(1-A-B)*(H : ℝ)| < 1/2

def literalSigma (n d : ℕ) (a : Fin 3) : Word :=
  [if a = 1 then 1 else 0] ++
    List.replicate (if a = 0 then n+d else if a = 1 then n else n-1) 2 ++
    [if a = 2 then 1 else 0]

def literalPacket (a b : Fin 3) (p q r : ℤ) : Packet :=
  ⟨a, b, ![-p, -q, -r]⟩

def LiteralIndexedStep (s : Fin 3 → Word) (p : Packet) (i j : ℕ) (q : Packet) : Prop :=
  ∃ (dt : Mark (s p.top)) (db : Mark (s p.bottom)),
    dt.before.length = i ∧ db.before.length = j ∧
    q = ⟨dt.letter, db.letter,
      incidenceZ s *ᵥ p.delta + OccurrenceTransport.residual dt.before db.before⟩

def DecrementType : Prop :=
  ∀ n d H : ℕ, 5 ≤ d → 1 ≤ H → 2*d*H ≤ n →
    LiteralIndexedStep (literalSigma n d) (literalPacket 2 2 (H : ℤ) (-(H : ℤ)) 0)
      (d*H+2) 1 (literalPacket 2 2 (H : ℤ) (-(H : ℤ)) (-1)) ∧
    LiteralIndexedStep (literalSigma n d) (literalPacket 2 2 (H : ℤ) (-(H : ℤ)) (-1))
      1 (n+2-d*H) (literalPacket 2 2 ((H : ℤ)-1) (-(H : ℤ)-1) 2) ∧
    LiteralIndexedStep (literalSigma n d) (literalPacket 2 2 ((H : ℤ)-1) (-(H : ℤ)-1) 2)
      (((d : ℤ)*((H : ℤ)-1)-2).toNat+1)
      ((2-(d : ℤ)*((H : ℤ)-1)).toNat+1)
      (literalPacket 2 2 ((H : ℤ)-1) (-(H : ℤ)+1) 0)

def LiteralInterior (ℓ : Fin 3 → ℝ) (p : Packet) : Prop :=
  ∃ x : ℝ, 0 < x ∧ x < ℓ p.top ∧
    0 < x + (ℓ ⬝ᵥ fun a => (p.delta a : ℝ)) ∧
    x + (ℓ ⬝ᵥ fun a => (p.delta a : ℝ)) < ℓ p.bottom

def LiteralInteriorStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (p q : Packet) : Prop :=
  (∃ (dt : Mark (s p.top)) (db : Mark (s p.bottom)),
    q = ⟨dt.letter, db.letter,
      incidenceZ s *ᵥ p.delta + OccurrenceTransport.residual dt.before db.before⟩) ∧
    LiteralInterior ℓ q

def ComposablePathType : Prop :=
  ∀ n d : ℕ, 5 ≤ d → ∀ H : ℤ, 2*(d : ℤ)*|H| ≤ (n : ℤ) →
    ∀ (ℓ : Fin 3 → ℝ) (β : ℝ), (∀ a, 0 < ℓ a) → 0 < β →
      (∀ a, physicalLength ℓ (literalSigma n d a) = β*ℓ a) →
      LiteralInterior ℓ (literalPacket 2 2 H (-H) 0) ∧
        Relation.ReflTransGen (LiteralInteriorStep (literalSigma n d) ℓ)
          (literalPacket 2 2 H (-H) 0) (literalPacket 2 2 0 0 0)

example : ForwardBoundType := ClassAMinusConstantRecurrence.forward_integer_bound
example : TwoSidedType := ClassAMinusConstantRecurrence.bounded_two_sided_classification
example : PeriodicType := ClassAMinusConstantRecurrence.periodic_cycle_classification
example : EventualTailType := ClassAMinusConstantRecurrence.eventual_constant_tail
example : AmplitudeType := ClassAMinusConstantRecurrence.constant_nearest_iff
example : DecrementType := ClassAMinusConstantRecurrence.three_run_decrement
example : ComposablePathType := ClassAMinusConstantRecurrence.constant_composable_path

theorem wrongTypeControl : True := True.intro
theorem extraForward : True → ForwardBoundType :=
  fun _ => ClassAMinusConstantRecurrence.forward_integer_bound
theorem extraTwoSided : True → TwoSidedType :=
  fun _ => ClassAMinusConstantRecurrence.bounded_two_sided_classification
theorem extraPeriodic : True → PeriodicType :=
  fun _ => ClassAMinusConstantRecurrence.periodic_cycle_classification
theorem extraEventualTail : True → EventualTailType :=
  fun _ => ClassAMinusConstantRecurrence.eventual_constant_tail
theorem extraAmplitude : True → AmplitudeType :=
  fun _ => ClassAMinusConstantRecurrence.constant_nearest_iff
theorem extraDecrement : True → DecrementType :=
  fun _ => ClassAMinusConstantRecurrence.three_run_decrement
theorem extraComposablePath : True → ComposablePathType :=
  fun _ => ClassAMinusConstantRecurrence.constant_composable_path

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``ClassAMinusConstantRecurrence.forward_integer_bound, ``ForwardBoundType, ``extraForward),
      (``ClassAMinusConstantRecurrence.bounded_two_sided_classification, ``TwoSidedType, ``extraTwoSided),
      (``ClassAMinusConstantRecurrence.periodic_cycle_classification, ``PeriodicType, ``extraPeriodic),
      (``ClassAMinusConstantRecurrence.eventual_constant_tail, ``EventualTailType, ``extraEventualTail),
      (``ClassAMinusConstantRecurrence.constant_nearest_iff, ``AmplitudeType, ``extraAmplitude),
      (``ClassAMinusConstantRecurrence.three_run_decrement, ``DecrementType, ``extraDecrement),
      (``ClassAMinusConstantRecurrence.constant_composable_path, ``ComposablePathType, ``extraComposablePath)]
    let env ← getEnv
    let matchesType (name expected : Name) : Term.TermElabM Bool := do
      let some info := env.find? name | return false
      if !info.isTheorem then return false
      let some expectedInfo := env.find? expected | return false
      if info.levelParams.length != expectedInfo.levelParams.length then return false
      withNewMCtxDepth do
        let declaration ← mkConstWithFreshMVarLevels name
        let declarationType ← inferType declaration
        let expectedType := mkConst expected (expectedInfo.levelParams.map Level.param)
        withTransparency .all <| isDefEq declarationType expectedType
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let mod := `PscVerif.ClassAMinusConstantRecurrence
    let some index := env.getModuleIdx? mod
      | throwError "Missing compiled minus-Class-A constant recurrence module"
    let data := env.header.moduleData[index.toNat]!
    let mut declarations := 0
    let mut proofs := 0
    for info in data.constants do
      let some owner := env.getModuleIdxFor? info.name | continue
      if owner != index then continue
      if info.isAxiom then throwError "Local minus-Class-A constant recurrence axiom: {info.name}"
      let axioms ← collectAxioms info.name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard minus-Class-A constant recurrence axiom in {info.name}: {ax}"
      declarations := declarations + 1
      if info.isTheorem then proofs := proofs + 1
    if declarations == 0 then throwError "Empty compiled minus-Class-A constant recurrence module"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_MINUS_CONSTANT_MODULE\t{mod}\t{declarations}\t{proofs}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_MINUS_CONSTANT_DECLARATIONS\t1\t{declarations}\t{proofs}"
    for (name, expected, _) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed minus-Class-A constant recurrence endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Minus-Class-A constant recurrence endpoint has no imported owner: {name}"
      unless owner == index do
        throwError "Wrong minus-Class-A constant recurrence endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_CLASS_A_MINUS_CONSTANT_ENDPOINT\t{name}"
    let missing := `Psc.ClassAMinusConstantRecurrenceAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing control name collision"
    for (_, expected, extra) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Minus-Class-A constant recurrence audit accepted a wrong-type theorem"
      if ← matchesType missing expected then
        throwError "Minus-Class-A constant recurrence audit accepted a missing declaration"
      if ← matchesType extra expected then
        throwError "Minus-Class-A constant recurrence audit accepted an extra premise"
    Lean.Core.liftIOCore <| IO.println "PSC_CLASS_A_MINUS_CONSTANT_AUDIT_COMPLETE\t7\t21"

end Psc.ClassAMinusConstantRecurrenceAudit
