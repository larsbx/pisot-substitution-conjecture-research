/- Exact semantic acceptance for the central nearest-integer recurrence.
The expected types independently spell the real hypotheses, strict rounding
error, quantifiers, actual image words, original indices and integral signs.
No central-entry density theorem or complete zero-hit theorem is audited here. -/
import PscVerif.ClassACentralRecurrence
import Lean.Util.CollectAxioms

namespace Psc.ClassACentralRecurrenceAudit

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Matrix

def ForwardBoundType : Prop :=
  ∀ h α : ℝ, 0 < h → h < 1/8 → 0 < α → α+2*h < 1 →
    ∀ u : ℕ → ℤ,
      (∀ n, |(u (n+2) : ℝ)-(2*h*(u n : ℝ)-α*(u (n+1) : ℝ))| < 1/2) →
      ∃ C : ℕ, ∀ n, |u n| ≤ (C : ℤ)

def PeriodicType : Prop :=
  ∀ h α : ℝ, 0 < h → h < 1/8 → 0 < α → α+2*h < 1 →
    ∀ (u : ℤ → ℤ) (T : ℤ), 0 < T → (∀ z, u (z+T) = u z) →
      (∀ z, |(u (z+2) : ℝ)-(2*h*(u z : ℝ)-α*(u (z+1) : ℝ))| < 1/2) →
      ∃ H : ℤ, 0 ≤ H ∧ (1-α-2*h)*(H : ℝ) < 1/2 ∧
        (∀ z, u z = H ∨ u z = -H) ∧ (∀ z, u (z+1) = -u z)

def TwoSidedType : Prop :=
  ∀ h α : ℝ, 0 < h → h < 1/8 → 0 < α → α+2*h < 1 →
    ∀ u : ℤ → ℤ,
      (∀ z, |(u (z+2) : ℝ)-(2*h*(u z : ℝ)-α*(u (z+1) : ℝ))| < 1/2) →
      (∃ C : ℤ, ∀ z, |u z| ≤ C) →
      ∃ H : ℤ, 0 ≤ H ∧ (1-α-2*h)*(H : ℝ) < 1/2 ∧
        (∀ z, u z = H ∨ u z = -H) ∧ (∀ z, u (z+1) = -u z)

def GapType : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ β θ : ℝ, 0 < β → β < (n : ℝ)+3 → |θ| < 1/2 →
    ∀ g : ℤ, |β*θ+(g : ℝ)| < 1/2 →
      -((n-2 : ℕ) : ℤ) ≤ g ∧ g ≤ ((n-2 : ℕ) : ℤ)

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

def RunDigitsType : Prop :=
  ∀ n d : ℕ, 2 ≤ n → ∀ p q r g : ℤ,
    -((n-2 : ℕ) : ℤ) ≤ g → g ≤ ((n-2 : ℕ) : ℤ) →
      LiteralIndexedStep (literalSigma n d) (literalPacket 2 2 p q r)
        ((-g).toNat+1) (g.toNat+1)
        (literalPacket 2 2 (2*p+q+r) (q+r)
          (((n+d : ℕ) : ℤ)*p+(n : ℤ)*q+((n-1 : ℕ) : ℤ)*r+g))

def CoordinateType : Prop :=
  ∀ (h α : ℝ) (a b r : ℤ),
    |(2+α-h)*(b : ℝ)+(1+h)*((b-2*a : ℤ) : ℝ)+r| < 1/2 →
      |((3*b-2*a+r : ℤ) : ℝ)-(2*h*(a : ℝ)-α*(b : ℝ))| < 1/2

def EventualTailType : Prop :=
  ∀ h α : ℝ, 0 < h → h < 1/8 → 0 < α → α+2*h < 1 →
    ∀ u : ℕ → ℤ,
      (∀ n, |(u (n+2) : ℝ)-(2*h*(u n : ℝ)-α*(u (n+1) : ℝ))| < 1/2) →
      ∃ N : ℕ, ∃ H : ℤ, 0 ≤ H ∧ (1-α-2*h)*(H : ℝ) < 1/2 ∧
        (∀ m, u (N+m) = H ∨ u (N+m) = -H) ∧
        (∀ m, u (N+m+1) = -u (N+m))

example : ForwardBoundType := ClassACentralRecurrence.forward_integer_bound
example : PeriodicType := ClassACentralRecurrence.periodic_cycle_classification
example : TwoSidedType := ClassACentralRecurrence.bounded_two_sided_classification
example : GapType := ClassACentralRecurrence.central_gap_in_run
example : RunDigitsType := ClassACentralRecurrence.run_gap_digit_step
example : CoordinateType := ClassACentralRecurrence.central_coordinate_recurrence
example : EventualTailType := ClassACentralRecurrence.eventual_alternating_tail

theorem wrongTypeControl : True := True.intro
theorem extraForward : True → ForwardBoundType :=
  fun _ => ClassACentralRecurrence.forward_integer_bound
theorem extraPeriodic : True → PeriodicType :=
  fun _ => ClassACentralRecurrence.periodic_cycle_classification
theorem extraTwoSided : True → TwoSidedType :=
  fun _ => ClassACentralRecurrence.bounded_two_sided_classification
theorem extraGap : True → GapType := fun _ => ClassACentralRecurrence.central_gap_in_run
theorem extraRunDigits : True → RunDigitsType :=
  fun _ => ClassACentralRecurrence.run_gap_digit_step
theorem extraCoordinate : True → CoordinateType :=
  fun _ => ClassACentralRecurrence.central_coordinate_recurrence
theorem extraEventualTail : True → EventualTailType :=
  fun _ => ClassACentralRecurrence.eventual_alternating_tail

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``ClassACentralRecurrence.forward_integer_bound, ``ForwardBoundType, ``extraForward),
      (``ClassACentralRecurrence.periodic_cycle_classification, ``PeriodicType, ``extraPeriodic),
      (``ClassACentralRecurrence.bounded_two_sided_classification, ``TwoSidedType, ``extraTwoSided),
      (``ClassACentralRecurrence.central_gap_in_run, ``GapType, ``extraGap),
      (``ClassACentralRecurrence.run_gap_digit_step, ``RunDigitsType, ``extraRunDigits),
      (``ClassACentralRecurrence.central_coordinate_recurrence, ``CoordinateType, ``extraCoordinate),
      (``ClassACentralRecurrence.eventual_alternating_tail, ``EventualTailType, ``extraEventualTail)]
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
    let mod := `PscVerif.ClassACentralRecurrence
    let some index := env.getModuleIdx? mod
      | throwError "Missing compiled Class-A central recurrence module"
    let data := env.header.moduleData[index.toNat]!
    let mut declarations := 0
    let mut proofs := 0
    for info in data.constants do
      let some owner := env.getModuleIdxFor? info.name | continue
      if owner != index then continue
      if info.isAxiom then throwError "Local Class-A central recurrence axiom: {info.name}"
      let axioms ← collectAxioms info.name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard Class-A central recurrence axiom in {info.name}: {ax}"
      declarations := declarations + 1
      if info.isTheorem then proofs := proofs + 1
    if declarations == 0 then throwError "Empty compiled Class-A central recurrence module"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_CENTRAL_MODULE\t{mod}\t{declarations}\t{proofs}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_CENTRAL_DECLARATIONS\t1\t{declarations}\t{proofs}"
    for (name, expected, _) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed Class-A central recurrence endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Class-A central recurrence endpoint has no imported owner: {name}"
      unless owner == index do
        throwError "Wrong Class-A central recurrence endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_CLASS_A_CENTRAL_ENDPOINT\t{name}"
    let missing := `Psc.ClassACentralRecurrenceAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing control name collision"
    for (_, expected, extra) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Class-A central recurrence audit accepted a wrong-type theorem"
      if ← matchesType missing expected then
        throwError "Class-A central recurrence audit accepted a missing declaration"
      if ← matchesType extra expected then
        throwError "Class-A central recurrence audit accepted an extra premise"
    Lean.Core.liftIOCore <| IO.println "PSC_CLASS_A_CENTRAL_AUDIT_COMPLETE\t7\t21"

end Psc.ClassACentralRecurrenceAudit
