/- Exact-type acceptance for the constructive Class-A escape subfamilies.
Expected types retain literal source images, both proper-prefix occurrences,
the chosen numeric ordinals, full integral offsets, and strict composition.
The full zero-defect ten-edge theorem is not a Lean endpoint of this audit. -/
import PscVerif.ClassAZeroDefectEscape
import Lean.Util.CollectAxioms

namespace Psc.ClassAZeroDefectEscapeAudit

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Matrix

/-- Independent literal spelling of the actual three substitution words. -/
def literalSigma (n d : ℕ) (a : Fin 3) : Word :=
  [if a = 1 then 1 else 0] ++
    List.replicate (if a = 0 then n + d else if a = 1 then n else n - 1) 2 ++
    [if a = 2 then 1 else 0]

def literalPacket (a b : Fin 3) (p q r : ℤ) : Packet :=
  ⟨a, b, ![-p, -q, -r]⟩

/-- Literal prefix lengths pin the original source occurrence ordinals. -/
def LiteralIndexedStep (s : Fin 3 → Word) (p : Packet) (i j : ℕ)
    (q : Packet) : Prop :=
  ∃ (dt : Mark (s p.top)) (db : Mark (s p.bottom)),
    dt.before.length = i ∧ db.before.length = j ∧
    q = ⟨dt.letter, db.letter,
      incidenceZ s *ᵥ p.delta + OccurrenceTransport.residual dt.before db.before⟩

def LiteralInteriorStep (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (p : Packet) (i j : ℕ) (q : Packet) : Prop :=
  LiteralIndexedStep s p i j q ∧ q.Interior ℓ

def literalRunLength (n d : ℕ) (a : Fin 3) : ℕ :=
  if a = 0 then n + d else if a = 1 then n else n - 1

def literalDifference (a b : Fin 3) : ℤ :=
  (if a = 1 then 0 else 1) - (if b = 1 then 0 else 1)

def literalSlice (n d : ℕ) (a b : Fin 3) (S h : ℤ) : Packet :=
  let q := h - ((d : ℤ) + 1) * literalDifference a b + ((d : ℤ) - n) * S
  literalPacket a b (literalDifference a b - S) q (2*S-literalDifference a b-q)

def OverrunDigitsType : Prop :=
  ∀ n d : ℕ, 2 ≤ n →
    LiteralIndexedStep (literalSigma n d)
      (literalPacket 2 2 0 ((n : ℤ)+1) (-(n : ℤ)-1)) n 0
      (literalPacket 1 0 (-1) 0 2) ∧
    LiteralIndexedStep (literalSigma n d) (literalPacket 1 0 (-1) 0 2)
      (n+1) (d+1) (literalPacket 0 2 1 1 (-2)) ∧
    LiteralIndexedStep (literalSigma n d) (literalPacket 0 2 1 1 (-2))
      (d+2) 0 (literalPacket 2 0 0 (-1) 1) ∧
    LiteralIndexedStep (literalSigma n d) (literalPacket 2 0 0 (-1) 1)
      1 2 (literalPacket 2 2 0 0 0)

def OverrunStepsType : Prop :=
  ∀ n d : ℕ, 2 ≤ n → ∀ (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (literalSigma n d a) = β * ℓ a) →
    LiteralInteriorStep (literalSigma n d) ℓ
      (literalPacket 2 2 0 ((n : ℤ)+1) (-(n : ℤ)-1)) n 0
      (literalPacket 1 0 (-1) 0 2) ∧
    LiteralInteriorStep (literalSigma n d) ℓ (literalPacket 1 0 (-1) 0 2)
      (n+1) (d+1) (literalPacket 0 2 1 1 (-2)) ∧
    LiteralInteriorStep (literalSigma n d) ℓ (literalPacket 0 2 1 1 (-2))
      (d+2) 0 (literalPacket 2 0 0 (-1) 1) ∧
    LiteralInteriorStep (literalSigma n d) ℓ (literalPacket 2 0 0 (-1) 1)
      1 2 (literalPacket 2 2 0 0 0) ∧
    (literalPacket 2 2 0 ((n : ℤ)+1) (-(n : ℤ)-1)).Interior ℓ ∧
    (literalPacket 2 2 0 0 0).delta = 0

def OverrunPathType : Prop :=
  ∀ n d : ℕ, 2 ≤ n → ∀ (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (literalSigma n d a) = β * ℓ a) →
    Relation.ReflTransGen (InteriorStep (literalSigma n d) ℓ)
      (literalPacket 2 2 0 ((n : ℤ)+1) (-(n : ℤ)-1)) (literalPacket 2 2 0 0 0)

def RunDigitsType : Prop :=
  ∀ n d : ℕ, 2 ≤ n → ∀ (a b : Fin 3) (S h : ℤ),
    1 - (literalRunLength n d b : ℤ) ≤ h →
    h ≤ (literalRunLength n d a : ℤ) - 1 →
    -((n - 1 : ℕ) : ℤ) ≤ 2*S → 2*S ≤ ((n - 1 : ℕ) : ℤ) →
    ∃ goal : Packet,
      LiteralIndexedStep (literalSigma n d) (literalSlice n d a b S h)
        (h.toNat+1) ((-h).toNat+1) (literalPacket 2 2 0 (2*S) (-2*S)) ∧
      LiteralIndexedStep (literalSigma n d) (literalPacket 2 2 0 (2*S) (-2*S))
        ((2*S).toNat+1) ((-(2*S)).toNat+1) goal ∧ goal.delta = 0

def RunStepsType : Prop :=
  ∀ n d : ℕ, 2 ≤ n → ∀ (a b : Fin 3) (S h : ℤ),
    1 - (literalRunLength n d b : ℤ) ≤ h →
    h ≤ (literalRunLength n d a : ℤ) - 1 →
    -((n - 1 : ℕ) : ℤ) ≤ 2*S → 2*S ≤ ((n - 1 : ℕ) : ℤ) →
    ∀ (ℓ : Fin 3 → ℝ) (β : ℝ),
    (∀ c, 0 < ℓ c) → 0 < β →
    (∀ c, physicalLength ℓ (literalSigma n d c) = β * ℓ c) →
    ∃ goal : Packet,
      LiteralInteriorStep (literalSigma n d) ℓ (literalSlice n d a b S h)
        (h.toNat+1) ((-h).toNat+1) (literalPacket 2 2 0 (2*S) (-2*S)) ∧
      LiteralInteriorStep (literalSigma n d) ℓ (literalPacket 2 2 0 (2*S) (-2*S))
        ((2*S).toNat+1) ((-(2*S)).toNat+1) goal ∧
      (literalSlice n d a b S h).Interior ℓ ∧ goal.delta = 0

example : OverrunDigitsType := ClassAZeroDefectEscape.overrun_four_digit_steps
example : OverrunStepsType := ClassAZeroDefectEscape.overrun_four_steps
example : OverrunPathType := ClassAZeroDefectEscape.overrun_composable_path
example : RunDigitsType := ClassAZeroDefectEscape.run_slice_two_digit_steps
example : RunStepsType := ClassAZeroDefectEscape.run_slice_two_steps

theorem wrongTypeControl : True := True.intro

theorem extraOverrunDigits : True → OverrunDigitsType :=
  fun _ => ClassAZeroDefectEscape.overrun_four_digit_steps
theorem extraOverrunSteps : True → OverrunStepsType :=
  fun _ => ClassAZeroDefectEscape.overrun_four_steps
theorem extraOverrunPath : True → OverrunPathType :=
  fun _ => ClassAZeroDefectEscape.overrun_composable_path
theorem extraRunDigits : True → RunDigitsType :=
  fun _ => ClassAZeroDefectEscape.run_slice_two_digit_steps
theorem extraRunSteps : True → RunStepsType :=
  fun _ => ClassAZeroDefectEscape.run_slice_two_steps

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``ClassAZeroDefectEscape.overrun_four_digit_steps, ``OverrunDigitsType,
        ``extraOverrunDigits),
      (``ClassAZeroDefectEscape.overrun_four_steps, ``OverrunStepsType, ``extraOverrunSteps),
      (``ClassAZeroDefectEscape.overrun_composable_path, ``OverrunPathType, ``extraOverrunPath),
      (``ClassAZeroDefectEscape.run_slice_two_digit_steps, ``RunDigitsType, ``extraRunDigits),
      (``ClassAZeroDefectEscape.run_slice_two_steps, ``RunStepsType, ``extraRunSteps)]
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
    let mod := `PscVerif.ClassAZeroDefectEscape
    let some index := env.getModuleIdx? mod
      | throwError "Missing compiled Class-A escape module"
    let data := env.header.moduleData[index.toNat]!
    let mut declarations := 0
    let mut proofs := 0
    for info in data.constants do
      let some owner := env.getModuleIdxFor? info.name | continue
      if owner != index then continue
      if info.isAxiom then throwError "Local Class-A escape axiom: {info.name}"
      let axioms ← collectAxioms info.name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard Class-A escape axiom in {info.name}: {ax}"
      declarations := declarations + 1
      if info.isTheorem then proofs := proofs + 1
    if declarations == 0 then throwError "Empty compiled Class-A escape module"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_ESCAPE_MODULE\t{mod}\t{declarations}\t{proofs}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_ESCAPE_DECLARATIONS\t1\t{declarations}\t{proofs}"
    for (name, expected, _) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed Class-A escape endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Class-A escape endpoint has no imported owner: {name}"
      unless owner == index do
        throwError "Wrong Class-A escape endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_CLASS_A_ESCAPE_ENDPOINT\t{name}"
    let missing := `Psc.ClassAZeroDefectEscapeAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing control name collision"
    for (_, expected, extra) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Class-A escape audit accepted a wrong-type theorem"
      if ← matchesType missing expected then
        throwError "Class-A escape audit accepted a missing declaration"
      if ← matchesType extra expected then
        throwError "Class-A escape audit accepted an extra premise"
    Lean.Core.liftIOCore <| IO.println "PSC_CLASS_A_ESCAPE_AUDIT_COMPLETE\t5\t15"

end Psc.ClassAZeroDefectEscapeAudit
