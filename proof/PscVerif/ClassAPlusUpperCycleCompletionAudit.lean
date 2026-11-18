/- Independent literal endpoint types and transitive axiom audit for the
complete upper-height occurrence construction. No expected type is read
from the implementation declaration under inspection. -/
import PscVerif.ClassAPlusUpperCycleCompletion
import Lean.Util.CollectAxioms

namespace Psc.ClassAPlusUpperCycleCompletionAudit

open Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAMinusPrefixAssembly Matrix

def literalSigma (n J : ℕ) (a : Fin 3) : Word :=
  [if a=1 then 1 else 0] ++
    List.replicate (if a=0 then n+(2*n+12-J) else if a=1 then n else n+1) 2 ++
    [if a=2 then 1 else 0]

def literalPacket (a b : Fin 3) (p q r : ℤ) : Packet := ⟨a,b,![-p,-q,-r]⟩
def literalW (H : ℕ) : Packet := literalPacket 2 2 (H : ℤ) (3*(H : ℤ)) (-6*(H : ℤ))
def literalZero : Packet := literalPacket 2 2 0 0 0
def literalDec (J H : ℕ) : List (ℕ × ℕ) := [(0,J*H-2),(J*(H-1)+4,1)]
def literalBaseOne (n H : ℕ) : List (ℕ × ℕ) :=
  [(0,0),(1,1+(n+4)*H),(1,2*H+1)]
def literalBaseTwo (n : ℕ) : List (ℕ × ℕ) := [(0,0),(0,2*n+6),(1,2)]
def literalIndices (n J H : ℕ) : List (ℕ × ℕ) :=
  Nat.rec [] (fun k path =>
    if 3 ≤ J*(k+1) then literalDec J (k+1) ++ path
    else if J=1 then literalBaseOne n (k+1) else literalBaseTwo n) H
def literalSignedSource (rev : Bool) (H : ℕ) : Packet :=
  if rev then (literalW H).swap else literalW H
def literalSignedIndices (rev : Bool) (n J H : ℕ) : List (ℕ × ℕ) :=
  if rev then (literalIndices n J H).map Prod.swap else literalIndices n J H

def DecrementType : Prop :=
  ∀ n J H : ℕ, 7 ≤ n → 1 ≤ J → 1 ≤ H → 3 ≤ J*H → J*H ≤ n-1 →
    OrderedPath (literalSigma n J) (literalW H) (literalDec J H) (literalW (H-1))

def AllPathsType : Prop :=
  ∀ n J H : ℕ, 7 ≤ n → 1 ≤ J → J ≤ n+7 → J*H ≤ n-1 →
    OrderedPath (literalSigma n J) (literalW H) (literalIndices n J H) literalZero

def SignedPathsType : Prop :=
  ∀ n J H : ℕ, 7 ≤ n → 1 ≤ J → J ≤ n+7 → J*H ≤ n-1 → ∀ rev : Bool,
    OrderedPath (literalSigma n J) (literalSignedSource rev H)
      (literalSignedIndices rev n J H) literalZero

def TracedStrictType : Prop :=
  ∀ n J H : ℕ, 7 ≤ n → 1 ≤ J → J ≤ n+7 → J*H ≤ n-1 → ∀ rev : Bool,
    ∀ (ℓ : Fin 3 → ℝ) (β : ℝ), (∀ a, 0 < ℓ a) → 0 < β →
    (∀ a, physicalLength ℓ (literalSigma n J a) = β*ℓ a) →
    OrderedInteriorPath (literalSigma n J) ℓ (literalSignedSource rev H)
      (literalSignedIndices rev n J H) literalZero ∧
    ∃ (top : Mark ((Psc.Binomial.subst (literalSigma n J))^[(literalSignedIndices rev n J H).length]
        [(literalSignedSource rev H).top]))
      (bottom : Mark ((Psc.Binomial.subst (literalSigma n J))^[(literalSignedIndices rev n J H).length]
        [(literalSignedSource rev H).bottom])),
      MarkTrace (literalSigma n J) (literalSignedSource rev H).top
        ((literalSignedIndices rev n J H).map Prod.fst) top.before top.letter top.after ∧
      MarkTrace (literalSigma n J) (literalSignedSource rev H).bottom
        ((literalSignedIndices rev n J H).map Prod.snd) bottom.before bottom.letter bottom.after ∧
      top.letter=2 ∧ bottom.letter=2 ∧
      incidenceZ (literalSigma n J) ^ (literalSignedIndices rev n J H).length *ᵥ
        (-(literalSignedSource rev H).delta) = parikhZ top.before-parikhZ bottom.before

example : DecrementType := ClassAPlusUpperCycleCompletion.decrement_path
example : AllPathsType := ClassAPlusUpperCycleCompletion.all_ordered_paths
example : SignedPathsType := ClassAPlusUpperCycleCompletion.all_signed_ordered_paths
example : TracedStrictType := ClassAPlusUpperCycleCompletion.all_traced_strict_prefixes

theorem wrongTypeControl : True := True.intro
theorem extraDecrement : True → DecrementType :=
  fun _ => ClassAPlusUpperCycleCompletion.decrement_path
theorem extraAll : True → AllPathsType :=
  fun _ => ClassAPlusUpperCycleCompletion.all_ordered_paths
theorem extraSigned : True → SignedPathsType :=
  fun _ => ClassAPlusUpperCycleCompletion.all_signed_ordered_paths
theorem extraTraced : True → TracedStrictType :=
  fun _ => ClassAPlusUpperCycleCompletion.all_traced_strict_prefixes

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``ClassAPlusUpperCycleCompletion.decrement_path, ``DecrementType, ``extraDecrement),
      (``ClassAPlusUpperCycleCompletion.all_ordered_paths, ``AllPathsType, ``extraAll),
      (``ClassAPlusUpperCycleCompletion.all_signed_ordered_paths, ``SignedPathsType, ``extraSigned),
      (``ClassAPlusUpperCycleCompletion.all_traced_strict_prefixes, ``TracedStrictType, ``extraTraced)]
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
    let mod := `PscVerif.ClassAPlusUpperCycleCompletion
    let some index := env.getModuleIdx? mod
      | throwError "Missing compiled upper-cycle completion module: {mod}"
    let data := env.header.moduleData[index.toNat]!
    let mut declarations := 0
    let mut proofs := 0
    for info in data.constants do
      let some owner := env.getModuleIdxFor? info.name | continue
      if owner != index then continue
      if info.isAxiom then throwError "Local upper-cycle completion axiom: {info.name}"
      let axioms ← collectAxioms info.name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard upper-cycle completion axiom in {info.name}: {ax}"
      declarations := declarations+1
      if info.isTheorem then proofs := proofs+1
    if declarations == 0 then throwError "Empty upper-cycle completion module"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_PLUS_UPPER_COMPLETION_MODULE\t{mod}\t{declarations}\t{proofs}"
    for (name, expected, _) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed upper-cycle completion endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Upper-cycle completion endpoint has no compiled owner: {name}"
      unless owner == index do throwError "Wrong upper-cycle completion endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_CLASS_A_PLUS_UPPER_COMPLETION_ENDPOINT\t{name}"
    let missing := `Psc.ClassAPlusUpperCycleCompletionAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing control name collision"
    for (_, expected, extra) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Completion audit accepted a wrong-type theorem"
      if ← matchesType missing expected then
        throwError "Completion audit accepted a missing declaration"
      if ← matchesType extra expected then
        throwError "Completion audit accepted an extra premise"
    Lean.Core.liftIOCore <| IO.println
      "PSC_CLASS_A_PLUS_UPPER_COMPLETION_AUDIT_COMPLETE\t4\t12"

end Psc.ClassAPlusUpperCycleCompletionAudit
