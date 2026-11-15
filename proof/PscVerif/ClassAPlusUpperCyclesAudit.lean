/- Independent endpoint types and transitive axiom audit for the upper
eight-case occurrence construction. All literal words, source coordinates,
transcripts, parameter guards and strict/prefix premises are restated here. -/
import PscVerif.ClassAPlusUpperCycles
import Lean.Util.CollectAxioms

namespace Psc.ClassAPlusUpperCyclesAudit

open Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAMinusPrefixAssembly Matrix

def literalSigma (n J : ℕ) (a : Fin 3) : Word :=
  [if a=1 then 1 else 0] ++
    List.replicate (if a=0 then n+(2*n+12-J) else if a=1 then n else n+1) 2 ++
    [if a=2 then 1 else 0]

def literalPacket (a b : Fin 3) (p q r : ℤ) : Packet := ⟨a,b,![-p,-q,-r]⟩
def literalW (H : ℕ) : Packet := literalPacket 2 2 (H : ℤ) (3*(H : ℤ)) (-6*(H : ℤ))
def literalZero : Packet := literalPacket 2 2 0 0 0
def literalCases (J H : ℕ) : Prop :=
  (J,H) ∈ [(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,1)]
def literalDec (J H : ℕ) : List (ℕ × ℕ) := [(0,J*H-2),(J*(H-1)+4,1)]
def literalBaseOne (n H : ℕ) : List (ℕ × ℕ) :=
  [(0,0),(1,1+(n+4)*H),(1,2*H+1)]
def literalBaseTwo (n : ℕ) : List (ℕ × ℕ) := [(0,0),(0,2*n+6),(1,2)]
def literalIndices (n J H : ℕ) : List (ℕ × ℕ) :=
  if J=1 then
    if H=1 then literalBaseOne n 1
    else if H=2 then literalBaseOne n 2
    else if H=3 then literalDec 1 3 ++ literalBaseOne n 2
    else literalDec 1 4 ++ literalDec 1 3 ++ literalBaseOne n 2
  else if J=2 then
    if H=1 then literalBaseTwo n else literalDec 2 2 ++ literalBaseTwo n
  else literalDec J H
def literalSignedSource (rev : Bool) (H : ℕ) : Packet :=
  if rev then (literalW H).swap else literalW H
def literalSignedIndices (rev : Bool) (n J H : ℕ) : List (ℕ × ℕ) :=
  if rev then (literalIndices n J H).map Prod.swap else literalIndices n J H

def DecrementType : Prop :=
  ∀ n J H : ℕ, 7 ≤ n → 1 ≤ J → 1 ≤ H → 3 ≤ J*H → J*H ≤ 4 →
    OrderedPath (literalSigma n J) (literalW H) (literalDec J H) (literalW (H-1))

def BaseOneType : Prop :=
  ∀ n H : ℕ, 7 ≤ n → 1 ≤ H → H ≤ 2 →
    OrderedPath (literalSigma n 1) (literalW H) (literalBaseOne n H) literalZero

def BaseTwoType : Prop :=
  ∀ n : ℕ, 7 ≤ n →
    OrderedPath (literalSigma n 2) (literalW 1) (literalBaseTwo n) literalZero

def EightPathsType : Prop :=
  ∀ n J H : ℕ, 7 ≤ n → literalCases J H →
    OrderedPath (literalSigma n J) (literalW H) (literalIndices n J H) literalZero

def SignedPathsType : Prop :=
  ∀ n J H : ℕ, 7 ≤ n → literalCases J H → ∀ rev : Bool,
    OrderedPath (literalSigma n J) (literalSignedSource rev H)
      (literalSignedIndices rev n J H) literalZero

def TracedStrictType : Prop :=
  ∀ n J H : ℕ, 7 ≤ n → literalCases J H → ∀ rev : Bool,
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

def TypedZeroType : Prop := literalZero.Diagonal

def LastControlType : Prop :=
  ∀ n d : ℕ,
    (ClassAPlusUpperCycles.lastMark n d 2).index = n+2 ∧
      (ClassAPlusUpperCycles.lastMark n d 2).letter=1 ∧
      (ClassAPlusUpperCycles.lastMark n d 2).letter ≠ 2

example : DecrementType := ClassAPlusUpperCycles.small_decrement
example : BaseOneType := ClassAPlusUpperCycles.base_one_path
example : BaseTwoType := ClassAPlusUpperCycles.base_two_path
example : EightPathsType := ClassAPlusUpperCycles.eight_ordered_paths
example : SignedPathsType := ClassAPlusUpperCycles.signed_ordered_paths
example : TracedStrictType := ClassAPlusUpperCycles.eight_traced_strict_prefixes
example : TypedZeroType := ClassAPlusUpperCycles.zero_typed
example : LastControlType := ClassAPlusUpperCycles.disputed_last_is_c

theorem wrongTypeControl : True := True.intro
theorem extraDecrement : True → DecrementType := fun _ => ClassAPlusUpperCycles.small_decrement
theorem extraBaseOne : True → BaseOneType := fun _ => ClassAPlusUpperCycles.base_one_path
theorem extraBaseTwo : True → BaseTwoType := fun _ => ClassAPlusUpperCycles.base_two_path
theorem extraEight : True → EightPathsType := fun _ => ClassAPlusUpperCycles.eight_ordered_paths
theorem extraSigned : True → SignedPathsType := fun _ => ClassAPlusUpperCycles.signed_ordered_paths
theorem extraTraced : True → TracedStrictType := fun _ => ClassAPlusUpperCycles.eight_traced_strict_prefixes
theorem extraZero : True → TypedZeroType := fun _ => ClassAPlusUpperCycles.zero_typed
theorem extraLast : True → LastControlType := fun _ => ClassAPlusUpperCycles.disputed_last_is_c

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let endpoints : Array (Name × Name × Name) := #[
      (``ClassAPlusUpperCycles.small_decrement, ``DecrementType, ``extraDecrement),
      (``ClassAPlusUpperCycles.base_one_path, ``BaseOneType, ``extraBaseOne),
      (``ClassAPlusUpperCycles.base_two_path, ``BaseTwoType, ``extraBaseTwo),
      (``ClassAPlusUpperCycles.eight_ordered_paths, ``EightPathsType, ``extraEight),
      (``ClassAPlusUpperCycles.signed_ordered_paths, ``SignedPathsType, ``extraSigned),
      (``ClassAPlusUpperCycles.eight_traced_strict_prefixes, ``TracedStrictType, ``extraTraced),
      (``ClassAPlusUpperCycles.zero_typed, ``TypedZeroType, ``extraZero),
      (``ClassAPlusUpperCycles.disputed_last_is_c, ``LastControlType, ``extraLast)]
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
    let modules := #[`PscVerif.ClassAMinusPrefixAssembly, `PscVerif.ClassAPlusUpperCycles]
    let mut declarations := 0
    let mut proofs := 0
    for mod in modules do
      let some index := env.getModuleIdx? mod
        | throwError "Missing compiled upper-cycle dependency module: {mod}"
      let data := env.header.moduleData[index.toNat]!
      let mut localDeclarations := 0
      let mut localProofs := 0
      for info in data.constants do
        let some owner := env.getModuleIdxFor? info.name | continue
        if owner != index then continue
        if info.isAxiom then throwError "Local upper-cycle axiom: {info.name}"
        let axioms ← collectAxioms info.name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Nonstandard upper-cycle axiom in {info.name}: {ax}"
        localDeclarations := localDeclarations+1
        if info.isTheorem then localProofs := localProofs+1
      if localDeclarations == 0 then throwError "Empty upper-cycle dependency module: {mod}"
      declarations := declarations+localDeclarations
      proofs := proofs+localProofs
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_CLASS_A_PLUS_UPPER_MODULE\t{mod}\t{localDeclarations}\t{localProofs}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_CLASS_A_PLUS_UPPER_DECLARATIONS\t{modules.size}\t{declarations}\t{proofs}"
    let some ownerIndex := env.getModuleIdx? `PscVerif.ClassAPlusUpperCycles
      | throwError "Missing upper-cycle endpoint module"
    for (name, expected, _) in endpoints do
      unless ← matchesType name expected do
        throwError "Missing or wrong-typed upper-cycle endpoint: {name}"
      let some owner := env.getModuleIdxFor? name
        | throwError "Upper-cycle endpoint has no compiled owner: {name}"
      unless owner == ownerIndex do throwError "Wrong upper-cycle endpoint owner: {name}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_CLASS_A_PLUS_UPPER_ENDPOINT\t{name}"
    let missing := `Psc.ClassAPlusUpperCyclesAudit.absentEndpoint
    if (env.find? missing).isSome then throwError "Missing control name collision"
    for (_, expected, extra) in endpoints do
      if ← matchesType ``wrongTypeControl expected then
        throwError "Upper-cycle audit accepted a wrong-type theorem"
      if ← matchesType missing expected then
        throwError "Upper-cycle audit accepted a missing declaration"
      if ← matchesType extra expected then
        throwError "Upper-cycle audit accepted an extra premise"
    Lean.Core.liftIOCore <| IO.println "PSC_CLASS_A_PLUS_UPPER_AUDIT_COMPLETE\t8\t24"

end Psc.ClassAPlusUpperCyclesAudit
