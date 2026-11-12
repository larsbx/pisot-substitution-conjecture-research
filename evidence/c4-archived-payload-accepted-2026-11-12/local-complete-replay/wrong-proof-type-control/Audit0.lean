import Source0
import PscVerif.ArchivedPayloadEmit
import Lean.Util.CollectAxioms
open Set MeasureTheory
open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceGraphBinding
open Psc.OccurrencePiece Psc.OccurrenceResidue
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedProductHaar
open Psc.ArchivedGraphRefinement
example : Psc.ArchivedPayloadGenerated.Source0.packet.fixture = 0 := rfl
example : Psc.ArchivedPayloadGenerated.Source0.packet.count = 7150 := rfl
example : Psc.ArchivedPayloadGenerated.Source0.packet.Valid := Psc.ArchivedPayloadGenerated.Source0.valid
example : Psc.ArchivedPayloadGenerated.Source0.packet.check = true := Psc.ArchivedPayloadGenerated.Source0.accepted
example : (Psc.ArchivedPayloadGenerated.Source0.packet.toCertificate Psc.ArchivedPayloadGenerated.Source0.valid).check = true := Psc.ArchivedPayloadGenerated.Source0.typed_accepted
example (u : Psc.OccurrenceTransport.Packet) :
    (u ∈ orderedLift Psc.ArchivedPayloadGenerated.Source0.packet.states ∧
      (overlap (ambientStar (substitution Psc.ArchivedPayloadGenerated.Source0.packet.fixture) piZ)
        (tiles Psc.ArchivedPayloadGenerated.Source0.packet.fixture) u).Nonempty) ↔
    (Ancestry (iterateImages (substitution Psc.ArchivedPayloadGenerated.Source0.packet.fixture) 2) ArchivedRoot u ∧
      (overlap (ambientStar (substitution Psc.ArchivedPayloadGenerated.Source0.packet.fixture) piZ)
        (tiles Psc.ArchivedPayloadGenerated.Source0.packet.fixture) u).Nonempty) := Psc.ArchivedPayloadGenerated.Source0.domain_iff u
example (ν : Measure (H (substitution Psc.ArchivedPayloadGenerated.Source0.packet.fixture)))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :
    ∀ k, (volume.prod ν)
      (overlap (ambientStar (substitution Psc.ArchivedPayloadGenerated.Source0.packet.fixture) piZ)
        (tiles Psc.ArchivedPayloadGenerated.Source0.packet.fixture) (archivedRoot k)) = 0 := Psc.ArchivedPayloadGenerated.Source0.roots_null ν
example (ν : Measure (H (substitution Psc.ArchivedPayloadGenerated.Source0.packet.fixture)))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (u : Psc.OccurrenceTransport.Packet)
    (hu : Ancestry (iterateImages (substitution Psc.ArchivedPayloadGenerated.Source0.packet.fixture) 2) ArchivedRoot u) :
    (volume.prod ν)
      (overlap (ambientStar (substitution Psc.ArchivedPayloadGenerated.Source0.packet.fixture) piZ)
        (tiles Psc.ArchivedPayloadGenerated.Source0.packet.fixture) u) = 0 := Psc.ArchivedPayloadGenerated.Source0.ancestors_null ν u hu
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Source0 | throwError "Missing generated module"
  let data := env.header.moduleData[idx.toNat]!
  let mut count := 0
  let mut proofs := 0
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for info in data.constants do
    let name := info.name
    if info.isAxiom then throwError "Local generated axiom"
    let axs ← collectAxioms name
    for ax in axs do
      if !allowed.contains ax then throwError "Nonstandard generated axiom"
    count := count + 1
    if info.isTheorem then proofs := proofs + 1
    let names := String.intercalate "," (axs.toList.map toString)
    liftIO <| IO.println s!"PSC_ARCHIVED_AXIOMS 0\t{name}\t{names}"
  if proofs < 6 then throwError "Missing concrete semantic proofs"
  liftIO <| IO.println s!"PSC_ARCHIVED_AUDIT_COMPLETE 0\t{count}\t{proofs}"
def main : IO Unit := Psc.ArchivedPayloadGenerated.Source0.packet.emit
