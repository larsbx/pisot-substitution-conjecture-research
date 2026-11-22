/- Replay directly with `lake env lean PeriodicPartnerAudit.lean`.
Audit every compiled declaration owned by the periodic-partner modules and
every imported PscVerif dependency, including definitions and generated helpers.
The isolated shell gate additionally binds the source import closure and checks
that every named source theorem was reached by this compiled audit. -/
import PscVerif.PeriodicPartner
import PscVerif.PeriodicPartnerControls
import PscVerif.PeriodicPartnerDynamics
import PscVerif.PeriodicPartnerCollapse
import PscVerif.PeriodicPartnerModels
import PscVerif.PeriodicPartnerDichotomy
import PscVerif.PeriodicPartnerReflection
import PscVerif.PeriodicPartnerAsymptotic
import PscVerif.PeriodicPartnerHull
import PscVerif.PeriodicPartnerSelection
import PscVerif.PeriodicPartnerHullSelection
import PscVerif.PeriodicPartnerVertexPartner
import PscVerif.PeriodicPartnerCompleteRange
import PscVerif.PeriodicPartnerDirectional
import PscVerif.PeriodicPartnerSeamCycles
import PscVerif.PeriodicPartnerReturnBoundary
import PscVerif.PeriodicPartnerMarkerParity
import PscVerif.PeriodicPartnerMarkerReachability
import PscVerif.PeriodicPartnerMarkerDecision
import PscVerif.PeriodicPartnerMarkerFamily
import PscVerif.PeriodicPartnerWinding
import PscVerif.PeriodicPartnerWindingSeams
import PscVerif.PeriodicPartnerLiteralDefect
import PscVerif.PeriodicPartnerEvenTails
import PscVerif.PeriodicPartnerFixedPointParity
import PscVerif.PeriodicPartnerFixedPointHull
import PscVerif.PeriodicPartnerTwinEndpoint
import PscVerif.PeriodicPartnerStackWordRigidity
import PscVerif.PeriodicPartnerGradedLift
import PscVerif.PeriodicPartnerCompanionWords
import PscVerif.PeriodicPartnerRealization
import PscVerif.PeriodicPartnerRealizationModels
import PscVerif.PeriodicPartnerSpectral
import PscVerif.PeriodicPartnerSpectralModels
import PscVerif.PeriodicPartnerSpectralCertificate
import PscVerif.PeriodicPartnerSpectralCensus
import PscVerif.PeriodicPartnerHullNonempty
import PscVerif.PeriodicPartnerLocalHausdorff
import PscVerif.PeriodicPartnerHullLeft
import PscVerif.PeriodicPartnerHullContinuity
import PscVerif.PeriodicPartnerLocalTopology
import PscVerif.PeriodicPartnerLocalTopologyControls
import PscVerif.PeriodicPartnerLocalRealization
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := #[`PscVerif.PeriodicPartner, `PscVerif.PeriodicPartnerControls,
    `PscVerif.PeriodicPartnerDynamics, `PscVerif.PeriodicPartnerCollapse,
    `PscVerif.PeriodicPartnerModels, `PscVerif.PeriodicPartnerDichotomy,
    `PscVerif.PeriodicPartnerReflection, `PscVerif.PeriodicPartnerAsymptotic,
    `PscVerif.PeriodicPartnerHull, `PscVerif.PeriodicPartnerSelection,
    `PscVerif.PeriodicPartnerHullSelection, `PscVerif.PeriodicPartnerVertexPartner,
    `PscVerif.PeriodicPartnerCompleteRange,
    `PscVerif.PeriodicPartnerDirectional, `PscVerif.PeriodicPartnerSeamCycles,
    `PscVerif.PeriodicPartnerReturnBoundary, `PscVerif.PeriodicPartnerMarkerParity,
    `PscVerif.PeriodicPartnerMarkerReachability, `PscVerif.PeriodicPartnerMarkerDecision,
    `PscVerif.PeriodicPartnerMarkerFamily,
    `PscVerif.PeriodicPartnerWinding,
    `PscVerif.PeriodicPartnerWindingSeams, `PscVerif.PeriodicPartnerLiteralDefect,
    `PscVerif.PeriodicPartnerEvenTails, `PscVerif.PeriodicPartnerFixedPointParity,
    `PscVerif.PeriodicPartnerFixedPointHull, `PscVerif.PeriodicPartnerTwinEndpoint,
    `PscVerif.PeriodicPartnerStackWordRigidity,
    `PscVerif.PeriodicPartnerGradedLift,
    `PscVerif.PeriodicPartnerCompanionWords, `PscVerif.VertexAsymptoteRange,
    `PscVerif.PeriodicPartnerRealization, `PscVerif.PeriodicPartnerRealizationModels,
    `PscVerif.PeriodicPartnerSpectral, `PscVerif.PeriodicPartnerSpectralModels,
    `PscVerif.PeriodicPartnerSpectralCertificate, `PscVerif.PeriodicPartnerSpectralCensus,
    `PscVerif.PeriodicPartnerHullContinuity, `PscVerif.PeriodicPartnerLocalTopology,
    `PscVerif.PeriodicPartnerLocalTopologyControls, `PscVerif.PeriodicPartnerLocalRealization,
    `PscVerif.PeriodicPartnerHullNonempty, `PscVerif.PeriodicPartnerLocalHausdorff,
    `PscVerif.PeriodicPartnerHullLeft]
  for mod in required do
    unless (env.getModuleIdx? mod).isSome do
      throwError "Missing compiled periodic-partner module: {mod}"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut theorems := 0
  let mut modules := 0
  for index in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[index]!
    if mod.getRoot != `PscVerif then continue
    let data := env.header.moduleData[index]!
    let mut localCount := 0
    let mut localTheorems := 0
    for info in data.constants do
      let name := info.name
      let some owner := env.getModuleIdxFor? name | continue
      if owner.toNat != index then continue
      if info.isAxiom then throwError "Local periodic-partner axiom: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard periodic-partner axiom in {name}: {ax}"
      localCount := localCount + 1
      if info.isTheorem then localTheorems := localTheorems + 1
      let kind := if info.isTheorem then "theorem" else "declaration"
      let names := String.intercalate "," (axioms.toList.map toString)
      liftIO <| IO.println
        s!"PSC_AXIOMS\t{kind}\t{mod}\t{name}\t{privateToUserName name}\t{names}"
    if localCount == 0 then throwError "Empty periodic-partner dependency module: {mod}"
    count := count + localCount
    theorems := theorems + localTheorems
    modules := modules + 1
    liftIO <| IO.println
      s!"PSC_PERIODIC_PARTNER_MODULE\t{mod}\t{localCount}\t{localTheorems}"
  if modules < required.size || theorems == 0 then
    throwError "Incomplete periodic-partner compiled import closure"
  liftIO <| IO.println s!"PSC_AUDIT_COMPLETE\t{count}\t{theorems}"

