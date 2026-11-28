/- Replay with `lake env lean BetaNumerationAudit.lean` after compiling the
beta-numeration modules. This is an endpoint acceptance fixture, not a cached
library target. The unchanged full proof-bank audit separately inspects every
imported project constant. -/
import PscVerif.C4FamilyBetaTranscendence
import PscVerif.BetaGoldenEndpoint
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let endpoints := #[
    `Psc.WordComplexity.eventuallyPeriodic_of_complexity_succ_le,
    `Psc.WordComplexity.succ_le_complexity,
    `Psc.WordComplexity.complexity_comp,
    `Psc.WordComplexity.window_flatten,
    `Psc.BetaNumeration.renyiExpansion_value,
    `Psc.BetaNumeration.isUnique_of_tails,
    `Psc.BetaNumeration.transcendental_of_greedy,
    `Psc.BetaMetallic.beta_sq,
    `Psc.BetaMetallic.top_sub_one,
    `Psc.BetaMetallic.beta_one,
    `Psc.BetaMetallic.isPisot,
    `Psc.BetaMetallic.isUnique_of_low,
    `Psc.BetaMetallic.isUnique_interior,
    `Psc.BetaMetallic.interior_renyi,
    `Psc.ParameterFamilyFixedWord.fixedWord_eq,
    `Psc.ParameterFamilyFixedWord.charpoly_identity,
    `Psc.ParameterFamilyFixedWord.no_rational_root,
    `Psc.ParameterFamilyFixedWord.not_eventuallyPeriodic,
    `Psc.ParameterFamilyFixedWord.frequently_linear,
    `Psc.FamilyBetaTranscendence.xi_isUnique,
    `Psc.FamilyBetaTranscendence.xi_mem,
    `Psc.FamilyBetaTranscendence.renyi_xi,
    `Psc.FamilyBetaTranscendence.xi_transcendental,
    `Psc.BetaGoldenEndpoint.isUnique_iff]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in endpoints do
    let some info := env.find? name | throwError "Missing endpoint {name}"
    if !info.isTheorem then throwError "Endpoint is not a theorem: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    let names := String.intercalate "," (axioms.toList.map toString)
    liftIO <| IO.println s!"PSC_BETA_ENDPOINT\t{name}\t{names}"
  liftIO <| IO.println s!"PSC_BETA_AUDIT_COMPLETE\t{endpoints.size}"
