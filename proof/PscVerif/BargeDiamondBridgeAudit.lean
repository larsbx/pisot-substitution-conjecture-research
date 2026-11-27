/- Scoped replay, including generated helpers in the full imported project
closure. Cached upstream dependency artifacts remain an explicit trust input;
this does not replace tools/check_lean.sh or the complete library audit. -/
import PscVerif.BargeDiamondBridgeControls
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  let mut theorems := 0
  let mut bridgeCount := 0
  let mut bridgeTheorems := 0
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for index in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[index]!
    if mod.getRoot != `PscVerif then continue
    let isBridge := mod == `PscVerif.BargeDiamondBridge || mod == `PscVerif.BargeDiamondBridgeControls
    let data := env.header.moduleData[index]!
    for info in data.constants do
      let name := info.name
      let some owner := env.getModuleIdxFor? name | continue
      if owner.toNat != index then continue
      if info.isAxiom then throwError "Local axiom: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        if !allowed.contains ax then throwError "Nonstandard axiom in {name}: {ax}"
      count := count + 1
      if info.isTheorem then theorems := theorems + 1
      if isBridge then
        bridgeCount := bridgeCount + 1
        if info.isTheorem then bridgeTheorems := bridgeTheorems + 1
        let kind := if info.isTheorem then "theorem" else "declaration"
        let names := String.intercalate "," (axioms.toList.map toString)
        liftIO <| IO.println s!"BD_AXIOMS\t{kind}\t{mod}\t{name}\t{names}"
  if bridgeTheorems == 0 then throwError "No bridge theorems were audited"
  liftIO <| IO.println s!"BD_AUDIT_COMPLETE\t{count}\t{theorems}\t{bridgeCount}\t{bridgeTheorems}"
