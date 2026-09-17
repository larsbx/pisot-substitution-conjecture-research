"""The proof-dependency ledger is generated from tla/ledger.json and says what the old hand-written models said."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "tools"))

import make_ledger  # noqa: E402
from proof_records import generate_ledgers as gl  # noqa: E402

MODELS = ("Open", "Imports", "G1AndProducer", "G1Only", "G1AndC4", "RenewalGateAssumed", "SpectralGateAssumed", "OverlapGateAssumed")


def reachable(model: str) -> set[str]:
    text = (ROOT / "tla" / f"MCLedger{model}.tla").read_text(encoding="utf-8")
    body = text[text.index("Reachable == {"):text.index("EventuallyReachable")]
    return set(re.findall(r'"([A-Za-z0-9_]+)"', body))


def test_generated_surfaces_are_current():
    result = subprocess.run([sys.executable, str(ROOT / "scripts" / "make_ledger.py"), "--check"], capture_output=True, text=True, check=False)
    assert result.returncode == 0, result.stdout


def test_every_ledger_node_is_a_validated_record_with_a_generated_claim():
    analysis = gl.analyse(gl.load_ledger(ROOT / "tla" / "ledger.json"))
    names = {e.name for e in analysis.entries}
    tla = (ROOT / "tla" / "Ledger.tla").read_text(encoding="utf-8")
    assert names == set(re.findall(r'^    "([A-Za-z0-9_]+)",?$', tla[tla.index("ResultSet == {"):tla.index("RequiresDef")], re.M))
    policy = tomllib.loads((ROOT / "claim_governance.toml").read_text(encoding="utf-8"))
    claims = {c["name"]: c for c in policy["claim"]}
    assert names <= set(claims)
    assert claims["G1"]["status"] == "open" and claims["CoincidenceDensityOne"]["status"] == "proved" and claims["SinkSCCReduction"]["status"] == "conditional"
    assert claims["DensityToPDSBridge"]["status"] == "imported" and claims["V5Thm51"]["status"] == "retired"
    assert claims["PDSOverlapRoute"]["status"] == "conditional"
    statuses = {e.name: e.status for e in analysis.entries}
    assert all(claims[n]["status"] == s for n, s in statuses.items())


def test_status_overrides_are_recorded_in_the_records():
    data = json.loads((ROOT / "tla" / "ledger.json").read_text(encoding="utf-8"))
    for name in make_ledger.STATUS_NOTES:
        record = data["records"][name]
        assert any(t.startswith("status:") for t in record["tags"]) and ["status_note", make_ledger.STATUS_NOTES[name]] in record["evidence"]


def test_models_state_what_the_hand_written_configurations_demonstrated():
    open_set = reachable("Open")
    assert "SpectralBlackBox" in open_set and "G1b1BoundedDiscrepancy" in open_set and "SwapOverlapFiniteness" in open_set
    for gate in ("PDS", "LoadBearingSCC", "SCCProducer", "G1b2RenewalFiniteness", "ConcentrationAuxB", "OverlapProductivity", "PDSImpliesRepoG1", "V5Thm51"):
        assert gate not in open_set, gate
    assert "DensityToPDSBridge" not in open_set and "DensityToPDSBridge" in reachable("Imports")
    assert "PDS" in reachable("G1AndProducer") and "PDS" in reachable("G1AndC4")
    assert "LoadBearingSCC" in reachable("G1Only") and "PDS" not in reachable("G1Only")
    assert "G1" in reachable("RenewalGateAssumed")
    assert "PDSSpectralRoute" in reachable("SpectralGateAssumed")
    assert {"CoincidenceDensityOne", "PDSOverlapRoute"} <= reachable("OverlapGateAssumed")
    assert all("V5Thm51" not in reachable(m) for m in MODELS)


def test_check_script_runs_every_generated_model_and_no_stale_model_remains():
    script = (ROOT / "tla" / "check.sh").read_text(encoding="utf-8")
    for model in MODELS:
        assert f'"MCLedger{model}:HOLD"' in script
        assert (ROOT / "tla" / f"MCLedger{model}.cfg").exists()
    assert not list((ROOT / "tla").glob("MCArchitecture*"))
    assert "MCArchitecture" not in script
