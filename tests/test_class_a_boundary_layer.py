"""Exact independent Python replay of the class-A boundary layer.

The 261-state BPA graph is a finite, non-target-aware proxy only.
"""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ORACLE = ROOT / "oracles/python/class_a_boundary_probe.py"
RECEIPT = ROOT / "evidence/class-a-boundary-layer-2026-10-26/probe.json"


def test_exact_boundary_receipt():
    actual = json.loads(subprocess.check_output(
        [sys.executable, str(ORACLE), "--bpa-example"], cwd=ROOT, text=True
    ))
    expected = json.loads(RECEIPT.read_text())
    assert actual == expected
    r = actual["finite_bpa_example"]
    assert (r["normalized_states"], r["ordered_factor_edges"],
            r["max_state_word_length"]) == (261, 12546, 22592)
    assert not r["cap_exhausted"]
    assert r["all_states_reach_diagonal"]
    assert r["seed_witnesses"]["02|20"][0]["span"] == [0, 1]
    assert r["ordered_factor_edge_sha256"] == (
        "ac39017ae34f7ca7c8fb092080bf3292f435c8e3cdcc16244cd2ceafb037ba1b"
    )


def test_parameter_refusals():
    sys.path.insert(0, str(ORACLE.parent))
    from class_a_boundary_probe import params, replay_bpa
    import pytest
    with pytest.raises(AssertionError):
        params(2, -1, 0)
    with pytest.raises(AssertionError):
        params(4, 0, 0)
    with pytest.raises(RuntimeError, match="cap hit"):
        replay_bpa(3, 5, -1, max_states=5)
