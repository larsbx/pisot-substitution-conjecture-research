"""Complete finite-domain replay and semantic controls for cut-prefix witnesses."""

import importlib.util
import os
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "c4_cut_prefix_embedding", ROOT / "oracles/python/c4_cut_prefix_embedding.py")
ORACLE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ORACLE)


def test_complete_literal_domain():
    packet = ORACLE.expected_packet()
    ORACLE.verify_packet(packet)
    assert packet["counts"][0] > 3000
    assert packet["counts"][2] == 272
    assert packet["counts"][3] > 0
    assert {w["address"][1] for w in packet["witnesses"]} == {0, 2, 4, 6}


def test_complete_packet_mutations_and_json_controls():
    assert len(ORACLE.run_controls()) == 19


def test_same_incidence_keeps_distinct_original_words():
    first = ORACLE.witness(0, (1,), 0, 0)
    second = ORACLE.witness(1, (1,), 0, 0)
    assert first["reference"] != second["reference"]
    assert first["correction"] != second["correction"]
    for a in range(3):
        for b in range(3):
            assert ORACLE.IMAGES[0][a].count(b) == ORACLE.IMAGES[1][a].count(b)


@pytest.mark.parametrize("power", [1, 3, 5])
def test_odd_reference_power_refuses(power):
    with pytest.raises(ORACLE.InvalidPacket):
        ORACLE.witness(0, (1,), power, 0)


def test_terminal_cut_has_no_following_occurrence():
    output = ORACLE.inflated(0, (0,), 2)
    with pytest.raises(ORACLE.InvalidPacket):
        ORACLE.witness(0, (0,), 2, len(output))


def test_native_complete_packet_when_supplied():
    name = os.environ.get("C4_CUT_PREFIX_NATIVE")
    if not name:
        pytest.skip("set C4_CUT_PREFIX_NATIVE for exact native packet comparison")
    ORACLE.verify_packet(ORACLE.strict_loads(Path(name).read_text()))
