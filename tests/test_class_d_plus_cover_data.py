import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "kernel/psc/class_d_plus_cover_data.mojo"
PACKET = ROOT / "evidence/class-d-plus-template-2026-10-14/oracle.json"


def test_materialized_plus_cover_matches_sealed_packet_exactly():
    text = DATA.read_text()
    rows = [
        [int(x) for x in m.groups()]
        for m in re.finditer(
            r"^\s*\[(-?\d+),(-?\d+),(-?\d+),(-?\d+),(-?\d+)\],\s*$",
            text,
            flags=re.MULTILINE,
        )
    ]
    packet = json.loads(PACKET.read_text())
    assert len(rows) == 718
    assert rows == packet["vertices"]
    assert len(set(map(tuple, rows))) == 718
