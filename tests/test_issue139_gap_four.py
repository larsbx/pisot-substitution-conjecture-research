"""A finite fit with complete closure can still fail infinite-ray rank descent."""
import json
from pathlib import Path

import pytest
from test_class_a_residue_rays import _load, tabulated

ROOT = Path(__file__).resolve().parents[1]


def test_all_eight_gap_four_rays_are_registered():
    rays = {(d, eps, r) for d, eps, r, *_ in tabulated() if d == 4}
    assert rays == {(4, eps, r) for eps in (-1, 1) for r in range(4)}


def test_sampled_descent_fit_does_not_certify_the_infinite_ray():
    oracle = _load("4,1,0")
    candidate = json.loads((ROOT / "evidence/issue139-ac-gap4-2026-10-22/a-pre-refit-candidate.json").read_text())
    pieces = [(ri, *lo, *hi, *fit) for ri, lo, hi, fit in candidate["pieces"]]
    descents = [(pi, *lo, *hi, *ty, child) for pi, lo, hi, ty, child in candidate["descent"]]
    rows = oracle.carrier_rows()
    assert oracle.verify_closure(rows, 36)["seeds_real"] == 9
    with pytest.raises(ValueError, match="potential does not drop"):
        oracle.verify_descent(rows, pieces, descents, 36)
    # The final exact integer rank accepts the SAME occurrence choices.
    assert descents == oracle.descents()
    assert [p[:5] for p in pieces] == [p[:5] for p in oracle.pieces()]
    assert oracle.verify_descent(rows, oracle.pieces(), descents, 36)["targets"] == 8
