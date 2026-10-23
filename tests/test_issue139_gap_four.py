"""A finite fit with complete closure can still fail infinite-ray rank descent."""
import json
from pathlib import Path

import pytest
from test_class_a_residue_rays import _load, tabulated

ROOT = Path(__file__).resolve().parents[1]
VERDICTS = json.loads((ROOT / "evidence/issue139-ac-gap4-2026-10-22/ray-verdicts.json").read_text())


def rank_oracle(eps, residue):
    oracle = _load(f"4,{eps},{residue}")
    oracle.ROWS_SRC = oracle.DATA_SRC = ROOT / f"kernel/psc/class_a_ray_d4{'p' if eps == 1 else 'm'}_rank.mojo"
    return oracle


@pytest.mark.parametrize("verdict", VERDICTS, ids=lambda v: f"rank-{v['eps']}-{v['r']}")
def test_preserved_rank_certificate(verdict):
    oracle = rank_oracle(verdict["eps"], verdict["r"])
    rows = oracle.carrier_rows()
    assert rows == _load(f"4,{verdict['eps']},{verdict['r']}").carrier_rows()
    assert oracle.verify_closure(rows, verdict["floor"]) == verdict["closure"]
    assert oracle.verify_descent(rows, oracle.pieces(), oracle.descents(), verdict["floor"]) == verdict["descent"]



def test_all_eight_gap_four_rays_are_registered():
    rays = {(d, eps, r) for d, eps, r, *_ in tabulated() if d == 4}
    assert rays == {(4, eps, r) for eps in (-1, 1) for r in range(4)}


def test_sampled_descent_fit_does_not_certify_the_infinite_ray():
    oracle = rank_oracle(1, 0)
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
