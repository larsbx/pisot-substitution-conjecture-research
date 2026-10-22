"""Receipt completeness and independent exact strip calibrations."""
import json
import os
from pathlib import Path
import pytest
from oracles.python import class_d_minus_boundary_strips as oracle


def test_complete_strip_calibration():
    path=os.environ.get('CLASS_D_MINUS_STRIPS_REPORT')
    out=json.loads(Path(path).read_text()) if path else dict(samples=[oracle.specimen(a,b) for a in (0,1) for b in (1,2)])
    assert all(not row['non_hitting_indices'] for row in out['samples'])
    assert {r['a'] for r in out['samples']}=={0,1}
    if log:=os.environ.get('CLASS_D_MINUS_COMPLETE_LOG'):
        oracle.compare_receipts(out,log)


def test_incomplete_or_duplicate_strip_receipts_refuse(tmp_path):
    path=tmp_path/'partial.log'
    row='MINUS_STRIP_CERTIFIED 0 n=b-1 threshold 42 vertices 140 finite_pip 42 crosschecks 42 47\n'
    marker='CLASS_D_MINUS_RESIDUAL_BH_CERTIFIED a>=0 b>=0 components=4 universal_139=open\n'
    for data in (row+marker,row+row+marker):
        path.write_text(data)
        with pytest.raises(ValueError):
            oracle.compare_receipts(dict(samples=[]),path)


def test_cap_and_invalid_strip_are_not_success():
    with pytest.raises(ValueError,match='capped'):
        oracle.specimen(0,1,cap=1)
    for a,b in ((2,1),(0,0),(1,101)):
        with pytest.raises(ValueError,match='budget'):
            oracle.specimen(a,b)
