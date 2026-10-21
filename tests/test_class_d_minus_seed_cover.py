"""Independent rational geometry, complete cover, and negative controls."""
import json
import os
from pathlib import Path
import pytest
from oracles.python import class_d_minus_seed_cover as oracle


def test_independent_complete_carrier_closure():
    report_path=os.environ.get('CLASS_D_SEED_COVER_REPORT')
    out=json.loads(Path(report_path).read_text()) if report_path else oracle.report()
    assert out['unresolved']==[]
    assert out['counts']==[145,9,3,2,1287,12255,1218,9034,2003]
    assert not out['parameter_grid']
    if path:=os.environ.get('CLASS_D_SEED_COVER_MOJO_LOG'):
        oracle.compare_mojo(out,path)


def test_correlations_are_necessary_for_this_certificate():
    forms=oracle.region(False)+oracle.margins((0,1,0,0,-1))+oracle.margins((2,2,-1,-1,1))
    assert oracle.strict_witness(forms) is not None
    assert oracle.strict_witness(forms+[(0,10,-7),(10,-10,-3)]) is None
    # The absent seed is real in the loose box but not in the true region.
    seed=(2,2,-1,0,0)
    assert seed not in oracle.COVER
    assert oracle.strict_witness(oracle.region(False)+oracle.margins(seed)) is not None
    assert oracle.strict_witness(oracle.region()+oracle.margins(seed)) is None


def test_strict_boundary_is_not_interior():
    assert oracle.strict_witness(oracle.region()+[(0,0,0)]) is None
    assert oracle.strict_witness(oracle.region()+[(1,0,0)]) is not None


def test_missing_completion_receipt_refuses(tmp_path):
    path=tmp_path/'partial.log'
    path.write_text('MINUS_SEED_COVER_COUNTS 145 9 3 2 1287 12255 1218 9034 2003\n')
    with pytest.raises(ValueError,match='completion'):
        oracle.compare_mojo(oracle.report(),path)


def test_no_high_sum_formal_state_is_added_to_the_cover():
    # The all-k statement follows algebraically from every cover sum <=1;
    # these values are only independent negative controls on the data table.
    assert all(abs(sum(v[2:]))<=1 for v in oracle.COVER)
    for k in (2,3,8,10000):
        assert (2,1,-2*k,4*k,-3*k) not in oracle.COVER
        assert (1,2,2*k,-4*k,3*k) not in oracle.COVER
