"""Independent n-symbolic and Q(beta) tests for 518 d2 shell states."""
import importlib.util
from pathlib import Path
import pytest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location(
    "d2_shell",ROOT/"oracles/python/class_a_d2_constant_shell.py")
oracle=importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_uniform_518_state_one_step_shell():
    result=oracle.verify_shell()
    assert result["additional_states"]==518
    assert result["explicit_hitting_states"]==598
    assert result["strict_margin_certificates"]==1036
    assert result["uniform_actual_one_step_edges"]==518
    assert result["hitting_bound"]==5
    assert result["rank_histogram"]=={2:230,3:176,4:106,5:6}
    assert result["source_sum_counts"]=={-1:259,1:259}


@pytest.mark.parametrize("n",[4,8,9])
def test_complete_field_replay_of_all_518_actual_index_pairs(n):
    assert oracle.finite_field_replay(n)["replayed_actual_edges"]==518


def test_wrong_index_and_n_slope_refusals():
    with pytest.raises(ValueError):
        oracle.prefix(0,1,4)
    with pytest.raises(ValueError):
        oracle.prefix(1,1,-4)
    with pytest.raises(ValueError):
        oracle.prefix(2,2,0)
    src=oracle.records()
    bad=src.copy()
    row=list(bad[0]);row[7]=4;bad[0]=tuple(row)
    with pytest.raises(ValueError):
        oracle.verify_shell(bad)
    bad=src.copy()
    row=list(bad[0]);row[4]+=1;bad[0]=tuple(row)
    with pytest.raises(ValueError):
        oracle.verify_shell(bad)


def test_no_false_overlap_or_forged_child():
    assert oracle.strict_margin((0,1,0))==(0,5,5)
    with pytest.raises(ValueError):
        oracle.strict_margin((0,0,0))
    with pytest.raises(ValueError):
        oracle.strict_margin((-1,0,0))
    src=oracle.records()
    bad=src.copy()
    row=list(bad[0]);row[10]=0;bad[0]=tuple(row)
    with pytest.raises(ValueError):
        oracle.verify_shell(bad)
    bad=src.copy();bad[4]=bad[0]
    with pytest.raises(ValueError,match="duplicate"):
        oracle.verify_shell(bad)
    with pytest.raises(ValueError):
        oracle.finite_field_replay(25)
