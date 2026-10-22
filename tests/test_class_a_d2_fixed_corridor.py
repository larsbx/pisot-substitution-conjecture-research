"""Independent complete exact audit of 80 all-parameter d2 hitting states."""
from pathlib import Path
import importlib.util
import pytest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location(
    "d2_fixed_corridor",ROOT/"oracles/python/class_a_d2_fixed_corridor.py")
oracle=importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_exact_all_parameter_corridor():
    evidence=oracle.prove()
    assert evidence["rows"]==80
    assert evidence["offset_zero_targets"]==8
    assert evidence["chosen_real_edges"]==72
    assert evidence["strict_margins"]==160
    assert evidence["uniform_hitting_depth"]==4
    assert evidence["depth_histogram"]=={0:8,1:20,2:26,3:22,4:4}


def test_exact_all_parameter_parity_candidate_inclusion():
    assert oracle.prove_candidate_inclusion()==(80,80)


@pytest.mark.parametrize("n",[4,8,9,12])
def test_complete_fraction_field_differential_replay(n):
    checked=oracle.exact_finite_replay(n)
    assert checked["rows"]==80
    assert checked["replayed_occurrences"]==72


def test_zero_and_negative_geometry_refused():
    assert oracle.bernstein_certified((0,1,0))
    assert not oracle.bernstein_certified((0,0,0))
    assert not oracle.bernstein_certified((-1,0,0))
    with pytest.raises(ValueError,match="cancelle"):
        oracle.margins((0,0,1,0,0))
    with pytest.raises(ValueError):
        oracle.actual_child((0,0,1,0,0),0,1)


def test_tampered_real_occurrence_refused():
    given=oracle.rows()
    bad=given.copy()
    changed=list(bad[0])
    changed[6]=5
    bad[0]=tuple(changed)
    with pytest.raises(ValueError):
        oracle.prove(bad)
    bad=given.copy()
    changed=list(bad[0])
    changed[8]=0
    bad[0]=tuple(changed)
    with pytest.raises(ValueError):
        oracle.prove(bad)
    bad=given.copy()
    bad[5]=bad[0]
    with pytest.raises(ValueError,match="duplicate"):
        oracle.prove(bad)


def test_target_and_sum_zero_fail_closed():
    given=oracle.rows()
    bad=given.copy()
    changed=list(bad[3])
    changed[2]=1
    bad[3]=tuple(changed)
    with pytest.raises(ValueError):
        oracle.prove(bad)
    bad=given.copy()
    changed=list(bad[0])
    changed[4]+=1
    bad[0]=tuple(changed)
    with pytest.raises(ValueError):
        oracle.prove(bad)
    with pytest.raises(ValueError):
        oracle.exact_finite_replay(25)
