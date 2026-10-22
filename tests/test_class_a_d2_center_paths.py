"""All-parameter exact central d2 two-step lemma and actual prefix replays."""
from pathlib import Path
import importlib.util
import pytest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location(
    "center_paths",ROOT/"oracles/python/class_a_d2_center_paths.py")
oracle=importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_uniform_symbolic_path_and_strict_margins():
    results=oracle.prove_uniform()
    assert len(results)==2
    assert all(r["all_n_ge_4"] and r["terminal"]==(2,2,0,0,0) for r in results)
    assert results[0]["indices"]==((0,2),(1,2))
    assert results[1]["indices"]==((2,0),(2,1))


@pytest.mark.parametrize("n",[4,7,8,9,12])
def test_actual_fraction_field_ordered_occurrences(n):
    assert oracle.finite_replay(n)["two_explicit_paths_replayed"]


def test_strict_geometry_and_index_refusals():
    with pytest.raises(ValueError):
        oracle.symbolic_child((0,0,1,0,0),0,2) # uncancelled n coefficient
    with pytest.raises(ValueError):
        oracle.symbolic_child((1,0,-1,1,0),0,2) # c letter unsupported
    with pytest.raises(ValueError):
        oracle.symbolic_child((0,0,-1,1,0),0,999)
    with pytest.raises(ValueError):
        oracle.strict_real_all_positive_h((0,0,3,-3,0))
    for n in (3,25):
        with pytest.raises(ValueError):
            oracle.finite_replay(n)
