"""Exact independent recovery validation for the three class-A selected exits."""
from pathlib import Path
import runpy
import pytest

SOURCE = Path(__file__).resolve().parents[1] / "oracles/python/class_a_boundary_three_exit_recovery.py"
m = runpy.run_path(str(SOURCE))


def test_unbounded_integer_transport_and_strict_geometry():
    result = m["symbolic_certificate"]()
    assert result["families"] == 3
    assert result["actual_symbolic_edges"] == 14
    assert result["oriented_states"] == 13
    assert result["strict_margins"] == 26
    assert result["per_source_path_depth"] == [2, 2, 3]
    assert result["universal_BH"] is False


def test_separate_exact_fraction_literal_replay():
    result = m["literal_probe"](SOURCE.parent)
    assert result == dict(members=117, selected_actual_edge_replays=1638)


def test_reject_nonexistent_run_ordinal_or_false_typed_target():
    with pytest.raises(AssertionError):
        m["certify_edge"](m["R3"], 0, 0, m["Q"])
    with pytest.raises(AssertionError):
        m["certify_edge"](m["R3"], m["D"], 0, m["H1"])
    with pytest.raises(AssertionError):
        m["certify_nonnegative"](m["Aff"](k=-1, c=1000))


def test_distinct_orientations_and_wrong_physical_overlap():
    for w in m["SOURCES"]:
        assert m["reverse"](m["reverse"](w)) == w
    with pytest.raises(AssertionError):
        m["certify_strict"]((0, 0, 0, 0, 100))
