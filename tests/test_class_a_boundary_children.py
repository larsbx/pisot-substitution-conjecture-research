"""Finite independent exact controls; universal proof is in Mojo plus the note."""
import importlib.util
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "boundary_children", ROOT / "oracles/python/class_a_boundary_children.py")
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_exhaustive_literal_word_pairs():
    receipt = oracle.probe()
    assert receipt["members"] == 56
    assert receipt["pairs"] > 20_000


@pytest.mark.parametrize("eps,k,t", [(-1, 0, 0), (1, 0, 0), (1, 3, 0), (1, 4, 0)])
def test_deliberately_invalid_geometric_controls(eps, k, t):
    g = oracle.Geometry(eps, k, t)
    root = (0, 1, 0, 0, 0)
    wrong = g.child(root, 1, 1)
    assert wrong == (2, 2, -1, 1, 0)
    assert not g.interior(wrong)
    last = g.child(root, g.n+2, g.n+1)
    assert g.interior(last) == (eps == -1)
    target = g.child(root, 0, 1)
    assert target != (0, 2, 0, 1, 1)
    assert target != (2, 2, 0, 1, 0)
    with pytest.raises(ValueError):
        g.child(root, -1, 0)
    with pytest.raises(ValueError):
        g.child(root, len(g.words[0]), 0)
    # Endpoint contact is not strict overlap, even for equal letters.
    assert not g.interior((0, 0, 1, 0, 0))
    assert not g.interior((0, 0, -1, 0, 0))


def test_reject_invalid_chamber():
    for args in [(0, 0, 0), (1, -1, 0), (-1, 0, -1)]:
        with pytest.raises(ValueError):
            oracle.Geometry(*args)
