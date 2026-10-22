"""Independent symbolic verification of the tabulated class-A residue rays (n+d, n, n+eps), n = d l + r."""
import importlib.util
import re
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


def _load(ray):
    """A fresh oracle module instance; the oracle selects its ray from argv at import."""
    saved = sys.argv
    sys.argv = ["class_a_carrier_closure", "--ray", ray]
    try:
        spec = importlib.util.spec_from_file_location("class_a_ray_" + ray.replace(",", "_").replace("-", "m"),
                                                      ROOT / "oracles/python/class_a_carrier_closure.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    finally:
        sys.argv = saved
    return module


def tabulated():
    """The `tabulated_rays()` table of the canonical Mojo registry."""
    text = (ROOT / "kernel/psc/class_a_ray_tables.mojo").read_text()
    body = text[text.index("def tabulated_rays("):text.index("def ray_tables(")]
    return [tuple(map(int, m.split(","))) for m in re.findall(r"List\[Int\]\(\[(-?\d+(?:, *-?\d+){5})\]\)", body)]


RAYS = tabulated()


def test_registry_is_nonempty():
    assert len(RAYS) >= 2


@pytest.mark.parametrize("d,eps,r,n0,slope,const", RAYS)
def test_ray_closure_and_descent(d, eps, r, n0, slope, const):
    oracle = _load("%d,%d,%d" % (d, eps, r))
    oracle._check_line()
    rows = oracle.carrier_rows()
    assert sum(row[6] - row[4] for row in rows) == slope
    assert sum(row[7] - row[5] + 1 for row in rows) == const
    closure = oracle.verify_closure(rows, n0)
    assert closure["seeds_real"] == 9 and closure["seeds_unreal"] == 3
    descent = oracle.verify_descent(rows, oracle.pieces(), oracle.descents(), n0)
    assert descent["targets"] == 8 and descent["bound_slope"] >= 0
    with pytest.raises(ValueError):
        oracle.verify_closure(rows[1:], n0)
    P, D = oracle.pieces(), oracle.descents()
    with pytest.raises(ValueError):
        oracle.verify_descent(rows, P, [tuple(D[0][:7]) + (D[0][7] + 1, D[0][8])] + D[1:], n0)
    with pytest.raises(ValueError):
        oracle.verify_descent(rows, P, D[1:], n0)


@pytest.mark.parametrize("d,eps,r,n0,slope,const", [ray for ray in RAYS if ray[0] > 1])
def test_other_residue_carrier_does_not_fit(d, eps, r, n0, slope, const):
    oracle = _load("%d,%d,%d" % (d, eps, r))
    other = _load("%d,%d,%d" % (d, eps, (r + 1) % d))
    with pytest.raises(ValueError):
        oracle.verify_closure(other.carrier_rows(), n0)
