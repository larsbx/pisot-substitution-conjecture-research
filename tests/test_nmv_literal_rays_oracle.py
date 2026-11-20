"""Independent literal-word oracle for the (NM_V) census.

The canonical census is kernel/nmv_census.mojo (kernel/psc/zero_fibre_asymptotes.mojo),
pinned by kernel/tests/test_zero_fibre_asymptotes.mojo, with its log in
evidence/nmv-census-2026-11-18/. This test runs the stdlib oracle
oracles/python/nmv_literal_rays.py, which shares no code with it, on every
failing pair of that log and requires each to be confirmed.
"""
import ast
import runpy
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ORACLE = runpy.run_path(str(ROOT / "oracles/python/nmv_literal_rays.py"))
LOG = ROOT / "evidence/nmv-census-2026-11-18/nmv-census.log"


def test_every_census_failure_is_a_literal_asymptote():
    assert ORACLE["confirm_log"](LOG) == 96


def test_census_totals_are_recorded():
    text = LOG.read_text()
    assert "domain (unit, >=2 periodic letters on both sides) 936" in text
    assert "NM_V holds 888 left failures 24 right failures 24" in text
    assert "scope: beta1 >= 2 492 of which NM_V holds 492" in text
    assert sum(1 for line in text.splitlines() if line.startswith("fail")) == 48


def periodic_count(endpoint):
    power = range(3)
    for _ in range(6):
        power = [endpoint[a] for a in power]
    return sum(a == image for a, image in enumerate(power))


def test_all_census_failures_have_a_small_side():
    shapes = Counter()
    for line in LOG.read_text().splitlines():
        if not line.startswith("fail: "):
            continue
        words, summary = line.split(" sigma ")[1].split(" b1 ")
        sigma = ast.literal_eval(words)
        rank = int(summary.split()[0])
        left = periodic_count([w[-1] for w in sigma])
        right = periodic_count([w[0] for w in sigma])
        if "[R " in line:
            assert left == 2
        if "[L " in line:
            assert right == 2
        assert rank <= (left - 1) * (right - 1)
        shapes[rank, left, right] += 1
    assert shapes == {(0, 2, 3): 12, (0, 3, 2): 12, (1, 2, 2): 24}


def test_literal_rays_confirm_rank_two_counterexamples():
    for sigma, address, right in (
        ([[0, 1], [2, 1, 0], [1, 0, 2, 1]], [-1, 0, 1], True),
        ([[1, 0], [0, 1, 2], [1, 2, 0, 1]], [1, 0, 0], False),
        ([[0, 1], [2, 1, 0, 0], [1, 0, 0, 2, 1]], [-1, 0, 1], True),
    ):
        vertex = ORACLE["vertex_ray"](sigma, 0, right)
        interior = ORACLE["interior_ray"](sigma, 2, address, right)
        assert ORACLE["agree"](vertex, [0, 0, 0], interior, [-a for a in address], right)
