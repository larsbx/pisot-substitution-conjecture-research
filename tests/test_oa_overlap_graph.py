"""Exploratory helper regressions: exact enumeration window for G_O types."""
import pytest

from psc_research.oa_overlap_graph import fixed_point_prefix, oa_types, oa_window, prolongable_power
from psc_research.overlap_graph import OverlapGraph

TRIB = {1: (1, 2), 2: (1, 3), 3: (1,)}
WIDE = {1: (2,), 2: (3,), 3: (1, 3, 3)}  # large l_max / l_min ratio


def _setup(sigma, n=6000):
    g = OverlapGraph(sigma)
    q, c = prolongable_power(sigma)
    return g, fixed_point_prefix(sigma, q, c, n)


def test_window_is_least_integer_above_exact_bound():
    g, u = _setup(WIDE)
    F = g.F
    l_min = min(g.l, key=lambda x: sum(F.sign(F.sub(x, y)) for y in g.l))
    l_max = max(g.l, key=lambda x: sum(F.sign(F.sub(x, y)) for y in g.l))
    for k in (1, 8, 24):
        n = oa_window(g, u, k)
        bound = l_max
        for a in u[:k]:
            bound = F.add(bound, g.l[a - 1])
        scale = lambda m: tuple(x * m for x in l_min)
        assert F.sign(F.sub(scale(n), bound)) > 0
        assert F.sign(F.sub(scale(n - 1), bound)) <= 0


def test_heuristic_window_was_too_small_and_is_rejected():
    g, u = _setup(WIDE)
    assert oa_window(g, u, 24) > 14 + 24
    with pytest.raises(ValueError):
        oa_types(g, u, 24, 14 + 24)
    with pytest.raises(ValueError):
        oa_types(g, u[:10], 1)  # prefix too short for the window (6)


def test_tribonacci_level_zero_types_included_in_seed_graph():
    g, u = _setup(TRIB)
    seed = set(g.states)
    oa = oa_types(g, u, 1)
    assert oa and all(s in seed for s in oa if not OverlapGraph.is_coincidence(s))
