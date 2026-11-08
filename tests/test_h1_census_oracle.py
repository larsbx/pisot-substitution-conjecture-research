"""Pytest wrapper of the Anderson-Putnam oracle oracles/python/h1_census_ap.py:
published calibration values, the corpus specimens pinned by the Mojo
regression, and the order-independent census tables."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "oracles", "python"))

import h1_census_ap as ap  # noqa: E402

REPO = os.path.join(HERE, "..")


def dim(sigma):
    return ap.analyse([tuple(w) for w in sigma])["dimH1"]


def test_published_calibration_values():
    assert dim([[0, 1], [0]]) == 2
    assert dim([[0, 1], [1, 0]]) == 2
    assert dim([[0, 1], [0, 0]]) == 2
    assert dim([[0, 1], [0, 2], [0]]) == 3
    assert dim([[1, 0, 0, 0, 1], [0, 1, 0]]) == 3
    assert dim([[0, 1], [1, 2], [2, 0, 0]]) == 7
    assert dim([[0, 1], [1, 2], [2, 0]]) == 7
    r = ap.analyse([(0, 1, 2, 3, 0), (0, 1), (2, 3, 1, 2), (3, 1)])   # Barge-Diamond 2008 Ex. 8
    assert r["dimH1"] == 3 and r["evrank"] == 4


def test_corpus_specimens_across_the_strata():
    expected = {
        (3, 1): [[1], [2], [0, 2]], (3, -1): [[1], [0, 1, 2], [2, 1]], (3, 2): [[1], [2, 2], [0, 1, 2]],
        (4, 1): [[1], [1, 2], [2, 0, 1]], (4, -1): [[1], [0, 2, 1], [1, 2]], (4, 2): [[1], [0, 1, 2], [0, 0, 1]],
        (5, 1): [[1], [2], [0, 1]], (5, -1): [[0, 1], [0, 2], [2, 1, 0]], (5, 2): [[1], [2, 2], [0, 2, 1]],
        (7, 1): [[1], [0, 2], [2, 0, 0]], (7, -1): [[1], [0, 2], [2, 2, 0]], (7, 2): [[0, 1], [2, 2], [1, 0, 0]],
    }
    for (d, det), sigma in expected.items():
        r = ap.analyse([tuple(w) for w in sigma])
        assert (r["dimH1"], r["det"]) == (d, det), (sigma, r)


def test_corpus_census_tables():
    t = ap.census(ap.corpus_sigmas(REPO))
    assert t["total"] == 4554
    assert dict(t["dimensions"]) == {3: 3102, 4: 552, 5: 720, 7: 180}
    assert dict(t["unimodular"]) == {3: 1740, 4: 396, 5: 408, 7: 84}
    assert dict(t["det_dimension"]) == {
        (-1, 3): 420, (-1, 4): 144, (-1, 5): 72, (-1, 7): 12,
        (1, 3): 1320, (1, 4): 252, (1, 5): 336, (1, 7): 72,
        (2, 3): 1362, (2, 4): 156, (2, 5): 312, (2, 7): 96,
    }
    assert dict(t["endpoint_dimension"]) == {
        (0, 0, 3): 48, (0, 1, 3): 192, (0, 2, 3): 72, (0, 3, 3): 6, (0, 4, 3): 24, (0, 5, 3): 84, (0, 6, 3): 150,
        (1, 0, 3): 192, (1, 1, 3): 348, (1, 2, 3): 198, (1, 3, 3): 6, (1, 4, 3): 120, (1, 5, 3): 318, (1, 6, 3): 138,
        (2, 0, 3): 72, (2, 1, 3): 198, (2, 2, 3): 30, (2, 4, 3): 6, (2, 4, 4): 24, (2, 5, 4): 228, (2, 6, 5): 222,
        (3, 0, 3): 6, (3, 1, 3): 6, (3, 5, 5): 24, (3, 6, 7): 24,
        (4, 0, 3): 24, (4, 1, 3): 120, (4, 2, 3): 6, (4, 2, 4): 24, (4, 4, 5): 12, (4, 5, 3): 24, (4, 5, 5): 18, (4, 6, 7): 66,
        (5, 0, 3): 84, (5, 1, 3): 318, (5, 2, 4): 228, (5, 3, 5): 24, (5, 4, 3): 24, (5, 4, 5): 18, (5, 5, 4): 48, (5, 6, 5): 90,
        (6, 0, 3): 150, (6, 1, 3): 138, (6, 2, 5): 222, (6, 3, 7): 24, (6, 4, 7): 66, (6, 5, 5): 90,
    }


def test_refusals():
    for bad in ([(0, 0), (1, 1)], [(0,), (1,)]):
        try:
            ap.analyse(bad)
        except (ValueError, AssertionError):
            pass
        else:
            raise AssertionError(f"non-primitive input accepted: {bad}")
