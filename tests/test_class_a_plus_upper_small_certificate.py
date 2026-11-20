"""Independent complete S18 certificates for the 70 upper plus-Class-A members
n=0..6, n+5<=d<=2n+11, the exact PIP boundary d<=2n+11, and scope refusals."""
from fractions import Fraction
from pathlib import Path
import runpy
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
O = runpy.run_path(str(ROOT / "oracles/python/class_a_plus_small_certificate.py"))
PLUS = runpy.run_path(str(ROOT / "oracles/python/class_a_plus_constant_entry.py"))
sys.path.insert(0, str(ROOT / "reference"))
from psc_research import pip_screen as P  # noqa: E402

UPPER = O["UPPER_MEMBERS"]


def screen(n, d):
    words = ((0,) + (2,)*(n+d) + (0,), (1,) + (2,)*n + (0,), (0,) + (2,)*(n+1) + (1,))
    M = P.mat({k+1: tuple(a+1 for a in w) for k, w in enumerate(words)})
    T, U, D = P.charpoly(M)
    return P.primitive(M) and P.irreducible(T, U, D) and P.pisot(T, U, D)


def test_upper_scope_is_exactly_the_seventy_members():
    assert UPPER == tuple((n, d) for n in range(7) for d in range(n+5, 2*n+12))
    assert len(UPPER) == 70 and not set(UPPER) & set(O["MEMBERS"])


@pytest.mark.parametrize("n,d", UPPER)
def test_complete_original_graph_and_every_prefix(n, d):
    packet, summary = O["make_member"](n, d)
    assert screen(n, d)
    assert summary["sources"] == 18 and summary["complete"]
    assert summary["target_policy"] == "typed full integral zero"
    assert len(summary["original_prefix_certificates"]) == summary["vertices"] == summary["paths"]
    assert sum(p["depth"] for p in summary["original_prefix_certificates"]) == summary["path_edges"]
    for certificate in summary["original_prefix_certificates"]:
        assert certificate["scaled_source"] == [
            p-q for p, q in zip(certificate["top_prefix"], certificate["bottom_prefix"])]
        assert certificate["terminal_letters"][0] == certificate["terminal_letters"][1]
    for _, top, bottom, x, c, y, distance, selected, _ in packet["vertices"]:
        if (x, c, y) == (0, 0, 0):
            assert (distance == 0) == (top == bottom) == (selected == -1)


@pytest.mark.parametrize("n", range(40))
def test_pip_boundary_is_exactly_d_at_most_2n_plus_11(n):
    """chi(-1) = -(2n+12-d): a root at -1 when d=2n+12, a real root below -1 beyond."""
    chi = lambda x, d: x**3 - (n+4)*x*x + (n+5-d)*x - 2
    for d in range(1, 2*n+12):
        assert chi(-1, d) < 0
    assert chi(-1, 2*n+12) == 0 and not screen(n, 2*n+12)
    for d in range(2*n+13, 2*n+20):
        assert chi(-1, d) > 0 and not screen(n, d)
    if n <= 6:
        assert all(screen(n, d) for d in range(n+5, 2*n+12))


@pytest.mark.parametrize("n,d", UPPER + tuple((n, n+4) for n in range(1, 6)))
def test_perron_bracket_is_exact(n, d):
    lo, hi = PLUS["perron_bracket"](n, d)
    chi = lambda x: x**3 - (n+4)*x*x + (n+5-d)*x - 2
    assert hi == lo+1 and chi(lo) < 0 < chi(hi) and lo.denominator == 1
    assert all(chi(Fraction(x)) > 0 for x in range(int(hi), int(hi)+n+d+8))


@pytest.mark.parametrize("n,d", ((7, 12), (0, 12), (0, 4), (6, 24), (-1, 5), (True, 6)))
def test_upper_scope_does_not_expand(n, d):
    with pytest.raises(ValueError):
        O["make_member"](n, d)


@pytest.mark.parametrize("kwargs", ({"state_cap": 18}, {"pair_cap": 1}))
def test_caps_refuse_incomplete_upper_graphs(kwargs):
    with pytest.raises((ValueError, RuntimeError)):
        O["make_member"](0, 5, **kwargs)


def test_native_transcript_scope_is_bound():
    with pytest.raises(ValueError):
        O["verify_native_text"]("", "upper")
    with pytest.raises(KeyError):
        O["verify_native_text"]("", "everything")
