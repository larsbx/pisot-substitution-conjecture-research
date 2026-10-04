"""Regressions for valuation ascent on the box graph (`psc.valuation_ascent`)."""

from std.testing import assert_equal, assert_true
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.claim_tests import require_contract
from psc.valuation_ascent import NU_INFINITY, m_valuation, valuation_ascent


def test_valuation_of_image_lattice_vectors() raises:
    """`0 -> 1, 1 -> 22, 2 -> 012` has `|det M| = 2`; `M e_a` has valuation
    at least 1 and `0` has infinite valuation."""
    var sigma: List[List[Int]] = [[1], [2, 2], [0, 1, 2]]
    var m = Mat3(substitution_incidence(sigma))
    assert_equal(abs(m.det()), 2)
    assert_equal(m_valuation(m, [0, 0, 0]), NU_INFINITY)
    for a in range(3):
        var e: List[Int] = [0, 0, 0]
        e[a] = 1
        assert_true(m_valuation(m, m.apply(e)) >= 1 + m_valuation(m, e))


def test_one_step_ascent_fails_on_a_catch_up_free_specimen() raises:
    """The first total Q1 failure of §5.6b: one-step valuation ascent fails
    on 368 of its 826 nonzero-offset descendants of recurrent vertices, so it
    is not a local mechanism for T2; failures occur at every valuation."""
    var v = valuation_ascent([[1], [2, 2], [0, 1, 2]])
    assert_true(v.catch_up_free)
    assert_equal(v.vertices, 826)
    assert_equal(v.one_step_failures, 368)
    assert_equal(v.max_valuation, 6)
    assert_equal(v.max_ascent_depth, 14)
    var expected: List[Int] = [156, 100, 54, 30, 14, 12, 2]
    assert_equal(len(v.failures_by_valuation), len(expected))
    for k in range(len(expected)):
        assert_equal(v.failures_by_valuation[k], expected[k])


def test_unimodular_valuation_fails_closed() raises:
    """`0 -> 1, 1 -> 2, 2 -> 01` is unimodular: every vector lies in `M Z^3`,
    so the valuation is undefined and must raise rather than loop."""
    var sigma: List[List[Int]] = [[1], [2], [0, 1]]
    var m = Mat3(substitution_incidence(sigma))
    var raised = False
    try:
        _ = m_valuation(m, [1, 0, 0])
    except:
        raised = True
    assert_true(raised)


def main() raises:
    test_valuation_of_image_lattice_vectors()
    test_one_step_ascent_fails_on_a_catch_up_free_specimen()
    test_unimodular_valuation_fails_closed()
    print("[PASS] valuation ascent: M-adic valuation, refuting specimen, unimodular fail-closed")
    require_contract("one-step M-adic valuation ascent on the box graph is decided exactly per catch-up-free substitution; it fails on 0 -> 1, 1 -> 22, 2 -> 012 (368 of 826 vertices), so it is not a local mechanism for simultaneous-birth reachability; a unimodular valuation fails closed")
