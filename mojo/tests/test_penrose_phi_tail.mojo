"""Exact regressions for the Penrose H_tail Phi increment cocycle."""

from std.testing import assert_equal, assert_true

from psc.claim_tests import require_contract
from psc.penrose_phi_tail import (
    PenrosePhiElt,
    cycle_gain,
    h_tail_branch_cycle,
    h_tail_period_gain,
    phi_state_potential_obstruction,
)


def test_both_tail_cycles_have_the_same_exact_gain() raises:
    var expected = PenrosePhiElt(4, -1)
    assert_equal(cycle_gain(h_tail_branch_cycle(0)), expected)
    assert_equal(cycle_gain(h_tail_branch_cycle(1)), expected)
    assert_equal(h_tail_period_gain(), expected)


def test_period_gain_has_exact_norm_eleven():
    # N(4 - phi) = 4^2 + 4*(-1) - (-1)^2 = 11.
    assert_equal(h_tail_period_gain().norm(), 11)


def test_positive_growth_channel_is_not_a_state_potential():
    # A genuine state potential telescopes to zero around a closed loop.
    # The source-grounded increment channel has gain 4-phi != 0, so the
    # accumulated exact-prefix height must live on a lift of H_tail.
    assert_true(phi_state_potential_obstruction())


def main() raises:
    test_both_tail_cycles_have_the_same_exact_gain()
    print("[PASS] test_both_tail_cycles_have_the_same_exact_gain")
    test_period_gain_has_exact_norm_eleven()
    print("[PASS] test_period_gain_has_exact_norm_eleven")
    test_positive_growth_channel_is_not_a_state_potential()
    print("[PASS] test_positive_growth_channel_is_not_a_state_potential")
    print("3 Penrose H_tail Phi-cocycle tests passed.")
    require_contract("penrose H_tail penrose_phi_increment channel")
