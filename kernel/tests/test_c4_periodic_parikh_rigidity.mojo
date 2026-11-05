"""Canonical exact integer phase-rank necessary-condition controls.

M=[[1,0,1],[1,2,1],[0,1,1]] is primitive irreducible Pisot.
The h=2,3 block cyclic packets are SYNTHETIC, not balanced word SCCs.
"""
from std.testing import assert_equal
from mojo_smoke.claims import require_contract
from psc.c4_periodic_parikh_phase import audit_periodic_parikh_phase_rank


def refusal_reason(
    M: List[List[Int]],
    P: List[List[Int]],
    N: List[List[Int]],
    phases: List[Int],
    period: Int,
) raises -> String:
    """The audit's error message, or "" if it accepted the packet."""
    try:
        _ = audit_periodic_parikh_phase_rank(M, P, N, phases, period)
    except e:
        return String(e)
    return String("")


def test_pip_synthetic_six_state_period_two_saturates_bound() raises:
    var M: List[List[Int]] = [
        [1, 0, 1], [1, 2, 1], [0, 1, 1],
    ]
    # P=[I,M], N=[[0,M^2],[I,0]], and P*N=M*P.
    var P: List[List[Int]] = [
        [1, 0, 0, 1, 0, 1],
        [0, 1, 0, 1, 2, 1],
        [0, 0, 1, 0, 1, 1],
    ]
    var N: List[List[Int]] = [
        [0, 0, 0, 1, 1, 2],
        [0, 0, 0, 3, 5, 4],
        [0, 0, 0, 1, 3, 2],
        [1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0],
    ]
    var phases: List[Int] = [0, 0, 0, 1, 1, 1]
    var sizes = audit_periodic_parikh_phase_rank(M, P, N, phases, 2)
    assert_equal(sizes, [3, 3])


def test_pip_synthetic_nine_state_period_three_saturates_bound() raises:
    var M: List[List[Int]] = [
        [1, 0, 1], [1, 2, 1], [0, 1, 1],
    ]
    # P=[I,M,M^2]. N maps phase0->1 and 1->2 by I,
    # and phase2->0 by M^3=[[2,4,4],[8,14,12],[4,8,6]].
    var P: List[List[Int]] = [
        [1, 0, 0, 1, 0, 1, 1, 1, 2],
        [0, 1, 0, 1, 2, 1, 3, 5, 4],
        [0, 0, 1, 0, 1, 1, 1, 3, 2],
    ]
    var N: List[List[Int]] = [
        [0,0,0,0,0,0,2,4,4],
        [0,0,0,0,0,0,8,14,12],
        [0,0,0,0,0,0,4,8,6],
        [1,0,0,0,0,0,0,0,0],
        [0,1,0,0,0,0,0,0,0],
        [0,0,1,0,0,0,0,0,0],
        [0,0,0,1,0,0,0,0,0],
        [0,0,0,0,1,0,0,0,0],
        [0,0,0,0,0,1,0,0,0],
    ]
    var phases: List[Int] = [0,0,0,1,1,1,2,2,2]
    assert_equal(audit_periodic_parikh_phase_rank(M, P, N, phases, 3), [3,3,3])


def test_broken_intertwiner_and_phase_fail_closed() raises:
    var M: List[List[Int]] = [
        [1,0,1], [1,2,1], [0,1,1],
    ]
    var P: List[List[Int]] = [
        [1,0,0,1,0,1], [0,1,0,1,2,1], [0,0,1,0,1,1],
    ]
    var N: List[List[Int]] = [
        [0,0,0,1,1,2], [0,0,0,3,5,4], [0,0,0,1,3,2],
        [1,0,0,0,0,0], [0,1,0,0,0,0], [0,0,1,0,0,0],
    ]
    var phases: List[Int] = [0,0,0,1,1,1]
    var broken_P: List[List[Int]] = [
        [1,0,0,2,0,1], [0,1,0,1,2,1], [0,0,1,0,1,1],
    ]
    # Refused by the exact intertwiner check, not by a budget guard.
    assert_equal(
        refusal_reason(M, broken_P, N, phases, 2),
        "exact Parikh intertwiner P N = M P fails",
    )

    # Refused by the phase-transition logic: state 0 is labelled phase 1,
    # but its child (state 3) is also phase 1, not phase 0.
    var wrong_phase: List[Int] = [1,0,0,1,1,1]
    assert_equal(
        refusal_reason(M, P, N, wrong_phase, 2),
        "child violates supplied phase transition",
    )

    # Refused ONLY by the input budget guard r >= 3*period (6 < 9): this
    # is a resource/shape refusal, not a phase-rank verdict.
    assert_equal(
        refusal_reason(M, P, N, phases, 3),
        "invalid periodic class size/period budget",
    )


def test_real_strict_primitive_but_reducible_four_state_refuses() raises:
    # Actual strict complete word system of #462; M is reducible cubic,
    # rank(P)=2 (p0=p2). It is not a genuine PIP strict carrier.
    var M: List[List[Int]] = [
        [1,1,0], [1,1,2], [0,1,1],
    ]
    var P: List[List[Int]] = [
        [1,1,2,4], [1,3,4,6], [1,1,2,4],
    ]
    var N: List[List[Int]] = [
        [0,0,3,5], [0,0,1,3], [1,0,1,1], [0,1,0,0],
    ]
    var phases: List[Int] = [0,0,0,0]
    # PN=MP holds and every phase edge is valid; the packet passes the
    # budget guard (r=4 >= 3) and is refused by the rank logic itself.
    assert_equal(
        refusal_reason(M, P, N, phases, 1),
        "period class has rational Parikh rank less than three",
    )


def main() raises:
    test_pip_synthetic_six_state_period_two_saturates_bound()
    test_pip_synthetic_nine_state_period_three_saturates_bound()
    test_broken_intertwiner_and_phase_fail_closed()
    test_real_strict_primitive_but_reducible_four_state_refuses()
    print("C4 periodic class Parikh rank controls passed.")
    require_contract("a supplied complete strict ternary irreducible Pisot SCC of period h has full Parikh rank three in EACH phase and at least 3h states; exact synthetic period-2/3 saturations, real reducible strict rank-two refusal, no claim of actual Pisot SCC")
