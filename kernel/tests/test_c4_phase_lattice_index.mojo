"""Canonical bounded exact index accounting in cyclic strict-C4 templates.

Synthetic PIP matrix packets are NOT literal strict balanced-word systems.
A caller still needs full word child closure, PIP and actual phase labels.
"""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_phase_lattice_index import audit_phase_lattice_index


def _m2() -> List[List[Int]]:
    return [[1,0,1], [1,2,1], [0,1,1]]


def _p_first() -> List[List[Int]]:
    return [
        [1,0,0,1,0,1],
        [0,1,0,1,2,1],
        [0,0,1,0,1,1],
    ]


def _n_first() -> List[List[Int]]:
    return [
        [0,0,0,1,1,2],
        [0,0,0,3,5,4],
        [0,0,0,1,3,2],
        [1,0,0,0,0,0],
        [0,1,0,0,0,0],
        [0,0,1,0,0,0],
    ]


def test_nonunit_phase_budget_one_four() raises:
    var cert = audit_phase_lattice_index(
        _m2(), _p_first(), _n_first(), [0,0,0,1,1,1], 2,
    )
    assert_equal(cert.det_M, 2)
    assert_equal(cert.class_indices, [1, 2])
    assert_equal(cert.transition_indices, [1, 4])


def test_nonunit_phase_budget_two_two_with_full_letter_support() raises:
    var P: List[List[Int]] = [
        [1,1,2,1,1,2],
        [3,5,4,3,5,4],
        [1,3,2,1,3,2],
    ]
    var N: List[List[Int]] = [
        [0,0,0,1,0,1],
        [0,0,0,1,2,1],
        [0,0,0,0,1,1],
        [1,0,1,0,0,0],
        [1,2,1,0,0,0],
        [0,1,1,0,0,0],
    ]
    var cert = audit_phase_lattice_index(
        _m2(), P, N, [0,0,0,1,1,1], 2,
    )
    assert_equal(cert.class_indices, [4, 4])
    assert_equal(cert.transition_indices, [2, 2])
    for row in range(3):
        for col in range(6):
            assert_true(P[row][col] > 0)


def test_unimodular_phase_lattices_do_not_leak() raises:
    # Tribonacci M det=+1, P=[M^3,M^3], N off-diagonal copies M.
    var M: List[List[Int]] = [
        [1,1,1], [1,0,0], [0,1,0],
    ]
    var P: List[List[Int]] = [
        [4,3,2,4,3,2],
        [2,2,1,2,2,1],
        [1,1,1,1,1,1],
    ]
    var N: List[List[Int]] = [
        [0,0,0,1,1,1],
        [0,0,0,1,0,0],
        [0,0,0,0,1,0],
        [1,1,1,0,0,0],
        [1,0,0,0,0,0],
        [0,1,0,0,0,0],
    ]
    var cert = audit_phase_lattice_index(M,P,N,[0,0,0,1,1,1],2)
    assert_equal(cert.det_M, 1)
    assert_equal(cert.class_indices, [1,1])
    assert_equal(cert.transition_indices, [1,1])


def test_bad_intertwiner_and_phase_labels_fail_closed() raises:
    var P = _p_first()
    P[0][3] = 2
    var refused = False
    try:
        _ = audit_phase_lattice_index(
            _m2(), P, _n_first(), [0,0,0,1,1,1], 2
        )
    except:
        refused = True
    assert_true(refused)

    refused = False
    try:
        _ = audit_phase_lattice_index(
            _m2(), _p_first(), _n_first(), [1,0,0,1,1,1], 2
        )
    except:
        refused = True
    assert_true(refused)

    var N = _n_first()
    N[3][0] = 0
    refused = False
    try:
        _ = audit_phase_lattice_index(
            _m2(), _p_first(), N, [0,0,0,1,1,1], 2
        )
    except:
        refused = True
    assert_true(refused)

    var M: List[List[Int]] = [[0,0,0],[0,0,0],[0,0,0]]
    refused = False
    try:
        _ = audit_phase_lattice_index(
            M, _p_first(), _n_first(), [0,0,0,1,1,1], 2
        )
    except:
        refused = True
    assert_true(refused)


def test_real_strict_reducible_rank_two_is_not_pip() raises:
    # Real 4-state strict derived system of #462, but reducible char.
    var M: List[List[Int]] = [[1,1,0],[1,1,2],[0,1,1]]
    var P: List[List[Int]] = [
        [1,1,2,4],[1,3,4,6],[1,1,2,4],
    ]
    var N: List[List[Int]] = [
        [0,0,3,5],[0,0,1,3],[1,0,1,1],[0,1,0,0],
    ]
    var refused = False
    try:
        _ = audit_phase_lattice_index(M,P,N,[0,0,0,0],1)
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_nonunit_phase_budget_one_four()
    test_nonunit_phase_budget_two_two_with_full_letter_support()
    test_unimodular_phase_lattices_do_not_leak()
    test_bad_intertwiner_and_phase_labels_fail_closed()
    test_real_strict_reducible_rank_two_is_not_pip()
    print("C4 phase-lattice indices and exact determinant budgets passed.")
    require_contract(
        "supplied finite strict Pisot SCC phases have integer index transports whose product is abs(det M)^h; unit transport is exact lattice equality, 3h transition blocks nonsingular; synthetic unit/nonunit controls and false-phase/low-rank refusals; no actual PIP SCC or C4/PSC conclusion"
    )
