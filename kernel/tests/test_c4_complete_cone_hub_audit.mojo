"""Exact necessary cross-layer C4 strict-cone audit; no theorem promotion."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_complete_cone_hub_audit import audit_complete_strict_cones
from psc.words import Pair


def golden_strict() -> List[Pair]:
    return [
        Pair([1, 0, 2], [2, 1, 0]),
        Pair([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1],
             [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]),
    ]


def test_closed_fullrank_nonpisot_flatness_has_exact_eigen_obstruction() raises:
    # chi_M=(x-1)(x^2-2x-2); 4 literal states/16 occurrences.
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var a = audit_complete_strict_cones(sigma, golden_strict())
    assert_equal(a.candidate_good_mask, 3)
    assert_equal(a.flat_candidate_good_mask, 3)
    assert_equal(a.global_rank, 2)
    assert_equal(a.root_ranks, [2, 2, 2, 2])
    assert_equal(a.plane_normal, [1, 0, -1])
    assert_equal(a.plane_eigenvalue, 1)
    assert_equal(len(a.root_pivots), 4)
    for root in range(4):
        assert_equal(len(a.root_pivots[root]), 2)
        assert_equal(a.root_pivots[root][0].depth, 0)
        assert_equal(a.root_pivots[root][0].state_id, root)
    # The two actual pivots for root 0 are itself and its sole first
    # child S2, not two synthetic quotient vertices.
    assert_equal(a.root_pivots[0][1].depth, 1)
    assert_equal(a.root_pivots[0][1].state_id, 2)
    assert_equal(a.root_pivots[0][1].first_ordinal, 0)


def test_reject_productive_pip_or_truncated_strict_support() raises:
    # A recurrent PRODUCTIVE Tribonacci source SCC cannot be reclassified
    # by hiding diagonal occurrences from the complete child word.
    var trib: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var productive: List[Pair] = [
        Pair([0, 1], [1, 0]),
        Pair([1, 0, 2], [2, 0, 1]),
        Pair([0, 1, 0, 2], [2, 0, 1, 0]),
    ]
    var refused = False
    try:
        _ = audit_complete_strict_cones(trib, productive)
    except:
        refused = True
    assert_true(refused)

    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var full = golden_strict()
    var incomplete: List[Pair] = [full[0].copy(), full[1].copy(), full[2].copy()]
    refused = False
    try:
        _ = audit_complete_strict_cones(sigma, incomplete)
    except:
        refused = True
    assert_true(refused)


def test_explicit_cap_and_invalid_image_refusals() raises:
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var refused = False
    try:
        _ = audit_complete_strict_cones(sigma, golden_strict(), occurrence_cap=1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = audit_complete_strict_cones(sigma, golden_strict(), occurrence_cap=0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    var bad: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 3]]
    try:
        _ = audit_complete_strict_cones(bad, golden_strict())
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_closed_fullrank_nonpisot_flatness_has_exact_eigen_obstruction()
    test_reject_productive_pip_or_truncated_strict_support()
    test_explicit_cap_and_invalid_image_refusals()
    print("C4 complete strict cone rank/hub audit: exact obstruction and fail-closed controls.")
    require_contract("all-child strict derived system audit checks literal Parikh intertwining, two-level root cone ranks, all compatible hub words and primitive integral rank-two left eigenvector; never certifies genuine good edge or general PSC")
