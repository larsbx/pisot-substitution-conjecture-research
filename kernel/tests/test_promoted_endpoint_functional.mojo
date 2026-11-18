"""Telescoping of the promotion-weighted endpoint functional on literal boxes."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.one_track_seam_spectrum import overlap_boundary_masks
from psc.periodic_overlap_returns import PeriodicOverlapGraph
from psc.promoted_endpoint_functional import endpoint_telescoping


def check(sigma: List[List[Int]], naive_failures: Int) raises:
    var graph = PeriodicOverlapGraph(sigma)
    var masks = overlap_boundary_masks(graph.tables, graph.graph.states)
    for eps in [1, -1]:
        var weighted = endpoint_telescoping(graph, masks, eps)
        var naive = endpoint_telescoping(graph, masks, eps, False)
        print(sigma, "eps", eps, "columns", weighted.columns, "promoted seams", weighted.promoted_seams,
              "failures", weighted.failures, "naive failures", naive.failures)
        assert_equal(weighted.failures, 0)
        assert_true(weighted.promoted_seams > 0)
        assert_equal(naive.failures, naive_failures)


def main() raises:
    check([[0, 1], [1, 2, 2], [2, 0, 1]], 42)
    check([[0, 1], [1, 2], [0, 2, 1]], 38)
    check([[1], [0, 2], [2, 0, 2]], 22)
    check([[1], [2], [0, 2, 1]], 16)
    check([[0, 1], [0, 2], [0]], 20)
    check([[1, 2], [0, 2, 1], [1, 2, 2]], 40)
    var refused = False
    try:
        var graph = PeriodicOverlapGraph([[0, 1], [0, 2], [0]])
        _ = endpoint_telescoping(graph, overlap_boundary_masks(graph.tables, graph.graph.states), 0)
    except e:
        refused = String(e).find("eps") >= 0
    assert_true(refused)
    require_contract("On literal full overlap boxes the promotion-weighted endpoint functional telescopes column by column modulo local shared-cut and endpoint-equivariance forms, at both signs; promoted adjacencies are literal saturated shared cuts; the unweighted functional fails.")
