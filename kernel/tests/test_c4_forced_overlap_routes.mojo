"""Complete occurrence graphs of the two C4 weighted physical crossing controls."""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.overlap_seed_patch import (
    OverlapState, build_seed_overlap_tables, build_overlap_graph_from_seeds,
    first_coincidence_depths, first_depths, interior_overlap, selected_overlap_child,
)
from psc.perron_field3 import CubicElt
from psc.words import parikh


def aligned_good(state: OverlapState) -> Bool:
    return state.shift.is_zero() and (
        (state.top == 0 and state.bottom == 2) or
        (state.top == 2 and state.bottom == 0)
    )


def check_route(
    sigma: List[List[Int]], totals: List[Int], first: List[List[Int]],
    first_remaining: List[Int], direct: List[List[Int]], last_letter: Int,
    good_depth: Int, via_good: Int,
) raises:
    var tables = build_seed_overlap_tables(sigma)
    # Graph shifts are bottom-start minus top-start. The literal Parikh
    # convention is the opposite, so E=-e_0 is represented by +ell_0.
    var seed = OverlapState(2, 1, tables.lengths.at(0))
    assert_true(interior_overlap(tables, seed))
    var sign_cache = Dict[CubicElt, Int]()
    var graph = build_overlap_graph_from_seeds(tables, [seed], sign_cache, 128)
    assert_false(graph.capped)
    assert_equal(graph.size(), totals[0])
    assert_equal(graph.states[0], seed)
    var depths = first_coincidence_depths(graph)
    var edge_count = 0
    var max_depth = 0
    var good = List[Bool]()
    for i in range(graph.size()):
        edge_count += len(graph.adj[i])
        assert_true(depths[i] >= 0)
        max_depth = max(max_depth, depths[i])
        good.append(aligned_good(graph.states[i]))
    assert_equal([edge_count, max_depth], [totals[1], totals[2]])
    assert_equal(depths[0], len(direct))
    assert_equal(first_depths(graph, good)[0], good_depth)

    var best_via_good = -1
    for i in range(graph.size()):
        if good[i]:
            var singleton = List[Bool](length=graph.size(), fill=False)
            singleton[i] = True
            var to_good = first_depths(graph, singleton)[0]
            assert_true(to_good >= 0)
            var total = to_good + depths[i]
            if best_via_good < 0 or total < best_via_good:
                best_via_good = total
    assert_equal(best_via_good, via_good)

    # The initial defect is -e_0. The hub occurs once in sigma(0),
    # and no proper prefix of sigma(2) contains a hub. All actual
    # first choices have a strictly negative hub coordinate.
    assert_equal(parikh(sigma[0])[1], 1)
    var seen = List[List[Int]]()
    var top_hubs = 0
    for i in range(len(sigma[2])):
        assert_equal(top_hubs, 0)
        var bottom_hubs = 0
        for j in range(len(sigma[1])):
            var child = selected_overlap_child(tables, seed, i, j)
            if interior_overlap(tables, child):
                var k = len(seen)
                assert_true(k < len(graph.adj[0]))
                var id = graph.adj[0][k]
                assert_equal(graph.states[id], child)
                assert_equal(depths[id], first_remaining[k])
                assert_true(-1 + top_hubs - bottom_hubs < 0)
                seen.append([i, j])
            bottom_hubs += Int(sigma[1][j] == 1)
        top_hubs += Int(sigma[2][i] == 1)
    assert_equal(seen, first)
    assert_equal(len(seen), len(graph.adj[0]))

    var state = seed
    for i in range(len(direct)):
        assert_false(aligned_good(state))
        assert_false(state.is_coincidence())
        state = selected_overlap_child(tables, state, direct[i][0], direct[i][1])
        assert_true(interior_overlap(tables, state))
    assert_true(state.is_coincidence())
    assert_equal(state.top, last_letter)


def main() raises:
    check_route(
        [[1], [0, 2], [2, 2, 0]], [39, 80, 5], [[0, 0], [0, 1], [1, 1]],
        [4, 5, 2], [[1, 1], [0, 0], [0, 1]], 2, 3, 7,
    )
    check_route(
        [[0, 1], [1, 2], [0, 2, 1]], [68, 146, 6], [[1, 0], [2, 0], [2, 1]],
        [4, 3, 2], [[2, 1], [1, 0], [2, 1]], 1, 4, 5,
    )
    require_contract("complete forced-overlap graphs, all actual first choices, necessary first-step hub-plane escape, and shortest direct and aligned-good-edge routes")
