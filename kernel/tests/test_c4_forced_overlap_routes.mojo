"""Complete occurrence graphs of C4 weighted physical crossing controls."""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, decompose, newborn_sync_positions
from psc.c4_addressed_newborn import addressed_newborn
from psc.overlap_seed_patch import (
    OverlapState, build_seed_overlap_tables, build_overlap_graph_from_seeds,
    first_coincidence_depths, first_depths, interior_overlap, selected_overlap_child,
)
from psc.perron_field3 import CubicElt, cubic_sub_checked, sign_at_perron
from psc.words import Pair, parikh


def aligned_good(state: OverlapState, hub: Int = 1) -> Bool:
    return (state.shift.is_zero() and state.top != state.bottom
            and state.top != hub and state.bottom != hub)


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


def test_forced_crossing_without_good_edge_route() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [0, 0, 2]]
    assert_equal([sigma[0][0], sigma[1][0], sigma[2][0]], [1, 0, 0])
    var pair = Pair([0, 1], [1, 0])
    for _ in range(2):
        var row = decompose(apply_substitution(sigma, pair.u),
                            apply_substitution(sigma, pair.v))
        pair = row[0].copy()
    assert_equal(pair, Pair([0, 2, 1, 0], [1, 0, 0, 2]))
    var children = decompose(apply_substitution(sigma, pair.u),
                             apply_substitution(sigma, pair.v))
    assert_equal(len(children), 1)
    assert_equal(children[0], Pair([1, 0, 0, 2, 0, 2, 1], [0, 2, 1, 1, 0, 0, 2]))
    var grandchildren = decompose(apply_substitution(sigma, children[0].u),
                                  apply_substitution(sigma, children[0].v))
    assert_equal(len(grandchildren), 3)
    assert_equal(grandchildren[1], Pair([0], [0]))
    assert_equal(grandchildren[2], Pair([2], [2]))

    var tables = build_seed_overlap_tables(sigma)
    # The second bottom hub starts at ell_1 + ell_0. Top source 1
    # is letter 2 and spans [ell_0, ell_0 + ell_2].
    assert_equal(sign_at_perron(tables.field, cubic_sub_checked(
        tables.lengths.at(2), tables.lengths.at(1))), 1)
    var root = OverlapState(pair.u[1], pair.v[2], tables.lengths.at(1))
    assert_true(interior_overlap(tables, root))
    var cache = Dict[CubicElt, Int]()
    var graph = build_overlap_graph_from_seeds(tables, [root], cache, 128)
    assert_false(graph.capped)
    assert_equal(graph.size(), 54)
    var edges = 0
    var left_good = List[Bool]()
    var right_good = List[Bool]()
    for i in range(graph.size()):
        edges += len(graph.adj[i])
        var state = graph.states[i]
        left_good.append(aligned_good(state, 0))
        var end_alignment = cubic_sub_checked(tables.lengths.at(state.top),
                                              tables.lengths.at(state.bottom))
        right_good.append(state.top != state.bottom and state.top != 0 and
                          state.bottom != 0 and state.shift == end_alignment)
    assert_equal(edges, 94)
    assert_equal(first_depths(graph, left_good)[0], -1)
    assert_equal(first_depths(graph, right_good)[0], 7)
    assert_equal(first_coincidence_depths(graph)[0], 8)

    var top: List[Int] = [2, 2, 2, 1, 0, 1, 2, 1]
    var bottom: List[Int] = [0, 1, 0, 0, 0, 0, 1, 0]
    var current = root
    for i in range(len(top)):
        current = selected_overlap_child(tables, current, top[i], bottom[i])
        assert_true(interior_overlap(tables, current))
    assert_true(current.is_coincidence())
    assert_equal(current.top, 0)
    var witness = addressed_newborn(sigma, pair, 1, 2, top, bottom)
    assert_equal(witness.ordinals, [0, 0, 1, 0, 0, 0, 1, 1])
    assert_equal(witness.parent, Pair([1, 0, 0, 2, 0, 2, 0, 2, 1],
                                      [0, 2, 0, 2, 1, 1, 0, 0, 2]))
    assert_equal(witness.cut, 5)
    assert_true(witness.sync_right)
    assert_true(witness.cut in newborn_sync_positions(sigma, witness.parent))

    # The alternative shortest path enters the right-aligned good pair.
    # Its shared suffix supplies a different physical diagonal and newborn.
    top = [2, 2, 2, 2, 2, 0, 0, 0]
    bottom = [0, 1, 0, 0, 1, 2, 2, 1]
    current = root
    for i in range(7):
        current = selected_overlap_child(tables, current, top[i], bottom[i])
        assert_true(interior_overlap(tables, current))
    assert_equal([current.top, current.bottom], [1, 2])
    assert_equal(current.shift, cubic_sub_checked(tables.lengths.at(1),
                                                 tables.lengths.at(2)))
    current = selected_overlap_child(tables, current, top[7], bottom[7])
    assert_true(current.is_coincidence())
    var via_right = addressed_newborn(sigma, pair, 1, 2, top, bottom)
    assert_equal(via_right.ordinals, [0, 0, 1, 0, 0, 0, 1, 3])
    assert_equal(via_right.parent, witness.parent)
    assert_equal(via_right.cut, 15)
    assert_true(via_right.sync_right)
    assert_true(via_right.cut in newborn_sync_positions(sigma, via_right.parent))


def main() raises:
    check_route(
        [[1], [0, 2], [2, 2, 0]], [39, 80, 5], [[0, 0], [0, 1], [1, 1]],
        [4, 5, 2], [[1, 1], [0, 0], [0, 1]], 2, 3, 7,
    )
    check_route(
        [[0, 1], [1, 2], [0, 2, 1]], [68, 146, 6], [[1, 0], [2, 0], [2, 1]],
        [4, 3, 2], [[2, 1], [1, 0], [2, 1]], 1, 4, 5,
    )
    test_forced_crossing_without_good_edge_route()
    require_contract("literal first physical hub crossing with complete flat one-step row, shortest diagonal at depth eight, no left-aligned good edge, and a right-aligned good edge at depth seven")
    require_contract("the right-aligned route to a shortest diagonal transports to Sync+ at cut 15")
    require_contract("complete forced-overlap graphs, all actual first choices, necessary first-step hub-plane escape, and shortest direct and aligned-good-edge routes")

