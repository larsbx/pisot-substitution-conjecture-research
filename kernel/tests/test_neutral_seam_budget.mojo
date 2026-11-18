"""Neutral-sign counterexamples and the conditional source-orbit budget.

This is not a repeat of the 48 power comparisons. It tests the new bound,
the missing-orbit correction, and positive corrections at the actual neutral
sign on new productive controls, with literal source-occurrence witnesses.
"""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_geometric_f import PrototileMap, PrototileState, StableRadiiCache, decide_geometric_f_with
from psc.h1_census import h1_profile
from psc.literal_seam_replay import literal_one_track_returns, replay_interior_return, replay_seam_return
from psc.neutral_seam_budget import optional_source_budget, represented_source_budget, source_orbit_budget
from psc.one_track_seam_spectrum import one_track_seam_cycles, overlap_boundary_masks
from psc.periodic_overlap_returns import PeriodicOverlapGraph
from psc.rank_two_parity import ERGraphMap, er_graph_map
from test_c4_cut_attractor import test_reducible_strict_control
from test_literal_seam_replay import (
    compare_endpoint_identities, compare_seam_identities, expected_endpoints, expected_seams,
)


def _power(perm: List[Int], q: Int) -> List[Int]:
    var result = List[Int]()
    for start in range(len(perm)):
        var x = start
        for _ in range(q):
            x = perm[x]
        result.append(x)
    return result^


def _subset_mult(perm: List[Int], used: List[Bool], sign: Int) raises -> Int:
    var seen = List[Bool](length=len(perm), fill=False)
    var count = 0
    for start in range(len(perm)):
        if not used[start] or seen[start]:
            continue
        var x = start
        var length = 0
        while not seen[x]:
            assert_true(used[x])
            seen[x] = True
            length += 1
            x = perm[x]
        assert_equal(x, start)
        count += Int(sign == 1 or length % 2 == 0)
    return count


def _all_invariant_subgraphs(graph: ERGraphMap) raises -> Int:
    # Independent finite oracle: select the literal edge subset, build its
    # incident vertices, and walk the powered permutations directly. S may
    # be disconnected. Empty S is dealt with by the positive-part envelope.
    assert_true(graph.edge_count() <= 9)
    var checks = 0
    for q in range(1, 7):
        var ep = _power(graph.edge_image, q)
        var vp = _power(graph.vertex_image, q)
        for bits in range(1, 1 << graph.edge_count()):
            var used_e = List[Bool]()
            for k in range(graph.edge_count()):
                used_e.append((bits & (1 << k)) != 0)
            var invariant = True
            for k in range(graph.edge_count()):
                invariant = invariant and used_e[k] == used_e[ep[k]]
            if not invariant:
                continue
            var used_v = List[Bool](length=graph.vertex_count(), fill=False)
            for k in range(graph.edge_count()):
                if used_e[k]:
                    var a = graph.edges[k] // graph.letters
                    var b = graph.letters + graph.edges[k] % graph.letters
                    for j in range(graph.vertex_count()):
                        if graph.vertices[j] == a or graph.vertices[j] == b:
                            used_v[j] = True
            for sign in [-1, 1]:
                var delta = sign if q % 2 else 1
                var correction = _subset_mult(ep, used_e, delta) - _subset_mult(vp, used_v, delta)
                var bound = source_orbit_budget(graph, q, sign)
                assert_true(correction <= bound)
                if bits == (1 << graph.edge_count()) - 1:
                    assert_equal(correction, bound)
                checks += 1
    return checks


def _control(
    sigma: List[List[Int]], det: Int, betti: Int, expected_periods: List[Int],
    plus: Int, minus: Int, optional_plus: Int, optional_minus: Int,
    literal_power: Int = 0,
) raises -> Int:
    var source = er_graph_map(sigma)
    assert_equal(source.betti(), betti)
    var h1 = h1_profile(sigma)
    assert_equal(h1.components, 1)
    assert_equal(h1.dimension, 3 + betti)
    var m = PrototileMap(sigma)
    assert_equal(m.incidence.det(), det)
    var boxes = StableRadiiCache()
    var verdict = decide_geometric_f_with(m, boxes)
    var periods = List[Int]()
    for cycle in verdict.cycles:
        periods.append(cycle.period())
    assert_equal(periods, expected_periods)
    var product = represented_source_budget(source, periods)
    var envelope = optional_source_budget(source, periods)
    assert_equal(product.plus, plus)
    assert_equal(product.minus, minus)
    assert_equal(envelope.plus, optional_plus)
    assert_equal(envelope.minus, optional_minus)

    # One full-box construction per specimen, retaining actual occurrences.
    # Its zero sink count makes explicit that no strict carrier is tested.
    var graph = PeriodicOverlapGraph(sigma)
    assert_equal(graph.aligned_sinks, 0)
    var masks = overlap_boundary_masks(graph.tables, graph.graph.states)
    var profile = one_track_seam_cycles(graph.graph.adj, masks)
    assert_equal(profile.cyclotomic_correction(1), plus)
    assert_equal(profile.cyclotomic_correction(2), minus)
    print("source", sigma, "det", det, "ER", source.edges, "edge_map", source.edge_image,
          "vertices", source.vertices, "vertex_map", source.vertex_image,
          "betti", betti, "interior_periods", periods, "radii", verdict.radii,
          "full_correction", plus, minus, "optional_budget", optional_plus, optional_minus,
          "seam_cycles", profile.first, profile.last, profile.seam,
          "aligned_sinks", graph.aligned_sinks)

    if literal_power > 0:
        var literal = literal_one_track_returns(sigma, literal_power)
        assert_equal(literal.fixed_counts(), profile.fixed_counts(literal_power))
        compare_endpoint_identities(literal.first, expected_endpoints(graph, masks, literal_power, False))
        compare_endpoint_identities(literal.last, expected_endpoints(graph, masks, literal_power, True))
        compare_seam_identities(literal.seams, expected_seams(graph, masks, profile, literal_power))
        # Compare exact interior states with the complete certified cycles;
        # the literal constructor did not consume that cycle search.
        var expected = List[PrototileState]()
        for cycle in verdict.cycles:
            if literal_power % cycle.period() == 0:
                for state in cycle.states:
                    expected.append(state)
        assert_equal(len(literal.interiors), len(expected))
        var seen = List[PrototileState]()
        for item in literal.interiors:
            assert_true(item.state in expected)
            assert_true(item.state not in seen)
            seen.append(item.state)
            replay_interior_return(literal.images, item)
            print("literal_witness", "power", literal_power, "state", item.state,
                  "ordinal", item.ordinal, "prefix", item.prefix,
                  "source_word", literal.images[item.state.letter])
        for seam in literal.seams:
            replay_seam_return(graph.tables, literal.images, literal.interiors, literal.bigrams, seam)
    return _all_invariant_subgraphs(source)


def _missing_orbit_counterexample() raises:
    # E is one fixed edge. The ambient inventory has two fixed marked
    # copies, but S occupies only one. -1 > -2 disproves ambient signed-sum
    # monotonicity, even for nonempty S. This is a graph witness, not PIP3.
    var edge = er_graph_map([[0, 1], [0, 1]])
    assert_equal(edge.edge_count(), 1)
    assert_equal(edge.vertex_count(), 2)
    var full = represented_source_budget(edge, [1, 1])
    var used = represented_source_budget(edge, [1])
    var safe = optional_source_budget(edge, [1, 1])
    assert_equal(full.plus, -2)
    assert_equal(used.plus, -1)
    assert_true(used.plus > full.plus)
    assert_equal(safe.plus, 0)


def _four_letter_scope() raises:
    # Literal primitive source with all bigrams, first map identity and last
    # map a four-cycle. Neither has a two-cycle. With a hypothetical odd
    # interior mark its source-orbit minus budget is +3, not zero. The mark
    # is not claimed to be a periodic state of this non-PIP3 source.
    var sigma = List[List[Int]]()
    for a in range(4):
        var word: List[Int] = [a]
        for b in range(4):
            for c in range(4):
                word.append(b)
                word.append(c)
        word.append((a + 1) % 4)
        sigma.append(word^)
    var graph = er_graph_map(sigma)
    assert_equal(graph.edge_count(), 16)
    assert_equal(graph.betti(), 9)
    assert_equal(source_orbit_budget(graph, 1, -1), 3)
    print("four_letter_graph_control", "first=identity", "last=4-cycle", "q=1 minus_budget=3; no actual interior-state claim")


def _refusals() raises:
    var graph = er_graph_map([[0, 1], [0, 1]])
    var refused = False
    try:
        _ = source_orbit_budget(graph, 0, 1)
    except e:
        refused = "interior period must be positive" in String(e)
    assert_true(refused)
    refused = False
    try:
        _ = source_orbit_budget(graph, 1, 0)
    except e:
        refused = "target must be +1 or -1" in String(e)
    assert_true(refused)
    # A genuine available literal strict component, outside unit PIP3.
    # Replay the existing four-state words, child matrix and closure first;
    # then verify that the connected-source budget refuses its graph.
    test_reducible_strict_control()
    refused = False
    try:
        _ = er_graph_map([[1, 0], [1, 0, 2], [2, 1, 1]])
    except e:
        refused = "eventual range is disconnected" in String(e)
    assert_true(refused)
    print("strict_control", "10/102/211 four-state literal closure replayed; connected-source budget refused; reducible det=-2")


def main() raises:
    var checks = 0
    checks += _control([[0, 1], [1, 2], [0, 2, 1]], 1, 1, [1], -1, 1, 0, 1)
    checks += _control([[1], [0, 2], [2, 0, 2]], -1, 0, [2], -1, -1, 0, 0)
    checks += _control([[1], [2], [0, 2, 1]], 1, 2, [], 0, 0, 0, 0)
    checks += _control([[0, 1], [0, 2], [0]], 1, 0, [], 0, 0, 0, 0)
    # New literal counterexamples to determinant-selected nonpositivity.
    checks += _control([[0, 1], [1, 2, 2], [2, 0, 1]], 1, 2, [4], 1, 1, 1, 1, 4)
    checks += _control([[1, 2], [0, 1, 2], [2, 2, 1]], -1, 2, [1, 1], 0, 2, 0, 2, 2)
    # A real source inventory where unused negative orbits matter.
    checks += _control([[1, 2], [1, 2, 0], [2, 2, 1]], -1, 2, [3, 1], 0, 0, 1, 0, 3)
    _missing_orbit_counterexample()
    _four_letter_scope()
    _refusals()
    print("finite_invariant_subgraph_sign_checks", checks)
    require_contract("Conditional neutral seam budget: the connected source ER gives a sharp bound for each represented interior orbit at eps^q, and the sum of positive parts is safe when source orbits may be absent. Exact graph subsets test the inequality and equality on the full slice; a missing negative orbit refutes ambient signed-sum monotonicity. New productive unit PIP3 controls 01/122/201 and 12/012/221 have positive corrections at determinant-selected neutral signs, checked by literal occurrence witnesses and canonical full-box seams; 12/120/221 has cancelling period-three and period-one source contributions. All seven controls have no aligned nonproductive sink. A four-letter graph preserves the corrected endpoint-cycle scope; no strict joining, universal exclusion or PSC is certified")
