"""Exact uniform-width control for occurrence-level whole-factor enclosure."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries, decompose, normalise, suffix_endpoint_map
from psc.derived_system import build_derived_system, oriented_derived_word
from psc.endpoint_core import endpoint_type, endpoint_type_name
from psc.words import Pair, parikh


def test_each_source_routes_to_all_targets() raises:
    var sigma: List[List[Int]] = [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
    var states: List[Pair] = [
        Pair(sigma[0], sigma[1]), Pair(sigma[0], sigma[2]), Pair(sigma[1], sigma[2]),
    ]
    var system = build_derived_system(sigma, states)
    var routes = 0
    for root in range(system.size()):
        var top = states[root].u.copy()
        var bottom = states[root].v.copy()
        for _ in range(2):
            top = apply_substitution(sigma, top)
            bottom = apply_substitution(sigma, bottom)
        var cuts = coincidence_boundaries(top, bottom)
        var factors = oriented_derived_word(system, root, 2)
        assert_equal(len(cuts), len(factors) + 1)

        # The unit-width letter at index i on either track has its nine
        # descendants in [9*i,9*(i+1)). Select the middle balanced factor.
        for i in range(states[root].length()):
            var ordinal = 3 * i + 1
            var start = cuts[ordinal]
            var stop = cuts[ordinal + 1]
            assert_equal(start, 9 * i + 3)
            assert_equal(stop, 9 * i + 6)
            var u: List[Int] = [top[start], top[start + 1], top[start + 2]]
            var v: List[Int] = [bottom[start], bottom[start + 1], bottom[start + 2]]
            assert_equal(normalise(Pair(u, v)), system.states[factors[ordinal].state_id])
            var top_next = apply_substitution(sigma, u)
            var bottom_next = apply_substitution(sigma, v)
            var next_cuts = coincidence_boundaries(top_next, bottom_next)
            assert_equal(next_cuts, [0, 3, 6, 9])
            var seen: List[Bool] = [False, False, False]
            for child in range(3):
                var k = next_cuts[child]
                var child_top: List[Int] = [top_next[k], top_next[k + 1], top_next[k + 2]]
                var child_bottom: List[Int] = [bottom_next[k], bottom_next[k + 1], bottom_next[k + 2]]
                var target = normalise(Pair(child_top, child_bottom))
                assert_equal(parikh(child_top), parikh(child_bottom))
                for j in range(system.size()):
                    if target == system.states[j]:
                        seen[j] = True
                for letter in range(3):
                    # Both physical tracks have these same ancestor index
                    # bounds because every image has length three.
                    var pos = 3 * start + k + letter
                    assert_equal(pos // 27, i)
                    assert_true(child_top[letter] != child_bottom[letter])
                    routes += 1
            assert_equal(seen, [True, True, True])
    assert_equal(routes, 81)


def test_phase_zero_prefix_can_force_a_terminal_reversal() raises:
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var root = Pair([1, 0], [0, 1])
    var suffix = suffix_endpoint_map(sigma)
    assert_equal(endpoint_type_name(endpoint_type(suffix)), "F")
    var terminal: List[List[Int]] = [[0, 1], [1, 2], [2, 1]]
    for depth in range(2):
        var row = decompose(apply_substitution(sigma, root.u), apply_substitution(sigma, root.v))
        assert_equal(len(row), depth + 1)
        for j in range(len(row)):
            assert_equal(row[j].u[0], 1)
            assert_true(row[j].v[0] != 1)
        root = row[len(row) - 1].copy()
        var end = root.length() - 1
        var actual: List[Int] = [root.u[end], root.v[end]]
        var predicted: List[Int] = [suffix[terminal[depth][0]], suffix[terminal[depth][1]]]
        assert_equal(actual, terminal[depth + 1])
        assert_equal(predicted, actual)
    assert_equal(root, Pair([1, 2], [2, 1]))


def test_suffix_transposition_alone_is_insufficient() raises:
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var states: List[Pair] = [
        Pair([1, 0, 2], [2, 1, 0]),
        Pair([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]),
        Pair([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1],
             [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]),
    ]
    var system = build_derived_system(sigma, states)
    var suffix = suffix_endpoint_map(sigma)
    assert_equal(suffix, [0, 2, 1])
    assert_equal(endpoint_type_name(endpoint_type(suffix)), "E")
    var terminals: List[Int] = [2, 2, 1, 1]
    for j in range(system.size()):
        var parent = system.states[j].copy()
        assert_equal([parent.u[0], parent.v[0]], [1, 2])
        assert_equal([parent.u[parent.length() - 1], parent.v[parent.length() - 1]],
                     [terminals[j], 0])
        var row = oriented_derived_word(system, j, 1)
        for k in range(len(row)):
            assert_equal(row[k].sign, 1)

def main() raises:
    test_each_source_routes_to_all_targets()
    test_phase_zero_prefix_can_force_a_terminal_reversal()
    test_suffix_transposition_alone_is_insufficient()
    print("C4 whole-factor enclosure: 9 literal sources reach all 9 represented target occurrences.")
    require_contract("literal phase-zero terminal reversal and strict nonreversing suffix-transposition control")
    require_contract("an actual inflated overlap contains a whole balanced factor and routes to every represented target in the strict uniform control")
