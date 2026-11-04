"""Exact uniform-width control for occurrence-level whole-factor enclosure."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries, normalise
from psc.derived_system import build_derived_system, oriented_derived_word
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


def main() raises:
    test_each_source_routes_to_all_targets()
    print("C4 whole-factor enclosure: 9 literal sources reach all 9 represented target occurrences.")
    require_contract("an actual inflated overlap contains a whole balanced factor and routes to every represented target in the strict uniform control")
