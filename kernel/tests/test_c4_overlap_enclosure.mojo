"""Exact uniform-width control for occurrence-level whole-factor enclosure."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries, decompose, normalise, suffix_endpoint_map
from psc.derived_system import build_derived_system, oriented_derived_word
from psc.c4_legal_seams import legal_bigrams, phase_zero_legal_seams
from psc.endpoint_core import endpoint_type, endpoint_type_name
from psc.words import Pair, parikh
from psc.symmetry import reversed_substitution, reversed_word


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



def _assert_reversed_rows(sigma: List[List[Int]], states: List[Pair],
                          hub: Int, top_has_hub: Bool) raises:
    var reversed = reversed_substitution(sigma)
    for j in range(len(states)):
        var parent = states[j].copy()
        var original = decompose(apply_substitution(sigma, parent.u),
                                 apply_substitution(sigma, parent.v))
        var r = Pair(reversed_word(parent.u), reversed_word(parent.v))
        var row = decompose(apply_substitution(reversed, r.u), apply_substitution(reversed, r.v))
        assert_equal(len(row), len(original))
        for k in range(len(row)):
            var child = original[len(row) - 1 - k].copy()
            assert_equal(row[k], Pair(reversed_word(child.u), reversed_word(child.v)))
            assert_equal(row[k].u[0] == hub, top_has_hub)
            assert_equal(row[k].v[0] == hub, not top_has_hub)


def test_type_c_right_hub_transfers_to_reversal() raises:
    var sigma: List[List[Int]] = [[0, 2, 0], [2, 0], [1, 2]]
    var states: List[Pair] = [
        Pair([0, 1, 2], [1, 2, 0]), Pair([0, 2], [2, 0]),
        Pair([0, 2, 0, 1, 2], [1, 2, 0, 2, 0]),
    ]
    assert_equal(endpoint_type_name(endpoint_type(suffix_endpoint_map(sigma))), "C")
    var system = build_derived_system(sigma, states)
    var expected: List[List[Int]] = [[1, 2], [2], [1, 0, 1, 2]]
    for j in range(system.size()):
        assert_equal(system.images[j], expected[j])
        var parent = system.states[j].copy()
        assert_equal(parent.u[0], 0)
        assert_true(parent.v[0] != 0)
        assert_equal(parent.u[parent.length() - 1], 2)
        assert_equal(parent.v[parent.length() - 1], 0)
        for k in range(len(system.child_signs[j])):
            assert_equal(system.child_signs[j][k], 1)
    _assert_reversed_rows(sigma, states, 2, True)


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
    _assert_reversed_rows(sigma, states, 0, False)

def test_type_d_good_edge_forces_mirrored_descendants() raises:
    var reversed: List[List[Int]] = [[0, 2, 1], [1, 0, 2], [2, 0, 1]]
    var sigma = reversed_substitution(reversed)
    assert_equal(endpoint_type_name(endpoint_type(suffix_endpoint_map(sigma))), "D")
    var h: List[Int] = [1]
    var a: List[Int] = [0]
    var b: List[Int] = [2]
    var hub = apply_substitution(reversed, h)
    var left = apply_substitution(reversed, a)
    var right = apply_substitution(reversed, b)
    var hub_prefix: List[Int] = [hub[0], hub[1]]
    var left_prefix: List[Int] = [left[0], left[1]]
    var right_prefix: List[Int] = [right[0], right[1]]
    var ph = parikh(hub_prefix)
    var pa = parikh(left_prefix)
    var pb = parikh(right_prefix)
    assert_equal(pa, pb)
    assert_equal(left[2], right[2])
    assert_equal([hub[2], left[2]], [2, 1])
    assert_equal([right[2], hub[2]], [1, 2])
    assert_equal([pa[0] - ph[0], pa[1] - ph[1], pa[2] - ph[2]], [0, -1, 1])
    assert_equal([ph[0] - pb[0], ph[1] - pb[1], ph[2] - pb[2]], [0, 1, -1])
    # Unit tile widths put both marked tiles at the common position 2.
    assert_equal(len(hub), 3)


def _check_good_edge(sigma: List[List[Int]], a: Int, b: Int, depth: Int, pos: Int) raises:
    var top: List[Int] = [a]
    var bottom: List[Int] = [b]
    for _ in range(depth):
        top = apply_substitution(sigma, top)
        bottom = apply_substitution(sigma, bottom)
    assert_equal(top[pos], bottom[pos])
    var p = List[Int]()
    var q = List[Int]()
    for j in range(pos):
        p.append(top[j])
        q.append(bottom[j])
    assert_equal(parikh(p), parikh(q))


def test_paired_legal_seams_force_opposite_track_choices() raises:
    var a: List[List[Int]] = [[0, 1], [2, 0], [1, 0, 2]]
    var b: List[List[Int]] = [[0, 1], [2, 1], [1, 0, 2]]
    _check_good_edge(a, 1, 2, 2, 4)
    _check_good_edge(reversed_substitution(a), 0, 1, 2, 3)
    _check_good_edge(b, 1, 2, 4, 27)
    _check_good_edge(reversed_substitution(b), 0, 1, 1, 0)
    assert_equal(legal_bigrams(a), [True, True, True, True, True, True, True, False, False])
    assert_equal(legal_bigrams(b), [False, True, True, True, True, True, False, True, True])
    assert_equal(phase_zero_legal_seams(a, 0, 2, True), [55, 56, 64, 65])
    assert_equal(len(phase_zero_legal_seams(a, 0, 2, False)), 0)
    assert_equal(len(phase_zero_legal_seams(b, 0, 2, True)), 0)
    assert_equal(phase_zero_legal_seams(b, 0, 2, False), [46, 47])


def test_strict_control_literal_seams_survive_filter() raises:
    var sigma: List[List[Int]] = [[0, 2, 0], [2, 0], [1, 2]]
    var states: List[Pair] = [
        Pair([0, 1, 2], [1, 2, 0]), Pair([0, 2], [2, 0]),
        Pair([0, 2, 0, 1, 2], [1, 2, 0, 2, 0]),
    ]
    var possible = phase_zero_legal_seams(sigma, 0, 2, True)
    var count = 0
    for j in range(len(states)):
        var row = decompose(apply_substitution(sigma, states[j].u),
                            apply_substitution(sigma, states[j].v))
        for k in range(len(row) - 1):
            var end = row[k].length() - 1
            var terminal = 3 * row[k].u[end] + row[k].v[end]
            var initial = 3 * row[k + 1].u[0] + row[k + 1].v[0]
            assert_true(9 * terminal + initial in possible)
            count += 1
    assert_equal(count, 4)


def main() raises:
    test_each_source_routes_to_all_targets()
    test_paired_legal_seams_force_opposite_track_choices()
    test_strict_control_literal_seams_survive_filter()
    test_phase_zero_prefix_can_force_a_terminal_reversal()
    test_suffix_transposition_alone_is_insufficient()
    test_type_c_right_hub_transfers_to_reversal()
    test_type_d_good_edge_forces_mirrored_descendants()
    print("C4 whole-factor enclosure: 9 literal sources reach all 9 represented target occurrences.")
    require_contract("exact legal bigrams reject incompatible bilateral hub tracks and retain actual strict seams")
    require_contract("type D witnessed good edge produces swapped ordered overlap labels")
    require_contract("type C and E strict controls preserve every ordered child under right-hub reversal")
    require_contract("literal phase-zero terminal reversal and strict nonreversing suffix-transposition control")
    require_contract("an actual inflated overlap contains a whole balanced factor and routes to every represented target in the strict uniform control")
