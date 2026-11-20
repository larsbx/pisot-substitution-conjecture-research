"""Literal controls for normalized and ordered strict-component periods."""

from std.testing import assert_equal, assert_true
from finite_graph.scc import sccs
from finite_graph.signing import SignedEdge, directed_period
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries
from psc.derived_system import DerivedSystem, build_derived_system
from psc.endpoint_core import TYPE_E, endpoint_type, prefix_endpoint_map
from psc.hub_selector import strict_star_pair_viable
from psc.words import Pair, parikh


def power(sigma: List[List[Int]], word: List[Int], depth: Int) -> List[Int]:
    var result = word.copy()
    for _ in range(depth):
        result = apply_substitution(sigma, result)
    return result^


def interval(word: List[Int], start: Int, stop: Int) -> List[Int]:
    var result = List[Int]()
    for i in range(start, stop):
        result.append(word[i])
    return result^


def periods(system: DerivedSystem, ordered: Bool) raises -> List[Int]:
    var copies = 2 if ordered else 1
    var adj = List[List[Int]]()
    for parent in range(system.size()):
        for side in range(copies):
            var row = List[Int]()
            for i in range(len(system.images[parent])):
                var target = system.images[parent][i] * copies
                if ordered:
                    target += side ^ (1 if system.child_signs[parent][i] < 0 else 0)
                row.append(target)
            adj.append(row^)
    var result = List[Int]()
    var components = sccs(adj)
    for k in range(len(components)):
        ref component = components[k]
        var index = Dict[Int, Int]()
        for j in range(len(component)):
            index[component[j]] = j
        var edges = List[SignedEdge]()
        for j in range(len(component)):
            for i in range(len(adj[component[j]])):
                var target = adj[component[j]][i]
                assert_true(target in index)
                edges.append(SignedEdge(j, index[target], 0))
        result.append(directed_period(len(component), edges))
    return result^


def shared_factor(
    sigma: List[List[Int]], state: Pair, left: Int, right: Int,
) raises -> Pair:
    var upper = power(sigma, state.u, 7)
    var lower = power(sigma, state.v, 7)
    var cuts = coincidence_boundaries(upper, lower)
    for k in range(len(cuts) - 1):
        if cuts[k] == left and cuts[k + 1] == right:
            return Pair(interval(upper, left, right), interval(lower, left, right))
    raise Error("expected an entire consecutive-cut block inside the shared interval")


def test_cross_pair_period_collapse() raises:
    var sigma: List[List[Int]] = [[0, 1], [2, 0, 1], [1, 1, 2]]
    var states: List[Pair] = [
        Pair([0, 1, 2], [2, 0, 1]),
        Pair([0, 1, 1, 1, 2], [2, 0, 1, 1, 1]),
        Pair([0, 1, 2, 0, 1, 1, 1, 2], [1, 1, 2, 0, 1, 2, 0, 1]),
        Pair([0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 1, 1, 2],
             [1, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1]),
    ]
    var system = build_derived_system(sigma, states)
    assert_equal(prefix_endpoint_map(sigma), [0, 2, 1])
    assert_equal([states[0].u[0], states[0].v[0]], [0, 2])
    assert_equal([states[2].u[0], states[2].v[0]], [0, 1])
    assert_equal(system.images[0], [2])
    assert_equal(system.images[2][0], 0)
    assert_equal(periods(system, False), [1])
    assert_equal(periods(system, True), [1, 1])

    var a = power(sigma, [1], 4)
    var b = power(sigma, [2], 4)
    assert_equal(a[7], 1)
    assert_equal(b[7], 1)
    var a_prefix = interval(a, 0, 7)
    var b_prefix = interval(b, 0, 7)
    assert_equal(parikh(a_prefix), parikh(b_prefix))
    var left = len(power(sigma, a_prefix, 3))
    var right = left + len(power(sigma, [1], 3))
    assert_equal(left, 142)
    assert_equal(right, 164)
    assert_true(len(power(sigma, [0], 7)) > right)
    assert_true(left < 145 and 150 < right)
    assert_equal(shared_factor(sigma, states[0], 145, 150), states[1])
    assert_equal(shared_factor(sigma, states[2], 145, 150), states[1])


def test_ordered_period_two_survives_normalization() raises:
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var states: List[Pair] = [Pair([0, 1], [1, 0]), Pair([1, 2], [2, 1])]
    var system = build_derived_system(sigma, states)
    assert_equal(periods(system, False), [1])
    assert_equal(periods(system, True), [2])
    for i in range(system.size()):
        for j in range(len(system.images[i])):
            var child = system.states[system.images[i][j]].copy()
            var top = child.u.copy() if system.child_signs[i][j] > 0 else child.v.copy()
            var bottom = child.v.copy() if system.child_signs[i][j] > 0 else child.u.copy()
            # Hub 1 flips at each end, whichever physical track started there.
            assert_equal(top[0] == 1, system.states[i].u[0] != 1)
            assert_equal(bottom[0] == 1, system.states[i].v[0] != 1)
            assert_equal(top[len(top) - 1] == 1, system.states[i].u[1] != 1)
            assert_equal(bottom[len(bottom) - 1] == 1, system.states[i].v[1] != 1)


def test_exhaustive_endpoint_period_reduction() raises:
    var fixed = 0
    var swapped = 0
    var cross = 0
    for i in range(27):
        var g: List[Int] = [i // 9, (i // 3) % 3, i % 3]
        for h in range(3):
            var good = List[Int]()
            for a in range(3):
                if a != h:
                    good.append(a)
            for a in range(2):
                for b in range(a + 1, 3):
                    if not strict_star_pair_viable(g, good[0], good[1], a, b):
                        continue
                    var x = a
                    var y = b
                    for n in range(1, 7):
                        x = g[x]
                        y = g[y]
                        if x == a and y == b:
                            if n == 1:
                                fixed += 1
                            else:
                                assert_equal(n, 2)
                                assert_equal(endpoint_type(g), TYPE_E)
                                assert_equal(g[h], h)
                                assert_equal(g[good[0]], good[1])
                                cross += 1
                            break
                        if x == b and y == a:
                            assert_equal(n, 1)
                            swapped += 1
                            break
    assert_equal([fixed, swapped, cross], [18, 18, 6])


def main() raises:
    test_exhaustive_endpoint_period_reduction()
    test_cross_pair_period_collapse()
    test_ordered_period_two_survives_normalization()
    require_contract("literal strict-component period collapses for the shared type-E overlap and survives as ordered period two under both hub flips")
