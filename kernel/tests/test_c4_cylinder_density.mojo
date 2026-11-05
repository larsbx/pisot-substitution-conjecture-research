"""Literal density controls; the accepted uniform example is NON-PISOT.

No synthetic graph or productive Pisot substitution is called a strict
counterexample. No measure-theoretic theorem is machine verified here.
"""

from std.testing import assert_equal, assert_true, assert_false
from finite_exact.rat_q import Q
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, decompose
from psc.c4_cylinder_density import (
    all_column_pair_cover, all_column_target_cover, density_chart_name,
    literal_strict_cut_system, named_density_beta_upper,
    named_density_length_upper, uniform_strict_cut_density,
    verify_named_chart_density,
)
from psc.words import Pair


def rotation() -> List[List[Int]]:
    return [[0, 1, 2], [1, 2, 0], [2, 0, 1]]


def rotation_states() -> List[Pair]:
    return [Pair([0, 1, 2], [1, 2, 0]),
            Pair([1, 2, 0], [2, 0, 1]),
            Pair([2, 0, 1], [0, 1, 2])]


def rejects_system(sigma: List[List[Int]], states: List[Pair]) -> Bool:
    try:
        _ = literal_strict_cut_system(sigma, states)
        return False
    except:
        return True


def rejects_cover(images: List[List[Int]], target: List[Bool], depth: Int) -> Bool:
    try:
        _ = all_column_target_cover(images, target, depth)
        return False
    except:
        return True


def rejects_named(
    sigma: List[List[Int]], states: List[Pair], beta_hi: Q,
    lower: Q, normalization: String,
) -> Bool:
    try:
        _ = verify_named_chart_density(sigma, states, 0, 1, 1, beta_hi, lower, normalization)
        return False
    except:
        return True


def test_complete_nonpisot_uniform_control() raises:
    var sigma = rotation()
    var states = rotation_states()
    var system = literal_strict_cut_system(sigma, states)
    assert_equal(system.size(), 3)
    for parent in range(3):
        assert_equal(len(system.images[parent]), 3)
        var counts: List[Int] = [0, 0, 0]
        for occurrence in range(len(system.images[parent])):
            counts[system.images[parent][occurrence]] += 1
        assert_equal(counts, [1, 1, 1])
    for left in range(2):
        for right in range(left + 1, 3):
            all_column_pair_cover(system, left, right, 1)
            var lower = uniform_strict_cut_density(sigma, states, left, right, 1)
            assert_true(lower.eq(Q(1, 9)))

    # Independently count actual complete factors, rather than replaying the
    # Boolean recurrence. Each represented pair has physical density 1/9.
    for root in range(3):
        var top = states[root].u.copy()
        var bottom = states[root].v.copy()
        for _ in range(4):
            top = apply_substitution(sigma, top)
            bottom = apply_substitution(sigma, bottom)
            var factors = decompose(top, bottom)
            var counts: List[Int] = [0, 0, 0]
            for occurrence in range(len(factors)):
                var a = factors[occurrence].u[0]
                var b = factors[occurrence].v[0]
                if (a == 0 and b == 1) or (a == 1 and b == 0):
                    counts[0] += 1
                elif (a == 0 and b == 2) or (a == 2 and b == 0):
                    counts[1] += 1
                elif (a == 1 and b == 2) or (a == 2 and b == 1):
                    counts[2] += 1
                else:
                    raise Error("coincidence or omitted literal factor")
            for pair_id in range(3):
                assert_equal(9 * counts[pair_id], len(top))


def test_missing_occurrences_and_false_strictness() raises:
    var sigma = rotation()
    var complete = rotation_states()
    var selected = List[Pair]()
    selected.append(complete[0].copy())
    assert_true(rejects_system(sigma, selected))
    selected.append(complete[1].copy())
    assert_true(rejects_system(sigma, selected))
    var duplicate = complete.copy()
    duplicate.append(Pair(complete[0].v, complete[0].u))
    assert_true(rejects_system(sigma, duplicate))
    assert_true(rejects_system(sigma, [Pair([0], [0])]))
    assert_true(rejects_system(sigma, [Pair([0, 1], [1, 2])]))
    assert_true(rejects_system(sigma, [Pair([0, 1, 0, 1], [1, 0, 1, 0])]))
    assert_true(rejects_system([[0, 1], [0, 1], [2]], [Pair([0, 1], [1, 0])]))
    var empty = List[Pair]()
    assert_true(rejects_system(sigma, empty))
    assert_true(rejects_system(sigma, [Pair(List[Int](), List[Int]())]))
    assert_true(rejects_system(sigma, [Pair([0, 1], [1])]))
    assert_true(rejects_system(sigma, [Pair([0, 3], [3, 0])]))
    assert_true(rejects_system(sigma, [Pair([0, -1], [-1, 0])]))
    assert_true(rejects_system([[0], [1]], complete))
    assert_true(rejects_system([[0], List[Int](), [2]], complete))
    assert_true(rejects_system([[0, 3], [1], [2]], complete))
    var long_word = List[Int]()
    for _ in range(257):
        long_word.append(0)
    assert_true(rejects_system(sigma, [Pair(long_word, long_word)]))
    var many = List[Pair]()
    for _ in range(129):
        many.append(complete[0].copy())
    assert_true(rejects_system(sigma, many))


def test_exact_common_depth_and_caps() raises:
    # Synthetic imprimitive graph only: never a Pisot or word-system premise.
    var cycle: List[List[Int]] = [[1, 1], [0, 0]]
    for depth in range(33):
        assert_false(all_column_target_cover(cycle, [True, False], depth))
    assert_true(all_column_target_cover(cycle, [True, True], 0))
    assert_true(all_column_target_cover([[0, 1], [0, 1]], [True, False], 1))
    assert_false(all_column_target_cover([[0], [1]], [True, False], 32))
    assert_true(rejects_cover(cycle, [True, False], -1))
    assert_true(rejects_cover(cycle, [True, False], 33))
    assert_true(rejects_cover(cycle, [True], 1))
    assert_true(rejects_cover([[2], [0]], [True, False], 1))
    assert_true(rejects_cover([[-1], [0]], [True, False], 1))
    assert_true(rejects_cover([List[Int](), [0]], [True, False], 1))
    var system = literal_strict_cut_system(rotation(), rotation_states())
    var refused = False
    try:
        all_column_pair_cover(system, 0, 1, 0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        all_column_pair_cover(system, 1, 0, 1)
    except:
        refused = True
    assert_true(refused)


def test_named_chart_cannot_bless_a_false_component() raises:
    assert_true(named_density_beta_upper(Q(5, 2)).eq(Q(5, 2)))
    assert_true(named_density_beta_upper(Q(113477, 50000)).eq(Q(113477, 50000)))
    # This asserts only a physical-length bound, not closure of these words.
    assert_true(named_density_length_upper(rotation_states(), Q(5, 2)).eq(Q(25, 4)))
    for mode in range(5):
        var refused = False
        var beta_hi = Q(2, 1)
        if mode == 1:
            beta_hi = Q(9, 4)
        elif mode == 2:
            beta_hi = Q(3, 1)
        elif mode == 3:
            beta_hi = Q(0, 0)
        elif mode == 4:
            beta_hi = Q(226953, 100000)
        try:
            _ = named_density_beta_upper(beta_hi)
        except:
            refused = True
        assert_true(refused)
    var fake: List[Pair] = [Pair([0, 1], [1, 0])]
    for fixture in range(2):
        var sigma: List[List[Int]] = [[1], [0, 2, 1], [0, 0, 1]]
        if fixture == 1:
            sigma[1] = [0, 1, 2]
        assert_true(rejects_named(sigma, fake, Q(5, 2), Q(1, 100), density_chart_name()))
        assert_true(rejects_named(sigma, fake, Q(5, 2), Q(1, 100), String("unit-covolume")))
        assert_true(rejects_named(sigma, fake, Q(9, 4), Q(1, 100), density_chart_name()))
        assert_true(rejects_named(sigma, fake, Q(5, 2), Q(3, 4), density_chart_name()))
        assert_true(rejects_named(sigma, fake, Q(5, 2), Q(0, 1), density_chart_name()))
        assert_true(rejects_named(sigma, fake, Q(5, 2), Q(-1, 100), density_chart_name()))
        assert_true(rejects_named(sigma, fake, Q(5, 2), Q(1, 0), density_chart_name()))
    # A valid strict uniform system remains unsupported by the named geometry.
    assert_true(rejects_named(rotation(), rotation_states(), Q(5, 2), Q(1, 9), density_chart_name()))


def main() raises:
    test_complete_nonpisot_uniform_control()
    test_missing_occurrences_and_false_strictness()
    test_exact_common_depth_and_caps()
    test_named_chart_cannot_bless_a_false_component()
    print("C4_CYLINDER_DENSITY_PASS")
    require_contract("bounded complete literal strict child closure, exact all-column pair coverage, non-Pisot uniform density 1/9, authenticated named-chart growth and physical lengths; missing children, false components, phase confusion and unsupported normalization refuse; no machine measure proof or general C4 conclusion")
