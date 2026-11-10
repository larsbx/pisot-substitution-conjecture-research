"""Literal complete child rows and cyclic PF frequency controls for C4.

The strict rotation fixture is NON-PISOT; cyclic N is synthetic.
No Rauzy-measure or general C4 claim is checked by this executable.
"""
from std.testing import assert_equal
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, decompose


def test_actual_strict_rotation_counts_every_pair() raises:
    var sigma: List[List[Int]] = [
        [0, 1, 2],
        [1, 2, 0],
        [2, 0, 1],
    ]
    for root in range(3):
        var top = sigma[root].copy()
        var bottom = sigma[(root + 1) % 3].copy()
        var expected_each = 1
        for level in range(1, 6):
            top = apply_substitution(sigma, top)
            bottom = apply_substitution(sigma, bottom)
            var factors = decompose(top, bottom)
            var counts: List[Int] = [0, 0, 0]
            for k in range(len(factors)):
                var i = -1
                if factors[k].u == [0, 1, 2] and factors[k].v == [1, 2, 0]:
                    i = 0
                elif factors[k].u == [1, 2, 0] and factors[k].v == [2, 0, 1]:
                    i = 1
                elif factors[k].u == [2, 0, 1] and factors[k].v == [0, 1, 2]:
                    i = 2
                if i < 0:
                    raise Error("omitted or diagonal factor in strict control")
                counts[i] += 1
            assert_equal(counts, [expected_each, expected_each, expected_each])
            assert_equal(len(factors), 3 * expected_each)
            assert_equal(len(top), 9 * expected_each)
            assert_equal(len(bottom), 9 * expected_each)
            expected_each *= 3


def test_imprimitive_period_two_is_subsequence_only() raises:
    # N=[[0,2],[2,0]], beta=2, period h=2:
    # type 0 density alternates between 1 and zero.
    var count0 = 1
    var count1 = 0
    var power = 1
    for n in range(12):
        assert_equal(count0 + count1, power)
        if n % 2 == 0:
            assert_equal(count0, power)
            assert_equal(count1, 0)
        else:
            assert_equal(count0, 0)
            assert_equal(count1, power)
        var next0 = 2 * count1
        var next1 = 2 * count0
        count0 = next0
        count1 = next1
        power *= 2


def test_selected_recurrent_path_is_not_full_child_closure() raises:
    var sigma: List[List[Int]] = [
        [0, 1, 2],
        [1, 2, 0],
        [2, 0, 1],
    ]
    var factors = decompose(
        apply_substitution(sigma, [0, 1, 2]),
        apply_substitution(sigma, [1, 2, 0]),
    )
    assert_equal(len(factors), 3)
    var exits = 0
    for k in range(len(factors)):
        if factors[k].u != [0, 1, 2] or factors[k].v != [1, 2, 0]:
            exits += 1
    assert_equal(exits, 2)


def main() raises:
    test_actual_strict_rotation_counts_every_pair()
    test_imprimitive_period_two_is_subsequence_only()
    test_selected_recurrent_path_is_not_full_child_closure()
    print("C4 pairwise cut frequency exact controls passed.")
    require_contract("Complete cut counts, cyclic subsequences, and strict closure on finite controls")
