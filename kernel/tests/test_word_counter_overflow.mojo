"""Native overflow controls for the vendored counters and PSC consumers."""

from std.testing import assert_equal, assert_true
from finite_exact.checked_int import checked_add
from mojo_smoke.claims import require_contract
from psc.defect_degree import first_defect_degree, is_degree3, n4
from psc.words import Pair, k3, n2, n3
from substitution_dynamics import words as sd


def test_dimensions() raises:
    var empty = List[Int]()
    var square_refused = False
    try:
        _ = sd.n2(empty, Int.MAX)
    except e:
        square_refused = True
        assert_equal(String(e), "checked integer multiplication overflow")
    assert_true(square_refused)

    # The square fits, but the cube does not. Refusal precedes allocation.
    var cube_refused = False
    try:
        _ = sd.n3(empty, 3000000)
    except e:
        cube_refused = True
        assert_equal(String(e), "checked integer multiplication overflow")
    assert_true(cube_refused)


def test_prefix_addition_boundary() raises:
    # Inject a saturated prefix accumulator into the same primitive used by
    # N2/N3, without allocating a multi-billion-letter word.
    assert_equal(checked_add(Int.MAX - 1, 1), Int.MAX)
    var refused = False
    try:
        _ = checked_add(Int.MAX, 1)
    except e:
        refused = True
        assert_equal(String(e), "checked integer addition overflow")
    assert_true(refused)


def test_triple_boundary() raises:
    # Exact C(n, 3) from the independent binomial formula.
    var word = List[Int](length=3810779, fill=0)
    assert_equal(n3(word)[0], 9223371416043870029)
    word.append(0)
    var refused = False
    try:
        _ = n3(word)
    except e:
        refused = True
        assert_equal(String(e), "checked integer addition overflow")
    assert_true(refused)


def test_documented_case_and_propagation() raises:
    var word = List[Int](length=4000000, fill=0)
    assert_equal(n2(word)[0], 7999998000000)
    # A zero mathematical difference still needs two representable counts.
    var pair = Pair(word, word)
    for consumer in range(4):
        var refused = False
        try:
            if consumer == 0:
                _ = n3(word)
            elif consumer == 1:
                _ = k3(pair)
            elif consumer == 2:
                _ = is_degree3(pair)
            else:
                _ = first_defect_degree(pair)
        except e:
            refused = True
            assert_equal(String(e), "checked integer addition overflow")
        assert_true(refused)


def test_degree_four_refusal() raises:
    # Here N2/N3 fit, but C(200000, 4) exceeds Int.MAX.
    var word = List[Int](length=200000, fill=0)
    var refused = False
    try:
        _ = first_defect_degree(Pair(word, word))
    except e:
        refused = True
        assert_equal(String(e), "checked integer addition overflow")
    assert_true(refused)


def test_short_words_against_position_masks() raises:
    # Every ternary word through length six and every position subset.
    var word_count = 1
    for length in range(7):
        for word_code in range(word_count):
            var code = word_code
            var word = List[Int]()
            for _ in range(length):
                word.append(code % 3)
                code //= 3
            var pairs = List[Int](length=9, fill=0)
            var triples = List[Int](length=27, fill=0)
            var quadruples = List[Int](length=81, fill=0)
            for mask in range(1 << length):
                var slot = 0
                var degree = 0
                for i in range(length):
                    if (mask & (1 << i)) != 0:
                        slot = 3 * slot + word[i]
                        degree += 1
                if degree == 2:
                    pairs[slot] += 1
                elif degree == 3:
                    triples[slot] += 1
                elif degree == 4:
                    quadruples[slot] += 1
            assert_equal(n2(word), pairs)
            assert_equal(n3(word), triples)
            assert_equal(n4(word), quadruples)
        word_count *= 3


def main() raises:
    test_short_words_against_position_masks()
    test_dimensions()
    test_prefix_addition_boundary()
    test_triple_boundary()
    test_documented_case_and_propagation()
    test_degree_four_refusal()
    require_contract("scattered-subword counters refuse overflow through PSC consumers")
