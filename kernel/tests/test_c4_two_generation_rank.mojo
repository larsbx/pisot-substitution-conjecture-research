"""Uniform C4 two-generation Parikh-rank interface, with bounded literal tests.

The logical proof uses irreducible characteristic polynomial; this test checks
actual ordered word occurrences and negative input/lower-rank controls only.
"""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_two_generation_rank import literal_two_generation_parikh_rank
from psc.words import Pair


def test_real_secondary_is_sharp_at_second_generation() raises:
    # Real-secondary PIP: no newborn at depth one for swap (01,10).
    # First genuine full-rank descendant triple appears only at depth two.
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var root = Pair([0, 1], [1, 0])
    var a = literal_two_generation_parikh_rank(sigma, root)
    assert_equal(a.rank, 3)
    assert_equal(len(a.occurrences), 6)
    assert_equal(a.independent_ids, [0, 1, 4])
    assert_equal(a.occurrences[0].depth, 0)
    assert_equal(a.occurrences[1].depth, 1)
    assert_equal(a.occurrences[1].first_ordinal, 0)
    assert_equal(a.occurrences[4].depth, 2)
    assert_equal(a.occurrences[4].first_ordinal, 0)
    assert_equal(a.occurrences[4].second_ordinal, 2)
    assert_equal(a.occurrences[0].counts, [1, 1, 0])
    assert_equal(a.occurrences[1].counts, [1, 1, 1])
    assert_equal(a.occurrences[4].counts, [1, 0, 0])
    # No independent triple is available in depths zero and one.
    assert_equal(len(a.occurrences[0].counts), 3)
    assert_equal(a.occurrences[2].depth, 2)


def test_tribonacci_can_be_full_rank_earlier() raises:
    var sigma: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var a = literal_two_generation_parikh_rank(sigma, Pair([0, 1], [1, 0]))
    assert_equal(a.rank, 3)
    assert_equal(a.independent_ids, [0, 1, 2])
    assert_equal(a.occurrences[0].counts, [1, 1, 0])
    assert_equal(a.occurrences[1].counts, [1, 0, 0])
    assert_equal(a.occurrences[2].counts, [1, 1, 1])


def test_fullrank_primitive_but_reducible_strict_control_stays_rank_two() raises:
    # Non-PIP four-state strict SCC: M is full rank, but its reducible
    # cubic preserves the proper plane p0=p2.
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var a = literal_two_generation_parikh_rank(
        sigma, Pair([1, 0, 2], [2, 1, 0])
    )
    assert_equal(a.rank, 2)
    assert_equal(len(a.occurrences), 7)
    assert_equal(a.independent_ids, [0, 1])
    for i in range(len(a.occurrences)):
        assert_equal(a.occurrences[i].counts[0], a.occurrences[i].counts[2])


def test_caps_and_unbalanced_inputs_fail_closed() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var rejected = False
    try:
        _ = literal_two_generation_parikh_rank(
            sigma, Pair([0, 1], [1, 0]), node_cap=5
        )
    except:
        rejected = True
    assert_true(rejected)
    rejected = False
    try:
        _ = literal_two_generation_parikh_rank(
            sigma, Pair([0, 1], [0, 0])
        )
    except:
        rejected = True
    assert_true(rejected)
    rejected = False
    try:
        _ = literal_two_generation_parikh_rank(
            sigma, Pair([0, 1], [1, 0]), node_cap=0
        )
    except:
        rejected = True
    assert_true(rejected)


def test_repeated_diagonal_parents_and_exact_cap() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var seed = Pair([0, 0], [0, 0])
    var result = literal_two_generation_parikh_rank(sigma, seed, node_cap=7)
    assert_equal(len(result.occurrences), 7)
    assert_equal(result.independent_ids, [0, 1, 4])
    for i in range(2):
        assert_equal(result.occurrences[i + 1].first_ordinal, i)
        assert_equal(result.occurrences[i + 1].counts, [0, 1, 0])
        for j in range(2):
            var index = 3 + 2 * i + j
            assert_equal(result.occurrences[index].depth, 2)
            assert_equal(result.occurrences[index].first_ordinal, i)
            assert_equal(result.occurrences[index].second_ordinal, j)
        assert_equal(result.occurrences[3 + 2 * i].counts, [1, 0, 0])
        assert_equal(result.occurrences[4 + 2 * i].counts, [0, 0, 1])
    var rejected = False
    try:
        _ = literal_two_generation_parikh_rank(sigma, seed, node_cap=6)
    except:
        rejected = True
    assert_true(rejected)


def test_invalid_root_digits_are_rejected_before_counting() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    for digit in [-1, 3]:
        var rejected = False
        try:
            _ = literal_two_generation_parikh_rank(sigma, Pair([digit], [0]))
        except:
            rejected = True
        assert_true(rejected)
        rejected = False
        try:
            _ = literal_two_generation_parikh_rank(sigma, Pair([0], [digit]))
        except:
            rejected = True
        assert_true(rejected)


def main() raises:
    test_real_secondary_is_sharp_at_second_generation()
    test_tribonacci_can_be_full_rank_earlier()
    test_fullrank_primitive_but_reducible_strict_control_stays_rank_two()
    test_caps_and_unbalanced_inputs_fail_closed()
    test_repeated_diagonal_parents_and_exact_cap()
    test_invalid_root_digits_are_rejected_before_counting()
    print("C4 two-generation literal Parikh rank controls passed.")
    require_contract("irreducible ternary PIP has a literal rank-three Parikh triple within two complete generations; real-secondary depth-two sharpness, productive Tribonacci early rank, reducible strict rank-two, and cap/refusal negative controls")
