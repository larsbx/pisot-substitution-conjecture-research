"""Literal witness and residue controls for two-sided phase-one seams."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries
from psc.c4_legal_seams import legal_bigrams, phase_one_birth_seams, strict_birth_seams
from psc.derived_system import build_derived_system
from psc.symmetry import reversed_substitution
from psc.words import Pair, parikh


def inflate(sigma: List[List[Int]], a: Int, depth: Int) -> List[Int]:
    var word: List[Int] = [a]
    for _ in range(depth):
        word = apply_substitution(sigma, word)
    return word^


def check_witness(sigma: List[List[Int]], a: Int, b: Int, depth: Int,
                  cut: Int, expected: List[Int], letter: Int) raises:
    var top = inflate(sigma, a, depth)
    var bottom = inflate(sigma, b, depth)
    assert_equal(top[cut], letter)
    assert_equal(bottom[cut], letter)
    var top_prefix = List[Int]()
    var bottom_prefix = List[Int]()
    for i in range(cut):
        top_prefix.append(top[i])
        bottom_prefix.append(bottom[i])
    assert_equal(parikh(top_prefix), expected)
    assert_equal(parikh(bottom_prefix), expected)


def check_family() raises:
    for r in range(2, 13):
        for k in range(r, r + 7):
            var middle: List[Int] = [0]
            for _ in range(k):
                middle.append(1)
            middle.append(2)
            var tail = List[Int]()
            for _ in range(r):
                tail.append(0)
            tail.append(1)
            var sigma: List[List[Int]] = [[1], middle^, tail^]
            check_witness(sigma, 1, 2, 1, 0, [0, 0, 0], 0)
            var reversed = reversed_substitution(sigma)
            if k == r:
                check_witness(reversed, 0, 1, 4, k * k + 4 * k + 2,
                              [2 * k, k * k + k + 1, k + 1], 1)
            else:
                check_witness(reversed, 0, 1, 3, k + 2 * r + 4,
                              [r + 1, k + r + 1, 2], 1)
            assert_equal(legal_bigrams(sigma),
                         [True, True, False, True, True, True, True, True, False])
            assert_equal(len(phase_one_birth_seams(sigma, 0, 2, True)), 0)
            assert_equal(len(phase_one_birth_seams(sigma, 0, 2, False)), 0)
            assert_equal(len(strict_birth_seams(sigma, 0, 2, True)), 0)
            assert_equal(len(strict_birth_seams(sigma, 0, 2, False)), 0)

    var exceptional: List[List[Int]] = [[1], [0, 1, 2], [0, 0, 1]]
    check_witness(exceptional, 1, 2, 1, 0, [0, 0, 0], 0)
    check_witness(reversed_substitution(exceptional), 0, 1, 5, 20, [7, 9, 4], 0)
    assert_equal(strict_birth_seams(exceptional, 0, 2, True), [])
    assert_equal(strict_birth_seams(exceptional, 0, 2, False), [])


def check_literal_strict_survivor() raises:
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1, 0, 1]]
    var states: List[Pair] = [
        Pair([0, 1], [1, 0]), Pair([1, 2], [2, 1]),
        Pair([1, 0, 1, 2], [2, 1, 0, 1]),
    ]
    var system = build_derived_system(sigma, states)
    assert_equal(system.images[0], [0, 1])
    assert_equal(system.images[1], [0, 2])
    assert_equal(system.images[2], [0, 2, 2])
    check_witness(sigma, 0, 2, 1, 0, [0, 0, 0], 1)
    check_witness(reversed_substitution(sigma), 0, 2, 1, 0, [0, 0, 0], 1)
    assert_equal(len(phase_one_birth_seams(sigma, 1, 1, True)), 0)
    var possible = phase_one_birth_seams(sigma, 1, 1, False)
    assert_equal(possible, [12, 14, 66, 68])
    var count = 0
    for i in range(len(states)):
        var top = apply_substitution(sigma, states[i].u)
        var bottom = apply_substitution(sigma, states[i].v)
        var cuts = coincidence_boundaries(top, bottom)
        assert_equal(len(cuts), len(system.images[i]) + 1)
        for j in range(1, len(cuts) - 1):
            var cut = cuts[j]
            var a = top[cut - 1]
            var b = bottom[cut - 1]
            var c = top[cut]
            var d = bottom[cut]
            if c != 1:
                (a, b) = (b, a)
                (c, d) = (d, c)
            assert_equal(c, 1)
            assert_equal(b, 1)
            assert_true(27 * a + 9 * b + 3 * c + d in possible)
            count += 1
    assert_equal(count, 4)


def check_productive_survivor() raises:
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [2, 1]]
    check_witness(sigma, 1, 2, 2, 4, [1, 2, 1], 2)
    check_witness(reversed_substitution(sigma), 0, 1, 3, 5, [1, 2, 2], 1)
    assert_equal(phase_one_birth_seams(sigma, 0, 2, True), [])
    assert_equal(phase_one_birth_seams(sigma, 0, 2, False), [46])


def check_refusal() raises:
    var singular: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var refused = False
    try:
        _ = strict_birth_seams(singular, 1, 1, False)
    except:
        refused = True
    assert_true(refused)

    # The first image alone exceeds the exact arithmetic budget.
    var long_image = List[Int]()
    for _ in range(65):
        long_image.append(1)
    var too_long: List[List[Int]] = [long_image^, [0, 1, 2], [0, 0, 1]]
    refused = False
    try:
        _ = phase_one_birth_seams(too_long, 0, 2, False)
    except:
        refused = True
    assert_true(refused)


def main() raises:
    check_family()
    check_literal_strict_survivor()
    check_productive_survivor()
    check_refusal()
    require_contract("exact oriented and unordered newborn seam filters preserve actual strict seams and exclude the witnessed two-parameter family")
