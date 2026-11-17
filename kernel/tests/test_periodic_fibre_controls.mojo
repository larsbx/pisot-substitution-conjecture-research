"""Complete nonzero periodic-fibre catalogues and independent word replay."""

from std.testing import assert_equal, assert_false, assert_true
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, substitution_incidence
from psc.periodic_fibre import PeriodicFibre, catalogue_periodic_fibre
from psc.periodic_pair import centre_offset, image_sizes, incidence_power, interior_occurrences
from psc.pisot import is_pip
from psc.zero_fibre import compare_zero_fibre


def fixed_digits_in_class(
    sigma: List[List[Int]], n: Int, numerator: List[Int], denominator: Int,
) raises -> List[List[Int]]:
    # Named nonzero classes require only interior marks. A vertex at zero
    # in a periodic tiling has lattice start fixed by M^n, hence start zero.
    assert_true(denominator > 1 and numerator != [0, 0, 0])
    for x in numerator:
        assert_true(0 <= x < denominator)
    var entries = incidence_power(sigma, n).e.copy()
    for i in range(3):
        entries[4 * i] -= 1
    var a = Mat3(entries)
    assert_true(a.det() != 0)
    var negative_image = a.apply(numerator)
    for i in range(3):
        assert_equal(negative_image[i] % denominator, 0)
        negative_image[i] = -(negative_image[i] // denominator)
    # The based centre has start -A^{-1}p. It represents numerator /
    # denominator precisely when p + A*(numerator / denominator) is in AZ^3.
    var found = List[List[Int]]()
    for letter in range(3):
        var origins = interior_occurrences(sigma, letter, n, 1024)
        for origin in origins:
            if len(centre_offset(sigma, n, origin.prefix, negative_image)) == 3:
                found.append([letter, origin.index])
    return found^


def replay_returns(
    sigma: List[List[Int]], fibre: PeriodicFibre, permutation: List[Int], alignment_bound: Int,
) raises:
    assert_equal(len(fibre.lifts), len(permutation))
    assert_equal(fibre.alignment_depth_bound, alignment_bound)
    var n = fibre.return_power
    var sizes = image_sizes(sigma, n)
    var m_power = incidence_power(sigma, n)
    var targets = List[Bool](length=len(permutation), fill=False)
    var fixed = List[List[Int]]()
    for i in range(len(fibre.lifts)):
        ref lift = fibre.lifts[i]
        assert_equal(lift.next_lift, permutation[i])
        assert_false(targets[lift.next_lift])
        targets[lift.next_lift] = True
        assert_equal(len(lift.indices), n)
        var word: List[Int] = [lift.centre.letter]
        var letter = lift.centre.letter
        var ordinal = 0
        for level in range(n):
            var digit = lift.indices[level]
            assert_true(0 <= digit < len(sigma[letter]))
            for j in range(digit):
                ordinal += sizes[n - level - 1][sigma[letter][j]]
            letter = sigma[letter][digit]
            word = apply_substitution(sigma, word)
        var target = fibre.lifts[lift.next_lift].centre
        assert_true(0 <= ordinal < len(word))
        assert_equal(word[ordinal], target.letter)
        assert_equal(letter, target.letter)
        var expected = m_power.apply(lift.centre.vector())
        for j in range(ordinal):
            expected[word[j]] -= fibre.denominator
        assert_equal(expected, target.vector())
        if i == lift.next_lift:
            assert_true(0 < ordinal < len(word) - 1)
            fixed.append([letter, ordinal])

    var p = fibre.lifts[0].centre.vector()
    for a in range(3):
        p[a] = (-p[a]) % fibre.denominator
    var exhaustive_marks = fixed_digits_in_class(sigma, n, p, fibre.denominator)
    assert_equal(len(fixed), len(exhaustive_marks))
    for mark in fixed:
        assert_true(mark in exhaustive_marks)

    var k = 0
    for i in range(len(fibre.lifts)):
        for j in range(i + 1, len(fibre.lifts)):
            var pair = fibre.pairs[k]
            assert_equal(pair.top, i)
            assert_equal(pair.bottom, j)
            assert_true(pair.bounded_gaps())
            assert_true(0 <= pair.shared_vertex_depth <= alignment_bound)
            assert_true(pair.shared_vertex_depth <= pair.coincidence_depth)
            k += 1
    assert_equal(len(fibre.pairs), k)


def test_four_fixed_lifts() raises:
    var sigma: List[List[Int]] = [[1], [2], [0, 2, 1]]
    var m = Mat3(substitution_incidence(sigma))
    assert_true(is_pip(m))
    assert_equal(abs(m.det()), 1)
    var zero = compare_zero_fibre(sigma)
    assert_true(zero.all_meet_reference())
    assert_equal(
        fixed_digits_in_class(sigma, 3, [1, 0, 1], 2), [[1, 3], [2, 3], [2, 5], [2, 7]],
    )
    var fibre = catalogue_periodic_fibre(sigma, [1, 0, 1], 2, 3)
    replay_returns(sigma, fibre, [0, 1, 2, 3], 5)
    assert_equal(fibre.pairs[0].shared_vertex_depth, 0)
    assert_equal(fibre.pairs[0].coincidence_depth, 4)


def test_exchanged_lifts() raises:
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var m = Mat3(substitution_incidence(sigma))
    assert_true(is_pip(m))
    assert_equal(abs(m.det()), 1)
    var zero = compare_zero_fibre(sigma)
    assert_equal(zero.depths, [0, 0, 0, 4, 1])
    assert_equal(fixed_digits_in_class(sigma, 3, [17, 4, 7], 19), [[1, 4]])
    assert_equal(
        fixed_digits_in_class(sigma, 6, [17, 4, 7], 19),
        [[1, 57], [1, 106], [1, 143], [2, 106], [2, 143]],
    )
    var fibre = catalogue_periodic_fibre(sigma, [17, 4, 7], 19, 3)
    replay_returns(sigma, fibre, [3, 2, 1, 0, 4], 4)
    assert_equal(fibre.pairs[0].shared_vertex_depth, 0)
    assert_equal(fibre.pairs[0].coincidence_depth, 4)
    var squared = catalogue_periodic_fibre(sigma, [17, 4, 7], 19, 6)
    replay_returns(sigma, squared, [0, 1, 2, 3, 4], 4)
    for i in range(len(fibre.lifts)):
        assert_true(squared.lifts[i].centre == fibre.lifts[i].centre)
        var indices = fibre.lifts[i].indices.copy()
        for digit in fibre.lifts[fibre.lifts[i].next_lift].indices:
            indices.append(digit)
        assert_equal(squared.lifts[i].indices, indices)


def test_no_fixed_lift() raises:
    var sigma: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var fibre = catalogue_periodic_fibre(sigma, [1, 1, 1], 2, 1)
    replay_returns(sigma, fibre, [1, 2, 0], 3)


def rejects(
    sigma: List[List[Int]], numerator: List[Int], denominator: Int, n: Int, expected: String,
    max_work: Int = 2000000, max_overlap_states: Int = 20000,
) -> Bool:
    try:
        _ = catalogue_periodic_fibre(sigma, numerator, denominator, n, max_work, max_overlap_states)
    except e:
        return expected in String(e)
    return False


def test_rejections() raises:
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    assert_true(rejects(sigma, [17, 4, 7], 19, 1, "base class does not return"))
    assert_true(rejects(sigma, [0, 0, 0], 19, 3, "expected a nonzero normalized rational class"))
    assert_true(rejects(sigma, [17, 19, 7], 19, 3, "expected a nonzero normalized rational class"))
    assert_true(rejects(sigma, [17, 4, 7], 0, 3, "expected a nonzero normalized rational class"))
    assert_true(rejects(sigma, [17, 4, 7], 19, 0, "return power and caps must be positive"))
    assert_true(rejects(sigma, [17, 4, 7], 19, 3, "work cap reached", max_work=3))
    assert_true(rejects(sigma, [17, 4, 7], 19, 3, "capped partial graph", max_overlap_states=1))
    assert_true(rejects([[1], [0, 1, 2], [1, 0, 1]], [1, 0, 1], 2, 3, "primitive irreducible Pisot"))
    assert_true(rejects([[1], [0, 1, 2], [0, 0, 1]], [1, 0, 1], 2, 3, "must be unimodular"))


def main() raises:
    test_four_fixed_lifts()
    test_exchanged_lifts()
    test_no_fixed_lift()
    test_rejections()
    print("Nonzero periodic fibres: four fixed lifts, one fixed lift and two exchanged pairs, and a three-cycle.")
    require_contract("Literal periodic fibres away from zero can have four fixed lifts, or five lifts of which only one is fixed by the first return. All interior marks in the two named torus classes are replayed exactly.")
    require_contract("The nonzero periodic fibre catalogue checks all returning centre states, records the literal index path and permutation of each lift, and tests shared cuts, bounded gaps and actual tile coincidence on every unordered pair. Exact controls have fibre sizes four, five and three, with respectively four, one and zero fixed lifts. Invalid classes, nonunit or reducible input and incomplete searches are refused.")
