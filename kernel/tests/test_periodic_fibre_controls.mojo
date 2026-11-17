"""Two literal controls for larger fibres over nonzero periodic points."""

from std.testing import assert_equal, assert_true
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.bpa import substitution_incidence
from psc.periodic_pair import centre_offset, incidence_power, interior_occurrences
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


def main() raises:
    test_four_fixed_lifts()
    test_exchanged_lifts()
    print("Nonzero periodic fibres: four fixed lifts in power three, and one fixed lift in power three with five in power six.")
    require_contract("Literal periodic fibres away from zero can have four fixed lifts, or five lifts of which only one is fixed by the first return. All interior marks in the two named torus classes are replayed exactly.")
