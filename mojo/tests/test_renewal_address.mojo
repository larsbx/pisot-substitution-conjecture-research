"""Canonical regressions for the level-scaled G1b-2 renewal address."""

from std.testing import assert_equal, assert_false, assert_true
from psc.bpa import substitution_incidence
from psc.renewal import same_labelled_return, strict_first_return_word
from psc.renewal_address import renewal_cut_address, same_relative_address
from psc.words import Pair


def nonunimodular_pisot_sigma() -> List[List[Int]]:
    # 0 -> 1, 1 -> 021, 2 -> 001.
    # Incidence characteristic polynomial: x^3 - x^2 - 2x - 2.
    # det(M)=2, so this regression prevents a hidden unimodular-only address.
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    var sigma = List[List[Int]]()
    sigma.append(a0)
    sigma.append(a1)
    sigma.append(a2)
    return sigma^


def collision_pair_a() -> Pair:
    var u: List[Int] = [0, 0, 1]
    var v: List[Int] = [1, 0, 0]
    return Pair(u, v)


def collision_pair_b() -> Pair:
    var u: List[Int] = [0, 2, 1]
    var v: List[Int] = [1, 2, 0]
    return Pair(u, v)


def det3(m: List[Int]) -> Int:
    return (
        m[0] * (m[4] * m[8] - m[5] * m[7])
        - m[1] * (m[3] * m[8] - m[5] * m[6])
        + m[2] * (m[3] * m[7] - m[4] * m[6])
    )


def test_nonunimodular_level_one_certificate() raises:
    var sigma = nonunimodular_pisot_sigma()
    var incidence = substitution_incidence(sigma)
    assert_equal(det3(incidence), 2)

    # sigma(001)=11021 and sigma(100)=02111.
    # Position 4 is an interior zero return.
    var address = renewal_cut_address(sigma, collision_pair_a(), 1, 4)
    assert_equal(address.level, 1)
    assert_equal(address.digit_levels(), 1)
    assert_equal(address.source_index_delta, 0)
    assert_equal(address.source_defect.x, 1)
    assert_equal(address.source_defect.y, -1)
    assert_equal(address.source_defect.z, 0)
    assert_equal(address.top_source_letter, 1)
    assert_equal(address.bottom_source_letter, 0)
    assert_equal(address.top_digits, [1, 2])
    assert_equal(address.bottom_digits, [0, 0])

    # M*(1,-1,0)=(-1,0,-1); finite digit prefixes contribute (1,0,1).
    assert_equal(address.scaled_defect.x, -1)
    assert_equal(address.scaled_defect.y, 0)
    assert_equal(address.scaled_defect.z, -1)
    assert_equal(address.correction.x, 1)
    assert_equal(address.correction.y, 0)
    assert_equal(address.correction.z, 1)
    assert_true(address.certificate_closes())


def test_inherited_level_two_certificate() raises:
    var sigma = nonunimodular_pisot_sigma()

    # The depth-one zero return at 4 inflates to the depth-two zero return at 10.
    var address = renewal_cut_address(sigma, collision_pair_a(), 2, 10)
    assert_equal(address.level, 2)
    assert_equal(address.digit_levels(), 2)
    assert_equal(address.source_defect.x, 1)
    assert_equal(address.source_defect.y, -1)
    assert_equal(address.source_defect.z, 0)
    assert_equal(address.top_digits, [1, 2, 1, 0])
    assert_equal(address.bottom_digits, [0, 0, 1, 0])
    assert_equal(address.scaled_defect.x, -2)
    assert_equal(address.scaled_defect.y, -2)
    assert_equal(address.scaled_defect.z, 0)
    assert_equal(address.correction.x, 2)
    assert_equal(address.correction.y, 2)
    assert_equal(address.correction.z, 0)
    assert_true(address.certificate_closes())


def test_nonreturn_cut_fails_closed() raises:
    var caught = False
    try:
        _ = renewal_cut_address(
            nonunimodular_pisot_sigma(), collision_pair_a(), 1, 3
        )
    except:
        caught = True
    assert_true(caught)


def test_source_pair_must_be_strict_first_return() raises:
    var u: List[Int] = [0, 1]
    var v: List[Int] = [0, 1]
    var caught = False
    try:
        _ = renewal_cut_address(nonunimodular_pisot_sigma(), Pair(u, v), 1, 1)
    except:
        caught = True
    assert_true(caught)


def test_relative_address_does_not_replace_labels() raises:
    var sigma = nonunimodular_pisot_sigma()
    var a_word = strict_first_return_word(collision_pair_a())
    var b_word = strict_first_return_word(collision_pair_b())
    assert_false(same_labelled_return(a_word, b_word))

    # A has its first inflated interior zero return at 4; B has the analogous
    # return at 6.  Their relative level-one address is the same even though the
    # labelled first-return words differ.  Therefore this coordinate augments,
    # and never quotients away, the merged labelled-renewal representation.
    var a_address = renewal_cut_address(sigma, collision_pair_a(), 1, 4)
    var b_address = renewal_cut_address(sigma, collision_pair_b(), 1, 6)
    assert_true(same_relative_address(a_address, b_address))


def main() raises:
    test_nonunimodular_level_one_certificate()
    print("[PASS] test_nonunimodular_level_one_certificate")
    test_inherited_level_two_certificate()
    print("[PASS] test_inherited_level_two_certificate")
    test_nonreturn_cut_fails_closed()
    print("[PASS] test_nonreturn_cut_fails_closed")
    test_source_pair_must_be_strict_first_return()
    print("[PASS] test_source_pair_must_be_strict_first_return")
    test_relative_address_does_not_replace_labels()
    print("[PASS] test_relative_address_does_not_replace_labels")
    print("5 renewal-address Mojo tests passed.")
