"""Bounded literal controls for uniform third-level Pisot family strong coincidence."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries, decompose
from psc.c4_third_level_coincidence_family import (
    symmetric_middle_family, verify_third_level_coincidence,
)


def _third_image(sigma: List[List[Int]], a: Int) -> List[Int]:
    var word = sigma[a].copy()
    for _ in range(2):
        word = apply_substitution(sigma, word)
    return word^


def test_bounded_family_simultaneous_three_letter_coincidences() raises:
    for k in range(1, 13):
        var result = verify_third_level_coincidence(k)
        var p = k * (2 * k + 1) + 1
        assert_equal(result.parameter, k)
        assert_equal(result.cut, p)
        assert_equal(result.prefix_parikh, [1, 2 * k * k, k])
        assert_equal(len(result.word_lengths), 3)
        var sigma = symmetric_middle_family(k)
        assert_equal(len(sigma[1]), 2 * k + 1)
        for a in range(3):
            var word = _third_image(sigma, a)
            assert_true(p < len(word))
            assert_equal(word[p], 1)
            assert_equal(result.word_lengths[a], len(word))


def test_all_three_balanced_swaps_have_actual_diagonal_child_by_level_three() raises:
    # This checks the *actual complete* BPA decomposition, not only
    # a synthetic letter-level coincidence or an endpoint mask.
    for k in range(1, 9):
        var sigma = symmetric_middle_family(k)
        var cut = k * (2 * k + 1) + 1
        for a in range(3):
            for b in range(a + 1, 3):
                var top: List[Int] = [a, b]
                var bottom: List[Int] = [b, a]
                for _ in range(3):
                    top = apply_substitution(sigma, top)
                    bottom = apply_substitution(sigma, bottom)
                var zeroes = coincidence_boundaries(top, bottom)
                var hit_before = False
                var hit_after = False
                for z in zeroes:
                    if z == cut:
                        hit_before = True
                    if z == cut + 1:
                        hit_after = True
                assert_true(hit_before and hit_after)
                assert_equal(top[cut], 1)
                assert_equal(bottom[cut], 1)
                var factors = decompose(top, bottom)
                var found = False
                for j in range(len(factors)):
                    if factors[j].u == [1] and factors[j].v == [1]:
                        found = True
                assert_true(found)


def test_invalid_and_excessive_parameters_refuse() raises:
    for k in [-3, 0, 17, 1000000]:
        var refused = False
        try:
            _ = verify_third_level_coincidence(k)
        except:
            refused = True
        assert_true(refused)


def main() raises:
    test_bounded_family_simultaneous_three_letter_coincidences()
    test_all_three_balanced_swaps_have_actual_diagonal_child_by_level_three()
    test_invalid_and_excessive_parameters_refuse()
    print("C4 uniform third-level family: complete literal strong coincidence controls passed.")
    require_contract("ternary symmetric middle family 01/(1^k 2 1^k)/012 has all three simultaneous depth-three balanced-prefix strong coincidences at k(2k+1)+1; actual swap BPA diagonals, bounded replay, invalid cap refusal; no global PSC promotion")
