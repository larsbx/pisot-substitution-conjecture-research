"""Bounded literal controls for uniform third-level Pisot family strong coincidence."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries, decompose
from psc.c4_third_level_coincidence_family import (
    symmetric_middle_family, verify_third_level_coincidence,
    asymmetric_middle_family, verify_asymmetric_third_level,
    closed_run_middle_family, verify_closed_run_coincidence,
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



def test_k_one_has_earlier_simultaneous_level_two_witness() raises:
    # The #475 specimen does not require the seam-residue exclusion
    # even for its third remaining candidate first edge {0,1}.
    var sigma = symmetric_middle_family(1)
    var words = List[List[Int]]()
    for a in range(3):
        words.append(apply_substitution(sigma, sigma[a]))
    assert_equal(words[0], [0, 1, 1, 2, 1])
    assert_equal(words[1], [1, 2, 1, 0, 1, 2, 1, 2, 1])
    assert_equal(words[2], [0, 1, 1, 2, 1, 0, 1, 2])
    for i in range(3):
        assert_equal(words[i][4], 1)
        var counts: List[Int] = [0, 0, 0]
        for j in range(4):
            counts[words[i][j]] += 1
        assert_equal(counts, [1, 2, 1])

def test_invalid_and_excessive_parameters_refuse() raises:
    for k in [-3, 0, 17, 1000000]:
        var refused = False
        try:
            _ = verify_third_level_coincidence(k)
        except:
            refused = True
        assert_true(refused)



def test_asymmetric_family_common_depth_three_for_unequal_runs() raises:
    # These are bounded actual letter words; the unbounded a,b theorem
    # uses the separate symbolic A/B/C word identity.
    for left in range(1, 9):
        for right in range(1, 9):
            var sigma = asymmetric_middle_family(left, right)
            var certificate = verify_asymmetric_third_level(left, right)
            var p = left * (left + right + 1) + 1
            assert_equal(len(sigma[1]), left + right + 1)
            assert_equal(certificate.left_run, left)
            assert_equal(certificate.right_run, right)
            assert_equal(certificate.cut, p)
            assert_equal(certificate.prefix_parikh, [
                1, left * (left + right), left
            ])
            for a in range(3):
                var word = _third_image(sigma, a)
                assert_equal(word[p], 1)
                assert_equal(len(word), certificate.word_lengths[a])


def test_asymmetric_all_three_swaps_produce_real_diagonal() raises:
    # A complete zero-return factor, not a merely matching character:
    # prefixes at p and p+1 are balanced on both tracks.
    for left in range(1, 6):
        for right in range(1, 6):
            var sigma = asymmetric_middle_family(left, right)
            var p = left * (left + right + 1) + 1
            for a in range(3):
                for b in range(a + 1, 3):
                    var top: List[Int] = [a, b]
                    var bottom: List[Int] = [b, a]
                    for _ in range(3):
                        top = apply_substitution(sigma, top)
                        bottom = apply_substitution(sigma, bottom)
                    var cuts = coincidence_boundaries(top, bottom)
                    var found_left = False
                    var found_right = False
                    for t in cuts:
                        if t == p:
                            found_left = True
                        if t == p + 1:
                            found_right = True
                    assert_true(found_left and found_right)
                    assert_equal(top[p], 1)
                    assert_equal(bottom[p], 1)


def test_fixed_incidence_does_not_fix_third_level_address() raises:
    # All three splittings of s=4 have identical incidence and PIP cubic,
    # but the common *literal* address is not incidence-determined.
    var positions = List[Int]()
    for left in range(1, 4):
        var result = verify_asymmetric_third_level(left, 4 - left)
        positions.append(result.cut)
    assert_equal(positions, [6, 11, 16])


def test_asymmetric_nonpositive_and_excessive_runs_refuse() raises:
    for left in [-1, 0, 17]:
        var refused = False
        try:
            _ = verify_asymmetric_third_level(left, 2)
        except:
            refused = True
        assert_true(refused)
    for right in [-1, 0, 17]:
        var refused = False
        try:
            _ = verify_asymmetric_third_level(2, right)
        except:
            refused = True
        assert_true(refused)


def _actual_letter_image_at_level(
    sigma: List[List[Int]], letter: Int, level: Int
) -> List[Int]:
    var word: List[Int] = [letter]
    for _ in range(level):
        word = apply_substitution(sigma, word)
    return word^


def test_both_zero_run_boundaries_are_genuine_letter_coincidences() raises:
    # a=0: all sigma^2 letters have the SAME first letter 0.
    # b=0: the indexed sigma^4 Parikh prefix is
    # (a+1,a^3+2a,a(a+1)), next letter 1.
    for a in range(1, 9):
        var zero_left = verify_closed_run_coincidence(0, a)
        assert_equal(zero_left.generation, 2)
        assert_equal(zero_left.cut, 0)
        assert_equal(zero_left.next_letter, 0)
        assert_equal(zero_left.prefix_parikh, [0, 0, 0])
        var zero_right = verify_closed_run_coincidence(a, 0)
        assert_equal(zero_right.generation, 4)
        assert_equal(zero_right.cut, a * a * a + a * a + 4 * a + 1)
        assert_equal(zero_right.next_letter, 1)
        assert_equal(zero_right.prefix_parikh, [
            a + 1, a * a * a + 2 * a, a * (a + 1),
        ])


def test_full_closed_quadrant_matches_existing_positive_family() raises:
    # The previous strictly positive public API is not weakened:
    # it still refuses either zero run.
    for a in range(1, 7):
        for b in range(1, 7):
            var old = verify_asymmetric_third_level(a, b)
            var new = verify_closed_run_coincidence(a, b)
            assert_equal(new.generation, 3)
            assert_equal(new.cut, old.cut)
            assert_equal(new.next_letter, 1)
            assert_equal(new.prefix_parikh, old.prefix_parikh)
            assert_equal(new.word_lengths, old.word_lengths)


def test_actual_swap_diagonal_at_both_boundary_cases() raises:
    for a in range(0, 7):
        for b in range(0, 7):
            if a + b == 0:
                continue
            if a > 0 and b > 0:
                continue
            var cert = verify_closed_run_coincidence(a, b)
            var sigma = closed_run_middle_family(a, b)
            for x in range(3):
                for y in range(x + 1, 3):
                    var top: List[Int] = [x, y]
                    var bottom: List[Int] = [y, x]
                    for _ in range(cert.generation):
                        top = apply_substitution(sigma, top)
                        bottom = apply_substitution(sigma, bottom)
                    var before = False
                    var after = False
                    var cuts = coincidence_boundaries(top, bottom)
                    for t in cuts:
                        if t == cert.cut:
                            before = True
                        if t == cert.cut + 1:
                            after = True
                    assert_true(before and after)
                    assert_equal(top[cert.cut], cert.next_letter)
                    assert_equal(bottom[cert.cut], cert.next_letter)


def test_same_incidence_different_boundary_depths_and_addresses() raises:
    # Fixed total run s=4; the five splittings have identical M,
    # but published explicit witness generation/address pairs differ.
    var generations = List[Int]()
    var cuts = List[Int]()
    for a in range(5):
        var cert = verify_closed_run_coincidence(a, 4 - a)
        generations.append(cert.generation)
        cuts.append(cert.cut)
    assert_equal(generations, [2, 3, 3, 3, 4])
    assert_equal(cuts, [0, 6, 11, 16, 97])


def test_closed_run_budget_and_invalid_inputs_refuse() raises:
    for a in [-1, 0, 17]:
        var refused = False
        try:
            _ = verify_closed_run_coincidence(a, 0)
        except:
            refused = True
        assert_true(refused)
    for b in [-1, 17]:
        var refused = False
        try:
            _ = verify_closed_run_coincidence(1, b)
        except:
            refused = True
        assert_true(refused)

def main() raises:
    test_bounded_family_simultaneous_three_letter_coincidences()
    test_all_three_balanced_swaps_have_actual_diagonal_child_by_level_three()
    test_invalid_and_excessive_parameters_refuse()
    test_k_one_has_earlier_simultaneous_level_two_witness()
    test_asymmetric_family_common_depth_three_for_unequal_runs()
    test_asymmetric_all_three_swaps_produce_real_diagonal()
    test_fixed_incidence_does_not_fix_third_level_address()
    test_asymmetric_nonpositive_and_excessive_runs_refuse()
    test_both_zero_run_boundaries_are_genuine_letter_coincidences()
    test_full_closed_quadrant_matches_existing_positive_family()
    test_actual_swap_diagonal_at_both_boundary_cases()
    test_same_incidence_different_boundary_depths_and_addresses()
    test_closed_run_budget_and_invalid_inputs_refuse()
    print("C4 uniform third-level family: complete literal strong coincidence controls passed.")
    require_contract("ternary symmetric middle family 01/(1^k 2 1^k)/012 has all three simultaneous depth-three balanced-prefix strong coincidences at k(2k+1)+1; actual swap BPA diagonals, bounded replay, invalid cap refusal; no global PSC promotion")
