"""Bounded literal controls for uniform third-level Pisot family strong coincidence."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries, decompose
from psc.c4_third_level_coincidence_family import (
    symmetric_middle_family, verify_third_level_coincidence,
    asymmetric_middle_family, verify_asymmetric_third_level,
    nonnegative_middle_family, verify_nonnegative_runs,
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


def test_uniform_nonnegative_run_boundary_witnesses() raises:
    for left in range(0, 9):
        for right in range(0, 9):
            if left == 0 and right == 0:
                continue
            var sigma = nonnegative_middle_family(left, right)
            var w = verify_nonnegative_runs(left, right)
            var depth = 3
            var cut = 0
            var next_letter = 1
            var Q: List[Int] = [0, 0, 0]
            if left == 0:
                depth = 2
                next_letter = 0
            elif right == 0:
                depth = 4
                cut = left * left * left + left * left + 4 * left + 1
                Q = [left + 1, left * left * left + 2 * left, left * (left + 1)]
            else:
                cut = left * (left + right + 1) + 1
                Q = [1, left * (left + right), left]
            assert_equal(w.level, depth)
            assert_equal(w.cut, cut)
            assert_equal(w.common_letter, next_letter)
            assert_equal(w.prefix_parikh, Q)
            assert_equal(len(w.word_lengths), 3)
            for letter in range(3):
                var word: List[Int] = [letter]
                for _ in range(depth):
                    word = apply_substitution(sigma, word)
                assert_true(cut < len(word))
                assert_equal(word[cut], next_letter)
                assert_equal(w.word_lengths[letter], len(word))


def test_nonnegative_boundary_complete_balanced_swaps() raises:
    # Complete balanced-factor proof control: the consecutive
    # cuts at p,p+1 must enclose an ACTUAL single-letter diagonal.
    for left in range(0, 6):
        for right in range(0, 6):
            if left == 0 and right == 0:
                continue
            var sigma = nonnegative_middle_family(left, right)
            var cert = verify_nonnegative_runs(left, right)
            for a in range(3):
                for b in range(a + 1, 3):
                    var top: List[Int] = [a, b]
                    var bottom: List[Int] = [b, a]
                    for _ in range(cert.level):
                        top = apply_substitution(sigma, top)
                        bottom = apply_substitution(sigma, bottom)
                    var cuts = coincidence_boundaries(top, bottom)
                    var at_p = False
                    var at_p_plus_1 = False
                    for value in cuts:
                        if value == cert.cut:
                            at_p = True
                        if value == cert.cut + 1:
                            at_p_plus_1 = True
                    assert_true(at_p and at_p_plus_1)
                    assert_equal(top[cert.cut], cert.common_letter)
                    assert_equal(bottom[cert.cut], cert.common_letter)
                    var found = False
                    var blocks = decompose(top, bottom)
                    for j in range(len(blocks)):
                        if len(blocks[j].u) == 1 and len(blocks[j].v) == 1:
                            if blocks[j].u[0] == cert.common_letter and blocks[j].v[0] == cert.common_letter:
                                found = True
                    assert_true(found)


def test_nonnegative_boundary_exact_controls_and_refusals() raises:
    var left_zero = verify_nonnegative_runs(0, 3)
    assert_equal(left_zero.level, 2)
    assert_equal(left_zero.cut, 0)
    assert_equal(left_zero.common_letter, 0)
    var right_zero = verify_nonnegative_runs(3, 0)
    assert_equal(right_zero.level, 4)
    assert_equal(right_zero.cut, 49)
    assert_equal(right_zero.prefix_parikh, [4, 33, 12])
    var excluded = False
    try:
        _ = verify_nonnegative_runs(0, 0)
    except:
        excluded = True
    assert_true(excluded)
    for left in [-1, 17]:
        excluded = False
        try:
            _ = verify_nonnegative_runs(left, 2)
        except:
            excluded = True
        assert_true(excluded)
    for right in [-1, 17]:
        excluded = False
        try:
            _ = verify_nonnegative_runs(2, right)
        except:
            excluded = True
        assert_true(excluded)
    # Preserve strict-positive semantics of the published API:
    # broadening the new nonnegative verifier must not make this pass.
    excluded = False
    try:
        _ = verify_asymmetric_third_level(0, 2)
    except:
        excluded = True
    assert_true(excluded)

def main() raises:
    test_bounded_family_simultaneous_three_letter_coincidences()
    test_all_three_balanced_swaps_have_actual_diagonal_child_by_level_three()
    test_invalid_and_excessive_parameters_refuse()
    test_k_one_has_earlier_simultaneous_level_two_witness()
    test_asymmetric_family_common_depth_three_for_unequal_runs()
    test_asymmetric_all_three_swaps_produce_real_diagonal()
    test_fixed_incidence_does_not_fix_third_level_address()
    test_asymmetric_nonpositive_and_excessive_runs_refuse()
    test_uniform_nonnegative_run_boundary_witnesses()
    test_nonnegative_boundary_complete_balanced_swaps()
    test_nonnegative_boundary_exact_controls_and_refusals()
    print("C4 uniform third-level family: complete literal strong coincidence controls passed.")
    require_contract("all nonnegative nonzero middle runs in 01/(1^a2 1^b)/012 have uniform simultaneous strong coincidence at depth at most four (boundary cases 2 and 4, interior 3), with genuine complete swap diagonals and refusal controls; no universal PSC promotion")
