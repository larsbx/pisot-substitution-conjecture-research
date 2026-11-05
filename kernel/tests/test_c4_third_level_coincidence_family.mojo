"""Bounded literal controls for uniform third-level Pisot family strong coincidence."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries, decompose
from psc.c4_third_level_coincidence_family import (
    symmetric_middle_family, verify_third_level_coincidence,
    asymmetric_middle_family, verify_asymmetric_third_level,
    closed_run_middle_family, verify_closed_run_coincidence,
    verify_sharp_closed_run_coincidence,
    reversed_closed_run_family, verify_reversed_closed_run_coincidence,
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



def test_reversed_family_all_five_chambers() raises:
    for a in range(9):
        for b in range(9):
            if a + b == 0 or a + b > 12:
                continue
            var cert = verify_reversed_closed_run_coincidence(a, b)
            var original = closed_run_middle_family(a, b)
            var reversed = reversed_closed_run_family(a, b)
            for letter in range(3):
                var old = original[letter].copy()
                var expected_word = List[Int]()
                for j in range(len(old)):
                    expected_word.append(old[len(old) - 1 - j])
                assert_equal(reversed[letter], expected_word)
                var actual = _actual_letter_image_at_level(
                    reversed, letter, cert.generation
                )
                assert_equal(actual[cert.cut], cert.next_letter)
                assert_equal(cert.word_lengths[letter], len(actual))
            assert_true(cert.generation <= 4)
            if b == 0:
                assert_equal(cert.generation, 2)
                assert_equal(cert.cut, 0)
                assert_equal(cert.next_letter, 2)
            elif a == 0:
                assert_equal(cert.generation, 4)
                assert_equal(cert.next_letter, 2)
            elif b == 1:
                assert_equal(cert.generation, 3)
                assert_equal(cert.cut, a + 5)
            else:
                assert_equal(cert.generation, 4)
                assert_equal(cert.next_letter, 1)


def test_reversed_family_actual_swap_diagonals() raises:
    for a in range(6):
        for b in range(6):
            if a + b == 0:
                continue
            var cert = verify_reversed_closed_run_coincidence(a, b)
            var sigma = reversed_closed_run_family(a, b)
            for x in range(3):
                for y in range(x + 1, 3):
                    var top: List[Int] = [x, y]
                    var bottom: List[Int] = [y, x]
                    for _ in range(cert.generation):
                        top = apply_substitution(sigma, top)
                        bottom = apply_substitution(sigma, bottom)
                    var before = False
                    var after = False
                    for cut in coincidence_boundaries(top, bottom):
                        if cut == cert.cut:
                            before = True
                        if cut == cert.cut + 1:
                            after = True
                    assert_true(before and after)
                    assert_equal(top[cert.cut], cert.next_letter)
                    assert_equal(bottom[cert.cut], cert.next_letter)
                    var factors = decompose(top, bottom)
                    var saw = False
                    for j in range(len(factors)):
                        if factors[j].u == [cert.next_letter] and factors[j].v == [cert.next_letter]:
                            saw = True
                    assert_true(saw)


def test_reversed_family_invalid_and_caps_refuse() raises:
    for a in [-2, 0, 9]:
        var refused = False
        try:
            _ = verify_reversed_closed_run_coincidence(a, 0)
        except:
            refused = True
        assert_true(refused)
    for b in [-1, 9]:
        var refused = False
        try:
            _ = verify_reversed_closed_run_coincidence(1, b)
        except:
            refused = True
        assert_true(refused)
    var refused_total = False
    try:
        _ = verify_reversed_closed_run_coincidence(8, 8)
    except:
        refused_total = True
    assert_true(refused_total)


def test_sharp_forward_family_all_five_parameter_chambers() raises:
    # The new API certifies earliest *simultaneous* three-letter depth.
    # The older exhibited-witness APIs remain unchanged for provenance.
    for a in range(9):
        for b in range(9):
            if a + b == 0:
                continue
            var cert = verify_sharp_closed_run_coincidence(a, b)
            var previous = verify_closed_run_coincidence(a, b)
            var expected_level = 3
            var expected_cut = a * (a + b + 1) + 1
            if a == 0:
                expected_level = 2
                expected_cut = 0
            elif a == 1 and b == 0:
                expected_level = 3
                expected_cut = 7
            elif a == 1:
                expected_level = 2
                expected_cut = b + 3
            elif b == 0:
                expected_level = 4
                expected_cut = a * a * a + a * a + 4 * a + 1
            assert_equal(cert.generation, expected_level)
            assert_equal(cert.cut, expected_cut)
            assert_true(cert.generation <= previous.generation)
            var sigma = closed_run_middle_family(a, b)
            for x in range(3):
                var word = _actual_letter_image_at_level(
                    sigma, x, cert.generation
                )
                assert_equal(word[cert.cut], cert.next_letter)
                assert_equal(len(word), cert.word_lengths[x])
                var prefix = List[Int]()
                for j in range(cert.cut):
                    prefix.append(word[j])
                # Fully check exact Parikh, not merely the next letter.
                var counts: List[Int] = [0, 0, 0]
                for t in prefix:
                    counts[t] += 1
                assert_equal(counts, cert.prefix_parikh)


def test_sharp_forward_family_actual_swap_diagonal() raises:
    for a in range(7):
        for b in range(7):
            if a + b == 0:
                continue
            var sigma = closed_run_middle_family(a, b)
            var cert = verify_sharp_closed_run_coincidence(a, b)
            for x in range(3):
                for y in range(x + 1, 3):
                    var top: List[Int] = [x, y]
                    var bottom: List[Int] = [y, x]
                    for _ in range(cert.generation):
                        top = apply_substitution(sigma, top)
                        bottom = apply_substitution(sigma, bottom)
                    var before = False
                    var after = False
                    for p in coincidence_boundaries(top, bottom):
                        if p == cert.cut:
                            before = True
                        if p == cert.cut + 1:
                            after = True
                    assert_true(before and after)
                    assert_equal(top[cert.cut], cert.next_letter)
                    assert_equal(bottom[cert.cut], cert.next_letter)


def test_sharp_forward_family_rejects_invalid_runs() raises:
    for a in [-1, 0, 17]:
        var refused = False
        try:
            _ = verify_sharp_closed_run_coincidence(a, 0)
        except:
            refused = True
        assert_true(refused)
    for b in [-1, 17]:
        var refused = False
        try:
            _ = verify_sharp_closed_run_coincidence(1, b)
        except:
            refused = True
        assert_true(refused)



def _letter_pair_strong_coincidence_at_level(
    sigma: List[List[Int]], x: Int, y: Int, level: Int,
) -> Bool:
    """Search ALL equal-Parikh/common-next-letter cuts, not only a preset p."""
    var u = _actual_letter_image_at_level(sigma, x, level)
    var v = _actual_letter_image_at_level(sigma, y, level)
    var limit = len(u)
    if len(v) < limit:
        limit = len(v)
    var pu: List[Int] = [0, 0, 0]
    var pv: List[Int] = [0, 0, 0]
    for p in range(limit):
        if pu == pv and u[p] == v[p]:
            return True
        pu[u[p]] += 1
        pv[v[p]] += 1
    return False


def test_sharp_forward_family_complete_pairwise_depths() raises:
    # For every member of the bounded test grid the three distinct
    # letter pairs attain their first witnesses at (D,1,D), respectively.
    # This validates a finite exact oracle; the uniform mathematical
    # lower bounds are independent and appear in the paper proof.
    for a in range(9):
        for b in range(9):
            if a + b == 0:
                continue
            var sigma = closed_run_middle_family(a, b)
            var sharp = verify_sharp_closed_run_coincidence(a, b)
            for level in range(1, sharp.generation + 1):
                assert_true(_letter_pair_strong_coincidence_at_level(
                    sigma, 0, 2, level
                ))
                var expected = level == sharp.generation
                assert_equal(_letter_pair_strong_coincidence_at_level(
                    sigma, 0, 1, level
                ), expected)
                assert_equal(_letter_pair_strong_coincidence_at_level(
                    sigma, 1, 2, level
                ), expected)


def test_forward_prefix_satellite_is_literal_at_all_bounded_depths() raises:
    # sigma(2)=sigma(0) + [2]; hence sigma^n(2)=
    # sigma^n(0) + sigma^(n-1)(2). Not an incidence-only identity.
    for a in range(7):
        for b in range(7):
            if a + b == 0:
                continue
            var sigma = closed_run_middle_family(a, b)
            for level in range(1, 5):
                var w0 = _actual_letter_image_at_level(sigma, 0, level)
                var w2 = _actual_letter_image_at_level(sigma, 2, level)
                var tail = _actual_letter_image_at_level(sigma, 2, level - 1)
                var full = w0.copy()
                for c in tail:
                    full.append(c)
                assert_equal(w2, full)


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
    test_reversed_family_all_five_chambers()
    test_reversed_family_actual_swap_diagonals()
    test_reversed_family_invalid_and_caps_refuse()
    test_sharp_forward_family_all_five_parameter_chambers()
    test_sharp_forward_family_actual_swap_diagonal()
    test_sharp_forward_family_rejects_invalid_runs()
    test_sharp_forward_family_complete_pairwise_depths()
    test_forward_prefix_satellite_is_literal_at_all_bounded_depths()
    print("C4 uniform third-level family: complete literal strong coincidence controls passed.")
    require_contract("ternary symmetric middle family 01/(1^k 2 1^k)/012 has all three simultaneous depth-three balanced-prefix strong coincidences at k(2k+1)+1; forward run family 01/(1^a 2 1^b)/012 has sharp simultaneous left-coincidence depth D(a,b) in {2,3,4} by five chambers with pairwise minimum depths ({0,1},{0,2},{1,2})=(D,1,D) by exhaustive earlier-cut scan and the literal prefix-satellite identity sigma^n(2)=sigma^n(0)sigma^(n-1)(2) on the bounded grid; actual swap BPA diagonals, bounded replay, invalid cap refusal; no global PSC promotion")
