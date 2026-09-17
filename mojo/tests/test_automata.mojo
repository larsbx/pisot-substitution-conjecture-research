"""Regressions for the automata kernel and the Dumont-Thomas numeration.

The kernel is the engine a decision procedure over a numeration system needs,
so what is pinned here is its algebra: complement is exact because transitions
are total, intersection and union are the synchronous product, projection is
the subset construction that discharges one existential quantifier, and
minimisation identifies exactly the automata with one language.

The numeration tests are the substantive ones. They say the automaton *is* the
fixed point -- letter by letter over a prefix, and by two counting identities
that tie it back to objects computed elsewhere in the repository: the image
lengths of the substitution, and the powers of its incidence matrix.
"""

from std.testing import assert_equal, assert_false, assert_true

from finite_linear_algebra.mat3 import Mat3, identity3
from psc.automata import (
    Dfa,
    accepted_count,
    complement,
    intersection,
    is_empty,
    minimised,
    project,
    same_language,
    union,
    with_sink,
    witness,
)
from psc.bpa import substitution_incidence
from psc.dumont_thomas import (
    digits,
    image_lengths,
    letter_at,
    letter_automaton,
    letter_of_digits,
    levels_to_cover,
    max_image_length,
    numeration_automaton,
    occurrences_of_length,
    positions_of_length,
    power_substitution,
    prolongable_form,
)
from psc.oa_overlap_types import fixed_point_prefix, prolongable_point


def even_ones() raises -> Dfa:
    """An even number of ones over `{0, 1}`."""
    var delta: List[Int] = [0, 1, 1, 0]
    var accepting: List[Bool] = [True, False]
    return Dfa(2, delta, accepting)


def tribonacci() -> List[List[Int]]:
    var sigma = List[List[Int]]()
    var a0: List[Int] = [0, 1]
    var a1: List[Int] = [0, 2]
    var a2: List[Int] = [0]
    sigma.append(a0^)
    sigma.append(a1^)
    sigma.append(a2^)
    return sigma^


def tau_sigma() -> List[List[Int]]:
    """`0 -> 1, 1 -> 021, 2 -> 001`: prolongable only at a power."""
    var sigma = List[List[Int]]()
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    sigma.append(a0^)
    sigma.append(a1^)
    sigma.append(a2^)
    return sigma^


def test_the_kernel_is_a_boolean_algebra_of_languages() raises:
    var even = even_ones()
    var odd = complement(even)
    var one: List[Int] = [1]
    var two: List[Int] = [1, 1]
    assert_true(even.accepts(two))
    assert_false(even.accepts(one))
    assert_true(odd.accepts(one))
    # Total transitions make complement exact: no word is accepted by both, and
    # every word by one.
    assert_true(is_empty(intersection(even, odd)))
    assert_true(is_empty(complement(union(even, odd))))
    # 2^(n-1) words of each parity at length n > 0.
    assert_equal(accepted_count(even, 3), 4)
    assert_equal(accepted_count(odd, 3), 4)
    assert_equal(accepted_count(even, 0), 1)
    # The shortest witness of an even count of ones is the empty word.
    assert_equal(len(witness(even).word), 0)
    assert_equal(len(witness(odd).word), 1)


def test_emptiness_reports_the_instance_not_only_the_verdict() raises:
    # A language with one word: 1 0 1. Its witness must be that word.
    # 0 start, 1 read 1, 2 read 10, 3 read 101 and accepting, 4 the sink.
    var delta: List[Int] = [4, 1, 2, 4, 4, 3, 4, 4, 4, 4]
    var accepting: List[Bool] = [False, False, False, True, False]
    var only = Dfa(2, delta, accepting)
    var found = witness(only)
    assert_false(found.empty)
    assert_equal(len(found.word), 3)
    assert_equal(found.word[0], 1)
    assert_equal(found.word[1], 0)
    assert_equal(found.word[2], 1)
    assert_true(only.accepts(found.word))
    # An automaton accepting nothing says so, and hands back no word.
    var nothing = complement(union(only, complement(only)))
    assert_true(is_empty(nothing))
    assert_equal(len(witness(nothing).word), 0)


def test_projection_discharges_one_existential_quantifier() raises:
    """Two tracks over `{0, 1}`, letters packed as `x + 2 y`.

    The language is `y = 1` on every letter. Projecting the `y` track must give
    every word over `x`, since some `y` always completes one; projecting the `x`
    track instead must give exactly the words with `y = 1` throughout, which is
    a smaller language. A projection that ignored which track it drops would
    return the same automaton twice."""
    var delta = List[Int]()
    var accepting: List[Bool] = [True, False]
    for state in range(2):
        for letter in range(4):
            var y = letter // 2
            delta.append(0 if (state == 0 and y == 1) else 1)
    var both = Dfa(4, delta, accepting)
    var over_x: List[Int] = [0, 1]
    var over_y = project(both, 2, 1)          # drop y: anything over x
    var over_second = project(both, 2, 0)     # drop x: keeps y = 1
    assert_equal(over_y.letters, 2)
    assert_true(over_y.accepts(over_x))
    var ones: List[Int] = [1, 1]
    var zeros: List[Int] = [0, 0]
    assert_true(over_second.accepts(ones))
    assert_false(over_second.accepts(zeros))
    assert_false(same_language(over_y, over_second))


def test_minimisation_identifies_exactly_equal_languages() raises:
    var even = even_ones()
    # The same language with a duplicated state and an unreachable one.
    var delta: List[Int] = [2, 1, 1, 0, 0, 1, 3, 3]
    var accepting: List[Bool] = [True, False, True, False]
    var redundant = Dfa(2, delta, accepting)
    assert_true(same_language(even, redundant))
    assert_equal(minimised(redundant).states(), 2)
    assert_equal(minimised(even).states(), 2)
    # Minimisation is idempotent and language-preserving.
    assert_true(same_language(minimised(redundant), redundant))
    assert_equal(minimised(minimised(redundant)).states(), 2)
    # A different language is not identified with it.
    assert_false(same_language(even, complement(even)))


def test_a_partial_table_is_completed_by_one_rejecting_sink() raises:
    var partial: List[Int] = [0, -1]
    var accepting: List[Bool] = [True]
    var completed = with_sink(2, partial, accepting)
    assert_equal(completed.states(), 2)
    var zeros: List[Int] = [0, 0]
    var one: List[Int] = [1]
    assert_true(completed.accepts(zeros))
    assert_false(completed.accepts(one))
    # The sink absorbs: once inadmissible, always inadmissible.
    var back: List[Int] = [1, 0]
    assert_false(completed.accepts(back))


def test_the_numeration_automaton_is_the_fixed_point() raises:
    """Letter by letter over a prefix, for both a substitution prolongable at a
    letter and one prolongable only at a power."""
    var cases = List[List[List[Int]]]()
    cases.append(tribonacci())
    cases.append(tau_sigma())
    for c in range(len(cases)):
        var sigma = cases[c].copy()
        var point = prolongable_point(sigma)
        var tau = prolongable_form(sigma)
        var u = fixed_point_prefix(sigma, point, 600)
        for n in range(500):
            assert_equal(letter_at(tau, point.letter, n), u[n])
        # The digits are the path, and the path names the letter.
        for n in range(60):
            var path = digits(tau, point.letter, n)
            assert_equal(letter_of_digits(tau, point.letter, path), u[n])
            assert_equal(len(path), levels_to_cover(tau, point.letter, n))


def test_position_counts_are_the_image_lengths() raises:
    """Admissible digit words of length `k` are in bijection with the positions
    of `tau^k(c)`, so counting them through the automaton must reproduce the
    image length computed by substituting."""
    var sigma = tribonacci()
    var point = prolongable_point(sigma)
    var tau = prolongable_form(sigma)
    var expected: List[Int] = [1, 2, 4, 7, 13, 24, 44, 81]
    for k in range(len(expected)):
        assert_equal(image_lengths(tau, k)[point.letter], expected[k])
        assert_equal(positions_of_length(tau, point.letter, k), expected[k])


def test_letter_counts_are_the_incidence_matrix() raises:
    """Digit words ending at a letter count that letter's occurrences, which is
    an entry of a power of the incidence matrix. Two computations that share no
    step: automata on one side, integer matrix powers on the other."""
    var cases = List[List[List[Int]]]()
    cases.append(tribonacci())
    cases.append(tau_sigma())
    for c in range(len(cases)):
        var sigma = cases[c].copy()
        var point = prolongable_point(sigma)
        var tau = prolongable_form(sigma)
        var m = Mat3(substitution_incidence(tau))
        var power = identity3()
        for k in range(6):
            var total = 0
            for target in range(3):
                var counted = occurrences_of_length(tau, point.letter, target, k)
                assert_equal(counted, power.at(target, point.letter))
                total += counted
            assert_equal(total, positions_of_length(tau, point.letter, k))
            power = power * m


def test_a_power_substitution_has_the_same_fixed_point() raises:
    var sigma = tau_sigma()
    var point = prolongable_point(sigma)
    assert_true(point.power > 1)                  # the reason the power is needed
    var tau = prolongable_form(sigma)
    assert_equal(len(tau[point.letter]), len(power_substitution(sigma, point.power)[point.letter]))
    assert_equal(tau[point.letter][0], point.letter)   # prolongable at the letter now
    assert_true(max_image_length(tau) >= max_image_length(sigma))
    var u = fixed_point_prefix(sigma, point, 200)
    for n in range(150):
        assert_equal(letter_at(tau, point.letter, n), u[n])


def main() raises:
    test_the_kernel_is_a_boolean_algebra_of_languages()
    print("[PASS] test_the_kernel_is_a_boolean_algebra_of_languages")
    test_emptiness_reports_the_instance_not_only_the_verdict()
    print("[PASS] test_emptiness_reports_the_instance_not_only_the_verdict")
    test_projection_discharges_one_existential_quantifier()
    print("[PASS] test_projection_discharges_one_existential_quantifier")
    test_minimisation_identifies_exactly_equal_languages()
    print("[PASS] test_minimisation_identifies_exactly_equal_languages")
    test_a_partial_table_is_completed_by_one_rejecting_sink()
    print("[PASS] test_a_partial_table_is_completed_by_one_rejecting_sink")
    test_the_numeration_automaton_is_the_fixed_point()
    print("[PASS] test_the_numeration_automaton_is_the_fixed_point")
    test_position_counts_are_the_image_lengths()
    print("[PASS] test_position_counts_are_the_image_lengths")
    test_letter_counts_are_the_incidence_matrix()
    print("[PASS] test_letter_counts_are_the_incidence_matrix")
    test_a_power_substitution_has_the_same_fixed_point()
    print("[PASS] test_a_power_substitution_has_the_same_fixed_point")
    print("9 automata and numeration tests passed.")
