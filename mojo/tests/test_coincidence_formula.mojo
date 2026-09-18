"""Strong coincidence, decided by the formula and checked against the images.

The automaton answers `SC(i, j)` by non-emptiness, and everything pinned here
is a way of not taking its word for it. A witness is split back into two
Dumont-Thomas paths and the Parikh vectors and letters are recomputed from the
substitution alone. The level it reports is compared with a direct search
through `sigma^k(i)` and `sigma^k(j)` -- the definition, carried out by
substituting -- including on a specimen whose pairs first coincide at level 15.
And nothing shorter than the reported level may be accepted, which is checked
by enumerating every pair word below it rather than inferred from the search.

The pruning bound is `slack = 1` here because it is derived rather than
estimated: `v^T delta' = beta v^T delta + v^T t` is an identity, not an
asymptotic ratio. Widening it must therefore change nothing, and that is
checked on the deepest specimen these tests carry.
"""

from std.testing import assert_equal, assert_false, assert_true

from psc.automata import minimised, same_language, witness
from psc.bpa import apply_substitution
from psc.claim_tests import require_contract
from psc.coincidence_formula import (
    coincidence_automaton,
    coincidence_automaton_with,
    coincidence_level,
    coincidence_witness,
    coincidence_witness_with,
    pair_paths,
    path_letter,
    path_prefix_parikh,
    strong_coincidence_level,
)
from psc.dumont_thomas import image_lengths, max_image_length
from psc.words import ALPHABET


def specimens() -> List[List[List[Int]]]:
    """Four corpus substitutions whose pairs first coincide at levels 1, 3, 14
    and 15: the tribonacci substitution, one middling specimen, and the two
    whose Perron root is small enough to make a deep search cheap."""
    var out = List[List[List[Int]]]()
    out.append([[0, 1], [0, 2], [0]])
    out.append([[1], [0, 1, 2], [0, 1, 0]])
    out.append([[1], [2], [0, 1]])
    out.append([[2], [0], [0, 1]])
    return out^


def least_level_by_images(
    sigma: List[List[Int]], top: Int, bottom: Int, max_level: Int
) raises -> Int:
    """The definition, carried out by substituting: the least `k` at which
    `sigma^k(top)` and `sigma^k(bottom)` carry one letter at one position after
    prefixes of one Parikh vector."""
    var above: List[Int] = [top]
    var below: List[Int] = [bottom]
    for level in range(max_level + 1):
        var counted_above = List[Int](length=ALPHABET, fill=0)
        var counted_below = List[Int](length=ALPHABET, fill=0)
        var shorter = len(above) if len(above) < len(below) else len(below)
        for p in range(shorter):
            var balanced = True
            for letter in range(ALPHABET):
                if counted_above[letter] != counted_below[letter]:
                    balanced = False
            if balanced and above[p] == below[p]:
                return level
            counted_above[above[p]] += 1
            counted_below[below[p]] += 1
        above = apply_substitution(sigma, above)
        below = apply_substitution(sigma, below)
    return -1


def test_a_witness_is_a_coincidence_the_substitution_confirms() raises:
    var corpus = specimens()
    for s in range(len(corpus)):
        ref sigma = corpus[s]
        var radix = max_image_length(sigma)
        for i in range(ALPHABET):
            for j in range(ALPHABET):
                var found = coincidence_witness(sigma, i, j)
                assert_false(found.empty)
                var paths = pair_paths(radix, found.word)
                assert_equal(len(paths[0]), len(found.word))
                assert_equal(
                    path_letter(sigma, i, paths[0]),
                    path_letter(sigma, j, paths[1]),
                )
                var above = path_prefix_parikh(sigma, i, paths[0])
                var below = path_prefix_parikh(sigma, j, paths[1])
                for letter in range(ALPHABET):
                    assert_equal(above[letter], below[letter])


def test_the_level_is_the_least_a_search_through_the_images_finds() raises:
    var corpus = specimens()
    var expected: List[Int] = [1, 3, 14, 15]
    for s in range(len(corpus)):
        ref sigma = corpus[s]
        assert_equal(strong_coincidence_level(sigma), expected[s])
        for i in range(ALPHABET):
            for j in range(ALPHABET):
                assert_equal(
                    coincidence_level(sigma, i, j),
                    least_level_by_images(sigma, i, j, 20),
                )


def test_nothing_shorter_than_the_level_is_accepted() raises:
    """The search returns a shortest word, so every shorter one must be
    rejected. Enumerated rather than inferred."""
    var sigma = specimens()[1].copy()
    var radix = max_image_length(sigma)
    var letters = radix * radix
    var automaton = coincidence_automaton(sigma, 0, 1)
    var level = coincidence_level(sigma, 0, 1)
    assert_true(level > 1)
    var words: List[List[Int]] = [List[Int]()]
    for _ in range(level):
        var longer = List[List[Int]]()
        for w in range(len(words)):
            for c in range(letters):
                var next = words[w].copy()
                next.append(c)
                longer.append(next^)
        for w in range(len(words)):
            assert_false(automaton.accepts(words[w]))
        words = longer^
    var accepted = 0
    for w in range(len(words)):
        if automaton.accepts(words[w]):
            accepted += 1
    assert_true(accepted > 0)


def test_the_parikh_track_is_the_prefix_it_names() raises:
    """`path_prefix_parikh` against counting the letters of the image directly,
    over every admissible path of a fixed length."""
    var sigma = specimens()[1].copy()
    var level = 3
    var lengths = image_lengths(sigma, level)
    for letter in range(ALPHABET):
        var image: List[Int] = [letter]
        for _ in range(level):
            image = apply_substitution(sigma, image)
        assert_equal(len(image), lengths[letter])
        var counted = List[Int](length=ALPHABET, fill=0)
        for position in range(len(image)):
            var path = _path_of(sigma, letter, level, position)
            var parikh = path_prefix_parikh(sigma, letter, path)
            for a in range(ALPHABET):
                assert_equal(parikh[a], counted[a])
            assert_equal(path_letter(sigma, letter, path), image[position])
            counted[image[position]] += 1


def _path_of(
    sigma: List[List[Int]], letter: Int, level: Int, position: Int
) raises -> List[Int]:
    """The level-`level` Dumont-Thomas path of a position, by descent."""
    var out = List[Int]()
    var current = letter
    var rest = position
    for step in range(level, 0, -1):
        var lengths = image_lengths(sigma, step - 1)
        var index = 0
        while index < len(sigma[current]):
            var block = lengths[sigma[current][index]]
            if rest < block:
                break
            rest -= block
            index += 1
        if index >= len(sigma[current]):
            raise Error("position escaped its block")
        out.append(index)
        current = sigma[current][index]
    return out^


def test_widening_the_pruning_bound_does_not_move_the_language() raises:
    var sigma = specimens()[3].copy()
    var reference = minimised(coincidence_automaton_with(sigma, 0, 1, 1, 1 << 20))
    for slack in range(2, 4):
        var other = coincidence_automaton_with(sigma, 0, 1, slack, 1 << 20)
        assert_true(other.states() > reference.states())
        assert_true(same_language(reference, minimised(other)))


def test_malformed_input_raises() raises:
    var sigma = specimens()[0].copy()

    var not_a_letter = False
    try:
        _ = coincidence_automaton(sigma, 0, ALPHABET)
    except:
        not_a_letter = True
    assert_true(not_a_letter)

    var no_room = False
    try:
        _ = coincidence_automaton_with(sigma, 0, 1, 1, 1)
    except:
        no_room = True
    assert_true(no_room)

    var past_the_cap = False
    try:
        _ = coincidence_automaton_with(specimens()[3].copy(), 0, 1, 1, 8)
    except:
        past_the_cap = True
    assert_true(past_the_cap)

    var search_past_the_cap = False
    try:
        _ = coincidence_witness_with(specimens()[3].copy(), 0, 1, 1, 4)
    except:
        search_past_the_cap = True
    assert_true(search_past_the_cap)

    var bad_digit = False
    try:
        _ = pair_paths(3, [9])
    except:
        bad_digit = True
    assert_true(bad_digit)

    var inadmissible = False
    try:
        _ = path_prefix_parikh(sigma, 2, [1])
    except:
        inadmissible = True
    assert_true(inadmissible)


def test_the_search_and_the_whole_language_agree() raises:
    """`coincidence_witness` stops at the first accepting state instead of
    closing the state set, so the two must still give one answer."""
    var corpus = specimens()
    for s in range(len(corpus)):
        ref sigma = corpus[s]
        for i in range(ALPHABET):
            for j in range(ALPHABET):
                var searched = coincidence_witness(sigma, i, j)
                var built = witness(coincidence_automaton(sigma, i, j))
                assert_equal(searched.empty, built.empty)
                assert_equal(len(searched.word), len(built.word))
                assert_true(coincidence_automaton(sigma, i, j).accepts(searched.word))


def main() raises:
    test_a_witness_is_a_coincidence_the_substitution_confirms()
    print("[PASS] test_a_witness_is_a_coincidence_the_substitution_confirms")
    test_the_level_is_the_least_a_search_through_the_images_finds()
    print("[PASS] test_the_level_is_the_least_a_search_through_the_images_finds")
    test_nothing_shorter_than_the_level_is_accepted()
    print("[PASS] test_nothing_shorter_than_the_level_is_accepted")
    test_the_parikh_track_is_the_prefix_it_names()
    print("[PASS] test_the_parikh_track_is_the_prefix_it_names")
    test_widening_the_pruning_bound_does_not_move_the_language()
    print("[PASS] test_widening_the_pruning_bound_does_not_move_the_language")
    test_malformed_input_raises()
    print("[PASS] test_malformed_input_raises")
    test_the_search_and_the_whole_language_agree()
    print("[PASS] test_the_search_and_the_whole_language_agree")
    print("7 coincidence formula tests passed.")
    require_contract("strong coincidence is decided per substitution by one automaton over synchronous Dumont-Thomas path pairs carrying the Parikh difference, whose state set is finite by the Pisot argument stated in psc/coincidence_formula.mojo rather than by an imported theorem; every witness is checked against the images themselves, and deciding the condition for a specimen is not deciding it for the alphabet-3 Pisot family, which stays open")
