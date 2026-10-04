"""The Dumont-Thomas numeration of a fixed point, as an automaton.

A primitive substitution `tau` prolongable at `c` has a fixed point
`u = tau^inf(c)`, and every position `n < |tau^k(c)|` has exactly one
decomposition along the prefix tree of `tau^k(c)`: read `tau(c) = b_0 b_1 ...`,
find the block `tau^(k-1)(b_j)` that contains `n`, keep `j` as a digit, and
recurse into that block. The digits `d_(k-1) ... d_0` are the Dumont-Thomas
representation of `n`, and the letter reached after the last digit is `u_n`.

Read as an automaton the recursion is small: the states are the letters, the
digit `j` moves from `a` to the `j`-th letter of `tau(a)`, and a digit past the
end of `tau(a)` is inadmissible. So `u` is a letter-valued output of a finite
automaton reading these digits, and the positions carrying a given letter are a
recognisable set -- the presentation a first-order decision procedure over this
numeration would quantify over.

What this module establishes is finite and checkable: the automaton reproduces
the fixed point letter by letter, admissible digit words of length `k` are in
bijection with positions of `tau^k(c)`, and the words ending at a letter are
counted by the incidence matrix. What it does *not* supply is the step from a
recognisable set to a decision procedure for first-order statements, which
needs recognisability of addition in the numeration; that is an imported
theorem, gated in
`docs/automatic-sequence-route-literature-gate-2026-09-17.md`.
"""

from finite_exact.bigint_z import BigZ
from psc.automata import Dfa, accepted_count, with_sink
from psc.oa_overlap_types import ProlongablePoint, apply_substitution, prolongable_point
from psc.words import ALPHABET


def power_substitution(sigma: List[List[Int]], power: Int) raises -> List[List[Int]]:
    """`sigma^power`, so a substitution prolongable only at a power becomes one
    prolongable at a letter, which is what the numeration needs."""
    if power < 1:
        raise Error("a substitution power is at least one")
    var out = List[List[Int]]()
    for a in range(len(sigma)):
        var image: List[Int] = [a]
        for _ in range(power):
            image = apply_substitution(sigma, image)
        out.append(image^)
    return out^


def prolongable_form(sigma: List[List[Int]]) raises -> List[List[Int]]:
    """The power of `sigma` that its least prolongable point makes prolongable."""
    return power_substitution(sigma, prolongable_point(sigma).power)


def max_image_length(tau: List[List[Int]]) -> Int:
    var longest = 0
    for a in range(len(tau)):
        if len(tau[a]) > longest:
            longest = len(tau[a])
    return longest


def image_lengths(tau: List[List[Int]], level: Int) raises -> List[Int]:
    """`|tau^level(a)|` for each letter `a`, by repeated substitution counts.

    These stay machine integers because they are positions: a position indexes
    a word this repository can hold. The growth is still exponential, so the
    accumulation is checked and a level past the range raises rather than
    wrapping -- a wrapped length would silently misplace every digit computed
    from it."""
    if level < 0:
        raise Error("a level is not negative")
    var lengths = List[Int](length=len(tau), fill=1)
    for _ in range(level):
        var next = List[Int](length=len(tau), fill=0)
        for a in range(len(tau)):
            for i in range(len(tau[a])):
                var add = lengths[tau[a][i]]
                if next[a] > Int.MAX - add:
                    raise Error("image length exceeds the machine integer range")
                next[a] += add
        lengths = next^
    return lengths^


def levels_to_cover(tau: List[List[Int]], letter: Int, position: Int) raises -> Int:
    """The least `k` with `position < |tau^k(letter)|`."""
    if position < 0:
        raise Error("a position is not negative")
    var k = 0
    while True:
        if image_lengths(tau, k)[letter] > position:
            return k
        k += 1
        if k > 64:
            raise Error("position is beyond the level cap")


def digits(tau: List[List[Int]], letter: Int, position: Int) raises -> List[Int]:
    """The Dumont-Thomas digits of `position`, most significant first.

    The digit at each step is the index of the child block containing what is
    left of the position; the recursion ends with nothing left, at the letter
    that stands there."""
    var level = levels_to_cover(tau, letter, position)
    var out = List[Int]()
    var current = letter
    var rest = position
    for step in range(level, 0, -1):
        var lengths = image_lengths(tau, step - 1)
        ref image = tau[current]
        var index = 0
        while index < len(image):
            var block = lengths[image[index]]
            if rest < block:
                break
            rest -= block
            index += 1
        if index >= len(image):
            raise Error("position escaped its block: the lengths disagree")
        out.append(index)
        current = image[index]
    return out^


def letter_at(tau: List[List[Int]], letter: Int, position: Int) raises -> Int:
    """`u_position` for the fixed point of `tau` at `letter`, by the digits."""
    var path = digits(tau, letter, position)
    var current = letter
    for i in range(len(path)):
        current = tau[current][path[i]]
    return current


def letter_of_digits(tau: List[List[Int]], letter: Int, path: List[Int]) raises -> Int:
    """Where an admissible digit word ends, which is the letter it names."""
    var current = letter
    for i in range(len(path)):
        if path[i] < 0 or path[i] >= len(tau[current]):
            raise Error("inadmissible digit for this letter")
        current = tau[current][path[i]]
    return current


def numeration_automaton(tau: List[List[Int]], letter: Int) raises -> Dfa:
    """Admissible digit words from `letter`: states are letters, a digit past
    the end of an image is inadmissible and falls into the sink."""
    _require_letter(tau, letter)
    var radix = max_image_length(tau)
    var partial = List[Int]()
    for a in range(len(tau)):
        for d in range(radix):
            partial.append(tau[a][d] if d < len(tau[a]) else -1)
    var accepting = List[Bool](length=len(tau), fill=True)
    var reordered = _start_at(partial, accepting, radix, letter)
    return with_sink(radix, reordered[0], _bools(reordered[1]))


def letter_automaton(tau: List[List[Int]], letter: Int, target: Int) raises -> Dfa:
    """Admissible digit words from `letter` that end at `target`: the positions
    of the fixed point carrying that letter, as a recognisable set."""
    _require_letter(tau, letter)
    _require_letter(tau, target)
    var radix = max_image_length(tau)
    var partial = List[Int]()
    for a in range(len(tau)):
        for d in range(radix):
            partial.append(tau[a][d] if d < len(tau[a]) else -1)
    var accepting = List[Bool]()
    for a in range(len(tau)):
        accepting.append(a == target)
    var reordered = _start_at(partial, accepting, radix, letter)
    return with_sink(radix, reordered[0], _bools(reordered[1]))


def _require_letter(tau: List[List[Int]], letter: Int) raises:
    """A letter outside the alphabet is refused rather than indexed with.

    These two entry points renumber the state set around the letter they are
    given, so an out-of-range one reaches a bare list index and aborts the
    process instead of raising -- a caller assembling a formula out of them
    would get a crash where it should get an error it can report."""
    if letter < 0 or letter >= len(tau):
        raise Error("letter lies outside the substitution's alphabet")


def _start_at(
    partial: List[Int], accepting: List[Bool], radix: Int, letter: Int
) -> List[List[Int]]:
    """Renumber so `letter` is state 0, which `Dfa` takes as the start.

    Returned as two integer rows because a Mojo function returns one type: the
    table, then the accepting flags as 0/1."""
    var states = len(accepting)
    var relabel = List[Int](length=states, fill=0)
    relabel[letter] = 0
    var used = 1
    for a in range(states):
        if a != letter:
            relabel[a] = used
            used += 1
    var table = List[Int](length=states * radix, fill=-1)
    var flags = List[Int](length=states, fill=0)
    for a in range(states):
        flags[relabel[a]] = 1 if accepting[a] else 0
        for d in range(radix):
            var to = partial[a * radix + d]
            table[relabel[a] * radix + d] = -1 if to < 0 else relabel[to]
    var out = List[List[Int]]()
    out.append(table^)
    out.append(flags^)
    return out^


def _bools(flags: List[Int]) -> List[Bool]:
    var out = List[Bool]()
    for i in range(len(flags)):
        out.append(flags[i] == 1)
    return out^


def positions_of_length(tau: List[List[Int]], letter: Int, level: Int) raises -> BigZ:
    """`|tau^level(letter)|` counted through the automaton rather than by
    substitution: the two must agree, and that is the content of the
    numeration being a bijection on positions.

    Exact and unbounded, like the count beneath it: image lengths grow like the
    Perron root to the level, so the type has to carry more than a machine
    integer for a level a caller may legitimately ask about."""
    return accepted_count(numeration_automaton(tau, letter), level)


def occurrences_of_length(
    tau: List[List[Int]], letter: Int, target: Int, level: Int
) raises -> BigZ:
    """How many positions of `tau^level(letter)` carry `target`, through the
    automaton. The incidence matrix counts the same thing."""
    return accepted_count(letter_automaton(tau, letter, target), level)
