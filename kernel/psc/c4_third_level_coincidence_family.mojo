"""Exact third-level simultaneous strong-coincidence witness for a Pisot family.

Family on letters 0,1,2:
    0 -> 01
    1 -> 1^k 2 1^k
    2 -> 012,     k >= 1.

The UNIFORM proof is in docs/c4-uniform-third-level-coincidence-family-2026-11-04.md.
This bounded checker independently inflates the three actual single-letter
words and checks the closed-form Parikh prefix and the next common letter.
It does not prove pure discrete spectrum or general PSC, and it never
interprets cap exhaustion as a mathematical counterexample.
"""

from psc.bpa import apply_substitution
from psc.words import parikh


struct ThirdLevelCoincidence(Copyable, Movable):
    var parameter: Int
    var cut: Int
    var prefix_parikh: List[Int]
    var word_lengths: List[Int]

    def __init__(
        out self,
        parameter: Int,
        cut: Int,
        prefix_parikh: List[Int],
        word_lengths: List[Int],
    ):
        self.parameter = parameter
        self.cut = cut
        self.prefix_parikh = prefix_parikh.copy()
        self.word_lengths = word_lengths.copy()


def symmetric_middle_family(k: Int) raises -> List[List[Int]]:
    if k <= 0 or k > 16:
        raise Error("family requires 1 <= k <= 16 for bounded Mojo replay")
    var middle = List[Int]()
    for _ in range(k):
        middle.append(1)
    middle.append(2)
    for _ in range(k):
        middle.append(1)
    return [[0, 1], middle.copy(), [0, 1, 2]]


def verify_third_level_coincidence(k: Int) raises -> ThirdLevelCoincidence:
    """Check the actual generation-three literal prefix, for bounded k.

    The common physical cut is p=k(2k+1)+1, and the common prefix
    Parikh vector is (1,2k^2,k); the letter at this cut is 1 in
    each of the three sigma^3(letter) words. Input k<=16 bounds
    all integer arithmetic and all word allocations.
    """
    var sigma = symmetric_middle_family(k)
    var p = k * (2 * k + 1) + 1
    var expected: List[Int] = [1, 2 * k * k, k]
    var lengths = List[Int]()
    for a in range(3):
        var word = sigma[a].copy()
        for _ in range(2):
            word = apply_substitution(sigma, word)
        if p >= len(word):
            raise Error("missing claimed third-level occurrence")
        if word[p] != 1:
            raise Error("third-level common tile is not letter 1")
        var prefix = List[Int]()
        for i in range(p):
            prefix.append(word[i])
        var counts = parikh(prefix)
        if counts != expected:
            raise Error("third-level prefix Parikh claim is false")
        lengths.append(len(word))
    return ThirdLevelCoincidence(k, p, expected, lengths)
