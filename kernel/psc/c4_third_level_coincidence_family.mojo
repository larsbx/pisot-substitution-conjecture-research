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


struct AsymmetricThirdLevelCoincidence(Copyable, Movable):
    var left_run: Int
    var right_run: Int
    var cut: Int
    var prefix_parikh: List[Int]
    var word_lengths: List[Int]

    def __init__(
        out self, left_run: Int, right_run: Int, cut: Int,
        prefix_parikh: List[Int], word_lengths: List[Int],
    ):
        self.left_run = left_run
        self.right_run = right_run
        self.cut = cut
        self.prefix_parikh = prefix_parikh.copy()
        self.word_lengths = word_lengths.copy()


def asymmetric_middle_family(left_run: Int, right_run: Int) raises -> List[List[Int]]:
    """The exact asymmetry is in word order, not the incidence matrix.

    For each fixed s=left_run+right_run all 1<=left_run<s have the
    same primitive irreducible Pisot incidence, but different
    literal common-coincidence occurrence addresses.
    """
    if left_run <= 0 or right_run <= 0 or left_run > 16 or right_run > 16:
        raise Error("asymmetric family requires 1 <= left,right <= 16")
    var middle = List[Int]()
    for _ in range(left_run):
        middle.append(1)
    middle.append(2)
    for _ in range(right_run):
        middle.append(1)
    return [[0, 1], middle.copy(), [0, 1, 2]]


def verify_asymmetric_third_level(
    left_run: Int, right_run: Int,
) raises -> AsymmetricThirdLevelCoincidence:
    """Check the true third images at p=left*(left+right+1)+1.

    The exact common prefix Parikh vector is
    (1,left*(left+right),left), with next letter 1.
    Bounded inputs protect machine arithmetic and allocations;
    the source-word theorem is uniform for all positive integers.
    """
    var sigma = asymmetric_middle_family(left_run, right_run)
    var p = left_run * (left_run + right_run + 1) + 1
    var expected: List[Int] = [
        1, left_run * (left_run + right_run), left_run,
    ]
    var lengths = List[Int]()
    for a in range(3):
        var word = sigma[a].copy()
        for _ in range(2):
            word = apply_substitution(sigma, word)
        if p >= len(word):
            raise Error("missing asymmetric third-level common occurrence")
        if word[p] != 1:
            raise Error("asymmetric common letter is not 1")
        var prefix = List[Int]()
        for i in range(p):
            prefix.append(word[i])
        if parikh(prefix) != expected:
            raise Error("asymmetric third-level Parikh prefix mismatch")
        lengths.append(len(word))
    return AsymmetricThirdLevelCoincidence(
        left_run, right_run, p, expected, lengths,
    )


def symmetric_middle_family(k: Int) raises -> List[List[Int]]:
    """Retain the published symmetric API through the new uniform kernel."""
    return asymmetric_middle_family(k, k)


def verify_third_level_coincidence(k: Int) raises -> ThirdLevelCoincidence:
    """Backward-compatible symmetric exact verifier."""
    var result = verify_asymmetric_third_level(k, k)
    return ThirdLevelCoincidence(
        k, result.cut, result.prefix_parikh.copy(),
        result.word_lengths.copy(),
    )


struct NonnegativeRunCoincidence(Copyable, Movable):
    var left_run: Int
    var right_run: Int
    var level: Int
    var cut: Int
    var prefix_parikh: List[Int]
    var common_letter: Int
    var word_lengths: List[Int]

    def __init__(
        out self, left_run: Int, right_run: Int,
        level: Int, cut: Int, prefix_parikh: List[Int],
        common_letter: Int, word_lengths: List[Int],
    ):
        self.left_run = left_run
        self.right_run = right_run
        self.level = level
        self.cut = cut
        self.prefix_parikh = prefix_parikh.copy()
        self.common_letter = common_letter
        self.word_lengths = word_lengths.copy()


def nonnegative_middle_family(left_run: Int, right_run: Int) raises -> List[List[Int]]:
    """Complete nonnegative-run extension: s=left+right >=1.

    This is a separate API; the existing strictly positive
    asymmetric and symmetric entrypoints keep their old refusal domain.
    The implementation cap is unrelated to the uniform paper theorem.
    """
    if left_run < 0 or right_run < 0 or left_run > 16 or right_run > 16:
        raise Error("nonnegative run outside bounded verification domain")
    if left_run + right_run == 0:
        raise Error("zero sum has singular incidence; outside Pisot family")
    var middle = List[Int]()
    for _ in range(left_run):
        middle.append(1)
    middle.append(2)
    for _ in range(right_run):
        middle.append(1)
    return [[0, 1], middle.copy(), [0, 1, 2]]


def verify_nonnegative_runs(
    left_run: Int, right_run: Int,
) raises -> NonnegativeRunCoincidence:
    """Literal uniform bounded witness of simultaneous coincidence.

    a=0, b>=1: depth 2, cut 0, next letter 0.
    a>=1, b>=1: depth 3, cut a(a+b+1)+1, letter 1.
    a>=1, b=0: depth 4, cut a^3+a^2+4a+1, letter 1.
    Every specified cut uses exact Parikh prefixes in ALL three
    source images, not a mere character-index coincidence.
    """
    var sigma = nonnegative_middle_family(left_run, right_run)
    var depth = 3
    var cut = 0
    var letter = 1
    var expected: List[Int] = [0, 0, 0]
    if left_run == 0:
        depth = 2
        cut = 0
        letter = 0
    elif right_run == 0:
        depth = 4
        cut = (
            left_run * left_run * left_run
            + left_run * left_run + 4 * left_run + 1
        )
        expected = [
            left_run + 1,
            left_run * left_run * left_run + 2 * left_run,
            left_run * (left_run + 1),
        ]
    else:
        cut = left_run * (left_run + right_run + 1) + 1
        expected = [
            1, left_run * (left_run + right_run), left_run,
        ]

    var lengths = List[Int]()
    for source in range(3):
        var word: List[Int] = [source]
        for _ in range(depth):
            word = apply_substitution(sigma, word)
        if cut >= len(word) or word[cut] != letter:
            raise Error("uniform nonnegative-run common tile not realized")
        var prefix = List[Int]()
        for j in range(cut):
            prefix.append(word[j])
        if parikh(prefix) != expected:
            raise Error("uniform nonnegative-run prefix Parikh mismatch")
        lengths.append(len(word))
    return NonnegativeRunCoincidence(
        left_run, right_run, depth, cut, expected, letter, lengths,
    )
