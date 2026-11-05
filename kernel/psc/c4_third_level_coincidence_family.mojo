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


struct ClosedRunCoincidence(Copyable, Movable):
    var left_run: Int
    var right_run: Int
    var generation: Int
    var cut: Int
    var next_letter: Int
    var prefix_parikh: List[Int]
    var word_lengths: List[Int]

    def __init__(
        out self, left_run: Int, right_run: Int, generation: Int,
        cut: Int, next_letter: Int, prefix_parikh: List[Int],
        word_lengths: List[Int],
    ):
        self.left_run = left_run
        self.right_run = right_run
        self.generation = generation
        self.cut = cut
        self.next_letter = next_letter
        self.prefix_parikh = prefix_parikh.copy()
        self.word_lengths = word_lengths.copy()


def closed_run_middle_family(left_run: Int, right_run: Int) raises -> List[List[Int]]:
    """Allow the one-sided zero-run boundaries without admitting s=0.

    Same incidence for any split of fixed s=left_run+right_run>=1.
    The 16-cap is a checked-executable budget, not the paper theorem.
    """
    if left_run < 0 or right_run < 0 or left_run > 16 or right_run > 16:
        raise Error("closed-run family outside bounded input")
    if left_run + right_run == 0:
        raise Error("closed-run family requires a nonzero total run")
    var middle = List[Int]()
    for _ in range(left_run):
        middle.append(1)
    middle.append(2)
    for _ in range(right_run):
        middle.append(1)
    return [[0, 1], middle.copy(), [0, 1, 2]]


def verify_closed_run_coincidence(
    left_run: Int, right_run: Int,
) raises -> ClosedRunCoincidence:
    """All nonnegative run splits with positive sum, uniform generation <=4.

    a=0: generation 2, index 0, next 0.
    a,b>0: generation 3, index a(a+b+1)+1, next 1.
    b=0: generation 4, index a^3+a^2+4a+1, next 1.
    Each is checked against *all three* complete actual letter images,
    with an exact prefix Parikh vector, not an endpoint-only match.
    """
    var sigma = closed_run_middle_family(left_run, right_run)
    var generation = 3
    var p = 0
    var next_letter = 1
    var expected: List[Int] = [0, 0, 0]
    if left_run == 0:
        generation = 2
        p = 0
        next_letter = 0
    elif right_run == 0:
        generation = 4
        p = left_run * left_run * left_run + left_run * left_run + 4 * left_run + 1
        expected = [
            left_run + 1,
            left_run * left_run * left_run + 2 * left_run,
            left_run * (left_run + 1),
        ]
    else:
        p = left_run * (left_run + right_run + 1) + 1
        expected = [
            1, left_run * (left_run + right_run), left_run,
        ]

    var lengths = List[Int]()
    for a in range(3):
        var word: List[Int] = [a]
        for _ in range(generation):
            word = apply_substitution(sigma, word)
        if p >= len(word) or word[p] != next_letter:
            raise Error("closed-run coincidence fails on actual letter word")
        var prefix = List[Int]()
        for i in range(p):
            prefix.append(word[i])
        if parikh(prefix) != expected:
            raise Error("closed-run coincidence has incorrect prefix Parikh")
        lengths.append(len(word))
    return ClosedRunCoincidence(
        left_run, right_run, generation, p, next_letter, expected, lengths,
    )


def asymmetric_middle_family(left_run: Int, right_run: Int) raises -> List[List[Int]]:
    """The exact asymmetry is in word order, not the incidence matrix.

    For each fixed s=left_run+right_run all 1<=left_run<s have the
    same primitive irreducible Pisot incidence, but different
    literal common-coincidence occurrence addresses.
    """
    if left_run <= 0 or right_run <= 0 or left_run > 16 or right_run > 16:
        raise Error("asymmetric family requires 1 <= left,right <= 16")
    return closed_run_middle_family(left_run, right_run)


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




def reversed_closed_run_family(left_run: Int, right_run: Int) raises -> List[List[Int]]:
    """Wordwise reversal of closed-run family, independently prefix-certified.

    The executable uses a tighter 8-per-run/12-total cap for level-four
    literal allocation. The theorem is for all nonnegative parameters.
    """
    if left_run < 0 or right_run < 0 or left_run > 8 or right_run > 8:
        raise Error("reversed-run family outside bounded input")
    if left_run + right_run == 0 or left_run + right_run > 12:
        raise Error("reversed-run total run outside bounded budget")
    var original = closed_run_middle_family(left_run, right_run)
    var reversed = List[List[Int]]()
    for letter in range(3):
        var old_word = original[letter].copy()
        var new_word = List[Int]()
        for j in range(len(old_word)):
            new_word.append(old_word[len(old_word) - 1 - j])
        reversed.append(new_word^)
    return reversed^


def verify_reversed_closed_run_coincidence(
    left_run: Int, right_run: Int,
) raises -> ClosedRunCoincidence:
    """All reverse closed-run Pisot words have a prefix witness by level 4.

    Distinguish b=0, (a,b)=(0,1), a=0,b>=2,
    a>=1,b=1, and a>=1,b>=2. Never infer the result merely
    from word reversal of a left-coincident substitution.
    """
    var sigma = reversed_closed_run_family(left_run, right_run)
    var s = left_run + right_run
    var generation = 4
    var p = 0
    var z = 1
    var expected: List[Int] = [0, 0, 0]
    if right_run == 0:
        generation = 2
        z = 2
    elif left_run == 0:
        z = 2
        if right_run == 1:
            p = 9
            expected = [2, 4, 3]
        else:
            var b = right_run
            p = b * b * b + b * b + 5 * b + 6
            expected = [
                b + 2, b * b * b + 3 * b + 2, b * b + b + 2,
            ]
    elif right_run == 1:
        generation = 3
        p = left_run + 5
        expected = [1, left_run + 2, 2]
    else:
        var b = right_run
        p = b * (s * s + 2 * s + 4) + 2 * s + 10
        expected = [
            b + 3,
            b * s * s + b * s + 2 * s + b + 3,
            b * s + 2 * b + 4,
        ]
    var lengths = List[Int]()
    for letter in range(3):
        var word: List[Int] = [letter]
        for _ in range(generation):
            word = apply_substitution(sigma, word)
        if p >= len(word) or word[p] != z:
            raise Error("reversed-run coincidence absent in literal image")
        var prefix = List[Int]()
        for j in range(p):
            prefix.append(word[j])
        if parikh(prefix) != expected:
            raise Error("reversed-run common prefix Parikh mismatch")
        lengths.append(len(word))
    return ClosedRunCoincidence(
        left_run, right_run, generation, p, z, expected, lengths,
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
