"""Exact M-adic zero-class filter for the strict-zipper hitting route.

For a level-m boundary hit, a proper-prefix difference d satisfies d = M^m w.
Therefore d lies in the lattice M^m Z^3.  Membership in that lattice is an
exact necessary condition for a hit and is the finite-cokernel shadow of the
non-unit finite-place coordinates.

This module deliberately issues only that one-sided certificate.  A prefix
difference in M^m Z^3 need not equal M^m w, so surviving the filter is unknown,
never a hit.  In the unimodular case M^m Z^3 = Z^3 and the filter correctly
becomes trivial.

The word cap is an implementation boundary.  Exceeding it raises rather than
turning an incomplete enumeration into a negative result.
"""

from finite_linear_algebra.madic_ball import contains
from substitution_dynamics.substitution import Substitution


struct MadicPrefixCandidate(Copyable, Movable):
    """One occurrence-labelled proper-prefix difference in the zero M-adic class."""

    var top_position: Int
    var bottom_position: Int
    var difference: List[Int]

    def __init__(
        out self, top_position: Int, bottom_position: Int, difference: List[Int]
    ):
        self.top_position = top_position
        self.bottom_position = bottom_position
        self.difference = difference.copy()


struct MadicLevelAudit(Copyable, Movable):
    """Exact finite-place filter count for one ordered letter pair and level."""

    var level: Int
    var top_prefix_count: Int
    var bottom_prefix_count: Int
    var pair_count: Int
    var zero_class_count: Int

    def __init__(
        out self,
        level: Int,
        top_prefix_count: Int,
        bottom_prefix_count: Int,
        pair_count: Int,
        zero_class_count: Int,
    ):
        self.level = level
        self.top_prefix_count = top_prefix_count
        self.bottom_prefix_count = bottom_prefix_count
        self.pair_count = pair_count
        self.zero_class_count = zero_class_count


def _validate_letter(letter: Int):
    if letter < 0 or letter >= 3:
        raise Error("strict-zipper M-adic filter expects letters in 0..2")


def _image_with_cap(
    substitution: Substitution, letter: Int, level: Int, word_cap: Int
) raises -> List[Int]:
    if level < 0:
        raise Error("M-adic prefix level must be non-negative")
    if word_cap <= 0:
        raise Error("M-adic prefix word cap must be positive")
    _validate_letter(letter)

    var word: List[Int] = [letter]
    for _ in range(level):
        var image = List[Int]()
        for i in range(len(word)):
            ref block = substitution.images[word[i]]
            if len(image) + len(block) > word_cap:
                raise Error("M-adic prefix expansion exceeded the explicit word cap")
            for j in range(len(block)):
                image.append(block[j])
        word = image^
    return word^


def _proper_prefix_parikhs(word: List[Int]) -> List[List[Int]]:
    """Parikh vectors before positions 0..|word|-1; whole word excluded."""
    var out = List[List[Int]]()
    var current: List[Int] = [0, 0, 0]
    for pos in range(len(word)):
        out.append(current.copy())
        current[word[pos]] += 1
    return out^


def _difference(top: List[Int], bottom: List[Int]) -> List[Int]:
    if len(top) != 3 or len(bottom) != 3:
        raise Error("M-adic prefix difference expects rank three")
    var out = List[Int]()
    for i in range(3):
        out.append(top[i] - bottom[i])
    return out^


def madic_zero_class_candidates(
    sigma: List[List[Int]],
    top_letter: Int,
    bottom_letter: Int,
    level: Int,
    word_cap: Int,
) raises -> List[MadicPrefixCandidate]:
    """Occurrence-labelled d in P_m(i)-P_m(j) with d in M^m Z^3."""
    var substitution = Substitution.checked(sigma)
    if substitution.size != 3:
        raise Error("strict-zipper M-adic filter is currently rank three")

    var top_word = _image_with_cap(substitution, top_letter, level, word_cap)
    var bottom_word = _image_with_cap(
        substitution, bottom_letter, level, word_cap
    )
    var top_prefixes = _proper_prefix_parikhs(top_word)
    var bottom_prefixes = _proper_prefix_parikhs(bottom_word)
    var entries = substitution.incidence()

    var out = List[MadicPrefixCandidate]()
    for i in range(len(top_prefixes)):
        for j in range(len(bottom_prefixes)):
            var d = _difference(top_prefixes[i], bottom_prefixes[j])
            if contains(entries, 3, level, d):
                out.append(MadicPrefixCandidate(i, j, d))
    return out^


def audit_madic_zero_class(
    sigma: List[List[Int]],
    top_letter: Int,
    bottom_letter: Int,
    level: Int,
    word_cap: Int,
) raises -> MadicLevelAudit:
    """Count the strongest level-m finite-cokernel survivors."""
    var substitution = Substitution.checked(sigma)
    if substitution.size != 3:
        raise Error("strict-zipper M-adic filter is currently rank three")
    var top_word = _image_with_cap(substitution, top_letter, level, word_cap)
    var bottom_word = _image_with_cap(
        substitution, bottom_letter, level, word_cap
    )
    var candidates = madic_zero_class_candidates(
        sigma, top_letter, bottom_letter, level, word_cap
    )
    return MadicLevelAudit(
        level,
        len(top_word),
        len(bottom_word),
        len(top_word) * len(bottom_word),
        len(candidates),
    )


def zero_class_survival_proves_hit() -> Bool:
    """A surviving finite-place class is only necessary, never sufficient."""
    return False
