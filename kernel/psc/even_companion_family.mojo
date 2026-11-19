"""Literal certificates for sigma_r = (1, 2, 100 2^r 1).

The uniform word theorem in docs/c4-even-companion-family-2026-11-19.md
uses r >= 3. This executable only verifies supplied, bounded parameters;
the unbounded argument is a separate Lean proof. For even r the companion
matrix is nilpotent modulo two, but neither this arithmetic condition nor
the complete eventual-range square is a certificate of coincidence rank.

Caps refuse to conclude. They never turn an exhausted computation into an
absence of coincidence. Arithmetic/Pisot/range implementations stay in
the existing canonical packages; this module supplies only family words
and the explicit positive prefix certificate.
"""

from psc.bpa import apply_substitution
from psc.words import parikh


def companion_family(r: Int, image_cap: Int = 4096) raises -> List[List[Int]]:
    """Build a family member for 1 <= r and r + 4 <= image_cap."""
    if image_cap < 5 or r < 1 or r > image_cap - 4:
        raise Error("companion family parameter outside the image budget")
    var w: List[Int] = [1, 0, 0]
    for _ in range(r):
        w.append(2)
    w.append(1)
    var sigma: List[List[Int]] = [[1], [2]]
    sigma.append(w^)
    return sigma^


def uniform_prefixes(r: Int, image_cap: Int = 4096) raises -> List[List[Int]]:
    """The two prefixes before the level-three tile 2, for r >= 3.

    P = 211 w 10022, Q = w 22211100. Both have Parikh (4,5,r+3).
    """
    if r < 3:
        raise Error("uniform level-three certificate requires r >= 3")
    var sigma = companion_family(r, image_cap)
    var top: List[Int] = [2, 1, 1]
    top.extend(sigma[2].copy())
    top.extend([1, 0, 0, 2, 2])
    var bottom = sigma[2].copy()
    bottom.extend([2, 2, 2, 1, 1, 1, 0, 0])
    var out = List[List[Int]]()
    out.append(top^)
    out.append(bottom^)
    return out^


def literal_iterate(
    sigma: List[List[Int]], letter: Int, depth: Int, word_cap: Int
) raises -> List[Int]:
    """Inflate a family letter, rejecting before an allocation can exceed cap.

    The bound is conservative (maximum image length times current length).
    A rejection therefore asserts nothing about the requested word.
    """
    if letter < 0 or letter >= 3 or depth < 0 or depth > 4 or word_cap < 1:
        raise Error("companion family literal replay outside the declared budget")
    if len(sigma) != 3:
        raise Error("companion family replay needs three images")
    var longest = 0
    for a in range(3):
        if len(sigma[a]) == 0:
            raise Error("companion family replay rejects an empty image")
        longest = max(longest, len(sigma[a]))
    var word: List[Int] = [letter]
    for _ in range(depth):
        if len(word) > word_cap // longest:
            raise Error("companion family literal word cap exhausted")
        word = apply_substitution(sigma, word)
    return word^


def verify_uniform_witness(r: Int, word_cap: Int = 100000) raises -> List[Int]:
    """Replay P 2 <= sigma^3(1), Q 2 <= sigma^3(2), and equal Parikh.

    Return [level, offset, common letter]. This is a positive witness;
    no assertion of shortestness or spectrum is made here.
    """
    var prefixes = uniform_prefixes(r)
    var sigma = companion_family(r)
    var expected: List[Int] = [4, 5, r + 3]
    if parikh(prefixes[0]) != expected or parikh(prefixes[1]) != expected:
        raise Error("companion family explicit prefixes are not balanced")
    var offset = r + 12
    for track in range(2):
        var word = literal_iterate(sigma, track + 1, 3, word_cap)
        if len(prefixes[track]) != offset or len(word) <= offset:
            raise Error("companion family witness lies outside the literal words")
        for i in range(offset):
            if word[i] != prefixes[track][i]:
                raise Error("companion family prefix decomposition failed")
        if word[offset] != 2:
            raise Error("companion family next literal letters differ")
    return [3, offset, 2]
