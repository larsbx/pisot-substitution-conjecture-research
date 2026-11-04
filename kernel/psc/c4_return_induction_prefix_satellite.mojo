"""Exact return-word induction/Pisot prefix-satellite negative control.

sigma=(01,121,012) has literal sigma(2)=sigma(0)+[2].
Its genuine 0-return substitution is tau=(012,3212,322,02).
The four return images form a prefix code, so NO positive power
has a literal prefix-satellite image pair. The all-power conclusion
is the paper lemma, not a finite-exhaustion conclusion.

Uniform symbolic proof: docs/c4-return-induction-prefix-satellite-counterexample-2026-11-04.md.
This canonical bounded verifier reconstructs ACTUAL ordered physical
return-word images; Python is an independent oracle, not authority.
"""

from psc.bpa import apply_substitution
from psc.words import parikh


def source_sigma() -> List[List[Int]]:
    return [[0, 1], [1, 2, 1], [0, 1, 2]]


def source_return_words() -> List[List[Int]]:
    # Order of first appearance between consecutive zeros of sigma^omega(0).
    return [
        [0, 1, 1, 2, 1, 1, 2, 1],
        [0, 1, 2, 1, 2, 1, 1, 2, 1],
        [0, 1, 2, 1, 2, 1],
        [0, 1, 1, 2, 1]
    ]


def expected_return_substitution() -> List[List[Int]]:
    return [
        [0, 1, 2],
        [3, 2, 1, 2],
        [3, 2, 2],
        [0, 2]
    ]


def _lookup_return_word(
    return_words: List[List[Int]], word: List[Int],
) raises -> Int:
    for idx in range(len(return_words)):
        if return_words[idx] == word:
            return idx
    raise Error("physical return segment is not in supplied complete set")


def induce_marker_zero_return(
    sigma: List[List[Int]], return_words: List[List[Int]],
) raises -> List[List[Int]]:
    """Derive a return substitution by complete ACTUAL marker-zero cuts.

    Requires a supplied complete set; refuses malformed words,
    an unknown child, and unsafe bounds. Does not mistake a finite
    observed return corpus for a proof that the set is complete.
    Marker-zero is required to be the first letter of sigma(0).
    """
    if len(sigma) != 3 or sigma[0] != [0, 1]:
        raise Error("this zero-return kernel requires source initial word 01")
    if len(return_words) == 0 or len(return_words) > 12:
        raise Error("return-word count exceeds finite exact budget")
    for r in range(len(return_words)):
        var word = return_words[r]
        if len(word) == 0 or len(word) > 48 or word[0] != 0:
            raise Error("invalid return word length or missing initial zero")
        for j in range(1, len(word)):
            if word[j] == 0 or word[j] < 0 or word[j] >= 3:
                raise Error("return word has interior zero or malformed letter")
        for other in range(r):
            if return_words[other] == word:
                raise Error("duplicate return word index")
    var result = List[List[Int]]()
    for idx in range(len(return_words)):
        var expanded = apply_substitution(sigma, return_words[idx])
        if len(expanded) == 0 or len(expanded) > 1024 or expanded[0] != 0:
            raise Error("return expansion exceeds budget or has wrong marker")
        var child = List[Int]()
        var current = List[Int]()
        for j in range(len(expanded)):
            var letter = expanded[j]
            if letter == 0 and len(current) != 0:
                child.append(_lookup_return_word(return_words, current))
                current = List[Int]()
            current.append(letter)
        if len(current) == 0:
            raise Error("return expansion ended on incomplete segment")
        child.append(_lookup_return_word(return_words, current))
        if len(child) == 0:
            raise Error("return expansion has no child")
        result.append(child)
    return result^


def _is_proper_prefix(u: List[Int], v: List[Int]) -> Bool:
    if len(u) >= len(v):
        return False
    for i in range(len(u)):
        if u[i] != v[i]:
            return False
    return True


def images_are_prefix_incomparable(
    substitution: List[List[Int]],
) raises -> Bool:
    if len(substitution) == 0 or len(substitution) > 12:
        raise Error("invalid prefix-code image count")
    for i in range(len(substitution)):
        if len(substitution[i]) == 0:
            raise Error("erasing image cannot be a prefix-code input")
        for k in substitution[i]:
            if k < 0 or k >= len(substitution):
                raise Error("image letter outside derived alphabet")
        for j in range(i+1, len(substitution)):
            if substitution[i] == substitution[j]:
                return False
            if _is_proper_prefix(substitution[i], substitution[j]):
                return False
            if _is_proper_prefix(substitution[j], substitution[i]):
                return False
    return True


def _apply_return_substitution(
    tau: List[List[Int]], word: List[Int],
) raises -> List[Int]:
    var out = List[Int]()
    for i in word:
        if i < 0 or i >= len(tau):
            raise Error("malformed return-code symbol")
        for c in tau[i]:
            out.append(c)
    return out^


def verify_exact_return_induction(max_power: Int) raises -> List[List[Int]]:
    """Check the exact four-return system and bounded literal powers.

    max_power=1..6 is a resource budget; no absence claim at arbitrary
    levels follows from this check alone. The prefix-code lemma supplies
    the unbounded deduction.
    """
    if max_power < 1 or max_power > 6:
        raise Error("invalid exact return induction power budget")
    var sigma = source_sigma()
    var returns = source_return_words()
    var tau = induce_marker_zero_return(sigma, returns)
    if tau != expected_return_substitution():
        raise Error("actual induced image does not match the exact return map")
    if not images_are_prefix_incomparable(tau):
        raise Error("return images unexpectedly have literal prefix satellite")
    # The very first return is the segment before the second 0 of sigma^3(0).
    var third: List[Int] = [0]
    for _ in range(3):
        third = apply_substitution(sigma, third)
    var next_zero = -1
    for i in range(1, len(third)):
        if third[i] == 0:
            next_zero = i
            break
    if next_zero < 0:
        raise Error("third iterate has no second marker zero")
    var first_return = List[Int]()
    for i in range(next_zero):
        first_return.append(third[i])
    if first_return != returns[0]:
        raise Error("first return word does not match the actual fixed prefix")
    # All three second images share literal balanced prefix Q=(1,2,1)
    # and symbol 1 at p=4 (not merely a matching physical position).
    for source in range(3):
        var word = apply_substitution(sigma, sigma[source])
        if len(word) <= 4 or word[4] != 1:
            raise Error("source PIP level-two coincidence is absent")
        var prefix = List[Int]()
        for p in range(4):
            prefix.append(word[p])
        if parikh(prefix) != [1, 2, 1]:
            raise Error("source coincidence prefix Parikh differs")
    # Bounded exact word-level intertwining and all-power prefix-code replay.
    var powers = List[List[Int]]()
    for i in range(len(tau)):
        powers.append([i])
    for _ in range(max_power):
        var new_powers = List[List[Int]]()
        for i in range(len(tau)):
            new_powers.append(_apply_return_substitution(tau, powers[i]))
        powers = new_powers
        if not images_are_prefix_incomparable(powers):
            raise Error("derived images at bounded power have a prefix pair")
    return tau^
