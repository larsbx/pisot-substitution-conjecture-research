"""Relabelling and reversal symmetries of alphabet-3 words, pairs and substitutions.

The symmetric group on `{0,1,2}` acts on a balanced pair by relabelling both
sides, and on a substitution by conjugation `sigma^p(p(a)) = p(sigma(a))`;
word reversal is a further involution commuting with inflation. Catalogue
taxonomies quote orbits under these actions, so the canonical representative
is the lexicographically least element of the orbit, with a pair first
normalised so that `(u, v)` and `(v, u)` coincide. Comparison is exact word
lexicographic order (a proper prefix precedes its extensions).
"""

from psc.words import ALPHABET, Pair


def word_less(a: List[Int], b: List[Int]) -> Bool:
    """Lexicographic order; a proper prefix precedes its extensions."""
    var n = len(a) if len(a) < len(b) else len(b)
    for i in range(n):
        if a[i] != b[i]:
            return a[i] < b[i]
    return len(a) < len(b)


def permutations(size: Int) -> List[List[Int]]:
    """The `size!` permutations of `0 .. size-1` as images `[p(0), ...]`,
    in lexicographic order, built by insertion into every position."""
    var out: List[List[Int]] = [List[Int]()]
    for letter in range(size):
        var grown = List[List[Int]]()
        for i in range(len(out)):
            for slot in range(len(out[i]) + 1):
                var extended = List[Int](capacity=len(out[i]) + 1)
                for j in range(slot):
                    extended.append(out[i][j])
                extended.append(letter)
                for j in range(slot, len(out[i])):
                    extended.append(out[i][j])
                grown.append(extended^)
        out = grown^
    sort(out, word_less)
    return out^


def permutations3() -> List[List[Int]]:
    """The six permutations of `{0,1,2}`, lexicographically."""
    return permutations(ALPHABET)


def inverse_permutation(p: List[Int]) -> List[Int]:
    var inv = List[Int](length=len(p), fill=0)
    for old in range(len(p)):
        inv[p[old]] = old
    return inv^


def relabel(w: List[Int], p: List[Int]) -> List[Int]:
    var out = List[Int](capacity=len(w))
    for i in range(len(w)):
        out.append(p[w[i]])
    return out^


def reversed_word(w: List[Int]) -> List[Int]:
    var out = List[Int](capacity=len(w))
    for i in range(len(w) - 1, -1, -1):
        out.append(w[i])
    return out^


def normalised_pair(u: List[Int], v: List[Int]) -> Pair:
    """`(u, v)` with the lexicographically smaller side first."""
    return Pair(v, u) if word_less(v, u) else Pair(u, v)


def pair_less(p: Pair, q: Pair) -> Bool:
    if p.u != q.u:
        return word_less(p.u, q.u)
    return word_less(p.v, q.v)


def relabelled_pair(p: Pair, perm: List[Int]) -> Pair:
    return normalised_pair(relabel(p.u, perm), relabel(p.v, perm))


def reversed_pair(p: Pair) -> Pair:
    return normalised_pair(reversed_word(p.u), reversed_word(p.v))


def canonical_pair(p: Pair) -> Pair:
    """Least normalised relabelling of `p`."""
    var perms = permutations3()
    var best = relabelled_pair(p, perms[0])
    for i in range(1, len(perms)):
        var candidate = relabelled_pair(p, perms[i])
        if pair_less(candidate, best):
            best = candidate^
    return best^


def conjugated_substitution(sigma: List[List[Int]], perm: List[Int]) -> List[List[Int]]:
    """`sigma^perm` with `sigma^perm(perm(a)) = perm(sigma(a))`."""
    var inv = inverse_permutation(perm)
    var out = List[List[Int]]()
    for letter in range(ALPHABET):
        out.append(relabel(sigma[inv[letter]], perm))
    return out^


def reversed_substitution(sigma: List[List[Int]]) -> List[List[Int]]:
    var out = List[List[Int]]()
    for a in range(len(sigma)):
        out.append(reversed_word(sigma[a]))
    return out^


def substitution_less(s: List[List[Int]], t: List[List[Int]]) -> Bool:
    for a in range(len(s)):
        if s[a] != t[a]:
            return word_less(s[a], t[a])
    return False


def canonical_substitution(sigma: List[List[Int]]) -> List[List[Int]]:
    """Least conjugate of `sigma` under alphabet relabelling."""
    var perms = permutations3()
    var best = conjugated_substitution(sigma, perms[0])
    for i in range(1, len(perms)):
        var candidate = conjugated_substitution(sigma, perms[i])
        if substitution_less(candidate, best):
            best = candidate^
    return best^


def word_key(w: List[Int]) -> String:
    var s = String("")
    for i in range(len(w)):
        s += String(w[i])
    return s


def substitution_key(sigma: List[List[Int]]) -> String:
    """`sigma(0)/sigma(1)/sigma(2)` with one digit per letter."""
    var s = word_key(sigma[0])
    for a in range(1, len(sigma)):
        s += "/" + word_key(sigma[a])
    return s


def parse_substitution_key(key: String) raises -> List[List[Int]]:
    """Inverse of `substitution_key`; letters are single digits `0..2`."""
    var out = List[List[Int]]()
    for image in key.split("/"):
        var w = List[Int]()
        for ch in image.codepoint_slices():
            var letter = Int(atol(String(ch)))
            if letter < 0 or letter >= ALPHABET:
                raise Error("substitution letter lies outside 0..2: " + String(ch))
            w.append(letter)
        out.append(w^)
    if len(out) != ALPHABET:
        raise Error("substitution key must have exactly three images: " + key)
    return out^
