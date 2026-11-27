"""Fixed tilings of the inflation, counted literally, and the nonunit
rank-two residue they leave.

docs/c4-nonunit-rank-two-residue-2026-11-21.md. `sigma` is a primitive
substitution on `k` letters, `Phi` its inflation on the tiling space, `g` and
`g_R` the first- and last-letter maps.

The count (Lemma N of the note)
-------------------------------
A tiling fixed by `Phi^n` is exactly one of:

- *interior*: the origin lies strictly inside a tile `a`, and the tile is the
  occurrence of `a` at a position `0 < i < |sigma^n(a)| - 1` of `sigma^n(a)`;
- *vertex*: the origin is a vertex with the legal word `b a` around it,
  `sigma^n(b)` ends with `b` and `sigma^n(a)` starts with `a`.

`fixed_tiling_count` counts both kinds from the words `sigma^n(a)` and the
legal two-letter words, with no matrix and no eventual range. In closed form
it is `tr(M^n) - #Fix(g^n) - #Fix(g_R^n) + #{fixed legal words}`; the
regression compares the two on every nonunit corpus member.

The residue (Theorem R of the note)
-----------------------------------
At nonunit determinant and coincidence rank two the twin involution is a
fixed-point-free involution of `Fix(Phi^n)`, so the count is even for every
`n >= 1`. `residue_profile` records, for one member of PIP3, the three written
exclusions of rank two and whether the member survives all of them:

- `theorem_e`: an endpoint map is injective and the opposite side of `ER` has
  two letters (Theorem E of the twin-endpoint note);
- `tree`: `ER` has cycle rank zero, so `dim H^1 = 3` (Theorem H3 of the
  rank-two wall note);
- `odd_power`: the least `n <= PARITY_DEPTH` with an odd count, or 0.

These are class counts under written conditional theorems. No coincidence
rank is computed and no claim status changes.

Fail closed: a word longer than `WORD_CAP` raises, as does a power below one;
malformed images raise through `psc.h1_census`.
"""

from psc.h1_census import eventual_range, legal_two_words

comptime WORD_CAP = 2000000
comptime PARITY_DEPTH = 8


def image_power(sigma: List[List[Int]], a: Int, n: Int) raises -> List[Int]:
    """The word `sigma^n(a)`."""
    if n < 1:
        raise Error("twin_fixed_points: power below one")
    var w: List[Int] = [a]
    for _ in range(n):
        var next = List[Int]()
        for x in w:
            for c in sigma[x]:
                next.append(c)
        if len(next) > WORD_CAP:
            raise Error("twin_fixed_points: word cap reached")
        w = next^
    return w^


def fixed_tiling_count(sigma: List[List[Int]], n: Int) raises -> Int:
    """`#Fix(Phi^n)`, counted from the words `sigma^n(a)` and the legal
    two-letter words."""
    var k = len(sigma)
    var legal = legal_two_words(sigma)
    var first = List[Int]()
    var last = List[Int]()
    var count = 0
    for a in range(k):
        var w = image_power(sigma, a, n)
        first.append(w[0])
        last.append(w[len(w) - 1])
        for i in range(1, len(w) - 1):
            count += Int(w[i] == a)
    for b in range(k):
        for a in range(k):
            count += Int(legal[k * b + a] and last[b] == b and first[a] == a)
    return count


def _injective(f: List[Int]) -> Bool:
    return f[0] != f[1] and f[0] != f[2] and f[1] != f[2]


struct ResidueProfile(Copyable, Movable):
    """The written rank-two exclusions on one member of PIP3."""

    var lefts: Int
    var rights: Int
    var edges: Int
    var theorem_e: Bool
    var tree: Bool
    var odd_power: Int

    def __init__(out self, lefts: Int, rights: Int, edges: Int, theorem_e: Bool, tree: Bool, odd_power: Int):
        self.lefts = lefts
        self.rights = rights
        self.edges = edges
        self.theorem_e = theorem_e
        self.tree = tree
        self.odd_power = odd_power

    def complete_bipartite(self) -> Bool:
        """`ER = K_{2,2}`."""
        return self.lefts == 2 and self.rights == 2 and self.edges == 4

    def survives(self) -> Bool:
        return not self.theorem_e and not self.tree and self.odd_power == 0


def residue_profile(sigma: List[List[Int]]) raises -> ResidueProfile:
    if len(sigma) != 3:
        raise Error("twin_fixed_points: three letters required")
    var er = eventual_range(sigma, legal_two_words(sigma))
    var left = List[Bool](length=3, fill=False)
    var right = List[Bool](length=3, fill=False)
    var edges = 0
    for b in range(3):
        for a in range(3):
            if er[3 * b + a]:
                edges += 1
                left[b] = True
                right[a] = True
    var lefts = 0
    var rights = 0
    for x in range(3):
        lefts += Int(left[x])
        rights += Int(right[x])
    if edges == 0:
        raise Error("twin_fixed_points: empty eventual range")
    var g = [sigma[a][0] for a in range(3)]
    var gr = [sigma[a][len(sigma[a]) - 1] for a in range(3)]
    var theorem_e = (_injective(g) and rights >= 2) or (_injective(gr) and lefts >= 2)
    var odd_power = 0
    for n in range(1, PARITY_DEPTH + 1):
        if fixed_tiling_count(sigma, n) % 2 != 0:
            odd_power = n
            break
    return ResidueProfile(lefts, rights, edges, theorem_e, edges - lefts - rights + 1 == 0, odd_power)
