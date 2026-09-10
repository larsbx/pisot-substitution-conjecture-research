"""Words over the 3-letter alphabet, scattered-subword counts, and the
horizontal invariants K_1, K_2, K_3 of a balanced pair.

Letters are zero-based (`0,1,2` for the alphabet `{1,2,3}`).

The scattered-subword kernels are deliberately Mojo-native streaming
algorithms.  Because the alphabet has fixed size three, `N2` and `N3` are
updated from prefix letter/pair accumulators in one pass rather than enumerating
all index pairs/triples.  This preserves exact integer counts while reducing
word-length complexity from O(n^2)/O(n^3) to O(n) with fixed small inner loops.
"""

from psc.tensor3 import idx3, zeros27


def parikh(w: List[Int]) -> List[Int]:
    """`N_i(w)` for `i` in `{0,1,2}`."""
    var out: List[Int] = [0, 0, 0]
    for p in range(len(w)):
        out[w[p]] += 1
    return out^


def n2(w: List[Int]) -> List[Int]:
    """`N_{ij}(w)` flattened row-major into `Z^9`, streamed in O(n).

    When the current letter is `j`, every previously seen `i` contributes one
    new scattered occurrence of `ij`.  The alphabet size is fixed at three, so
    each input symbol performs exactly three accumulator updates.
    """
    var out = List[Int]()
    for _ in range(9):
        out.append(0)
    var seen: List[Int] = [0, 0, 0]
    for p in range(len(w)):
        var j = w[p]
        for i in range(3):
            out[3 * i + j] += seen[i]
        seen[j] += 1
    return out^


def n3(w: List[Int]) -> List[Int]:
    """`N_{ijk}(w)` in lex coordinates of `V^(x3)`, streamed in O(n).

    `pairs[i,j]` stores the number of scattered `ij` subsequences already seen.
    On reading `k`, every stored pair becomes one new `ijk`; only afterwards do
    we extend single-letter prefixes into pairs ending at `k`.  With a fixed
    three-letter alphabet this is a constant amount of exact integer work per
    input symbol.
    """
    var out = zeros27()
    var seen: List[Int] = [0, 0, 0]
    var pairs = List[Int]()
    for _ in range(9):
        pairs.append(0)

    for p in range(len(w)):
        var k = w[p]
        for i in range(3):
            for j in range(3):
                out[idx3(i, j, k)] += pairs[3 * i + j]
        for i in range(3):
            pairs[3 * i + k] += seen[i]
        seen[k] += 1
    return out^


def _diff(u: List[Int], v: List[Int]) -> List[Int]:
    var out = List[Int]()
    for i in range(len(u)):
        out.append(u[i] - v[i])
    return out^


struct Pair(Copyable, Movable, Writable, Equatable):
    """A balanced pair `s = (u, v)`: `|u| == |v|` and `Parikh(u) == Parikh(v)`."""

    var u: List[Int]
    var v: List[Int]

    def __init__(out self, u: List[Int], v: List[Int]):
        self.u = u.copy()
        self.v = v.copy()

    def __eq__(self, o: Pair) -> Bool:
        return self.u == o.u and self.v == o.v

    def __ne__(self, o: Pair) -> Bool:
        return not (self == o)

    def length(self) -> Int:
        return len(self.u)

    def is_balanced(self) -> Bool:
        return len(self.u) == len(self.v) and parikh(self.u) == parikh(self.v)

    def is_coincidence(self) -> Bool:
        return self.u == self.v

    def k1(self) -> List[Int]:
        return _diff(parikh(self.u), parikh(self.v))

    def k2(self) -> List[Int]:
        return _diff(n2(self.u), n2(self.v))

    def k3(self) -> List[Int]:
        return _diff(n3(self.u), n3(self.v))

    def key(self) -> String:
        """A canonical string key, for use in dictionaries and sets.

        This remains exact and collision-free but is not the preferred long-term
        hot-path representation.  `AGENTS.md` tracks replacement by an interned
        compact state identity as a Mojo optimization target.
        """
        var s = String("")
        for i in range(len(self.u)):
            s += String(self.u[i])
        s += "|"
        for i in range(len(self.v)):
            s += String(self.v[i])
        return s

    def write_to[W: Writer](self, mut w: W):
        w.write(self.key())


def is_zero(v: List[Int]) -> Bool:
    for i in range(len(v)):
        if v[i] != 0:
            return False
    return True
