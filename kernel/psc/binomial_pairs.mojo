"""Irreducible distinct binomially equivalent word pairs: the exact census kernel.

`docs/c4-binomial-minimal-pairs-2026-11-07.md` (this census) and
`docs/c4-solidify-stop-go-2026-11-07.md` §0, §3 (experiment A, the gate it
follows). Manuscript `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`:
`def:balanced` (a balanced pair and its irreducible blocks), the
scattered-subword defects `K_r` of `thm:defect-intertwiner`.

**Domain.** For an alphabet `{0, ..., d-1}`, `d` in `{2, 3}`, and a length
`n >= 1`: the unordered pairs `{u, v}` of words with `u != v`,
`|u| = |v| = n`, `p(u) = p(v)` (`p` the Parikh vector, i.e. `K_1 = 0`) and
irreducible, i.e. `p(u[0, j)) != p(v[0, j))` for every `0 < j < n`. The
*first defect degree* of such a pair is `psc.defect_degree.first_defect_degree`:
`2`, `3`, `4`, or `DEGREE_FIVE_PLUS` when `K_2 = K_3 = K_4 = 0`. Binary words
are the sub-census of ternary words avoiding the letter `2`, with the same
alphabet-3 kernels (`psc.words.n2`, `n3`, `psc.defect_degree.n4`), not a
second kernel.

**Method (exact).**

* All irreducible pairs, of every degree, are counted by the lattice-walk
  recurrence `irreducible_ordered_pairs`: the prefix difference
  `d_j = p(u[0, j)) - p(v[0, j))` is a walk on the zero-sum lattice with the
  steps `e_a - e_b`, one per letter pair `(a, b)`; irreducible pairs are the
  walks that leave `0` and first return at step `n`. Checked machine
  arithmetic: an overflow raises, it never wraps.
* The pairs with `K_2 = 0` are found by enumeration. The words of one Parikh
  vector are listed in lexicographic order; their `N_2` rows are sorted by a
  stable merge sort; each run of equal rows is one `(N_1, N_2)` class; and
  every pair inside a class with distinct first letters and distinct last
  letters (equal ones cut the pair at `1`, resp. `n - 1`) is tested for
  irreducibility against prefix Parikh codes. Each pair kept is re-verified
  with the library predicates (`psc.bpa.coincidence_boundaries`,
  `psc.words.is_balanced`) and classified with `first_defect_degree`. The
  classification is cross-checked against the `N_3` and `N_4` sub-classes of
  the same sort; any disagreement raises.
* The degree-2 count is the total minus the enumerated `K_2 = 0` count.

The class counts `(N_1, N_2)`, `(N_1, N_2, N_3)`, `(N_1, ..., N_4)` are a
by-product of the same sort. On binary words they are the published
`k`-deck counts `D_3(n)`, `D_4(n)` for `n >= k` (Chrisnata, Kiah, Rao, Vardy,
Yaakobi, Yao, ISCIT 2019, Table I, transcribed below), which is the
calibration target of the gate; that the `k`-deck of a length-`n >= k` word
determines its `(N_1, ..., N_k)` is the standard deck lemma (reported by
Golm, Nahvi, Gabrys, Milenkovic, arXiv:2201.12671, §I), used only to read the
table.

Proved here, in full: nothing. This is executable exact enumeration over a
stated finite window; its outputs are finite counts for the lengths
enumerated, and a length outside the window is reported as not enumerated.

Not proved here: any statement for lengths outside the window, any
statement about pairs of a substitution's balanced-pair algorithm, and any
claim of novelty for unrestricted minimal lengths (those are the `k`-deck
numbers `S(k)`, known).
"""

from finite_exact.checked_int import checked_add, checked_mul
from psc.bpa import coincidence_boundaries
from psc.histogram import Histogram
from psc.defect_degree import DEGREE_FIVE_PLUS, DEGREE_FOUR, DEGREE_THREE, DEGREE_TWO, first_defect_degree, n4
from psc.symmetry import canonical_pair, pair_less, reversed_pair, word_less
from psc.words import ALPHABET, Pair, is_balanced, n2, n3
from substitution_dynamics.symmetry import sort_words

comptime N2_WIDTH = ALPHABET * ALPHABET
comptime N3_WIDTH = ALPHABET * ALPHABET * ALPHABET
comptime N4_WIDTH = ALPHABET * ALPHABET * ALPHABET * ALPHABET
comptime DEGREE_SLOTS = DEGREE_FIVE_PLUS + 1


# ----------------------------------------------------------------------------
# All irreducible pairs: the lattice-walk recurrence


def _check_alphabet(alphabet: Int) raises:
    if alphabet < 2 or alphabet > ALPHABET:
        raise Error("binomial pair census: alphabet size must be 2 or 3, got " + String(alphabet))


def irreducible_ordered_pairs(alphabet: Int, n: Int) raises -> Int:
    """Ordered pairs `(u, v)`, `u != v`, over `{0..alphabet-1}`, `|u| = |v| = n`,
    balanced and irreducible.

    Walk `d_j = p(u[0,j)) - p(v[0,j))` in the coordinates `(d_0, d_1)` (the
    third is `-d_0 - d_1`), one step `e_a - e_b` per letter pair `(a, b)`.
    A walk is counted when it is `0` at step `n` and nonzero at every step
    `0 < j < n`. For `n >= 2` the condition at `j = 1` excludes `u = v`; for
    `n = 1` every balanced pair is a coincidence `(a, a)`, so the count is 0.
    """
    _check_alphabet(alphabet)
    if n < 1:
        raise Error("binomial pair census: length must be at least 1")
    if n == 1:
        return 0
    var side = 2 * n + 1
    var cells = side * side
    var origin = n * side + n
    var dx = List[Int]()
    var dy = List[Int]()
    for a in range(alphabet):
        for b in range(alphabet):
            dx.append((1 if a == 0 else 0) - (1 if b == 0 else 0))
            dy.append((1 if a == 1 else 0) - (1 if b == 1 else 0))
    var cur = List[Int](length=cells, fill=0)
    cur[origin] = 1
    for step in range(1, n + 1):
        var nxt = List[Int](length=cells, fill=0)
        for x in range(side):
            for y in range(side):
                var c = cur[x * side + y]
                if c == 0:
                    continue
                for s in range(len(dx)):
                    var nx = x + dx[s]
                    var ny = y + dy[s]
                    if nx < 0 or nx >= side or ny < 0 or ny >= side:
                        raise Error("binomial pair census: lattice walk left its box")
                    nxt[nx * side + ny] = checked_add(nxt[nx * side + ny], c)
        if step < n:
            nxt[origin] = 0
        cur = nxt^
    return cur[origin]


def catalan(m: Int) raises -> Int:
    """`C_m = binom(2m, m) / (m + 1)` by `C_{i+1} = C_i * 2(2i+1) / (i+2)`,
    each division checked exact."""
    if m < 0:
        raise Error("catalan: negative index")
    var c = 1
    for i in range(m):
        var num = checked_mul(c, 2 * (2 * i + 1))
        if num % (i + 2) != 0:
            raise Error("catalan: inexact division")
        c = num // (i + 2)
    return c


def binary_closed_form_ordered(n: Int) raises -> Int:
    """`2 * C_{n-1}`: the ordered irreducible distinct binary pairs of length
    `n >= 2` (stop/go note §3.3 (b)). The calibration target, not an input."""
    if n < 2:
        raise Error("binary closed form is stated for n >= 2")
    return checked_mul(2, catalan(n - 1))


# ----------------------------------------------------------------------------
# Word enumeration by Parikh vector


def parikh_vectors(alphabet: Int, n: Int) raises -> List[List[Int]]:
    """Every `(c_0, c_1, c_2)` with `c_0 + c_1 + c_2 = n`, `c_a = 0` for
    `a >= alphabet`, in lexicographic order."""
    _check_alphabet(alphabet)
    var out = List[List[Int]]()
    for c0 in range(n + 1):
        if alphabet == 2:
            var v: List[Int] = [c0, n - c0, 0]
            out.append(v^)
        else:
            for c1 in range(n - c0 + 1):
                var v: List[Int] = [c0, c1, n - c0 - c1]
                out.append(v^)
    return out^


def class_words(parikh: List[Int]) raises -> List[Int]:
    """All words with Parikh vector `parikh`, row-major (`n` letters a row),
    in lexicographic order, by the next-permutation step on a multiset."""
    if len(parikh) != ALPHABET:
        raise Error("class_words: a Parikh vector has three coordinates")
    var w = List[Int]()
    for a in range(ALPHABET):
        if parikh[a] < 0:
            raise Error("class_words: negative Parikh coordinate")
        for _ in range(parikh[a]):
            w.append(a)
    var n = len(w)
    var out = List[Int]()
    if n == 0:
        return out^
    while True:
        for i in range(n):
            out.append(w[i])
        var i = n - 2
        while i >= 0 and w[i] >= w[i + 1]:
            i -= 1
        if i < 0:
            break
        var j = n - 1
        while w[j] <= w[i]:
            j -= 1
        var t = w[i]
        w[i] = w[j]
        w[j] = t
        var lo = i + 1
        var hi = n - 1
        while lo < hi:
            var s = w[lo]
            w[lo] = w[hi]
            w[hi] = s
            lo += 1
            hi -= 1
    return out^


def word_at(words: List[Int], n: Int, i: Int) -> List[Int]:
    var out = List[Int](capacity=n)
    for t in range(n):
        out.append(words[i * n + t])
    return out^


# ----------------------------------------------------------------------------
# Stable sort of fixed-width integer rows


def _row_less(rows: List[Int], width: Int, i: Int, j: Int) -> Bool:
    for t in range(width):
        var a = rows[i * width + t]
        var b = rows[j * width + t]
        if a != b:
            return a < b
    return False


def rows_equal(rows: List[Int], width: Int, i: Int, j: Int) -> Bool:
    for t in range(width):
        if rows[i * width + t] != rows[j * width + t]:
            return False
    return True


def sorted_row_order(rows: List[Int], width: Int) raises -> List[Int]:
    """Row indices in lexicographic order of the rows, stable (equal rows keep
    their index order), by a bottom-up merge sort on indices."""
    if width <= 0 or len(rows) % width != 0:
        raise Error("sorted_row_order: the table is not a whole number of rows")
    var count = len(rows) // width
    var order = List[Int](capacity=count)
    for i in range(count):
        order.append(i)
    var buf = List[Int](length=count, fill=0)
    var run = 1
    while run < count:
        var lo = 0
        while lo < count:
            var mid = lo + run if lo + run < count else count
            var hi = lo + 2 * run if lo + 2 * run < count else count
            var i = lo
            var j = mid
            var k = lo
            while i < mid and j < hi:
                if _row_less(rows, width, order[j], order[i]):
                    buf[k] = order[j]
                    j += 1
                else:
                    buf[k] = order[i]
                    i += 1
                k += 1
            while i < mid:
                buf[k] = order[i]
                i += 1
                k += 1
            while j < hi:
                buf[k] = order[j]
                j += 1
                k += 1
            lo = hi
        for t in range(count):
            order[t] = buf[t]
        run *= 2
    return order^


# ----------------------------------------------------------------------------
# The census of one length


def prefix_codes(words: List[Int], n: Int) -> List[Int]:
    """For each word, `p(w[0, j))` for `1 <= j <= n-1` as one integer
    `c_0 (n+1) + c_1` (the third coordinate is `j - c_0 - c_1`), row-major
    with `n - 1` entries a word."""
    var count = len(words) // n if n > 0 else 0
    var out = List[Int](capacity=count * (n - 1 if n > 0 else 0))
    for i in range(count):
        var c0 = 0
        var c1 = 0
        for j in range(n - 1):
            var a = words[i * n + j]
            if a == 0:
                c0 += 1
            elif a == 1:
                c1 += 1
            out.append(c0 * (n + 1) + c1)
    return out^


def codes_irreducible(codes: List[Int], n: Int, i: Int, j: Int) -> Bool:
    """Words `i`, `j` of one Parikh class: no proper prefix length `0 < t < n`
    with equal Parikh vectors."""
    var w = n - 1
    for t in range(w):
        if codes[i * w + t] == codes[j * w + t]:
            return False
    return True


def is_irreducible_pair(p: Pair) -> Bool:
    """The library definition: balanced, equal length, and the coincidence
    boundaries are exactly `0` and `n`."""
    if len(p.u) != len(p.v) or len(p.u) == 0 or not is_balanced(p):
        return False
    var bd = coincidence_boundaries(p.u, p.v)
    return len(bd) == 2 and bd[0] == 0 and bd[1] == len(p.u)


def _rows_of(words: List[Int], n: Int, members: List[Int], degree: Int) raises -> List[Int]:
    """`N_degree` rows (`degree` in `3, 4`) of the listed words, in `members` order."""
    var width = N3_WIDTH if degree == 3 else N4_WIDTH
    var rows = List[Int](capacity=len(members) * width)
    for t in range(len(members)):
        var w = word_at(words, n, members[t])
        var r = n3(w) if degree == 3 else n4(w)
        if len(r) != width:
            raise Error("binomial pair census: scattered-count row of unexpected width")
        for s in range(width):
            rows.append(r[s])
    return rows^


struct LengthCensus(Copyable, Movable):
    """The census of one alphabet size and one length.

    `degree2` is `total - k2_zero()`; the three `K_2 = 0` degrees are the
    histogram of the enumerated pairs. `pairs` keeps the enumerated pairs of
    degree at least `kept_from` (each as `(u, v)` with `u` lexicographically
    first), with `degrees` parallel to it; the counts never depend on it."""

    var alphabet: Int
    var n: Int
    var words: Int
    var classes2: Int
    var classes3: Int
    var classes4: Int
    var candidates: Int
    var irreducible_ordered: Int
    var total: Int
    var degree2: Int
    var k2_zero_degrees: Histogram
    var kept_from: Int
    var pairs: List[Pair]
    var degrees: List[Int]

    def __init__(out self, alphabet: Int, n: Int, kept_from: Int):
        self.alphabet = alphabet
        self.n = n
        self.words = 0
        self.classes2 = 0
        self.classes3 = 0
        self.classes4 = 0
        self.candidates = 0
        self.irreducible_ordered = 0
        self.total = 0
        self.degree2 = 0
        self.k2_zero_degrees = Histogram(DEGREE_SLOTS)
        self.kept_from = kept_from
        self.pairs = List[Pair]()
        self.degrees = List[Int]()

    def count(self, degree: Int) -> Int:
        """Unordered pairs of this first defect degree (`2..4` or
        `DEGREE_FIVE_PLUS`)."""
        if degree == DEGREE_TWO:
            return self.degree2
        return self.k2_zero_degrees.count(degree)

    def k2_zero(self) -> Int:
        return self.k2_zero_degrees.total()

    def pairs_of_degree(self, degree: Int) raises -> List[Pair]:
        if degree < self.kept_from:
            raise Error("binomial pair census: pairs of degree " + String(degree) + " were counted, not kept, at n = " + String(self.n))
        var out = List[Pair]()
        for i in range(len(self.pairs)):
            if self.degrees[i] == degree:
                out.append(self.pairs[i].copy())
        return out^


def census_length(alphabet: Int, n: Int, kept_from: Int = DEGREE_THREE) raises -> LengthCensus:
    """Exact census of one `(alphabet, n)`: totals by the lattice walk, the
    `K_2 = 0` pairs by enumeration inside `(N_1, N_2)` classes.

    A pair inside a class is tested only when its first letters differ and
    its last letters differ: equal first letters cut it at `1`, equal last
    letters (with equal Parikh vectors) cut it at `n - 1`. Every pair the
    prefix codes call irreducible is re-checked by `is_irreducible_pair`, and
    its `first_defect_degree` must be `3`, `4` or `5+` and must agree with
    the `(N_1, N_2, N_3)` and `(N_1, ..., N_4)` sub-classes; any disagreement,
    a word count other than `alphabet^n`, or an odd ordered total raises."""
    _check_alphabet(alphabet)
    if n < 1:
        raise Error("binomial pair census: length must be at least 1")
    var out = LengthCensus(alphabet, n, kept_from)
    var expected_words = 1
    for _ in range(n):
        expected_words = checked_mul(expected_words, alphabet)

    var vectors = parikh_vectors(alphabet, n)
    for pv in range(len(vectors)):
        var words = class_words(vectors[pv])
        var m = len(words) // n
        out.words = checked_add(out.words, m)
        var codes = prefix_codes(words, n)
        var rows2 = List[Int](capacity=m * N2_WIDTH)
        for i in range(m):
            var r = n2(word_at(words, n, i))
            for t in range(N2_WIDTH):
                rows2.append(r[t])
        var order = sorted_row_order(rows2, N2_WIDTH)
        var id3 = List[Int](length=m, fill=-1)
        var id4 = List[Int](length=m, fill=-1)
        var next3 = 0
        var next4 = 0
        var lo = 0
        while lo < m:
            var hi = lo + 1
            while hi < m and rows_equal(rows2, N2_WIDTH, order[lo], order[hi]):
                hi += 1
            out.classes2 += 1
            # members of this (N1, N2) class, in increasing word index, which
            # is lexicographic word order (stable sort of a lex-ordered list)
            var members = List[Int](capacity=hi - lo)
            for t in range(lo, hi):
                members.append(order[t])
            for t in range(1, len(members)):
                if members[t] <= members[t - 1]:
                    raise Error("binomial pair census: class members out of order")
            # (N1, N2, N3) sub-classes, then (N1, ..., N4) sub-classes: runs of
            # the stable sort of the members' N3 rows, then of N4 rows
            if len(members) == 1:
                id3[members[0]] = next3
                id4[members[0]] = next4
                next3 += 1
                next4 += 1
                out.classes3 += 1
                out.classes4 += 1
            else:
                var rows3 = _rows_of(words, n, members, 3)
                var order3 = sorted_row_order(rows3, N3_WIDTH)
                var s3 = 0
                while s3 < len(order3):
                    var e3 = s3 + 1
                    while e3 < len(order3) and rows_equal(rows3, N3_WIDTH, order3[s3], order3[e3]):
                        e3 += 1
                    var sub = List[Int](capacity=e3 - s3)
                    for t in range(s3, e3):
                        sub.append(members[order3[t]])
                        id3[members[order3[t]]] = next3
                    next3 += 1
                    out.classes3 += 1
                    var rows4 = _rows_of(words, n, sub, 4)
                    var order4 = sorted_row_order(rows4, N4_WIDTH)
                    var s4 = 0
                    while s4 < len(order4):
                        var e4 = s4 + 1
                        while e4 < len(order4) and rows_equal(rows4, N4_WIDTH, order4[s4], order4[e4]):
                            e4 += 1
                        for t in range(s4, e4):
                            id4[sub[order4[t]]] = next4
                        next4 += 1
                        out.classes4 += 1
                        s4 = e4
                    s3 = e3
            # the pairs of the class; members are in lexicographic order, so
            # their first letters are nondecreasing and `block_end[a]` is the
            # first position after `a` with a larger first letter
            var block_end = List[Int](length=len(members), fill=len(members))
            for a in range(len(members) - 2, -1, -1):
                if words[members[a] * n] == words[members[a + 1] * n]:
                    block_end[a] = block_end[a + 1]
                elif words[members[a] * n] < words[members[a + 1] * n]:
                    block_end[a] = a + 1
                else:
                    raise Error("binomial pair census: class members are not in lexicographic order")
            for a in range(len(members)):
                var i = members[a]
                for b in range(block_end[a], len(members)):
                    var j = members[b]
                    if words[i * n] == words[j * n] or words[i * n + n - 1] == words[j * n + n - 1]:
                        continue
                    out.candidates += 1
                    if not codes_irreducible(codes, n, i, j):
                        continue
                    var p = Pair(word_at(words, n, i), word_at(words, n, j))
                    if not is_irreducible_pair(p) or p.u == p.v or not word_less(p.u, p.v):
                        raise Error("binomial pair census: prefix-code test disagrees with coincidence_boundaries at " + p.key())
                    var degree = first_defect_degree(p)
                    var by_class = DEGREE_THREE
                    if id3[i] == id3[j]:
                        by_class = DEGREE_FIVE_PLUS if id4[i] == id4[j] else DEGREE_FOUR
                    if degree == DEGREE_TWO or degree != by_class:
                        raise Error("binomial pair census: degree disagrees with the (N1,N2) class sort at " + p.key())
                    out.k2_zero_degrees.record(degree)
                    if degree >= kept_from:
                        out.pairs.append(p^)
                        out.degrees.append(degree)
            lo = hi
    if out.words != expected_words:
        raise Error("binomial pair census: enumerated " + String(out.words) + " words, expected " + String(expected_words))

    out.irreducible_ordered = irreducible_ordered_pairs(alphabet, n)
    if out.irreducible_ordered % 2 != 0:
        raise Error("binomial pair census: odd ordered count; the swap has no fixed point")
    out.total = out.irreducible_ordered // 2
    out.degree2 = out.total - out.k2_zero()
    if out.degree2 < 0:
        raise Error("binomial pair census: more K2 = 0 pairs than irreducible pairs")
    return out^


def census_window(alphabet: Int, n_max: Int, kept_from: Int = DEGREE_THREE) raises -> List[LengthCensus]:
    """`census_length(alphabet, n, kept_from)` for `n = 1 .. n_max`."""
    var out = List[LengthCensus]()
    for n in range(1, n_max + 1):
        out.append(census_length(alphabet, n, kept_from))
    return out^


def minimal_length(rows: List[LengthCensus], degree: Int) -> Int:
    """Least `n` in the window with a pair of this first defect degree, or
    `0` when the window has none (which is not a statement beyond it)."""
    for r in range(len(rows)):
        if rows[r].count(degree) > 0:
            return rows[r].n
    return 0


# ----------------------------------------------------------------------------
# Brute force over all balanced pairs (a control of the recurrence)


def brute_irreducible_ordered_pairs(alphabet: Int, n: Int) raises -> Int:
    """Ordered irreducible distinct pairs counted pair by pair with the
    library predicate `is_irreducible_pair`; cost `sum |class|^2`, so only
    for small `n`. The control of `irreducible_ordered_pairs`."""
    var count = 0
    var vectors = parikh_vectors(alphabet, n)
    for pv in range(len(vectors)):
        var words = class_words(vectors[pv])
        var m = len(words) // n
        for i in range(m):
            var u = word_at(words, n, i)
            for j in range(m):
                if i == j:
                    continue
                if is_irreducible_pair(Pair(u, word_at(words, n, j))):
                    count += 1
    return count


# ----------------------------------------------------------------------------
# Symmetry classes under relabelling x reversal x swap


def g_canonical(p: Pair) -> Pair:
    """Least element of the orbit of `p` under `S_3 x <reversal> x <swap>`:
    the lesser of the canonical relabellings of `p` and of its reversal."""
    var a = canonical_pair(p)
    var b = canonical_pair(reversed_pair(p))
    if pair_less(b, a):
        return b^
    return a^


def orbit_representatives(pairs: List[Pair], with_reversal: Bool) -> List[Pair]:
    """The distinct orbit minima of `pairs` under `S_3 x <swap>`, and also
    `<reversal>` when `with_reversal`, in lexicographic order. Each pair has
    sides of equal length, so the key `u ++ v` is injective and splits back
    at its midpoint."""
    var keys = List[List[Int]]()
    for i in range(len(pairs)):
        var c = g_canonical(pairs[i]) if with_reversal else canonical_pair(pairs[i])
        var k = c.u.copy()
        for t in range(len(c.v)):
            k.append(c.v[t])
        keys.append(k^)
    sort_words(keys)
    var out = List[Pair]()
    for i in range(len(keys)):
        if i > 0 and keys[i] == keys[i - 1]:
            continue
        var half = len(keys[i]) // 2
        var u = List[Int]()
        var v = List[Int]()
        for t in range(half):
            u.append(keys[i][t])
            v.append(keys[i][half + t])
        out.append(Pair(u, v))
    return out^


def g_representatives(pairs: List[Pair]) -> List[Pair]:
    """Orbit minima under `G = S_3 x <reversal> x <swap>` (gate §3.1)."""
    return orbit_representatives(pairs, True)


def contains_pair(pairs: List[Pair], p: Pair) -> Bool:
    """`p` or its swap is among `pairs`."""
    for i in range(len(pairs)):
        if (pairs[i].u == p.u and pairs[i].v == p.v) or (pairs[i].u == p.v and pairs[i].v == p.u):
            return True
    return False


# ----------------------------------------------------------------------------
# Calibration targets and controls


def table_i_d3() -> List[Int]:
    """`D_3(n)` for `n = 3 .. 20`, Chrisnata et al. ISCIT 2019 Table I."""
    var out: List[Int] = [8, 16, 32, 64, 126, 247, 480, 926, 1764, 3337, 6208, 11408, 20608, 36649, 63976, 109866, 185012, 306285]
    return out^


def table_i_d4() -> List[Int]:
    """`D_4(n)` for `n = 4 .. 20`, Chrisnata et al. ISCIT 2019 Table I."""
    var out: List[Int] = [16, 32, 64, 128, 256, 512, 1024, 2048, 4092, 8176, 16328, 32604, 65075, 129824, 258906, 516168, 1028448]
    return out^


def thue_morse_block(k: Int, letter: Int) raises -> List[Int]:
    """`phi^k(letter)` for Thue-Morse `phi: 0 -> 01, 1 -> 10`."""
    if letter != 0 and letter != 1:
        raise Error("thue_morse_block: letter must be 0 or 1")
    var w: List[Int] = [letter]
    for _ in range(k):
        var nxt = List[Int](capacity=2 * len(w))
        for i in range(len(w)):
            nxt.append(w[i])
            nxt.append(1 - w[i])
        w = nxt^
    return w^


def scattered_count(w: List[Int], x: List[Int]) raises -> Int:
    """`binom(w, x)`: occurrences of `x` as a scattered subword of `w`, by the
    classical prefix recurrence on `x`, in checked arithmetic. A single
    coordinate of any degree; the controls use it at degree five, beyond
    `psc.defect_degree`."""
    var c = List[Int](length=len(x) + 1, fill=0)
    c[0] = 1
    for i in range(len(w)):
        for t in range(len(x), 0, -1):
            if x[t - 1] == w[i]:
                c[t] = checked_add(c[t], c[t - 1])
    return c[len(x)]


def digits(s: String) raises -> List[Int]:
    """A word written as decimal letters `0..2`."""
    var out = List[Int]()
    for c in s.codepoints():
        var x = Int(c.to_u32()) - 48
        if x < 0 or x >= ALPHABET:
            raise Error("digits: letter outside 0..2 in " + s)
        out.append(x)
    return out^
