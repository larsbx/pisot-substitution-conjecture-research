"""The `K_2 = 0` window search for strict systems off the PIP corpus.

Gate: `docs/c4-solidify-stop-go-2026-11-07.md` §0, §4.3, §4.6 and §4.7
(experiment B, fused with experiment A). Contract and evidence:
`docs/c4-closed-component-search-2026-11-07.md`. Manuscript
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`: `def:balanced`
(balanced pairs, irreducible blocks), `def:bpa` (the zero-return
factorisation `red`), `thm:defect-intertwiner` (the defects `K_r`).

**Objects.** A *strict system* of `sigma` is a finite nonempty set `C` of
irreducible noncoincident balanced pairs containing every block of
`red(sigma(u), sigma(v))` for each `(u, v)` in `C` (cut-pair note §2). The
blocks of `red(sigma(v), sigma(u))` are the swaps of those of
`red(sigma(u), sigma(v))`, so the existence question is the same on
normalised states (`substitution_dynamics.balanced_pairs.normalise`; for an
irreducible noncoincident pair it orders the two sides by first letter, which
differ by `Psc.Binomial.heads_ne`), and every set of normalised states closed
under normalised children lifts to the ordered strict system `S u swap(S)`.

**The window (stop/go §4.3 item 4).** `P_L` is the complete list of
normalised irreducible noncoincident pairs with `K_1 = K_2 = 0` and length at
most `L`: it is read from experiment A (`psc.binomial_pairs.census_length`,
every pair of first defect degree at least three, for each length
`2..L`), never cut by a hard-coded minimum length. `greatest_fixed_point`
iterates `X -> {T in X : every child of T lies in X}` from `X = P_L`. The
limit contains every strict system all of whose states lie in `P_L` (such a
system `S` satisfies `S <= F(S)`), and a nonempty limit is itself closed under
children, so it contains a strict carrier (a sink SCC, read by
`psc.carrier.profile_component`). Hence: **the limit is empty iff `sigma` has
no strict system with `K_2 = 0` on every state and every state of length at
most `L`.** That is a window observation about this length class, never a
statement about longer states.

**Domain.** Every primitive triple over `psc.corpus.image_words` outside the
PIP corpus is classified exactly (`specimen_class`):
`CLASS_ONE_OUTSIDE` (`chi_M` irreducible, exactly one non-Perron root outside
the unit disc, the R3' class), `CLASS_BOTH_OUTSIDE` (both outside, the R3
class) or `CLASS_REDUCIBLE`; and it is *synchronizing* when its first-letter
or last-letter map is eventually constant (`is_synchronizing`). The window
domain is the non-synchronizing specimens of `CLASS_ONE_OUTSIDE` and
`CLASS_REDUCIBLE` (stop/go §4.6). A synchronizing specimen has no strict
system (stop/go §4.3 item 1, from `heads_ne`), and a both-outside specimen has
none (Theorem R3 of `docs/c4-general-structure-2026-11-06.md`, a written
proof): on those the window is run only as a consistency check, and a
nonempty limit there raises through `violations`.

**Strong coincidence (a verdict where a witness exists).** By Theorem A(4) of
the cut-pair note (nonerasing `sigma`), no first-letter pair of a strict
system is left strongly coincident; by reversal no last-letter pair is right
strongly coincident (Lemma 4 of the docs note). So all three letter pairs
left-witnessed, or all three right-witnessed, means no strict system at all,
of any length and any `K_2`. A pair with no witness inside the word budget is
undecided (`-1`), never a negative.

**Proved here, in full:** nothing. This is exact finite computation over
stated windows: integer words, the exact census of experiment A, and exact
rational Sturm–Tarski root counting (`psc.real_root_sign.count_real_roots`).

**Not proved here:** any statement for states longer than `L`, for states
with `K_2 != 0` (the reducible strict systems with `K_2 != 0` are the 28
pinned carriers of `kernel/tests/test_c4_quotient_spectrum.mojo`, not
searched for here), for images longer than three, for PIP substitutions,
or C4, (H), (N0), BH, A1', G1 or PSC.
"""

from finite_graph.scc import has_cycle, sccs
from finite_linear_algebra import qpoly
from finite_linear_algebra.mat3 import Mat3
from finite_linear_algebra.scalar import q_int
from psc.binomial_pairs import census_length, sorted_row_order
from psc.bpa import (
    apply_substitution,
    coincidence_boundaries,
    decompose,
    prefix_endpoint_map,
    sigma3,
    substitution_incidence,
    suffix_endpoint_map,
)
from psc.c4_cut_attractor import eventually_constant, left_witness, strict_closure
from psc.c4_cut_pair_reduction import pair_bit
from psc.carrier import emit_countermodel, profile_component
from psc.corpus import Specimen, image_words, substitution_of
from psc.defect_degree import DEGREE_FIVE_PLUS, DEGREE_THREE, first_defect_degree
from psc.exact import q_poly
from psc.pisot import CubicScreen, is_irreducible_cubic, is_primitive
from psc.real_root_sign import count_real_roots
from psc.symmetry import reversed_substitution
from psc.words import ALPHABET, Pair, is_balanced, k2
from substitution_dynamics.automaton import Automaton
from substitution_dynamics.balanced_pairs import normalise

# Arithmetic class of a primitive incidence cubic.
comptime CLASS_NOT_PRIMITIVE = -1
comptime CLASS_PIP = 0
comptime CLASS_ONE_OUTSIDE = 1
comptime CLASS_BOTH_OUTSIDE = 2
comptime CLASS_REDUCIBLE = 3
comptime CLASS_COUNT = 4

# The three unordered letter pairs, in `pair_bit` order {0,1}, {0,2}, {1,2}.
comptime PAIRS = 3
comptime ALL_PAIRS_MASK = 7
comptime MAX_WITNESS_LEVEL = 32

# Longest state a universe may hold: a base-3 word code of length n is below
# 3^n, and 3^39 < 2^63.
comptime MAX_UNIVERSE_LENGTH = 39


def class_name(klass: Int) -> String:
    if klass == CLASS_PIP:
        return "PIP"
    if klass == CLASS_ONE_OUTSIDE:
        return "one-outside"
    if klass == CLASS_BOTH_OUTSIDE:
        return "both-outside"
    if klass == CLASS_REDUCIBLE:
        return "reducible"
    return "not-primitive"


# ------------------------------------------------------------------- domain


def conjugates_outside(chi: List[Int]) raises -> Int:
    """For an irreducible cubic `chi_M` of a primitive `M` (Perron root
    `beta > 1`), the number of non-Perron roots outside the closed unit disc:
    `0` (Pisot), `1` (both real, the R3' class) or `2` (the R3 class).

    Exact (`count_real_roots`, a Sturm–Tarski count over unbounded
    rationals). Three real roots: count those in `(-1, 1)`; `+-1` are not
    roots of an irreducible cubic. One real root `beta` and a pair `alpha`,
    `conj alpha`: `beta |alpha|^2 = |det M|`, so the pair lies outside iff
    `beta < |det M|`, iff no real root lies in `(|det M|, B)` for the Cauchy
    bound `B`; `|det M|` is not a root, since an irreducible cubic has no
    rational root."""
    if not is_irreducible_cubic(chi):
        raise Error("conjugates_outside needs an irreducible cubic")
    var p = q_poly(chi)
    var bound = qpoly.root_bound(p)
    var real_roots = count_real_roots(p, bound.neg(), bound)
    if real_roots == 3:
        var inside = count_real_roots(p, q_int(-1), q_int(1))
        if inside < 0 or inside > 2:
            raise Error("a Perron root lies inside the unit disc")
        return 2 - inside
    if real_roots != 1:
        raise Error("an irreducible cubic has one or three real roots")
    var d = q_int(abs(chi[0]))
    if not d.lt(bound):
        return 2
    return 2 if count_real_roots(p, d, bound) == 0 else 0


def det_power_below_perron(chi: List[Int], k: Int) raises -> Bool:
    """Whether `|det M|^k < beta` for an irreducible cubic `chi_M` (equality is
    impossible: `beta` is irrational). Exact: some real root lies in
    `(|det M|^k, B)`."""
    if not is_irreducible_cubic(chi) or k < 1:
        raise Error("det_power_below_perron needs an irreducible cubic and k >= 1")
    var x = 1
    for _ in range(k):
        x *= abs(chi[0])
    var p = q_poly(chi)
    var bound = qpoly.root_bound(p)
    var d = q_int(x)
    if not d.lt(bound):
        return False
    return count_real_roots(p, d, bound) > 0


def specimen_class(mut screen: CubicScreen, m: Mat3) raises -> Int:
    """`CLASS_NOT_PRIMITIVE`, `CLASS_PIP`, `CLASS_ONE_OUTSIDE`,
    `CLASS_BOTH_OUTSIDE` or `CLASS_REDUCIBLE`. PIP is the corpus screen of
    `psc.pisot` (memoised per cubic); the split of the irreducible non-Pisot
    cubics is `conjugates_outside`, which must not call a non-PIP cubic
    Pisot."""
    if not is_primitive(m):
        return CLASS_NOT_PRIMITIVE
    var chi = m.charpoly()
    if not is_irreducible_cubic(chi):
        return CLASS_REDUCIBLE
    if screen.accepts_cubic(chi):
        return CLASS_PIP
    var outside = conjugates_outside(chi)
    if outside == 1:
        return CLASS_ONE_OUTSIDE
    if outside == 2:
        return CLASS_BOTH_OUTSIDE
    raise Error("an irreducible non-PIP cubic has no conjugate outside the unit disc")


def is_synchronizing(sigma: List[List[Int]]) -> Bool:
    """The first-letter map or the last-letter map is eventually constant
    (endpoint types A, B). Such a `sigma` has no strict system (stop/go §4.3
    item 1)."""
    return eventually_constant(prefix_endpoint_map(sigma)) or eventually_constant(suffix_endpoint_map(sigma))


struct OffCorpusSpecimen(Copyable, Movable):
    """A primitive substitution outside the PIP corpus, its class and its
    endpoint flag. `specimen.index` counts the off-corpus list."""

    var specimen: Specimen
    var klass: Int
    var synchronizing: Bool

    def __init__(out self, var specimen: Specimen, klass: Int, synchronizing: Bool):
        self.specimen = specimen^
        self.klass = klass
        self.synchronizing = synchronizing

    def in_window_domain(self) -> Bool:
        """Non-synchronizing, and one-outside or reducible (stop/go §4.6)."""
        return not self.synchronizing and (self.klass == CLASS_ONE_OUTSIDE or self.klass == CLASS_REDUCIBLE)


def off_corpus_specimens() raises -> List[OffCorpusSpecimen]:
    """Every primitive non-PIP triple over `psc.corpus.image_words`, in the
    corpus's `(i, j, k)` order; `label` is the corpus label."""
    var words = image_words()
    var screen = CubicScreen()
    var out = List[OffCorpusSpecimen]()
    for i in range(len(words)):
        for j in range(len(words)):
            for k in range(len(words)):
                var sigma = substitution_of(words, i, j, k)
                var m = Mat3(substitution_incidence(sigma))
                var klass = specimen_class(screen, m)
                if klass == CLASS_NOT_PRIMITIVE or klass == CLASS_PIP:
                    continue
                var sync = is_synchronizing(sigma)
                out.append(OffCorpusSpecimen(Specimen(len(out), i, j, k, sigma^, m^), klass, sync))
    return out^


# ------------------------------------------------------ strong coincidence


def _pair_letters(index: Int) -> List[Int]:
    """Letters of the unordered pair with `pair_bit` index 0, 1, 2."""
    if index == 0:
        return [0, 1]
    if index == 1:
        return [0, 2]
    return [1, 2]


def witness_level_budget(sigma: List[List[Int]], a: Int, b: Int, word_budget: Int) raises -> Int:
    """The largest level `n <= 32` at which `left_witness` still inflates
    within `word_budget`: it refuses at level `n` when
    `|sigma^(n-1)(x)| * max|sigma| > word_budget` for `x` in `{a, b}`.
    Lengths are summed over images, never built; `0` when even level one is
    over budget."""
    _ = sigma3(sigma)
    var image_bound = 0
    for x in range(ALPHABET):
        image_bound = max(image_bound, len(sigma[x]))
    var length: List[Int] = [1, 1, 1]
    var level = 0
    while level < MAX_WITNESS_LEVEL:
        if length[a] * image_bound > word_budget or length[b] * image_bound > word_budget:
            return level
        level += 1
        var next: List[Int] = [0, 0, 0]
        for x in range(ALPHABET):
            for y in range(len(sigma[x])):
                next[x] += length[sigma[x][y]]
                if next[x] > word_budget:
                    next[x] = word_budget + 1
        length = next^
    return level


def left_witness_levels(sigma: List[List[Int]], word_budget: Int) raises -> List[Int]:
    """For each unordered pair in `pair_bit` order, the least level of a left
    strong-coincidence witness, or `-1` when none exists within the word
    budget (undecided, not a negative)."""
    if word_budget <= 0:
        raise Error("word budget must be positive")
    var out = List[Int]()
    for p in range(PAIRS):
        var letters = _pair_letters(p)
        var levels = witness_level_budget(sigma, letters[0], letters[1], word_budget)
        if levels == 0:
            out.append(-1)
            continue
        var found = left_witness(sigma, letters[0], letters[1], levels, word_budget)
        out.append(found[0])
    return out^


def right_witness_levels(sigma: List[List[Int]], word_budget: Int) raises -> List[Int]:
    """Right strong-coincidence witness levels of `sigma`: the left witness
    levels of the reversed substitution."""
    return left_witness_levels(reversed_substitution(sigma), word_budget)


def witnessed_mask(levels: List[Int]) -> Int:
    var mask = 0
    for p in range(PAIRS):
        if levels[p] >= 1:
            mask |= 1 << p
    return mask


struct CoincidenceProfile(Copyable, Movable):
    """Left and right witness levels; `-1` is undecided."""

    var left: List[Int]
    var right: List[Int]

    def __init__(out self, var left: List[Int], var right: List[Int]):
        self.left = left^
        self.right = right^

    def left_mask(self) -> Int:
        return witnessed_mask(self.left)

    def right_mask(self) -> Int:
        return witnessed_mask(self.right)

    def excludes_strict_systems(self) -> Bool:
        """Theorem A(4), or its reversal: every pair witnessed on one side."""
        return self.left_mask() == ALL_PAIRS_MASK or self.right_mask() == ALL_PAIRS_MASK


def coincidence_profile(sigma: List[List[Int]], word_budget: Int) raises -> CoincidenceProfile:
    return CoincidenceProfile(left_witness_levels(sigma, word_budget), right_witness_levels(sigma, word_budget))


# ------------------------------------------------------------ pair universe


def _encode(w: List[Int]) -> Int:
    var c = 0
    for k in range(len(w)):
        c = 3 * c + w[k]
    return c


struct PairUniverse(Copyable, Movable):
    """A finite set of normalised irreducible noncoincident balanced pairs of
    length `2..max_length`, stored flat (one byte a letter) and looked up
    exactly by the base-3 codes `(code(u), code(v))` of the two sides (first
    letter most significant).

    Built by `add` (which validates each pair) and `seal`: per length `n`,
    `rows[n]` holds the codes as rows `(cu, cv)` sorted lexicographically
    (`psc.binomial_pairs.sorted_row_order`) and `row_index[n]` the member
    index of each row, so a lookup is a binary search; a duplicate raises at
    `seal`. `second_order_zero` records that every member has
    `K_1 = K_2 = 0`."""

    var max_length: Int
    var second_order_zero: Bool
    var sealed: Bool
    var flat_u: List[UInt8]
    var flat_v: List[UInt8]
    var start: List[Int]
    var by_length: List[Int]
    var rows: List[List[Int]]
    var row_index: List[List[Int]]

    def __init__(out self, max_length: Int) raises:
        if max_length < 2 or max_length > MAX_UNIVERSE_LENGTH:
            raise Error("a pair universe holds lengths 2.." + String(MAX_UNIVERSE_LENGTH))
        self.max_length = max_length
        self.second_order_zero = True
        self.sealed = False
        self.flat_u = List[UInt8]()
        self.flat_v = List[UInt8]()
        self.start = [0]
        self.by_length = List[Int](length=max_length + 1, fill=0)
        self.rows = List[List[Int]]()
        self.row_index = List[List[Int]]()
        for _ in range(max_length + 1):
            self.rows.append(List[Int]())
            self.row_index.append(List[Int]())

    def add(mut self, p: Pair) raises:
        """Append one pair: it must be balanced, irreducible, noncoincident,
        normalised (`u_0 < v_0`) and of length `2..max_length`."""
        if self.sealed:
            raise Error("pair universe: add after seal")
        var n = p.length()
        if n < 2 or n > self.max_length or len(p.v) != n:
            raise Error("pair universe: a pair of length outside 2.." + String(self.max_length))
        for t in range(n):
            if p.u[t] < 0 or p.u[t] >= ALPHABET or p.v[t] < 0 or p.v[t] >= ALPHABET:
                raise Error("pair universe: a letter outside the alphabet")
        if not is_balanced(p) or len(coincidence_boundaries(p.u, p.v)) != 2:
            raise Error("pair universe: " + p.key() + " is not an irreducible balanced pair")
        if p.u[0] >= p.v[0]:
            raise Error("pair universe: " + p.key() + " is not normalised (u_0 < v_0)")
        var d = k2(p)
        for t in range(len(d)):
            if d[t] != 0:
                self.second_order_zero = False
        self.rows[n].append(_encode(p.u))
        self.rows[n].append(_encode(p.v))
        self.row_index[n].append(self.size())
        self.by_length[n] += 1
        for t in range(n):
            self.flat_u.append(UInt8(p.u[t]))
            self.flat_v.append(UInt8(p.v[t]))
        self.start.append(len(self.flat_u))

    def seal(mut self) raises:
        """Sort each length's rows for lookup; a duplicate raises."""
        if self.sealed:
            raise Error("pair universe: sealed twice")
        for n in range(self.max_length + 1):
            var count = self.by_length[n]
            if count == 0:
                continue
            var order = sorted_row_order(self.rows[n], 2)
            var sorted_rows = List[Int](capacity=2 * count)
            var index = List[Int](capacity=count)
            for t in range(count):
                sorted_rows.append(self.rows[n][2 * order[t]])
                sorted_rows.append(self.rows[n][2 * order[t] + 1])
                index.append(self.row_index[n][order[t]])
                if t > 0 and sorted_rows[2 * t] == sorted_rows[2 * t - 2] and sorted_rows[2 * t + 1] == sorted_rows[2 * t - 1]:
                    raise Error("pair universe: a duplicate pair of length " + String(n))
            self.rows[n] = sorted_rows^
            self.row_index[n] = index^
        self.sealed = True

    def size(self) -> Int:
        return len(self.start) - 1

    def count_of_length(self, n: Int) -> Int:
        if n < 0 or n > self.max_length:
            return 0
        return self.by_length[n]

    def pair(self, i: Int) -> Pair:
        """Member `i` as a `Pair`."""
        var u = List[Int]()
        var v = List[Int]()
        for k in range(self.start[i], self.start[i + 1]):
            u.append(Int(self.flat_u[k]))
            v.append(Int(self.flat_v[k]))
        return Pair(u^, v^)

    def lookup(self, n: Int, cu: Int, cv: Int) -> Int:
        """Member index of the normalised pair of length `n` with codes
        `(cu, cv)`, or `-1`. Only meaningful once sealed."""
        if n < 2 or n > self.max_length or self.by_length[n] == 0:
            return -1
        ref r = self.rows[n]
        var lo = 0
        var hi = self.by_length[n]
        while lo < hi:
            var mid = (lo + hi) // 2
            var a = r[2 * mid]
            var b = r[2 * mid + 1]
            if a < cu or (a == cu and b < cv):
                lo = mid + 1
            else:
                hi = mid
        if lo < self.by_length[n] and r[2 * lo] == cu and r[2 * lo + 1] == cv:
            return self.row_index[n][lo]
        return -1

    def index_of(self, p: Pair) -> Int:
        """Index of the normalisation of `p`, or `-1` when it is not a member."""
        var q = normalise(p)
        return self.lookup(q.length(), _encode(q.u), _encode(q.v))


def universe_of(max_length: Int, pairs: List[Pair]) raises -> PairUniverse:
    """A sealed universe holding exactly `pairs` (each validated by `add`)."""
    var out = PairUniverse(max_length)
    for i in range(len(pairs)):
        out.add(pairs[i])
    out.seal()
    return out^


def k2_zero_universe(max_length: Int) raises -> PairUniverse:
    """`P_L` for `L = max_length`: every normalised irreducible noncoincident
    ternary pair with `K_1 = K_2 = 0` and length at most `L`, read from the
    exact census of experiment A (`census_length(3, n, DEGREE_THREE)` for
    `n = 2..L`; it keeps every pair of first defect degree at least three,
    which is every `K_2 = 0` pair, as `(u, v)` with `u` lexicographically
    first). Raises unless the kept list has exactly the census's `K_2 = 0`
    count at each length and every member has `K_2 = 0`.

    Those two checks guard against a `kept_from` mismatch and a mislabelled
    member only: with `kept_from = DEGREE_THREE` the kept count and the
    `K_2 = 0` count come from the same loop of `census_length`, so they cannot
    detect a pair the enumeration missed. Completeness of `P_L` rests on the
    exactness of `census_length`'s class enumeration, pinned by
    `tests/test_binomial_pair_census.mojo` for `n <= 13`, and on independent
    replays of its `K_2 = 0` counts (`oracles/python/c4_closed_component_search.py
    universe L`)."""
    if max_length < 2:
        raise Error("the K2 = 0 universe needs L >= 2")
    var out = PairUniverse(max_length)
    for n in range(2, max_length + 1):
        var c = census_length(ALPHABET, n, DEGREE_THREE)
        if len(c.pairs) != c.k2_zero():
            raise Error("census at n = " + String(n) + " kept " + String(len(c.pairs)) + " of " + String(c.k2_zero()) + " K2 = 0 pairs")
        for i in range(len(c.pairs)):
            out.add(c.pairs[i])
    out.seal()
    if not out.second_order_zero:
        raise Error("the K2 = 0 universe holds a pair with K2 != 0")
    return out^


# --------------------------------------------------------- streamed children


struct ImageTable(Copyable, Movable):
    """The images of `sigma` laid out flat, computed once per specimen:
    `sigma(a)` is `letters[start[a] : start[a + 1]]` (AGENTS.md rule 3)."""

    var letters: List[Int]
    var start: List[Int]

    def __init__(out self, sigma: List[List[Int]]) raises:
        """Raises (never aborts) on a malformed or erasing `sigma`."""
        self.letters = List[Int]()
        self.start = List[Int]()
        if len(sigma) != ALPHABET:
            raise Error("an image table needs three images")
        for a in range(ALPHABET):
            if len(sigma[a]) == 0:
                raise Error("an image table needs a nonerasing substitution")
            self.start.append(len(self.letters))
            for t in range(len(sigma[a])):
                if sigma[a][t] < 0 or sigma[a][t] >= ALPHABET:
                    raise Error("an image letter outside the alphabet")
                self.letters.append(sigma[a][t])
        self.start.append(len(self.letters))


def child_indices(images: ImageTable, universe: PairUniverse, i: Int, mut out: List[Int]) raises -> Bool:
    """The normalised children of member `i` as universe indices, in factor
    order, streamed over the two inflations without building them. Returns
    `False` as soon as a child is coincident, longer than
    `universe.max_length`, or not a member (then `out` is a partial list).
    A zero return is `p(prefix of the u-track) = p(prefix of the v-track)`,
    tracked by the first two coordinates of the difference (the third is
    their negated sum, both tracks having read the same number of letters).
    A block is oriented by its first letters, which differ on an irreducible
    noncoincident block. An inflation that does not close raises."""
    if not universe.sealed:
        raise Error("child_indices needs a sealed universe")
    out.clear()
    var limit = universe.max_length
    var n = universe.start[i + 1] - universe.start[i]
    var base = universe.start[i]
    var iu = 0
    var iv = 0
    var pu = images.start[Int(universe.flat_u[base])]
    var eu = images.start[Int(universe.flat_u[base]) + 1]
    var pv = images.start[Int(universe.flat_v[base])]
    var ev = images.start[Int(universe.flat_v[base]) + 1]
    var d0 = 0
    var d1 = 0
    var block = 0
    var cu = 0
    var cv = 0
    var fa = 0
    var fb = 0
    while True:
        var a = images.letters[pu]
        var b = images.letters[pv]
        pu += 1
        pv += 1
        if block == 0:
            fa = a
            fb = b
        block += 1
        if block > limit:
            return False
        cu = 3 * cu + a
        cv = 3 * cv + b
        if a == 0:
            d0 += 1
        elif a == 1:
            d1 += 1
        if b == 0:
            d0 -= 1
        elif b == 1:
            d1 -= 1
        if d0 == 0 and d1 == 0:
            if block == 1:
                return False  # a coincident child (a, a)
            var idx = universe.lookup(block, cu, cv) if fa < fb else universe.lookup(block, cv, cu)
            if idx < 0:
                return False
            out.append(idx)
            block = 0
            cu = 0
            cv = 0
        if pu == eu:
            iu += 1
            if iu < n:
                pu = images.start[Int(universe.flat_u[base + iu])]
                eu = images.start[Int(universe.flat_u[base + iu]) + 1]
        if pv == ev:
            iv += 1
            if iv < n:
                pv = images.start[Int(universe.flat_v[base + iv])]
                ev = images.start[Int(universe.flat_v[base + iv]) + 1]
        if iu == n or iv == n:
            break
    if block != 0 or iu != n or iv != n:
        raise Error("an inflation of a balanced pair did not close")
    return True


# ---------------------------------------------------- greatest fixed point


struct WindowCore(Copyable, Movable):
    """The greatest fixed point of `X -> {T in X : children(T) <= X}` below a
    universe. `first_pass` counts the members all of whose children are
    members; `rounds` the removal rounds after it; `members` are the
    survivors (universe indices, increasing) and `adj[s]` the children of
    `members[s]`, as positions in `members`, in factor order."""

    var universe_size: Int
    var first_pass: Int
    var rounds: Int
    var members: List[Int]
    var adj: List[List[Int]]

    def __init__(out self, universe_size: Int, first_pass: Int, rounds: Int, var members: List[Int], var adj: List[List[Int]]):
        self.universe_size = universe_size
        self.first_pass = first_pass
        self.rounds = rounds
        self.members = members^
        self.adj = adj^

    def survivors(self) -> Int:
        return len(self.members)


def greatest_fixed_point(sigma: List[List[Int]], universe: PairUniverse) raises -> WindowCore:
    """Iterate the removal of members with a child outside the current set,
    from the whole universe, to the fixed point. Exact and finite."""
    var images = ImageTable(sigma)
    var cand = List[Int]()
    var cand_children = List[List[Int]]()
    var scratch = List[Int]()
    for i in range(universe.size()):
        if child_indices(images, universe, i, scratch):
            cand.append(i)
            cand_children.append(scratch.copy())
    var first = len(cand)
    if first == 0:
        return WindowCore(universe.size(), 0, 0, List[Int](), List[List[Int]]())
    var pos = Dict[Int, Int]()
    for c in range(first):
        pos[cand[c]] = c
    # children as candidate positions; -1 for a member that is not a candidate
    var kids = List[List[Int]]()
    for c in range(first):
        var row = List[Int]()
        for t in range(len(cand_children[c])):
            row.append(pos.get(cand_children[c][t], -1))
        kids.append(row^)
    var alive = List[Bool](length=first, fill=True)
    var rounds = 0
    var changed = True
    while changed:
        changed = False
        var dead = List[Int]()
        for c in range(first):
            if not alive[c]:
                continue
            for t in range(len(kids[c])):
                var k = kids[c][t]
                if k < 0 or not alive[k]:
                    dead.append(c)
                    break
        if len(dead) > 0:
            changed = True
            rounds += 1
            for d in range(len(dead)):
                alive[dead[d]] = False
    var renumber = List[Int](length=first, fill=-1)
    var members = List[Int]()
    for c in range(first):
        if alive[c]:
            renumber[c] = len(members)
            members.append(cand[c])
    var adj = List[List[Int]]()
    for c in range(first):
        if alive[c]:
            var row = List[Int]()
            for t in range(len(kids[c])):
                var kc = kids[c][t]
                if kc < 0 or renumber[kc] < 0:
                    raise Error("greatest fixed point: a survivor has a removed child")
                row.append(renumber[kc])
            adj.append(row^)
    return WindowCore(universe.size(), first, rounds, members^, adj^)


def core_automaton(universe: PairUniverse, core: WindowCore) -> Automaton:
    """The survivors as a complete (uncapped) `substitution_dynamics` graph."""
    var states = List[Pair]()
    for s in range(core.survivors()):
        states.append(universe.pair(core.members[s]))
    return Automaton(states, core.adj, False, ALPHABET)


def strict_carriers(a: Automaton) raises -> List[List[Int]]:
    """The strict carriers of a closed noncoincident graph, read with
    `psc.carrier.profile_component` (recurrent SCC, no coincidence child, no
    exit), in Tarjan emission order. A nonempty graph without one raises: a
    finite closed set has a sink SCC, and a noncoincident state has a child."""
    var out = List[List[Int]]()
    var comps = sccs(a.adj)
    for c in range(len(comps)):
        ref comp = comps[c]
        if not has_cycle(a.adj, comp):
            continue
        if profile_component(a, comp).is_closed_nonproductive():
            out.append(comp.copy())
    if a.size() > 0 and len(out) == 0:
        raise Error("a nonempty closed set carries no strict carrier")
    return out^


# --------------------------------------------- facts about a found carrier


def first_pair_mask_of(states: List[Pair]) raises -> Int:
    var mask = 0
    for s in range(len(states)):
        mask |= pair_bit(states[s].u[0], states[s].v[0])
    return mask


def last_pair_mask_of(states: List[Pair]) raises -> Int:
    var mask = 0
    for s in range(len(states)):
        var n = states[s].length()
        mask |= pair_bit(states[s].u[n - 1], states[s].v[n - 1])
    return mask


def least_defect_degree(states: List[Pair]) -> Int:
    """`r(C)`: the least first defect degree over the states (`2`, `3`, `4`,
    or `DEGREE_FIVE_PLUS` for `r >= 5`, undetermined beyond four)."""
    var r = DEGREE_FIVE_PLUS
    for s in range(len(states)):
        r = min(r, first_defect_degree(states[s]))
    return r


def verify_ordered_lift(sigma: List[List[Int]], states: List[Pair]) raises -> Int:
    """Re-derive the carrier on ordered pairs with the independent builder
    `psc.c4_cut_attractor.strict_closure` (which raises on a coincident
    factor) from its first state, and check that the ordered closure
    normalises onto the carrier. Returns the ordered size, `m` or `2m`."""
    if len(states) == 0:
        raise Error("empty component")
    var closure = strict_closure(sigma, states[0], 4 * len(states) + 4)
    var seen = Dict[String, Int]()
    for s in range(len(states)):
        seen[states[s].key()] = s
    var hit = List[Bool](length=len(states), fill=False)
    for t in range(closure.size()):
        var key = normalise(closure.states[t]).key()
        if key not in seen:
            raise Error("ordered closure leaves the normalised component")
        hit[seen[key]] = True
    for s in range(len(states)):
        if not hit[s]:
            raise Error("ordered closure misses a state of the component")
    if closure.size() != len(states) and closure.size() != 2 * len(states):
        raise Error("ordered lift is neither the component nor its double cover")
    return closure.size()


struct WindowComponent(Copyable, Movable):
    """One strict carrier found in a window: its normalised states, the size
    of its ordered lift, its first- and last-letter pair masks, `r(C)` and
    its longest state."""

    var states: List[Pair]
    var ordered_size: Int
    var first_mask: Int
    var last_mask: Int
    var degree: Int
    var longest: Int

    def __init__(out self, sigma: List[List[Int]], var states: List[Pair]) raises:
        self.ordered_size = verify_ordered_lift(sigma, states)
        self.first_mask = first_pair_mask_of(states)
        self.last_mask = last_pair_mask_of(states)
        self.degree = least_defect_degree(states)
        self.longest = 0
        for s in range(len(states)):
            self.longest = max(self.longest, states[s].length())
        self.states = states^


def component_automaton(sigma: List[List[Int]], states: List[Pair]) raises -> Automaton:
    """A supplied normalised component as a complete graph numbered `0..m-1`,
    its normalised children recomputed with `psc.bpa`; a child outside the
    component raises (the component is not closed)."""
    var adj = List[List[Int]]()
    var where = Dict[String, Int]()
    for s in range(len(states)):
        where[states[s].key()] = s
    for s in range(len(states)):
        var row = List[Int]()
        var blocks = decompose(apply_substitution(sigma, states[s].u), apply_substitution(sigma, states[s].v))
        for k in range(len(blocks)):
            var key = normalise(blocks[k]).key()
            if key not in where:
                raise Error("a child leaves the supplied component")
            row.append(where[key])
        adj.append(row^)
    return Automaton(states, adj, False, ALPHABET)


def ordered_children(sigma: List[List[Int]], a: Automaton) raises -> List[Int]:
    """The ordered child rows of a closed normalised component `a` (from
    `component_automaton`), flat, four entries a row `(i, k, j, o)`: the
    `k`-th block of `red(sigma(u_i), sigma(v_i))` is state `j` (`o = 0`) or
    its swap (`o = 1`). A block that is neither raises."""
    var out = List[Int]()
    for s in range(a.size()):
        ref state = a.states[s]
        var blocks = decompose(apply_substitution(sigma, state.u), apply_substitution(sigma, state.v))
        if len(blocks) != len(a.adj[s]):
            raise Error("ordered children: the component graph and the factorisation disagree")
        for k in range(len(blocks)):
            var j = a.adj[s][k]
            var o = 0 if blocks[k] == a.states[j] else 1
            if o == 1 and Pair(blocks[k].v, blocks[k].u) != a.states[j]:
                raise Error("an ordered child is neither the state nor its swap")
            out += [s, k, j, o]
    return out^


def lift_size(states: Int, rows: List[Int]) raises -> Int:
    """The size of the ordered closure of state `0` in orientation `0`,
    read from `ordered_children` rows: a swapped state's children are the
    swaps of its children (Lemma 1 of the docs note), so `(i, e)` has the
    child `(j, e xor o)`. An independent recount of `verify_ordered_lift`."""
    if states <= 0 or len(rows) % 4 != 0:
        raise Error("lift_size needs a nonempty component and whole rows")
    var seen = List[Bool](length=2 * states, fill=False)
    var stack: List[Int] = [0]
    seen[0] = True
    var count = 1
    while len(stack) > 0:
        var x = stack.pop()
        var i = x // 2
        var e = x % 2
        for t in range(len(rows) // 4):
            if rows[4 * t] != i:
                continue
            var y = 2 * rows[4 * t + 2] + (e ^ rows[4 * t + 3])
            if not seen[y]:
                seen[y] = True
                count += 1
                stack.append(y)
    return count


def emit_component(prefix: String, specimen_fields: String, comp_id: Int, sigma: List[List[Int]], c: WindowComponent) raises:
    """One exact replayable record: a `<prefix>_COMPONENT_META` line, the
    `psc.carrier.emit_countermodel` block (states `u|v`, normalised edges),
    and one `<prefix>_ORDERED_CHILD i k j o` line per row of
    `ordered_children`. Together they are the exact ordered strict system.
    Raises unless `lift_size` of those rows equals `c.ordered_size`."""
    var a = component_automaton(sigma, c.states)
    var rows = ordered_children(sigma, a)
    if lift_size(len(c.states), rows) != c.ordered_size:
        raise Error("the ordered child rows and the ordered closure disagree on the lift")
    print(
        prefix + "_COMPONENT_META {" + specimen_fields + ",\"component\":" + String(comp_id)
        + ",\"states\":" + String(len(c.states)) + ",\"ordered_states\":" + String(c.ordered_size)
        + ",\"longest\":" + String(c.longest) + ",\"degree\":" + String(c.degree)
        + ",\"first_pairs\":" + String(c.first_mask) + ",\"last_pairs\":" + String(c.last_mask) + "}"
    )
    var comp = List[Int]()
    for s in range(len(c.states)):
        comp.append(s)
    emit_countermodel(prefix, specimen_fields, comp_id, a, comp)
    for t in range(len(rows) // 4):
        print(prefix + "_ORDERED_CHILD", rows[4 * t], rows[4 * t + 1], rows[4 * t + 2], rows[4 * t + 3])


# --------------------------------------------------------- one specimen


struct WindowRecord(Copyable, Movable):
    """Everything the window search records about one specimen.
    `violations` names each consistency check it fails; the census raises on
    any (refuse to conclude)."""

    var klass: Int
    var synchronizing: Bool
    var left: List[Int]
    var right: List[Int]
    var universe_size: Int
    var first_pass: Int
    var rounds: Int
    var survivors: Int
    var components: List[WindowComponent]
    var violations: List[String]

    def __init__(out self, klass: Int, synchronizing: Bool, profile: CoincidenceProfile, core: WindowCore):
        self.klass = klass
        self.synchronizing = synchronizing
        self.left = profile.left.copy()
        self.right = profile.right.copy()
        self.universe_size = core.universe_size
        self.first_pass = core.first_pass
        self.rounds = core.rounds
        self.survivors = core.survivors()
        self.components = List[WindowComponent]()
        self.violations = List[String]()

    def left_all(self) -> Bool:
        return witnessed_mask(self.left) == ALL_PAIRS_MASK

    def right_all(self) -> Bool:
        return witnessed_mask(self.right) == ALL_PAIRS_MASK

    def coincidence_excludes(self) -> Bool:
        """All three pairs witnessed on one side: no strict system at all
        (Theorem A(4) or its reversal), a verdict."""
        return self.left_all() or self.right_all()

    def violation_line(self) -> String:
        var out = String("violations:")
        for v in range(len(self.violations)):
            out += " " + self.violations[v]
        return out


def specimen_violations(klass: Int, synchronizing: Bool, coincidence_excludes: Bool) -> List[String]:
    """The specimen-level checks a nonempty limit must pass, each failure
    named: `A4-all-pairs` (all pairs witnessed on one side: Theorem A(4) and
    its reversal), `endpoint` (a synchronizing specimen: stop/go §4.3 item 1),
    `R3` (the both-outside class: Theorem R3). Call only on a nonempty limit."""
    var out = List[String]()
    if coincidence_excludes:
        out.append("A4-all-pairs")
    if synchronizing:
        out.append("endpoint")
    if klass == CLASS_BOTH_OUTSIDE:
        out.append("R3")
    return out^


def r3prime_violation(chi: List[Int], degree: Int) raises -> String:
    """The R3' check of one carrier with `r(C) = degree` over the cubic `chi`
    of a specimen labelled one-outside: `R3prime-degree` for
    `r(C) = 2 (mod 3)`, `R3prime-det-power` for `r(C) = 3k` with
    `|det M|^k > beta`, `R3prime-unimodular` for `r(C) = 3k + 1` with
    `|det M| != 1`, and `""` when the carrier passes or `r(C)` is
    `DEGREE_FIVE_PLUS` (not determined, not checked). Raises on a cubic that
    is not irreducible, on every branch, so a mislabelled class fails closed
    whatever the degree."""
    if not is_irreducible_cubic(chi):
        raise Error("the R3' check needs an irreducible cubic")
    if degree < 2:
        raise Error("a balanced pair has first defect degree at least two")
    if degree >= DEGREE_FIVE_PLUS:
        return ""
    if degree % 3 == 2:
        return "R3prime-degree"
    if degree % 3 == 0:
        return "" if det_power_below_perron(chi, degree // 3) else "R3prime-det-power"
    return "" if abs(chi[0]) == 1 else "R3prime-unimodular"


def carrier_violations(
    klass: Int, chi: List[Int], left_mask: Int, right_mask: Int, first_mask: Int, last_mask: Int, degree: Int
) raises -> List[String]:
    """The carrier-level checks, each failure named: `A4-left` / `A4-right`
    (a left-witnessed first-letter pair or a right-witnessed last-letter
    pair: Theorem A(4) and its reversal), `R2` (`r(C) = 2` over an
    irreducible non-Pisot cubic: Theorem R2) and the `r3prime_violation` of
    a one-outside carrier (Theorem R3')."""
    var out = List[String]()
    if first_mask & left_mask:
        out.append("A4-left")
    if last_mask & right_mask:
        out.append("A4-right")
    if (klass == CLASS_ONE_OUTSIDE or klass == CLASS_BOTH_OUTSIDE) and degree == 2:
        out.append("R2")
    if klass == CLASS_ONE_OUTSIDE:
        var name = r3prime_violation(chi, degree)
        if name != "":
            out.append(name)
    return out^


def window_specimen(
    sigma: List[List[Int]], klass: Int, synchronizing: Bool, universe: PairUniverse, word_budget: Int
) raises -> WindowRecord:
    """The strong-coincidence profile and the window of one specimen, every
    strict carrier of a nonempty limit, and the consistency checks the
    results must satisfy (each failure named in `violations`):

    * `A4-all-pairs`: a nonempty limit although all pairs are witnessed on
      one side; `A4-left` / `A4-right`: a carrier with a left-witnessed
      first-letter pair or a right-witnessed last-letter pair (Theorem A(4)
      and its reversal);
    * `endpoint`: a nonempty limit on a synchronizing specimen (§4.3 item 1);
    * `R3`: a nonempty limit in the both-outside class (Theorem R3);
    * `R2`: a carrier state with `K_2 != 0` over an irreducible non-Pisot
      cubic (only possible with a universe that is not `P_L`);
    * `R3prime-degree`, `R3prime-det-power`, `R3prime-unimodular`: a
      one-outside carrier with `r(C) = 2 (mod 3)`, or `r(C) = 3k` with
      `|det M|^k > beta`, or `r(C) = 3k + 1` with `|det M| != 1` (Theorem
      R3'; `r >= 5` is not determined here and not checked; a reducible cubic
      labelled one-outside raises).

    The checks are `specimen_violations` and `carrier_violations`."""
    var core = greatest_fixed_point(sigma, universe)  # raises first on a malformed or erasing sigma
    var r = WindowRecord(klass, synchronizing, coincidence_profile(sigma, word_budget), core)
    if core.survivors() == 0:
        return r^
    var a = core_automaton(universe, core)
    var carriers = strict_carriers(a)
    for c in range(len(carriers)):
        var states = List[Pair]()
        for s in range(len(carriers[c])):
            states.append(a.states[carriers[c][s]].copy())
        r.components.append(WindowComponent(sigma, states^))
    r.violations = specimen_violations(klass, synchronizing, r.coincidence_excludes())
    var left = witnessed_mask(r.left)
    var right = witnessed_mask(r.right)
    var chi = Mat3(substitution_incidence(sigma)).charpoly()
    for c in range(len(r.components)):
        ref comp = r.components[c]
        r.violations += carrier_violations(klass, chi, left, right, comp.first_mask, comp.last_mask, comp.degree)
    return r^
