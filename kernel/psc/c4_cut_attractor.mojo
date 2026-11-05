"""Cut-attractor bookkeeping of a supplied strict C4 system, the first-letter
configuration census and the endpoint-collapse survey.

Contract (docs/c4-cut-attractor-window-2026-11-05.md). For the ordered child
closure `C` of a seed:

* the child matrix `N` and the Parikh matrix `P` satisfy `P N = M P`;
* every interior cut of `sigma(F)` lies inside one top image
  `sigma(u_F[i]) = Q c s` and one bottom image `sigma(v_F[i']) = Q' c' s'`
  with `d = M p(u_F[:i]) + p(Q) = M p(v_F[:i']) + p(Q')`, the letters after
  the cut are the child's first letters, and `e = p(u_F[:i]) - p(v_F[:i'])`
  is nonzero (the nesting data of Lemma N; the attractor `K_S` is the limit
  of these translations along backward paths and is not computed here);
* the cut lattice of `sigma^n(S)` is the multiplicity-one union
  `X_{n+1}(S) = U (M X_n(F) + d_{F,j})` (the recursion behind Lemma G);
* every cut pair of every inflation lies in `A(C)` (Theorem A(2)).

The configuration census enumerates the first-letter maps compatible with
Theorem A(3) and a left good edge. The endpoint-collapse survey counts the
corpus specimens whose prefix or suffix map is eventually constant, where every
letter pair has a trivial strong-coincidence witness. The bounded left-witness
search reports an exhausted budget as `-1`, never as a verdict.

Everything here is integer arithmetic on finite words. A coincident factor, a
cap, a failed identity or a malformed input raises (fail closed: refuse to
conclude). No C4, BH, G1, A1' or PSC inference is made.
"""

from psc.bpa import apply_substitution, coincidence_boundaries, sigma3, substitution_incidence
from psc.c4_cut_pair_reduction import pair_bit
from psc.corpus import Specimen
from psc.endpoint_core import (
    LetterPair,
    TYPE_A,
    TYPE_B,
    all_maps,
    endpoint_type,
    nonsynchronizing_pairs,
    prefix_endpoint_map,
    suffix_endpoint_map,
    synchronizes,
)
from psc.histogram import Histogram
from psc.words import ALPHABET, Pair, is_balanced, parikh

comptime KEY_RADIX = 1 << 20


def _slice(w: List[Int], start: Int, stop: Int) -> List[Int]:
    var out = List[Int](capacity=stop - start)
    for k in range(start, stop):
        out.append(w[k])
    return out^


def _check_letters(w: List[Int]) raises:
    for k in range(len(w)):
        if w[k] < 0 or w[k] >= ALPHABET:
            raise Error("letter outside the three-letter alphabet")


def _matvec(inc: List[Int], v: List[Int]) -> List[Int]:
    """`M v` for the row-major incidence `inc` of `substitution_incidence`."""
    var out: List[Int] = [0, 0, 0]
    for i in range(ALPHABET):
        for j in range(ALPHABET):
            out[i] += inc[ALPHABET * i + j] * v[j]
    return out^


def _add(a: List[Int], b: List[Int]) -> List[Int]:
    return [a[0] + b[0], a[1] + b[1], a[2] + b[2]]


def _key(v: List[Int]) -> Int:
    return (v[0] * KEY_RADIX + v[1]) * KEY_RADIX + v[2]


def _power(sigma: List[List[Int]], w: List[Int], n: Int) -> List[Int]:
    var out = w.copy()
    for _ in range(n):
        out = apply_substitution(sigma, out)
    return out^


struct StrictClosure(Copyable, Movable):
    """Ordered child closure of a seed. `rows[S]` lists the children of state
    `S` in factor order; `cuts[S]` gives the letter index of each child's cut
    in `sigma(u_S)` (the first child has cut 0)."""

    var states: List[Pair]
    var rows: List[List[Int]]
    var cuts: List[List[Int]]

    def __init__(out self, states: List[Pair], rows: List[List[Int]], cuts: List[List[Int]]):
        self.states = states.copy()
        self.rows = rows.copy()
        self.cuts = cuts.copy()

    def size(self) -> Int:
        return len(self.states)

    def index_of(self, p: Pair) -> Int:
        for i in range(len(self.states)):
            if self.states[i] == p:
                return i
        return -1

    def first_pair_mask(self) raises -> Int:
        var mask = 0
        for i in range(len(self.states)):
            mask |= pair_bit(self.states[i].u[0], self.states[i].v[0])
        return mask


def strict_closure(sigma: List[List[Int]], seed: Pair, cap: Int = 256) raises -> StrictClosure:
    """Breadth-first ordered child closure. Raises on a coincident factor (the
    seed does not generate a strict system), on the state cap, and on a
    malformed, unbalanced, reducible or coincident seed."""
    _ = sigma3(sigma)
    _check_letters(seed.u)
    _check_letters(seed.v)
    if seed.length() == 0 or not is_balanced(seed):
        raise Error("seed is not a nonempty balanced pair")
    if len(coincidence_boundaries(seed.u, seed.v)) != 2:
        raise Error("seed is reducible")
    if seed.is_coincidence():
        raise Error("seed is a coincidence")
    if cap <= 0:
        raise Error("state cap must be positive")
    var states: List[Pair] = [seed.copy()]
    var rows = List[List[Int]]()
    var cuts = List[List[Int]]()
    var q = 0
    while q < len(states):
        var top = apply_substitution(sigma, states[q].u)
        var bottom = apply_substitution(sigma, states[q].v)
        var bounds = coincidence_boundaries(top, bottom)
        var row = List[Int]()
        var row_cuts = List[Int]()
        for k in range(len(bounds) - 1):
            var child = Pair(_slice(top, bounds[k], bounds[k + 1]), _slice(bottom, bounds[k], bounds[k + 1]))
            if child.is_coincidence():
                raise Error("coincident factor reached: the seed does not generate a strict system")
            var idx = -1
            for i in range(len(states)):
                if states[i] == child:
                    idx = i
                    break
            if idx < 0:
                if len(states) >= cap:
                    raise Error("strict closure exceeded the state cap")
                states.append(child.copy())
                idx = len(states) - 1
            row.append(idx)
            row_cuts.append(bounds[k])
        rows.append(row.copy())
        cuts.append(row_cuts.copy())
        q += 1
    return StrictClosure(states, rows, cuts)


def child_matrix(c: StrictClosure) -> List[List[Int]]:
    """`N[T][S]`: number of occurrences of state `T` among the children of `S`."""
    var n = c.size()
    var N = List[List[Int]]()
    for _ in range(n):
        N.append(List[Int](length=n, fill=0))
    for s in range(n):
        for j in range(len(c.rows[s])):
            var t = c.rows[s][j]
            N[t][s] += 1
    return N^


def parikh_matrix(c: StrictClosure) -> List[List[Int]]:
    """`P[i][S]`: the `i`-th Parikh coordinate of state `S`."""
    var P = List[List[Int]]()
    for _ in range(ALPHABET):
        P.append(List[Int](length=c.size(), fill=0))
    for s in range(c.size()):
        var p = parikh(c.states[s].u)
        for i in range(ALPHABET):
            P[i][s] = p[i]
    return P^


def intertwines(sigma: List[List[Int]], c: StrictClosure) -> Bool:
    """`P N = M P`, the global Parikh intertwiner of a complete child-closed system."""
    var inc = substitution_incidence(sigma)
    var N = child_matrix(c)
    var P = parikh_matrix(c)
    for i in range(ALPHABET):
        for s in range(c.size()):
            var lhs = 0
            for t in range(c.size()):
                lhs += P[i][t] * N[t][s]
            var rhs = 0
            for j in range(ALPHABET):
                rhs += inc[ALPHABET * i + j] * P[j][s]
            if lhs != rhs:
                return False
    return True


struct CutEdge(Copyable, Movable):
    """One interior child edge `(F, j) -> S` with its cut translation and the
    two-track nesting data: the cut lies inside `sigma(u_F[top_source])` after
    `top_prefix` letters, and inside `sigma(v_F[bottom_source])` after
    `bottom_prefix` letters."""

    var parent: Int
    var child: Int
    var cut: Int
    var translation: List[Int]
    var top_source: Int
    var top_prefix: Int
    var bottom_source: Int
    var bottom_prefix: Int

    def __init__(
        out self, parent: Int, child: Int, cut: Int, translation: List[Int],
        top_source: Int, top_prefix: Int, bottom_source: Int, bottom_prefix: Int,
    ):
        self.parent = parent
        self.child = child
        self.cut = cut
        self.translation = translation.copy()
        self.top_source = top_source
        self.top_prefix = top_prefix
        self.bottom_source = bottom_source
        self.bottom_prefix = bottom_prefix


def _locate(sigma: List[List[Int]], word: List[Int], pos: Int) raises -> List[Int]:
    """`[i, q]`: the letter `word[i]` whose image contains index `pos` of
    `sigma(word)`, and the offset `q` of `pos` inside that image."""
    var acc = 0
    for i in range(len(word)):
        var image_length = len(sigma[word[i]])
        if acc <= pos and pos < acc + image_length:
            return [i, pos - acc]
        acc += image_length
    raise Error("cut position lies outside the inflated word")


def cut_edges(sigma: List[List[Int]], c: StrictClosure) raises -> List[CutEdge]:
    """The interior child edges with the identities of Lemma N checked exactly;
    an identity failure raises, because it would contradict a proved statement
    and so signals corrupted input."""
    var inc = substitution_incidence(sigma)
    var out = List[CutEdge]()
    for f in range(c.size()):
        var u = c.states[f].u.copy()
        var v = c.states[f].v.copy()
        var top = apply_substitution(sigma, u)
        for j in range(len(c.rows[f])):
            var pos = c.cuts[f][j]
            if pos == 0:
                continue
            var d = parikh(_slice(top, 0, pos))
            var where_top = _locate(sigma, u, pos)
            var where_bottom = _locate(sigma, v, pos)
            var i = where_top[0]
            var q = where_top[1]
            var i2 = where_bottom[0]
            var q2 = where_bottom[1]
            var lhs_top = _add(_matvec(inc, parikh(_slice(u, 0, i))), parikh(_slice(sigma[u[i]], 0, q)))
            var lhs_bottom = _add(_matvec(inc, parikh(_slice(v, 0, i2))), parikh(_slice(sigma[v[i2]], 0, q2)))
            if lhs_top != d or lhs_bottom != d:
                raise Error("cut translation does not match its two-track decomposition")
            var child = c.states[c.rows[f][j]].copy()
            if sigma[u[i]][q] != child.u[0] or sigma[v[i2]][q2] != child.v[0]:
                raise Error("letter after the cut is not the child's first letter")
            var pu = parikh(_slice(u, 0, i))
            var pv = parikh(_slice(v, 0, i2))
            if pu == pv:
                raise Error("zero source defect at an interior cut: the parent tiles coincide")
            out.append(CutEdge(f, c.rows[f][j], pos, d, i, q, i2, q2))
    return out^


def shifted_source_count(c: StrictClosure, edges: List[CutEdge]) -> Int:
    """Interior edges whose top source letter differs from the parent's first
    letter: the nesting is piecewise, not a vertex map of the two GIFS graphs."""
    var n = 0
    for k in range(len(edges)):
        var u = c.states[edges[k].parent].u.copy()
        if u[edges[k].top_source] != u[0]:
            n += 1
    return n


def _count_key(keys: List[Int], key: Int) -> Int:
    var n = 0
    for k in range(len(keys)):
        if keys[k] == key:
            n += 1
    return n


def cut_lattice_recursion_holds(sigma: List[List[Int]], c: StrictClosure, depth: Int) raises -> Bool:
    """`X_{n+1}(S) = U (M X_n(F) + d_{F,j})` with multiplicity one, checked for
    every root and every `n <= depth` against the direct factorisation of
    `sigma^n(root)`. A factor outside the closure raises."""
    if depth < 1 or depth > 6:
        raise Error("recursion depth must lie in 1..6")
    var inc = substitution_incidence(sigma)
    var n = c.size()
    # translation of every child edge, including the first child (zero).
    var translations = List[List[List[Int]]]()
    for f in range(n):
        var top = apply_substitution(sigma, c.states[f].u)
        var row = List[List[Int]]()
        for j in range(len(c.rows[f])):
            row.append(parikh(_slice(top, 0, c.cuts[f][j])))
        translations.append(row.copy())
    for root in range(n):
        var current = List[List[List[Int]]]()
        for _ in range(n):
            current.append(List[List[Int]]())
        current[root].append([0, 0, 0])
        for level in range(1, depth + 1):
            var following = List[List[List[Int]]]()
            for _ in range(n):
                following.append(List[List[Int]]())
            for f in range(n):
                for x in range(len(current[f])):
                    var mx = _matvec(inc, current[f][x])
                    for j in range(len(c.rows[f])):
                        following[c.rows[f][j]].append(_add(mx, translations[f][j]))
            # direct factorisation of sigma^level(root)
            var top = _power(sigma, c.states[root].u, level)
            var bottom = _power(sigma, c.states[root].v, level)
            var bounds = coincidence_boundaries(top, bottom)
            var direct = List[List[Int]]()
            for _ in range(n):
                direct.append(List[Int]())
            for k in range(len(bounds) - 1):
                var factor = Pair(_slice(top, bounds[k], bounds[k + 1]), _slice(bottom, bounds[k], bounds[k + 1]))
                var s = c.index_of(factor)
                if s < 0:
                    raise Error("a factor of an inflation lies outside the supplied closure")
                direct[s].append(_key(parikh(_slice(top, 0, bounds[k]))))
            for s in range(n):
                if len(direct[s]) != len(following[s]):
                    return False
                var keys = List[Int]()
                for x in range(len(following[s])):
                    keys.append(_key(following[s][x]))
                for x in range(len(keys)):
                    if _count_key(keys, keys[x]) != 1 or _count_key(direct[s], keys[x]) != 1:
                        return False
            current = following.copy()
    return True


def inflated_first_pair_mask(sigma: List[List[Int]], c: StrictClosure, depth: Int) raises -> Int:
    """Bit mask of the first pairs of all factors of `sigma^n(S)`, `1 <= n <= depth`;
    a pair outside `A(C)` or a coincident factor raises (Theorem A(2) fails)."""
    if depth < 1 or depth > 8:
        raise Error("inflation depth must lie in 1..8")
    var allowed = c.first_pair_mask()
    var mask = 0
    for s in range(c.size()):
        var top = c.states[s].u.copy()
        var bottom = c.states[s].v.copy()
        for _ in range(depth):
            top = apply_substitution(sigma, top)
            bottom = apply_substitution(sigma, bottom)
            var bounds = coincidence_boundaries(top, bottom)
            for k in range(len(bounds) - 1):
                var a = top[bounds[k]]
                var b = bottom[bounds[k]]
                if a == b:
                    raise Error("coincident factor in an inflation of a supplied strict state")
                var bit = pair_bit(a, b)
                if bit & ~allowed:
                    raise Error("a cut pair of an inflation lies outside A(C)")
                mask |= bit
    return mask


def hub_on_one_track(sigma: List[List[Int]], c: StrictClosure, hub: Int, depth: Int) raises -> Bool:
    """Whether the hub letter sits on exactly one track at every cut of every
    `sigma^n(S)`, `1 <= n <= depth`."""
    if hub < 0 or hub >= ALPHABET:
        raise Error("hub letter outside the alphabet")
    if depth < 1 or depth > 8:
        raise Error("inflation depth must lie in 1..8")
    for s in range(c.size()):
        var top = c.states[s].u.copy()
        var bottom = c.states[s].v.copy()
        for _ in range(depth):
            top = apply_substitution(sigma, top)
            bottom = apply_substitution(sigma, bottom)
            var bounds = coincidence_boundaries(top, bottom)
            for k in range(len(bounds) - 1):
                if (top[bounds[k]] == hub) == (bottom[bounds[k]] == hub):
                    return False
    return True


# ---------------------------------------------------------------- configurations


def _unordered(a: Int, b: Int) -> LetterPair:
    return LetterPair(a, b) if a < b else LetterPair(b, a)


def _contains(pairs: List[LetterPair], p: LetterPair) -> Bool:
    for k in range(len(pairs)):
        if pairs[k] == p:
            return True
    return False


struct ConfigurationCensus(Copyable, Movable):
    """The `(g, good edge, A)` triples compatible with Theorem A(3): `g` one of
    the 27 first-letter maps, the good edge one of the three pairs, `A` a
    nonempty set of pairs through the third letter that `g x g` preserves
    without collapsing. `transient_period` records, for every non-merged
    ordered `(g, pair)` instance, the key `8 t + m` of its transient `t` and
    period `m` under `g x g`."""

    var triples: Int
    var single_cycle_one: Int
    var double_cycle_one: Int
    var double_cycle_two: Int
    var single_fixed: Int
    var single_swap: Int
    var square_fixes_a_pair_everywhere: Bool
    var nonmerged_instances: Int
    var transient_period: Histogram

    def __init__(out self):
        self.triples = 0
        self.single_cycle_one = 0
        self.double_cycle_one = 0
        self.double_cycle_two = 0
        self.single_fixed = 0
        self.single_swap = 0
        self.square_fixes_a_pair_everywhere = True
        self.nonmerged_instances = 0
        self.transient_period = Histogram(64)


def _cycle_length(g: List[Int], p: LetterPair) -> Int:
    var q = p.copy()
    for _ in range(5):
        q = _unordered(g[q.a], g[q.b])
    var period = 1
    var r = _unordered(g[q.a], g[q.b])
    while r != q:
        period += 1
        r = _unordered(g[r.a], g[r.b])
    return period


def configuration_census() raises -> ConfigurationCensus:
    var out = ConfigurationCensus()
    var maps = all_maps(ALPHABET)
    var pairs: List[LetterPair] = [LetterPair(0, 1), LetterPair(0, 2), LetterPair(1, 2)]
    for m in range(len(maps)):
        var g = maps[m].copy()
        for e in range(len(pairs)):
            var good = pairs[e].copy()
            var hub = 3 - good.a - good.b
            var candidates: List[LetterPair] = [_unordered(hub, good.a), _unordered(hub, good.b)]
            for mask in range(1, 4):
                var chosen = List[LetterPair]()
                for k in range(2):
                    if (mask >> k) & 1:
                        chosen.append(candidates[k].copy())
                var ok = True
                for k in range(len(chosen)):
                    var p = chosen[k].copy()
                    if g[p.a] == g[p.b] or synchronizes(g, p.a, p.b):
                        ok = False
                    elif not _contains(chosen, _unordered(g[p.a], g[p.b])):
                        ok = False
                if not ok:
                    continue
                out.triples += 1
                var longest = 1
                var square_fixes = False
                for k in range(len(chosen)):
                    var p = chosen[k].copy()
                    var cycle = _cycle_length(g, p)
                    if cycle > longest:
                        longest = cycle
                    if g[g[p.a]] == p.a and g[g[p.b]] == p.b:
                        square_fixes = True
                if not square_fixes:
                    out.square_fixes_a_pair_everywhere = False
                if len(chosen) == 1:
                    if longest == 1:
                        out.single_cycle_one += 1
                    var p = chosen[0].copy()
                    if g[p.a] == p.a and g[p.b] == p.b:
                        out.single_fixed += 1
                    elif g[p.a] == p.b and g[p.b] == p.a:
                        out.single_swap += 1
                elif longest == 1:
                    out.double_cycle_one += 1
                else:
                    out.double_cycle_two += 1
        # transient and period of every non-merged ordered pair under g x g
        for e in range(len(pairs)):
            var p = pairs[e].copy()
            if synchronizes(g, p.a, p.b):
                continue
            out.nonmerged_instances += 1
            var orbit: List[LetterPair] = [p.copy()]
            for _ in range(12):
                orbit.append(orbit[len(orbit) - 1].step(g))
            var t = -1
            var period = -1
            for start in range(12):
                for later in range(start + 1, 13):
                    if orbit[later] == orbit[start]:
                        t = start
                        period = later - start
                        break
                if t >= 0:
                    break
            if t < 0:
                raise Error("an orbit of a map on three letters did not recur within 12 steps")
            out.transient_period.record(8 * t + period)
    return out^


# ---------------------------------------------------------------- corpus survey


struct EndpointCollapse(Copyable, Movable):
    """Specimens whose prefix map, suffix map, or either, is eventually
    constant (endpoint types A or B): every letter pair then has a trivial
    strong-coincidence witness. `joint` records, on the remainder, the key
    `4 n_+ + n_-` of the numbers of unordered non-merged pairs of the two maps."""

    var first: Int
    var last: Int
    var either: Int
    var remainder: Int
    var joint: Histogram

    def __init__(out self):
        self.first = 0
        self.last = 0
        self.either = 0
        self.remainder = 0
        self.joint = Histogram(16)


def eventually_constant(h: List[Int]) -> Bool:
    var t = endpoint_type(h)
    return t == TYPE_A or t == TYPE_B


def endpoint_collapse_survey(corpus: List[Specimen]) raises -> EndpointCollapse:
    var out = EndpointCollapse()
    for s in range(len(corpus)):
        var plus = prefix_endpoint_map(corpus[s].sigma)
        var minus = suffix_endpoint_map(corpus[s].sigma)
        var cf = eventually_constant(plus)
        var cl = eventually_constant(minus)
        if cf:
            out.first += 1
        if cl:
            out.last += 1
        if cf or cl:
            out.either += 1
        else:
            out.remainder += 1
            var n_plus = len(nonsynchronizing_pairs(plus)) // 2
            var n_minus = len(nonsynchronizing_pairs(minus)) // 2
            out.joint.record(4 * n_plus + n_minus)
    return out^


# ---------------------------------------------------------------- witnesses


def left_witness(
    sigma: List[List[Int]], a: Int, b: Int, max_level: Int, word_budget: Int = 100000
) raises -> List[Int]:
    """`[n, i, x]`: the least level `n <= max_level` at which `sigma^n(a)` and
    `sigma^n(b)` carry the same letter `x` at a common index `i` with equal
    prefix Parikh vectors, or `[-1, -1, -1]` when the level budget is exhausted.
    Exceeding the word budget raises: neither exhaustion is a verdict."""
    _ = pair_bit(a, b)
    _ = sigma3(sigma)
    if max_level <= 0 or max_level > 32:
        raise Error("level budget must lie in 1..32")
    var image_bound = 0
    for letter in range(ALPHABET):
        if len(sigma[letter]) > image_bound:
            image_bound = len(sigma[letter])
    var top: List[Int] = [a]
    var bottom: List[Int] = [b]
    for n in range(1, max_level + 1):
        if len(top) * image_bound > word_budget or len(bottom) * image_bound > word_budget:
            raise Error("word budget exhausted before the level budget")
        top = apply_substitution(sigma, top)
        bottom = apply_substitution(sigma, bottom)
        var delta: List[Int] = [0, 0, 0]
        var shorter = len(top) if len(top) < len(bottom) else len(bottom)
        for i in range(shorter):
            if delta[0] == 0 and delta[1] == 0 and delta[2] == 0 and top[i] == bottom[i]:
                return [n, i, top[i]]
            delta[top[i]] += 1
            delta[bottom[i]] -= 1
    return [-1, -1, -1]


def reversed_substitution(sigma: List[List[Int]]) -> List[List[Int]]:
    var out = List[List[Int]]()
    for a in range(len(sigma)):
        var image = List[Int](capacity=len(sigma[a]))
        for k in range(len(sigma[a]) - 1, -1, -1):
            image.append(sigma[a][k])
        out.append(image.copy())
    return out^
