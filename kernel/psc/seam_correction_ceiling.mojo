"""Source-only ceiling of the one-track seam correction for unit PIP3.

The seam-spectrum note embeds the top-only seam graph `S` of a hypothetical
strict carrier equivariantly in copies of the cyclic legal-bigram graph
`E` (left letters cyclic under the last-letter map `gR`, right letters
cyclic under the first-letter map `gL`), one copy per periodic interior
state. Seams carry the interior state of the other track, so `S` splits
over the interior f-cycles. For a cycle of period `p` the relevant action
on its base copy is `psi = (gR x gL)^p`, and an orbit of `psi` of length
`k` is an orbit of length `p k` of the whole permutation.

The correction at a primitive root of order `d` is

    b_d = #{edge orbits, d | length} - #{left-vertex orbits, d | length}
          - #{right-vertex orbits, d | length},

with the vertices of `S` the endpoints of its edges (every cyclic germ
extends to a cyclic edge). `seam_ceiling` maximises and minimises this
over every psi-invariant edge set of each copy, independently per interior
cycle, and also records the value of the whole copy (all of `E` over every
interior cycle). The maximum is an upper bound for `b_d` of every strict
carrier of `sigma`; it uses no strict-carrier information and constructs
none. The whole-copy value is what the complete overlap box of a
productive specimen realizes; the regression compares the two.

`copy_trace` counts the fixed edges minus fixed endpoint germs of the whole
copy at one power directly, without orbit weights, as an independent check
of the orbit formula.
"""

from psc.c4_geometric_f import decide_geometric_f
from psc.h1_census import eventual_range, legal_two_words
from psc.bpa import substitution_incidence
from finite_linear_algebra.mat3 import Mat3

comptime MAX_ORDER = 4


struct SeamCeiling(Copyable, Movable):
    """Per-order range of the seam correction over invariant edge sets.

    Index `d - 1` holds order `d` for `d = 1..MAX_ORDER`.
    """

    var periods: List[Int]
    var cyclic_bigrams: List[Bool]
    var ceiling: List[Int]
    var floor: List[Int]
    var whole: List[Int]

    def __init__(
        out self,
        periods: List[Int],
        cyclic_bigrams: List[Bool],
        ceiling: List[Int],
        floor: List[Int],
        whole: List[Int],
    ):
        self.periods = periods.copy()
        self.cyclic_bigrams = cyclic_bigrams.copy()
        self.ceiling = ceiling.copy()
        self.floor = floor.copy()
        self.whole = whole.copy()

    def at(self, values: List[Int], order: Int) raises -> Int:
        if order < 1 or order > MAX_ORDER:
            raise Error("seam ceiling: order outside 1..MAX_ORDER")
        return values[order - 1]


def _last_map(sigma: List[List[Int]]) -> List[Int]:
    return [sigma[a][len(sigma[a]) - 1] for a in range(3)]


def _first_map(sigma: List[List[Int]]) -> List[Int]:
    return [sigma[a][0] for a in range(3)]


def _iterate(f: List[Int], times: Int) -> List[Int]:
    var out = List[Int]()
    for x in range(len(f)):
        var y = x
        for _ in range(times):
            y = f[y]
        out.append(y)
    return out^


def _orbit_lengths(perm: List[Int], members: List[Int]) raises -> List[Int]:
    """Cycle lengths of `perm` on the invariant set `members`; raises if it
    is not invariant."""
    var inside = List[Bool](length=len(perm), fill=False)
    for x in members:
        inside[x] = True
    var seen = List[Bool](length=len(perm), fill=False)
    var out = List[Int]()
    for x in members:
        if seen[x]:
            continue
        var k = 0
        var y = x
        while not seen[y]:
            if not inside[y]:
                raise Error("seam ceiling: vertex set is not invariant")
            seen[y] = True
            y = perm[y]
            k += 1
        if y != x:
            raise Error("seam ceiling: map is not a permutation on its eventual range")
        out.append(k)
    return out^


def _divisible(lengths: List[Int], scale: Int, order: Int) -> Int:
    var n = 0
    for k in lengths:
        n += Int((scale * k) % order == 0)
    return n


struct _CopyRange(ImplicitlyCopyable, Copyable, Movable):
    var low: Int
    var high: Int
    var whole: Int

    def __init__(out self, low: Int, high: Int, whole: Int):
        self.low = low
        self.high = high
        self.whole = whole


def _copy_range(
    last: List[Int], first: List[Int], cyclic: List[Bool], period: Int, order: Int
) raises -> _CopyRange:
    var r = _iterate(last, period)
    var l = _iterate(first, period)
    var psi = [3 * r[e // 3] + l[e % 3] for e in range(9)]
    var orbits = List[List[Int]]()
    var owner = List[Int](length=9, fill=-1)
    for e in range(9):
        if not cyclic[e] or owner[e] >= 0:
            continue
        var orbit = List[Int]()
        var y = e
        while owner[y] < 0:
            if not cyclic[y]:
                raise Error("seam ceiling: cyclic bigrams are not invariant")
            owner[y] = len(orbits)
            orbit.append(y)
            y = psi[y]
        orbits.append(orbit^)
    if len(orbits) > 9:
        raise Error("seam ceiling: more than nine edge orbits")
    var low = 0
    var high = 0
    var whole = 0
    var full = (1 << len(orbits)) - 1
    for mask in range(1, full + 1):
        var left = List[Int]()
        var right = List[Int]()
        var edges = 0
        for j in range(len(orbits)):
            if (mask >> j) & 1 == 0:
                continue
            edges += Int((period * len(orbits[j])) % order == 0)
            for e in orbits[j]:
                if e // 3 not in left:
                    left.append(e // 3)
                if e % 3 not in right:
                    right.append(e % 3)
        var value = edges - _divisible(_orbit_lengths(r, left), period, order) - _divisible(
            _orbit_lengths(l, right), period, order
        )
        high = max(high, value)
        low = min(low, value)
        if mask == full:
            whole = value
    return _CopyRange(low, high, whole)


def _require_unit(sigma: List[List[Int]]) raises:
    var det = Mat3(substitution_incidence(sigma)).det()
    if det != 1 and det != -1:
        raise Error("seam ceiling: incidence matrix must be unimodular")


def interior_periods(sigma: List[List[Int]]) raises -> List[Int]:
    """Periods of the certified complete list of interior f-cycles."""
    var verdict = decide_geometric_f(sigma)
    return [verdict.cycles[c].period() for c in range(len(verdict.cycles))]


def seam_ceiling(sigma: List[List[Int]]) raises -> SeamCeiling:
    """Range of the one-track seam correction over invariant seam graphs.

    Raises unless `sigma` is unit PIP3 (through the certified interior
    search) and on a non-invariant eventual range."""
    _require_unit(sigma)
    var cyclic = eventual_range(sigma, legal_two_words(sigma))
    var periods = interior_periods(sigma)
    var last = _last_map(sigma)
    var first = _first_map(sigma)
    var ceiling = List[Int]()
    var floor = List[Int]()
    var whole = List[Int]()
    for order in range(1, MAX_ORDER + 1):
        var high = 0
        var low = 0
        var all = 0
        for p in periods:
            var copy = _copy_range(last, first, cyclic, p, order)
            high += copy.high
            low += copy.low
            all += copy.whole
        ceiling.append(high)
        floor.append(low)
        whole.append(all)
    return SeamCeiling(periods, cyclic, ceiling, floor, whole)


def copy_trace(sigma: List[List[Int]], ceiling: SeamCeiling, power: Int) raises -> Int:
    """Fixed edges minus fixed endpoint germs of the whole copy at `power`.

    An interior state of period `p` is fixed iff `p | power`; it then
    contributes the fixed cyclic bigrams of `(gR x gL)^power` minus the fixed
    left and right endpoint letters of those bigrams."""
    if power <= 0:
        raise Error("seam ceiling: power must be positive")
    var r = _iterate(_last_map(sigma), power)
    var l = _iterate(_first_map(sigma), power)
    var per_state = 0
    var left = List[Bool](length=3, fill=False)
    var right = List[Bool](length=3, fill=False)
    for e in range(9):
        if ceiling.cyclic_bigrams[e]:
            left[e // 3] = True
            right[e % 3] = True
            per_state += Int(r[e // 3] == e // 3 and l[e % 3] == e % 3)
    for a in range(3):
        per_state -= Int(left[a] and r[a] == a) + Int(right[a] and l[a] == a)
    var fixed_states = 0
    for p in ceiling.periods:
        if power % p == 0:
            fixed_states += p
    return fixed_states * per_state
