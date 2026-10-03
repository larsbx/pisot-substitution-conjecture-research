"""Exact catch-up analysis: is the cross-letter rigidity a one-tile question?

docs/p1b-vertex-coincidence-box-2026-10-02.md §5.6b. A *new* common vertex
arises on an edge `p -> u` into an offset-zero child `u` whose point `y` was
not already common at `p`'s level. If the top child index is 0, `y` is the
start of `p`'s top tile: it was already a vertex of tiling A and is *caught*
by B's subdivision (a catch-up); likewise for a bottom index 0. If both
indices are positive, `y` is born in both tilings at once (a simultaneous
birth). Both indices 0 would make `p` itself offset zero, so `y` would not be
new.

A catch-up into `y` happens at `p`'s left region endpoint: if the top index
is 0 then `y = 0` lies in the closure of `p`'s region, so `t_p <= 0` and the
left end is `0` (symmetrically for the bottom). So it is a step of `p`'s
*leftmost chain* -- the child whose region contains the parent's left end --
into offset zero. With `CU` the set of vertices whose leftmost chain reaches
offset zero:

    a vertex can reach a catch-up hit  <=>  it has a descendant in CU.

`CU` is the one-tile event: the left endpoint, a vertex of one tiling at
integral offset `s` inside a tile `b` of the other, is an eventual
subdivision boundary of `b`.

Right endpoints are the mirror image: reversing every image word (`mirror`)
reverses both tilings, so a catch-up at a right endpoint of `sigma` is a
left-endpoint catch-up of `mirror(sigma)`; `two_sided` checks both per
recurrent vertex. All signs are exact (`cached_sign`); a capped graph raises.
"""

from psc.overlap_obstruction import _has_cycle, overlap_sccs
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    SeedOverlapTables,
    build_seed_overlap_tables,
    cached_sign,
    interior_overlap_cached,
)
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_mul_beta, cubic_sub_checked
from psc.vertex_coincidence import build_box_graph

comptime CU_UNKNOWN = 0
comptime CU_ACTIVE = 1
comptime CU_HITS = 2
comptime CU_MISSES = 3


def leftmost_child(
    tables: SeedOverlapTables, mut cache: Dict[CubicElt, Int], state: OverlapState
) raises -> OverlapState:
    """The child whose region contains `state`'s left region endpoint
    (`state` must have nonzero offset)."""
    var s = cached_sign(tables, cache, state.shift)
    if s == 0:
        raise Error("leftmost child of an offset-zero vertex is not a catch-up step")
    var scaled = cubic_mul_beta(tables.field, state.shift)
    if s < 0:
        # left end is the top tile's start: top child 0, bottom child covering it
        var top = tables.sigma[state.top][0]
        for j in range(len(tables.sigma[state.bottom])):
            var child = OverlapState(top, tables.sigma[state.bottom][j], cubic_add_checked(scaled, tables.prefix(state.bottom, j)))
            if cached_sign(tables, cache, child.shift) <= 0 and interior_overlap_cached(tables, cache, child):
                return child
    else:
        # left end is the bottom tile's start: bottom child 0, top child covering it
        var bottom = tables.sigma[state.bottom][0]
        for i in range(len(tables.sigma[state.top])):
            var child = OverlapState(tables.sigma[state.top][i], bottom, cubic_sub_checked(scaled, tables.prefix(state.top, i)))
            if cached_sign(tables, cache, child.shift) >= 0 and interior_overlap_cached(tables, cache, child):
                return child
    raise Error("no child covers the parent's left endpoint")


struct OneTileVerdict(Copyable, Movable, Writable):
    var recurrent: Int
    var in_cu: Int
    var reach_cu: Int

    def __init__(out self):
        self.recurrent = 0
        self.in_cu = 0
        self.reach_cu = 0

    def write_to[W: Writer](self, mut w: W):
        w.write("recurrent=", self.recurrent, " in_cu=", self.in_cu, " reach_cu=", self.reach_cu)


def _recurrent_nonzero(a: SeedOverlapAutomaton) raises -> List[Int]:
    """Indices of the recurrent vertices of `a` with nonzero offset."""
    var out = List[Int]()
    var comps = overlap_sccs(a)
    for c in range(len(comps)):
        if not _has_cycle(a, comps[c]):
            continue
        for k in range(len(comps[c])):
            if not a.states[comps[c][k]].shift.is_zero():
                out.append(comps[c][k])
    return out^


def _cu_marks(tables: SeedOverlapTables, a: SeedOverlapAutomaton) raises -> List[Int]:
    """CU by memoised leftmost chains (a functional graph on nonzero offsets)."""
    var cache = Dict[CubicElt, Int]()
    var n = a.size()
    var index = Dict[OverlapState, Int]()
    for i in range(n):
        index[a.states[i]] = i
    var mark = List[Int](length=n, fill=CU_UNKNOWN)
    for i in range(n):
        if a.states[i].shift.is_zero():
            mark[i] = CU_HITS
    for start in range(n):
        if mark[start] != CU_UNKNOWN:
            continue
        var path = List[Int]()
        var x = start
        var verdict: Int
        while True:
            if mark[x] == CU_HITS or mark[x] == CU_MISSES:
                verdict = mark[x]
                break
            if mark[x] == CU_ACTIVE:
                verdict = CU_MISSES  # the chain cycles without reaching offset zero
                break
            mark[x] = CU_ACTIVE
            path.append(x)
            var child = leftmost_child(tables, cache, a.states[x])
            if child not in index:
                raise Error("leftmost child lies outside the closed box graph")
            x = index[child]
        for k in range(len(path)):
            mark[path[k]] = verdict
    return mark^


def _reaches_cu(a: SeedOverlapAutomaton, mark: List[Int]) -> List[Bool]:
    """Vertices with a descendant (themselves included) in CU at nonzero offset."""
    var n = a.size()
    var good = List[Bool](length=n, fill=False)
    var parents = List[List[Int]]()
    for _ in range(n):
        parents.append(List[Int]())
    for i in range(n):
        for j in range(len(a.adj[i])):
            parents[a.adj[i][j]].append(i)
    var queue = List[Int]()
    for i in range(n):
        if mark[i] == CU_HITS and not a.states[i].shift.is_zero():
            good[i] = True
            queue.append(i)
    var head = 0
    while head < len(queue):
        var k = queue[head]
        head += 1
        for j in range(len(parents[k])):
            var p = parents[k][j]
            if not good[p]:
                good[p] = True
                queue.append(p)
    return good^


def one_tile_from(tables: SeedOverlapTables, a: SeedOverlapAutomaton) raises -> OneTileVerdict:
    """Count the recurrent non-offset-zero vertices of the box graph `a` that lie
    in CU and that have a descendant in CU."""
    if a.capped:
        raise Error("one-tile analysis is undefined on a capped graph")
    var mark = _cu_marks(tables, a)
    var good = _reaches_cu(a, mark)
    var rec = _recurrent_nonzero(a)
    var v = OneTileVerdict()
    for k in range(len(rec)):
        v.recurrent += 1
        if mark[rec[k]] == CU_HITS:
            v.in_cu += 1
        if good[rec[k]]:
            v.reach_cu += 1
    return v^


def mirror(sigma: List[List[Int]]) -> List[List[Int]]:
    """Every image word reversed: the substitution of the mirrored tilings."""
    var out = List[List[Int]]()
    for a in range(len(sigma)):
        var w = List[Int]()
        for i in range(len(sigma[a]) - 1, -1, -1):
            w.append(sigma[a][i])
        out.append(w^)
    return out^


def one_tile(sigma: List[List[Int]]) raises -> OneTileVerdict:
    var tables = build_seed_overlap_tables(sigma)
    return one_tile_from(tables, build_box_graph(tables))


struct TwoSidedVerdict(Copyable, Movable, Writable):
    var recurrent: Int
    var reach_left: Int
    var reach_right: Int
    var reach_either: Int

    def __init__(out self):
        self.recurrent = 0
        self.reach_left = 0
        self.reach_right = 0
        self.reach_either = 0

    def write_to[W: Writer](self, mut w: W):
        w.write("recurrent=", self.recurrent, " reach_left=", self.reach_left, " reach_right=", self.reach_right, " reach_either=", self.reach_either)


def two_sided(sigma: List[List[Int]]) raises -> TwoSidedVerdict:
    """Per recurrent vertex: can it reach a catch-up at a left endpoint (CU of
    `sigma`) or at a right endpoint (CU of the mirror, through the vertex map
    `(a, b, t) -> (a, b, l_a - l_b - t)`)? Mirroring `x -> -x` maps the
    children of a pair to the children of its image, but the box graph stops at
    left-aligned vertices, and the mirror's stops at the images of the
    right-aligned ones, so the two recurrent parts differ (Tribonacci: 14 and
    8). Each side is searched up to its own first hit; a recurrent vertex whose
    image is missing from the mirror's box graph raises."""
    var tables = build_seed_overlap_tables(sigma)
    var a = build_box_graph(tables)
    var mtables = build_seed_overlap_tables(mirror(sigma))
    var m = build_box_graph(mtables)
    if a.capped or m.capped:
        raise Error("one-tile analysis is undefined on a capped graph")
    var good = _reaches_cu(a, _cu_marks(tables, a))
    var mgood = _reaches_cu(m, _cu_marks(mtables, m))
    var mindex = Dict[OverlapState, Int]()
    for i in range(m.size()):
        mindex[m.states[i]] = i
    var rec = _recurrent_nonzero(a)
    var v = TwoSidedVerdict()
    for k in range(len(rec)):
        var st = a.states[rec[k]]
        var image = OverlapState(
            st.top,
            st.bottom,
            cubic_sub_checked(cubic_sub_checked(mtables.lengths.at(st.top), mtables.lengths.at(st.bottom)), st.shift),
        )
        if image not in mindex:
            raise Error("mirror image of a recurrent vertex lies outside the mirror's box graph")
        var left = good[rec[k]]
        var right = mgood[mindex[image]]
        v.recurrent += 1
        if left:
            v.reach_left += 1
        if right:
            v.reach_right += 1
        if left or right:
            v.reach_either += 1
    return v^
