"""Asymptotic classes of the zero fibre and the vertex-asymptote condition (NM_V).

Round-4 note §3.1: `F₀` is the set of `Φ`-periodic tilings with `h = 0`. Its
members are the vertex-type tilings `T_(b,a)`, one for each edge `b.a` of the
Barge–Diamond eventual range, and the interior-type tilings, one for each state
of an interior `f`-cycle (certified complete by `decide_geometric_f`).
(NM_V) asks that a member left-asymptotic (resp. right-asymptotic) to a
vertex-type member be vertex-type with the same left (resp. right) letter.

**Exact decision of `T ∼_L S`.** Each member is fixed by `Φ^Q` for a common `Q`.
Track the tile of each member containing `0⁻`: for a vertex-type member, the
tile `b` ending at the origin; for an interior member, the state of its
`f`-cycle. The cell of the pair containing `0⁻` is an overlap state, and its
children split into the central child (again containing `0⁻`), the children to
its left and the children to its right. Every cell of the pair left of the
origin descends from a left child of some central cell, and descendants of a
left child at depth `k` lie in `β^k`·(a negative interval). So `T ∼_L S` iff no
non-coincident overlap state reachable from a left child lies on a cycle of
the overlap graph. If there is such a cycle, non-coincident cells occur
arbitrarily far left. If not, every left descendant is a coincidence within a
bounded depth, and the two tilings agree left of a bounded point. A shared
central tile gives agreement on both sides at once. The right side is the
mirror. Arithmetic is exact (`Z[β]` signs); every cap raises.
"""

from finite_exact.checked_int import checked_sub
from psc.c4_geometric_f import PrototileMap, PrototileState, StableRadiiCache, decide_geometric_f_with
from psc.h1_census import eventual_range, legal_two_words
from psc.overlap_seed_patch import (
    OverlapState,
    build_overlap_graph_from_seeds,
    interior_overlap_cached,
    selected_overlap_child,
)
from psc.perron_field3 import CubicElt, cubic_sub_checked

comptime MAX_CHAIN = 10000
comptime MAX_ASYMPTOTE_STATES = 200000


struct Member(ImplicitlyCopyable, Copyable, Movable):
    """A member of `F₀`. `vertex`: seam `left.right` at the origin. Otherwise
    `state` is an interior `f`-cycle state."""

    var vertex: Bool
    var left: Int
    var right: Int
    var state: PrototileState

    def __init__(out self, vertex: Bool, left: Int, right: Int, state: PrototileState):
        self.vertex = vertex
        self.left = left
        self.right = right
        self.state = state


def _unit(letter: Int) -> PrototileState:
    if letter == 0:
        return PrototileState(0, 1, 0, 0)
    if letter == 1:
        return PrototileState(1, 0, 1, 0)
    return PrototileState(2, 0, 0, 1)


struct Germ(ImplicitlyCopyable, Copyable, Movable):
    """The tile containing `0⁻` (left side) or `0⁺` (right side): its letter and
    the origin seen from its left end, as a lattice vector."""

    var state: PrototileState
    var index: Int  # child index in the parent image at the last step, -1 at start

    def __init__(out self, state: PrototileState, index: Int):
        self.state = state
        self.index = index


def _germ(member: Member, right: Bool) -> PrototileState:
    if not member.vertex:
        return member.state
    if right:
        return PrototileState(member.right, 0, 0, 0)
    return _unit(member.left)  # origin at the right end of the left tile


def _step(mut m: PrototileMap, s: PrototileState, right: Bool) raises -> Germ:
    """Next central tile. The left germ of a vertex member sits at the right end
    of its tile, which `PrototileMap.step` does not accept; its child is the
    last letter, again at its right end."""
    var e = _unit(s.letter)
    if not right and s == e:
        var last = len(m.tables.sigma[s.letter]) - 1
        return Germ(_unit(m.tables.sigma[s.letter][last]), last)
    var step = m.step(s)
    return Germ(step.child, step.index)


def _cell(mut m: PrototileMap, top: PrototileState, bottom: PrototileState) raises -> OverlapState:
    # top tile starts at -pos(top), bottom at -pos(bottom); shift = bottom start - top start
    return OverlapState(top.letter, bottom.letter, cubic_sub_checked(m.position(top), m.position(bottom)))


def _has_cycle(states: List[OverlapState], adj: List[List[Int]]) -> Bool:
    var n = len(states)
    var indeg = List[Int](length=n, fill=0)
    for i in range(n):
        for j in adj[i]:
            indeg[j] += 1
    var queue = List[Int]()
    for i in range(n):
        if indeg[i] == 0:
            queue.append(i)
    var removed = 0
    while len(queue) > 0:
        var i = queue.pop()
        removed += 1
        for j in adj[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                queue.append(j)
    return removed < n


def asymptotic(mut m: PrototileMap, a: Member, b: Member, right: Bool) raises -> Bool:
    """Exact decision of `a ∼_R b` (`right`) or `a ∼_L b` for members of `F₀`."""
    var ga = _germ(a, right)
    var gb = _germ(b, right)
    var seen = Dict[String, Bool]()
    var seeds = List[OverlapState]()
    var signs = m.signs.copy()
    for _ in range(MAX_CHAIN):
        var key = String(ga, "|", gb)
        if key in seen:
            break
        seen[key] = True
        var cell = _cell(m, ga, gb)
        if cell.is_coincidence():
            return True
        var na = _step(m, ga, right)
        var nb = _step(m, gb, right)
        # children of the central cell in physical (top-major) order, with indices
        var central = -1
        var children = List[OverlapState]()
        for i in range(len(m.tables.sigma[cell.top])):
            for j in range(len(m.tables.sigma[cell.bottom])):
                var child = selected_overlap_child(m.tables, cell, i, j)
                if interior_overlap_cached(m.tables, signs, child):
                    if i == na.index and j == nb.index:
                        central = len(children)
                    children.append(child)
        if central < 0:
            raise Error("zero-fibre asymptotes: central child not found")
        if right:
            for k in range(central + 1, len(children)):
                seeds.append(children[k])
        else:
            for k in range(central):
                seeds.append(children[k])
        ga = na.state
        gb = nb.state
    else:
        raise Error("zero-fibre asymptotes: central chain cap reached; inconclusive")
    if len(seeds) == 0:
        return True
    var graph = build_overlap_graph_from_seeds(m.tables, seeds, signs, MAX_ASYMPTOTE_STATES)
    if graph.capped:
        raise Error("zero-fibre asymptotes: overlap state cap reached; inconclusive")
    return not _has_cycle(graph.states, graph.adj)


struct NMVReport(Copyable, Movable):
    var members: Int
    var interior: Int
    var left_failures: List[String]
    var right_failures: List[String]

    def __init__(out self, members: Int, interior: Int):
        self.members = members
        self.interior = interior
        self.left_failures = List[String]()
        self.right_failures = List[String]()

    def holds(self) -> Bool:
        return len(self.left_failures) == 0 and len(self.right_failures) == 0


def zero_fibre_members(mut m: PrototileMap, mut boxes: StableRadiiCache) raises -> List[Member]:
    var sigma = m.tables.sigma.copy()
    var er = eventual_range(sigma, legal_two_words(sigma))
    var out = List[Member]()
    for b in range(3):
        for a in range(3):
            if er[3 * b + a]:
                out.append(Member(True, b, a, PrototileState(a, 0, 0, 0)))
    var verdict = decide_geometric_f_with(m, boxes)
    for c in range(len(verdict.cycles)):
        for k in range(verdict.cycles[c].period()):
            var s = verdict.cycles[c].states[k]
            out.append(Member(False, -1, -1, s))
    return out^


def _name(x: Member) -> String:
    if x.vertex:
        return String(x.left, ".", x.right)
    return String(x.state)


def nmv_report(mut m: PrototileMap, mut boxes: StableRadiiCache) raises -> NMVReport:
    """(NM_V) on both sides, with each violating pair named."""
    var members = zero_fibre_members(m, boxes)
    var interior = 0
    for x in members:
        interior += Int(not x.vertex)
    var report = NMVReport(len(members), interior)
    for vi in range(len(members)):
        var v = members[vi]
        if not v.vertex:
            continue
        for xi in range(len(members)):
            if xi == vi:
                continue
            var x = members[xi]
            if not (x.vertex and x.left == v.left):
                if asymptotic(m, v, x, False):
                    report.left_failures.append(String(v.left, ".", v.right, " ~L ", _name(x)))
            if not (x.vertex and x.right == v.right):
                if asymptotic(m, v, x, True):
                    report.right_failures.append(String(v.left, ".", v.right, " ~R ", _name(x)))
    return report^
