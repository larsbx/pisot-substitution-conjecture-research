"""Promotion-weighted endpoint functional on a literal overlap box.

Let a defect functional on bigons have endpoint-coboundary form
`D(u, v) = P(u_last, v_last) - Q(u_first, v_first)` with swap-odd `P`, `Q`
on ordered letter pairs. On overlap cells define

    kappa(c) = eps^-k P(pair of gR^k c)   (least k: right end of gR^k c shared)
             - eps^-j Q(pair of gL^j c)   (least j: left end of gL^j c shared),

with a term omitted when its end is never shared. Its column identity is

    sum over children u of c of kappa(u) - eps kappa(c)
        in span of the LOCAL forms of c,

the local forms being `P(left pair) - Q(right pair)` at every shared cut that
the row of `c` creates (at once, or after promotion of an interior one-track
seam) and the endpoint equivariance `P(gR pair) - eps P(pair)`,
`Q(gL pair) - eps Q(pair)` at shared ends of `c`. When those forms vanish
(the hypotheses of the written theorem), `kappa A = eps kappa` exactly.

The check is symbolic in the six values `P(01), P(02), P(12), Q(01), Q(02),
Q(12)` and therefore does not need a strict carrier: it verifies the
telescoping on every column of a supplied box. A promoted adjacency must be
an adjacent pair of the seam saturation with a shared boundary, or the
check raises. `promoted = False` drops the promotion terms; that naive
functional is the negative control.
"""

from finite_exact.rat_q import Q
from finite_linear_algebra.qlinalg import rank
from finite_linear_algebra.scalar import q_int
from psc.one_track_seam_spectrum import BOTH, CellBoundaryMasks
from psc.periodic_overlap_returns import PeriodicOverlapGraph

comptime UNKNOWNS = 6


def _pair_form(which: Int, a: Int, b: Int, coef: Int) -> List[Int]:
    """Coefficient vector of `coef * P(a, b)` (which = 0) or `Q` (which = 1)."""
    var v = List[Int](length=UNKNOWNS, fill=0)
    if a == b or coef == 0:
        return v^
    var lo = min(a, b)
    var hi = max(a, b)
    var slot = lo + hi - 1  # {0,1} -> 0, {0,2} -> 1, {1,2} -> 2
    v[3 * which + slot] = coef if a < b else -coef
    return v^


def _add(x: List[Int], y: List[Int], c: Int = 1) -> List[Int]:
    return [x[i] + c * y[i] for i in range(UNKNOWNS)]


struct _End(ImplicitlyCopyable, Copyable, Movable):
    var steps: Int  # -1: never shared
    var cell: Int

    def __init__(out self, steps: Int, cell: Int):
        self.steps = steps
        self.cell = cell


def _shared_end(graph: PeriodicOverlapGraph, masks: CellBoundaryMasks, c: Int, right: Bool) -> _End:
    var seen = List[Bool](length=graph.graph.size(), fill=False)
    var x = c
    var k = 0
    while not seen[x]:
        if (masks.right[x] if right else masks.left[x]) == BOTH:
            return _End(k, x)
        seen[x] = True
        ref row = graph.graph.adj[x]
        if len(row) == 0:
            return _End(-1, x)
        x = row[len(row) - 1] if right else row[0]
        k += 1
    return _End(-1, x)


struct EndpointTelescoping(ImplicitlyCopyable, Copyable, Movable):
    var columns: Int
    var failures: Int
    var promoted_seams: Int

    def __init__(out self, columns: Int, failures: Int, promoted_seams: Int):
        self.columns = columns
        self.failures = failures
        self.promoted_seams = promoted_seams


def _kappa(
    graph: PeriodicOverlapGraph, masks: CellBoundaryMasks, c: Int, eps: Int, promoted: Bool
) -> List[Int]:
    var v = List[Int](length=UNKNOWNS, fill=0)
    for side in range(2):
        var end = _shared_end(graph, masks, c, side == 0)
        if end.steps < 0 or (end.steps > 0 and not promoted):
            continue
        var weight = 1 if eps == 1 or end.steps % 2 == 0 else -1  # eps^-k, eps = +-1
        var s = graph.graph.states[end.cell]
        v = _add(v, _pair_form(side, s.top, s.bottom, weight if side == 0 else -weight))
    return v^


def _in_span(vector: List[Int], forms: List[List[Int]]) -> Bool:
    var base = List[List[Q]]()
    for f in forms:
        base.append([q_int(x) for x in f])
    var extended = base.copy()
    extended.append([q_int(x) for x in vector])
    return rank(extended) == rank(base)


def saturated_shared_adjacency(
    graph: PeriodicOverlapGraph, masks: CellBoundaryMasks
) raises -> Dict[Int, Bool]:
    """Keys `left * size + right` of saturated adjacent pairs with a shared
    boundary: row pairs closed under (last child, first child)."""
    var size = graph.graph.size()
    var seen = Dict[Int, Bool]()
    var todo = List[Int]()
    for v in range(size):
        ref row = graph.graph.adj[v]
        for i in range(len(row) - 1):
            var key = row[i] * size + row[i + 1]
            if key not in seen:
                seen[key] = True
                todo.append(key)
    while len(todo) > 0:
        var key = todo.pop()
        ref left = graph.graph.adj[key // size]
        ref right = graph.graph.adj[key % size]
        if len(left) == 0 or len(right) == 0:
            continue
        var nxt = left[len(left) - 1] * size + right[0]
        if nxt not in seen:
            seen[nxt] = True
            todo.append(nxt)
    var shared = Dict[Int, Bool]()
    for item in seen.items():
        var a = item.key // size
        var b = item.key % size
        if (masks.right[a] == BOTH) != (masks.left[b] == BOTH):
            raise Error("endpoint functional: adjacent cells disagree on a shared boundary")
        if masks.right[a] == BOTH:
            shared[item.key] = True
    return shared^


def endpoint_telescoping(
    graph: PeriodicOverlapGraph, masks: CellBoundaryMasks, eps: Int, promoted: Bool = True
) raises -> EndpointTelescoping:
    if eps != 1 and eps != -1:
        raise Error("endpoint functional: eps must be +1 or -1")
    var size = graph.graph.size()
    var shared = saturated_shared_adjacency(graph, masks)
    var kappa = [_kappa(graph, masks, c, eps, promoted) for c in range(size)]
    var columns = 0
    var failures = 0
    var promoted_seams = 0
    for c in range(size):
        ref row = graph.graph.adj[c]
        if len(row) == 0:
            continue
        columns += 1
        var local = List[List[Int]]()
        for i in range(len(row) - 1):
            var r = _shared_end(graph, masks, row[i], True)
            var l = _shared_end(graph, masks, row[i + 1], False)
            if (r.steps < 0) != (l.steps < 0) or r.steps != l.steps:
                raise Error("endpoint functional: the two sides of a seam promote at different steps")
            if r.steps < 0:
                continue
            if r.cell * size + l.cell not in shared:
                raise Error("endpoint functional: promoted adjacency is not a literal shared cut")
            promoted_seams += Int(r.steps > 0)
            var a = graph.graph.states[r.cell]
            var b = graph.graph.states[l.cell]
            local.append(_add(_pair_form(0, a.top, a.bottom, 1), _pair_form(1, b.top, b.bottom, -1)))
        var s = graph.graph.states[c]
        if masks.right[c] == BOTH:
            var u = graph.graph.states[row[len(row) - 1]]
            local.append(_add(_pair_form(0, u.top, u.bottom, 1), _pair_form(0, s.top, s.bottom, -eps)))
        if masks.left[c] == BOTH:
            var u = graph.graph.states[row[0]]
            local.append(_add(_pair_form(1, u.top, u.bottom, 1), _pair_form(1, s.top, s.bottom, -eps)))
        var residual = _add(List[Int](length=UNKNOWNS, fill=0), kappa[c], -eps)
        for u in row:
            residual = _add(residual, kappa[u])
        failures += Int(not _in_span(residual, local))
    return EndpointTelescoping(columns, failures, promoted_seams)
