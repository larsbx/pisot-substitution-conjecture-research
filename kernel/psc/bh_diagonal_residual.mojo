"""Exact, finite residual-to-small-box certificates in the diagonal family.

Pairs (z,y) range over [-r,r]^2. Edges are (z,y)->(y,t) with t in
that same box and |t+A*y+B*z|<=theta, decided in the cubic field.
Reverse BFS records shortest distances to the previously proved small box.
An uncovered pair reports only failure of this finite restricted graph.
No uniform-in-r verdict or all-source entry theorem is supplied here.
"""
from finite_exact.checked_int import checked_abs, checked_add, checked_mul, checked_sub
from finite_exact.closed_interval import IQ
from psc.bh_two_parameter_carrier import parikh_difference, tables_for
from psc.exact import interval_horner_int, strict_sign
from psc.occurrence_path import OccurrenceEdge
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, cached_sign,
    selected_overlap_child,
)
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_scale_checked, cubic_sub_checked,
)
from psc.perron_root_sign import perron_root_bracket


struct ResidualCertificate(Copyable, Movable):
    var r: Int
    var ranks: List[Int]
    var next_t: List[Int]
    var edge_count: Int

    def __init__(out self, r: Int, var ranks: List[Int], var next_t: List[Int],
                 edge_count: Int):
        self.r = r
        self.ranks = ranks^
        self.next_t = next_t^
        self.edge_count = edge_count


def _size(r: Int) raises -> Int:
    if r < 12 or r > 4096:
        raise Error("diagonal residual certificate requires 12 <= r <= 4096")
    var width = checked_add(checked_mul(2, r), 1)
    return checked_mul(width, width)


def pair_index(r: Int, z: Int, y: Int) raises -> Int:
    _ = _size(r)
    if checked_abs(z) > r or checked_abs(y) > r:
        raise Error("pair leaves the finite residual square")
    return checked_add(checked_mul(z + r, 2*r + 1), y + r)


def small_box(r: Int, z: Int, y: Int) raises -> Bool:
    _ = _size(r)
    return max(checked_abs(z), checked_abs(y)) <= (r - 2)//3


def within(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
           shift: CubicElt, radius: CubicElt) raises -> Bool:
    return cached_sign(tables, signs, cubic_sub_checked(radius, shift)) >= 0 and (
        cached_sign(tables, signs, cubic_add_checked(radius, shift)) >= 0
    )


def root_bracket(tables: SeedOverlapTables) raises -> IQ:
    """Reuse one certified root enclosure; an undecided sign still falls back."""
    return perron_root_bracket(tables.field.chi0, tables.field.chi1, tables.field.chi2, 24)


def bracket_sign(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
                  beta_box: IQ, value: CubicElt) raises -> Int:
    if value in signs:
        return signs[value]
    if value.is_zero():
        signs[value] = 0
        return 0
    var decided = strict_sign(interval_horner_int([value.a0, value.a1, value.a2], beta_box))
    if decided != 0:
        signs[value] = decided
        return decided
    return cached_sign(tables, signs, value)


def bracket_within(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int], beta_box: IQ,
                    shift: CubicElt, radius: CubicElt) raises -> Bool:
    return bracket_sign(tables, signs, beta_box, cubic_sub_checked(radius, shift)) >= 0 and (
        bracket_sign(tables, signs, beta_box, cubic_add_checked(radius, shift)) >= 0
    )


def bracket_strict(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int], beta_box: IQ,
                    state: OverlapState) raises -> Bool:
    return bracket_sign(tables, signs, beta_box,
        cubic_add_checked(state.shift, tables.lengths.at(state.bottom))) > 0 and (
        bracket_sign(tables, signs, beta_box,
            cubic_sub_checked(tables.lengths.at(state.top), state.shift)) > 0
    )


def packet(r: Int, x: Int, y: Int, z: Int) raises -> OverlapState:
    """Native lengths are beta times (1,beta,1+B), with opposite sign."""
    return OverlapState(1, 1, cubic_scale_checked(
        CubicElt(checked_mul(r, z), checked_add(x, z), y), -1))


def energy(r: Int, z: Int, y: Int) raises -> CubicElt:
    """beta*Q(z,y), retaining exact coefficients of the cubic field."""
    var zy = checked_mul(z, y)
    return CubicElt(checked_mul(r, checked_mul(z, z)),
        checked_sub(checked_mul(y, y), checked_mul(r, zy)), zy)


def _digits(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int], beta_box: IQ,
            z: Int, y: Int, digit_bound: Int = -1) raises -> List[Int]:
    # beta^2*(A*y+B*z) = r*y + beta*(2*y+r*z).
    var w = CubicElt(checked_mul(r, y), checked_add(checked_mul(2, y), checked_mul(r, z)))
    var radius = CubicElt(0, r - 1)
    var bound = r if digit_bound == -1 else digit_bound
    if bound < r or bound > 2*r:
        raise Error("residual digit scan bound is outside its supported finite range")
    var lo = -bound
    var hi = bound + 1
    # First t with beta^2*(t+A*y+B*z) >= -beta*(r-1).
    # The omitted endpoint r+1 is a sentinel, not an accepted graph state.
    while lo < hi:
        var mid = lo + (hi-lo)//2
        var shift = cubic_add_checked(w, CubicElt(0, 0, mid))
        if bracket_sign(tables, signs, beta_box, cubic_add_checked(shift, radius)) >= 0:
            hi = mid
        else:
            lo = mid + 1
    var result = List[Int]()
    var t = lo
    while t <= bound:
        var shift = cubic_add_checked(w, CubicElt(0, 0, t))
        if bracket_sign(tables, signs, beta_box, cubic_sub_checked(radius, shift)) < 0:
            break
        if not bracket_within(tables, signs, beta_box, shift, radius):
            raise Error("integer-interval enumeration violated its lower bound")
        result.append(t)
        t += 1
    return result^


def build_residual_certificate(r: Int, max_states: Int, max_edges: Int) raises -> ResidualCertificate:
    var count = _size(r)
    if max_states < count or max_edges < 0:
        raise Error("residual state budget exhausted; no verdict")
    var tables = tables_for(r, r)
    var beta_box = root_bracket(tables)
    var signs = Dict[CubicElt, Int]()
    var predecessors = List[List[Int]]()
    var ranks = List[Int]()
    var next_t = List[Int]()
    var queue = List[Int]()
    for z in range(-r, r + 1):
        for y in range(-r, r + 1):
            predecessors.append(List[Int]())
            ranks.append(0 if small_box(r, z, y) else -1)
            next_t.append(0)
            if small_box(r, z, y):
                queue.append(pair_index(r, z, y))
    var edges = 0
    for z in range(-r, r + 1):
        for y in range(-r, r + 1):
            var src = pair_index(r, z, y)
            for t in _digits(r, tables, signs, beta_box, z, y):
                if edges == max_edges:
                    raise Error("residual edge budget exhausted; no verdict")
                edges += 1
                predecessors[pair_index(r, y, t)].append(src)
    var head = 0
    while head < len(queue):
        var dest = queue[head]
        for src in predecessors[dest]:
            if ranks[src] < 0:
                ranks[src] = checked_add(ranks[dest], 1)
                next_t[src] = dest % (2*r + 1) - r
                queue.append(src)
        head += 1
    return ResidualCertificate(r, ranks^, next_t^, edges)


def verify_residual_certificate(certificate: ResidualCertificate) raises -> Tuple[Int, Int, Int, Int]:
    """Re-enumerate the graph and validate shortest ranks and witnesses.

    Returns (strict-disk sources, uncovered disk sources, maximum disk rank,
    uncovered square states). Uncovered is not a coincidence refusal.
    """
    var r = certificate.r
    var count = _size(r)
    if len(certificate.ranks) != count or len(certificate.next_t) != count:
        raise Error("residual certificate has incomplete state coverage")
    var tables = tables_for(r, r)
    var beta_box = root_bracket(tables)
    var signs = Dict[CubicElt, Int]()
    var edges = 0
    var sources = 0
    var uncovered = 0
    var square_uncovered = 0
    var maximum = 0
    for z in range(-r, r + 1):
        for y in range(-r, r + 1):
            var src = pair_index(r, z, y)
            var rank = certificate.ranks[src]
            var terminal = small_box(r, z, y)
            if rank < -1 or (rank == 0) != terminal:
                raise Error("residual rank has a false endpoint or invalid value")
            if rank <= 0 and certificate.next_t[src] != 0:
                raise Error("terminal or uncovered state has a forged next digit")
            var witnessed = terminal
            for t in _digits(r, tables, signs, beta_box, z, y):
                edges = checked_add(edges, 1)
                var child = certificate.ranks[pair_index(r, y, t)]
                if rank == -1 and child >= 0:
                    raise Error("uncovered region is not closed against reachable exits")
                if rank > 0 and child >= 0 and child < rank - 1:
                    raise Error("claimed shortest rank misses a shorter edge")
                if rank > 0 and t == certificate.next_t[src] and child == rank - 1:
                    witnessed = True
            if rank > 0 and not witnessed:
                raise Error("residual rank has no admissible descending witness")
            if rank == -1:
                square_uncovered += 1
            if z*z + y*y < r*r:
                sources += 1
                if rank < 0:
                    uncovered += 1
                else:
                    maximum = max(maximum, rank)
    if edges != certificate.edge_count:
        raise Error("residual certificate has an incorrect edge count")
    return (sources, uncovered, maximum, square_uncovered)


def sample_first_coordinates(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
                             beta_box: IQ, z: Int, y: Int) raises -> Tuple[Int, Int, Int]:
    """Exact left extreme, cancellation representative, and right extreme."""
    _ = pair_index(r, z, y)
    var middle = checked_sub(0, checked_add(checked_mul(r, y), checked_mul(2, z)))
    var radius = CubicElt(0, r - 1)
    if not bracket_within(tables, signs, beta_box, packet(r, middle, y, z).shift, radius):
        raise Error("cancellation representative is not in the exact run window")
    var extremes = List[Int]()
    for side in [-1, 1]:
        var lo = 0
        var hi = 2*r + 1
        if bracket_within(tables, signs, beta_box, packet(r, middle+side*hi, y, z).shift, radius):
            raise Error("first-coordinate search lacks a verified outside bracket")
        while hi-lo > 1:
            var mid = lo + (hi-lo)//2
            if bracket_within(tables, signs, beta_box, packet(r, middle+side*mid, y, z).shift, radius):
                lo = mid
            else:
                hi = mid
        var edge = middle + side*lo
        if not bracket_within(tables, signs, beta_box, packet(r, edge, y, z).shift, radius) or (
            bracket_within(tables, signs, beta_box, packet(r, edge+side, y, z).shift, radius)
        ):
            raise Error("computed first-coordinate extreme fails its adjacent control")
        extremes.append(edge)
    return (extremes[0], middle, extremes[1])


def verify_run_edge(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int], beta_box: IQ,
                    edge: OccurrenceEdge, t: Int) raises:
    _ = _size(r)
    if edge.source.top != 1 or edge.source.bottom != 1 or (
        not bracket_within(tables, signs, beta_box, edge.source.shift, CubicElt(0, r - 1))
    ) or not bracket_strict(tables, signs, beta_box, edge.source):
        raise Error("run edge source is not a strict window packet")
    if edge.top_index < 1 or edge.top_index > r or edge.bottom_index < 1 or edge.bottom_index > r:
        raise Error("run edge original ordinal is outside the type-1 run")
    var d = parikh_difference(r, edge.source.shift)
    var expected = packet(r, checked_add(d.a1, checked_mul(r, d.a2)), t, d.a1)
    var actual = selected_overlap_child(tables, edge.source, edge.top_index, edge.bottom_index)
    if actual != edge.target or edge.target != expected or (
        not bracket_strict(tables, signs, beta_box, edge.target)
    ) or not bracket_within(tables, signs, beta_box, edge.target.shift, CubicElt(0, r - 1)):
        raise Error("run edge does not realize the claimed full strict window packet")


def run_edge(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int], beta_box: IQ,
              current: OverlapState, t: Int) raises -> OccurrenceEdge:
    var d = parikh_difference(r, current.shift)
    var h = checked_sub(t, checked_add(checked_add(d.a0, checked_mul(r, d.a1)), d.a2))
    if checked_abs(h) >= r:
        raise Error("admissible residual digit has no literal run positions")
    var top = checked_add(1, max(h, 0))
    var bottom = checked_add(1, max(checked_sub(0, h), 0))
    var target = selected_overlap_child(tables, current, top, bottom)
    var edge = OccurrenceEdge(current, top, bottom, target)
    verify_run_edge(r, tables, signs, beta_box, edge, t)
    return edge


def trace_residual_to_box(certificate: ResidualCertificate, tables: SeedOverlapTables,
                          mut signs: Dict[CubicElt, Int], beta_box: IQ, source: OverlapState,
                          max_steps: Int) raises -> List[OccurrenceEdge]:
    var r = certificate.r
    var count = _size(r)
    if len(certificate.ranks) != count or len(certificate.next_t) != count or max_steps < 0:
        raise Error("invalid residual trace certificate or budget")
    if source.top != 1 or source.bottom != 1 or not bracket_strict(tables, signs, beta_box, source) or (
        not bracket_within(tables, signs, beta_box, source.shift, CubicElt(0, r - 1))
    ):
        raise Error("residual trace requires a strict full integral run-window source")
    var current = source
    var path = List[OccurrenceEdge]()
    while True:
        var d = parikh_difference(r, current.shift)
        var src = pair_index(r, d.a2, d.a1)
        var rank = certificate.ranks[src]
        if rank == 0:
            if not small_box(r, d.a2, d.a1):
                raise Error("trace stops at a forged small-box endpoint")
            return path^
        if rank < 0:
            raise Error("source is uncovered in this finite square; no verdict")
        if len(path) == max_steps:
            raise Error("residual trace budget exhausted; no verdict")
        var t = certificate.next_t[src]
        var dest = pair_index(r, d.a1, t)
        if certificate.ranks[dest] != rank-1:
            raise Error("residual trace does not descend its certified rank")
        var edge = run_edge(r, tables, signs, beta_box, current, t)
        path.append(edge)
        current = edge.target
