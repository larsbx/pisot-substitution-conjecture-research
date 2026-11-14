"""Bounded actual-occurrence entrance into the proved Class-A central slice.

The n>=6 mathematical theorem applies to every strict integral source.
This constructor retains a complete original occurrence transcript for its
successful output. Search, path, arithmetic or exact-sign limits refuse;
an exhausted run never reports a nonproductive mathematical source.
"""

from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, geometric_state, member_transport, verify_member_edge,
)
from psc.class_a_central_entry import _bind, _zero, is_central, central_escape
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, interior_overlap_cached, cached_sign,
)
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_sub_checked, cubic_scale_checked, cubic_mul_beta,
    sign_at_perron,
)


def verify_two_level_density(tables: SeedOverlapTables, k: Int, t: Int) raises:
    """Check nine strict inequalities using literal depth-two image counts.

    Y/(beta^2 L_a)>5/beta and X,C/(beta^2 L_a)<1/beta.
    This finite member verifier is separate from the uniform written proof.
    """
    _ = _bind(tables, k, t)
    for a in range(3):
        var counts = List[Int](length=3, fill=0)
        for b in tables.sigma[a]:
            for c in tables.sigma[b]:
                counts[c] = checked_add(counts[c], 1)
        var scaled_length = cubic_mul_beta(tables.field, tables.lengths.at(a))
        var y_margin = cubic_sub_checked(
            cubic_scale_checked(tables.lengths.l2, counts[2]),
            cubic_scale_checked(scaled_length, 5))
        var x_margin = cubic_sub_checked(scaled_length,
            cubic_scale_checked(tables.lengths.l2, counts[0]))
        var c_margin = cubic_sub_checked(scaled_length,
            cubic_scale_checked(tables.lengths.l2, counts[1]))
        if (sign_at_perron(tables.field, y_margin) <= 0 or
            sign_at_perron(tables.field, x_margin) <= 0 or
            sign_at_perron(tables.field, c_margin) <= 0):
            raise Error("literal two-level block density certificate failed")


def _finish(tables: SeedOverlapTables, k: Int, t: Int,
            states: List[BoundaryLabel], parents: List[Int],
            incoming_i: List[Int], incoming_j: List[Int], found: Int,
            step_cap: Int, typed_terminal: Bool) raises -> List[BoundaryEdge]:
    var backward = List[BoundaryEdge]()
    var cursor = found
    while parents[cursor] != -1:
        if len(backward) >= step_cap:
            raise Error("entrance path cap exhausted: no verdict")
        backward.append(BoundaryEdge(incoming_i[cursor], incoming_j[cursor], states[cursor]))
        cursor = parents[cursor]
    var path = List[BoundaryEdge]()
    for index in range(len(backward) - 1, -1, -1):
        path.append(backward[index])
    if not _terminal(states[found], typed_terminal):
        var tail = central_escape(tables, k, t, states[found],
                                  checked_sub(step_cap, len(path)))
        for edge in tail:
            path.append(edge)
    var parameters = _bind(tables, k, t)
    var w = states[0]
    for edge in path:
        if _terminal(w, typed_terminal):
            raise Error("entrance transcript continued after its terminal target")
        verify_member_edge(tables, -1, k, parameters[0], parameters[1],
                           w, edge.i, edge.j, edge.target)
        w = edge.target
    if not _terminal(w, typed_terminal):
        raise Error("entrance transcript failed its requested zero endpoint")
    return path^


def _terminal(w: BoundaryLabel, typed: Bool) -> Bool:
    return _zero(w) and (not typed or w.top == w.bottom)


def _entry_escape(tables: SeedOverlapTables, k: Int, t: Int,
                 source: BoundaryLabel, state_cap: Int = 10000,
                 pair_cap: Int = 20000000, step_cap: Int = 10000,
                 typed_terminal: Bool = False
                 ) raises -> List[BoundaryEdge]:
    """Find an original-address path from a strict source, or refuse a cap.

    The exact increasing-prefix sweep visits all actual strict children in
    top-major order, retaining first-discovery ancestry. Its conservative
    pair budget charges the full Cartesian address product before expansion.
    State interning checks that equal physical keys retain the same full
    integral offset. This is a witness search, not a finite-carrier claim.
    """
    var parameters = _bind(tables, k, t)
    var n = parameters[0]
    var d = parameters[1]
    if state_cap < 1 or pair_cap < 1 or step_cap < 0:
        raise Error("invalid entrance resource bounds")
    var cache = Dict[CubicElt, Int]()
    var root = geometric_state(tables, source)
    if not interior_overlap_cached(tables, cache, root):
        raise Error("entrance source is not a strict overlap")
    var states = List[BoundaryLabel]()
    var parents = List[Int]()
    var incoming_i = List[Int]()
    var incoming_j = List[Int]()
    var ids = Dict[OverlapState, Int]()
    states.append(source)
    parents.append(-1)
    incoming_i.append(-1)
    incoming_j.append(-1)
    ids[root] = 0
    var cursor = 0
    var charged_pairs = 0
    while cursor < len(states):
        var w = states[cursor]
        if _terminal(w, typed_terminal) or is_central(tables, w):
            return _finish(tables, k, t, states, parents,
                           incoming_i, incoming_j, cursor, step_cap, typed_terminal)
        charged_pairs = checked_add(charged_pairs,
            checked_mul(len(tables.sigma[w.top]), len(tables.sigma[w.bottom])))
        if charged_pairs > pair_cap:
            raise Error("entrance literal-pair cap exhausted: no verdict")
        var physical = geometric_state(tables, w)
        var scaled = cubic_mul_beta(tables.field, physical.shift)
        # Same ordered partition sweep as the existing occurrence builder;
        # retain only discovery ancestry, not a purported closed graph.
        var first_bottom = 0
        var bottom_count = len(tables.sigma[w.bottom])
        for i in range(len(tables.sigma[w.top])):
            var top_prefix = tables.prefix(w.top, i)
            var top_end = cubic_add_checked(top_prefix,
                tables.lengths.at(tables.sigma[w.top][i]))
            while first_bottom < bottom_count:
                var bottom_start = cubic_add_checked(scaled,
                    tables.prefix(w.bottom, first_bottom))
                var bottom_end = cubic_add_checked(bottom_start,
                    tables.lengths.at(tables.sigma[w.bottom][first_bottom]))
                if cached_sign(tables, cache, cubic_sub_checked(bottom_end, top_prefix)) > 0:
                    break
                first_bottom += 1
            var j = first_bottom
            while j < bottom_count:
                var bottom_start = cubic_add_checked(scaled, tables.prefix(w.bottom, j))
                if cached_sign(tables, cache, cubic_sub_checked(bottom_start, top_end)) >= 0:
                    break
                var child = member_transport(-1, k, n, d, w, i, j)
                var key = geometric_state(tables, child)
                if interior_overlap_cached(tables, cache, key):
                    if key in ids:
                        if states[ids[key]] != child:
                            raise Error("entrance interning lost an integral coordinate")
                    else:
                        if len(states) >= state_cap:
                            raise Error("entrance state cap exhausted: no verdict")
                        ids[key] = len(states)
                        states.append(child)
                        parents.append(cursor)
                        incoming_i.append(i)
                        incoming_j.append(j)
                j += 1
        cursor += 1
    raise Error("actual finite closure missed the proved entrance target")


def entry_escape(tables: SeedOverlapTables, k: Int, t: Int,
                 source: BoundaryLabel, state_cap: Int = 10000,
                 pair_cap: Int = 20000000, step_cap: Int = 10000
                 ) raises -> List[BoundaryEdge]:
    """BH witness: stop at the first full integral-zero offset."""
    return _entry_escape(tables, k, t, source, state_cap, pair_cap, step_cap, False)


def coincidence_escape(tables: SeedOverlapTables, k: Int, t: Int,
                       source: BoundaryLabel, state_cap: Int = 10000,
                       pair_cap: Int = 20000000, step_cap: Int = 10000
                       ) raises -> List[BoundaryEdge]:
    """Stronger witness: continue mixed-letter zero and stop at coincidence.

    The finite-block entrance proof permits this literal continuation. Its
    central y/y target and every central suffix have a typed-zero endpoint.
    This API therefore keeps the production typed-coincidence terminal rule.
    """
    return _entry_escape(tables, k, t, source, state_cap, pair_cap, step_cap, True)
