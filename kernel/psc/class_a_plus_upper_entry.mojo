"""Capped literal entry into the upper plus-Class-A central y/y domain."""
from finite_exact.checked_int import checked_add, checked_sub
from psc.class_a_boundary_children import BoundaryEdge, BoundaryLabel, geometric_state
from psc.class_a_plus_upper_recurrence import (
    _verify_edge, bind_upper, is_central, nearest_twice, transport,
)
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import SeedOverlapTables, interior_overlap
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_mul_beta, cubic_scale_checked,
    cubic_sub_checked, sign_at_perron,
)


def _boundary_sum(tables: SeedOverlapTables, top: Int, bottom: Int) raises -> CubicElt:
    var last = tables.sigma[top][len(tables.sigma[top])-1]
    return cubic_add_checked(tables.lengths.at(last),
                             tables.lengths.at(tables.sigma[bottom][0]))


def _direct_entry(tables: SeedOverlapTables, top: Int, bottom: Int,
                 inflated_margin: CubicElt) raises -> Bool:
    var twice_residual = cubic_scale_checked(
        cubic_sub_checked(inflated_margin, _boundary_sum(tables, top, bottom)), 2)
    return sign_at_perron(tables.field,
        cubic_sub_checked(twice_residual, tables.lengths.l2)) > 0


def _entry_edge(tables: SeedOverlapTables, n: Int, J: Int,
               source: BoundaryLabel) raises -> BoundaryEdge:
    var oriented = source
    var reversed_tracks = sign_at_perron(tables.field,
        geometric_state(tables, source).shift) < 0
    if reversed_tracks:
        oriented = reversed_label(source)
    var a = oriented.top
    var b = oriented.bottom
    var run_a = len(tables.sigma[a])-2
    var run_b = len(tables.sigma[b])-2
    var first_a = tables.sigma[a][0]
    var first_b = tables.sigma[b][0]
    var last_a = tables.sigma[a][run_a+1]
    var shift = geometric_state(tables, oriented).shift
    var D = cubic_mul_beta(tables.field, cubic_sub_checked(tables.lengths.at(a), shift))
    var G = tables.lengths.at(last_a)
    var E = _boundary_sum(tables, a, b)
    var i = run_a+1
    var j = 0
    var direct = _direct_entry(tables, a, b, D)
    if direct:
        var gap = cubic_add_checked(cubic_mul_beta(tables.field, shift),
            cubic_sub_checked(tables.lengths.at(first_b), tables.lengths.at(first_a)))
        var e = nearest_twice(tables, cubic_scale_checked(gap, 2), 1-run_b, run_a-1)
        i = checked_add(1, max(e, 0))
        j = checked_add(1, max(checked_sub(0, e), 0))
    elif sign_at_perron(tables.field, cubic_sub_checked(D, G)) > 0:
        var reverse_margin = cubic_sub_checked(E, D)
        if sign_at_perron(tables.field, reverse_margin) <= 0:
            j = 1
        elif not _direct_entry(tables, first_b, last_a,
                              cubic_mul_beta(tables.field, reverse_margin)):
            i = run_a
    if reversed_tracks:
        var swap_i = i
        i = j
        j = swap_i
    var edge = BoundaryEdge(i, j, transport(n, J, source, i, j))
    _verify_edge(tables, n, J, source, edge)
    if direct and not is_central(tables, edge.target):
        raise Error("upper entry direct edge failed to reach the central domain")
    return edge


def central_entry(tables: SeedOverlapTables, n: Int, J: Int,
                  source: BoundaryLabel, step_cap: Int = 128) raises -> List[BoundaryEdge]:
    """Construct entry with checked arithmetic and a bounded resource budget."""
    bind_upper(tables, n, J)
    if source.top < 0 or source.top >= 3 or source.bottom < 0 or source.bottom >= 3:
        raise Error("upper entry source letter outside alphabet")
    if not interior_overlap(tables, geometric_state(tables, source)):
        raise Error("upper entry source is not strict")
    if step_cap < 0:
        raise Error("upper entry step cap: no verdict")
    var path = List[BoundaryEdge]()
    var current = source
    while not is_central(tables, current):
        if len(path) >= step_cap:
            raise Error("upper entry step cap: no verdict")
        var edge = _entry_edge(tables, n, J, current)
        path.append(edge)
        current = edge.target
    return path^
