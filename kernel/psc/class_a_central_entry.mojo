"""Exact central RUN recurrence and actual exits from all its cycle states.

For the literal minus-Class-A words with n>=6, a central source is y/y
with |2*physical_shift|<=L_y. Every selected edge retains its two original
occurrence ordinals, and every returned path stops at full integral zero.
The written proof supplies termination and the separate all-strict-source
entrance theorem. Resource caps and machine-integer overflow refuse without
a mathematical verdict. No floating root or sampled source cover is used.
"""

from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, _run, _letter, check_boundary_member,
    member_transport, geometric_state, verify_member_edge,
)
from psc.class_a_zero_return import _parameters
from psc.class_a_x_ladder import reversed_label
from psc.class_a_x_transfer_plane import unit_descent_path, plane_middle
from psc.overlap_seed_patch import SeedOverlapTables
from psc.perron_field3 import (
    cubic_add_checked, cubic_sub_checked, cubic_scale_checked,
    cubic_mul_beta, sign_at_perron,
)


def _zero(w: BoundaryLabel) -> Bool:
    return w.x == 0 and w.c == 0 and w.y == 0


def _abs_checked(value: Int) raises -> Int:
    return checked_sub(0, value) if value < 0 else value


def _bind(tables: SeedOverlapTables, k: Int, t: Int) raises -> List[Int]:
    var parameters = _parameters(k, t)
    var n = parameters[0]
    var d = parameters[1]
    check_boundary_member(-1, k, n, d)
    if n < 6:
        raise Error("central RUN theorem requires n>=6")
    if len(tables.sigma) != 3:
        raise Error("central tables have the wrong number of image words")
    for a in range(3):
        var run = _run(-1, n, d, a)
        if len(tables.sigma[a]) != checked_add(run, 2):
            raise Error("central tables have different image lengths")
        for i in range(checked_add(run, 2)):
            if tables.sigma[a][i] != _letter(-1, n, d, a, i):
                raise Error("central tables have different original image words")
    return parameters^


def is_central(tables: SeedOverlapTables, source: BoundaryLabel) raises -> Bool:
    """Exact normalized central test; table binding is the caller's premise."""
    if source.top != 2 or source.bottom != 2:
        return False
    var twice = cubic_scale_checked(geometric_state(tables, source).shift, 2)
    return (sign_at_perron(tables.field,
              cubic_sub_checked(twice, tables.lengths.l2)) <= 0 and
            sign_at_perron(tables.field,
              cubic_add_checked(twice, tables.lengths.l2)) >= 0)


def _nearest_bound(tables: SeedOverlapTables, k: Int, n: Int, d: Int,
                   source: BoundaryLabel) raises -> BoundaryEdge:
    if not is_central(tables, source):
        raise Error("nearest RUN selector requires a central y/y source")
    # Binary search for the least gap g with 2*beta*T <= (2g+1)*L_y.
    # Thus g is the exact nearest integer to beta*T/L_y; equality is
    # harmless for the interval test, and is excluded by the written
    # irreducibility argument for actual integral sources.
    var twice = cubic_scale_checked(cubic_mul_beta(
        tables.field, geometric_state(tables, source).shift), 2)
    var radius = checked_sub(n, 2)
    var low = checked_sub(0, radius)
    var high = radius
    while low < high:
        var middle = checked_add(low, checked_sub(high, low) // 2)
        var odd = checked_add(checked_mul(2, middle), 1)
        var comparison = cubic_sub_checked(twice,
            cubic_scale_checked(tables.lengths.l2, odd))
        if sign_at_perron(tables.field, comparison) <= 0:
            high = middle
        else:
            low = checked_add(middle, 1)
    var gap = low
    var i = checked_add(1, max(gap, 0))
    var j = checked_add(1, max(checked_sub(0, gap), 0))
    if i < 1 or i > checked_sub(n, 1) or j < 1 or j > checked_sub(n, 1):
        raise Error("nearest central child is not a pair of actual RUN occurrences")
    var child = member_transport(-1, k, n, d, source, i, j)
    if not is_central(tables, child):
        raise Error("exact nearest RUN interval could not be certified")
    verify_member_edge(tables, -1, k, n, d, source, i, j, child)
    return BoundaryEdge(i, j, child)


def nearest_run_child(tables: SeedOverlapTables, k: Int, t: Int,
                      source: BoundaryLabel) raises -> BoundaryEdge:
    var parameters = _bind(tables, k, t)
    return _nearest_bound(tables, k, parameters[0], parameters[1], source)


def _append(tables: SeedOverlapTables, k: Int, n: Int, d: Int,
            mut path: List[BoundaryEdge], mut source: BoundaryLabel,
            i: Int, j: Int, step_cap: Int) raises:
    if _zero(source):
        raise Error("an actual zero path must stop at its first integral-zero hit")
    if len(path) >= step_cap:
        raise Error("central path step cap: no verdict")
    var child = member_transport(-1, k, n, d, source, i, j)
    verify_member_edge(tables, -1, k, n, d, source, i, j, child)
    path.append(BoundaryEdge(i, j, child))
    source = child


def cycle_escape(tables: SeedOverlapTables, k: Int, t: Int, height: Int,
                 flip: Bool = False, step_cap: Int = 10000) raises -> List[BoundaryEdge]:
    """Actual zero path from +/- W_H=yy(H,3H,-6H), when central.

    The nonzero nearest-RUN alternating orbit is not treated as a zero hit.
    Small KH cases use literal paths of length at most five; KH>=4 enters
    the previously proved reversed Q_H unit-descent tail.
    """
    var parameters = _bind(tables, k, t)
    var n = parameters[0]
    var d = parameters[1]
    if height <= 0 or step_cap < 0:
        raise Error("cycle escape requires positive height and nonnegative step cap")
    var K = checked_add(k, 1)
    var KH = checked_mul(K, height)
    var source = BoundaryLabel(2, 2, height, checked_mul(3, height),
                               checked_mul(-6, height))
    if not is_central(tables, source):
        raise Error("cycle source is outside the central interval")
    if KH > checked_sub(n, 2):
        raise Error("central cycle does not satisfy its proved actual-index bound")
    var original = source
    var path = List[BoundaryEdge]()
    var addresses = List[List[Int]]()
    if K == 1 and height <= 2:
        addresses = [[0, 0],
                     [1, checked_add(1, checked_mul(checked_add(n, 2), height))],
                     [checked_add(checked_mul(2, height), 1), 1]]
    elif K == 2 and height == 1:
        addresses = [[0, 0], [0, checked_add(checked_mul(2, n), 2)], [2, 1]]
    elif K == 3 and height == 1:
        addresses = [[0, 1], [1, 4]]
    elif K == 1 and height == 3:
        # At n=6, bottom 2n+6=A+1 is LAST x, not RUN y.
        addresses = [[0, 1], [0, 1], [checked_mul(2, n), 0],
                     [1, checked_add(checked_mul(2, n), 6)], [5, 1]]
    elif KH >= 4:
        addresses = [[1, KH], [0, checked_sub(checked_add(n, 3), KH)]]
    else:
        raise Error("unclassified positive KH<=3 factorization")
    for address in addresses:
        if _zero(source):
            break
        _append(tables, k, n, d, path, source, address[0], address[1], step_cap)
    if KH >= 4:
        var expected = reversed_label(plane_middle(1, 0, height))
        if source != expected:
            raise Error("central cycle exit did not retain the reversed Q_H packet")
        # The first edge of the reversed P_H path reaches R(Q_H). We have
        # already reached that exact packet through the two cycle-exit edges.
        var tail = unit_descent_path(k, t, height, True,
            checked_add(step_cap, 1))
        for index in range(1, len(tail)):
            if _zero(source):
                break
            _append(tables, k, n, d, path, source,
                    tail[index].i, tail[index].j, step_cap)
    if not _zero(source):
        raise Error("central cycle exit did not reach full integral offset zero")
    if flip:
        var reversed = List[BoundaryEdge]()
        source = reversed_label(original)
        for edge in path:
            var child = reversed_label(edge.target)
            verify_member_edge(tables, -1, k, n, d, source,
                               edge.j, edge.i, child)
            reversed.append(BoundaryEdge(edge.j, edge.i, child))
            source = child
        return reversed^
    return path^


def central_escape(tables: SeedOverlapTables, k: Int, t: Int,
                   source: BoundaryLabel, step_cap: Int = 10000) raises -> List[BoundaryEdge]:
    """Follow the exact central recurrence and escape its first W_H state.

    Every source is checked against the literal words and exact geometry.
    Finite integer pair recurrence supplies the mathematical termination
    proof; the executable keeps a checked finite guard and a caller cap.
    Both exhausted guards refuse, never accept a partial witness.
    """
    var parameters = _bind(tables, k, t)
    var n = parameters[0]
    var d = parameters[1]
    if step_cap < 0 or not is_central(tables, source):
        raise Error("central escape requires a central y/y source and nonnegative cap")
    var path = List[BoundaryEdge]()
    if _zero(source):
        return path^
    var next_x = checked_add(checked_add(checked_mul(2, source.x), source.c), source.y)
    var denominator = checked_mul(2, checked_add(k, 1))
    var ceiling = checked_add(checked_add(n, 4), checked_sub(denominator, 1)) // denominator
    var C = max(max(_abs_checked(source.x), _abs_checked(next_x)), ceiling)
    var width = checked_add(checked_mul(2, C), 1)
    var pair_budget = checked_add(checked_mul(width, width), 2)
    var w = source
    for _ in range(pair_budget):
        if _zero(w):
            return path^
        if (w.c == checked_mul(3, w.x) and w.y == checked_mul(-6, w.x)):
            var tail = cycle_escape(tables, k, t, _abs_checked(w.x),
                                    w.x < 0, checked_sub(step_cap, len(path)))
            for edge in tail:
                # cycle_escape has checked every edge from this exact source.
                path.append(edge)
            return path^
        if len(path) >= step_cap:
            raise Error("central recurrence step cap: no verdict")
        var edge = _nearest_bound(tables, k, n, d, w)
        path.append(edge)
        w = edge.target
    raise Error("central integer-pair guard exhausted: no verdict")
