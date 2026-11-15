"""Eight literal upper plus-Class-A cycle exits, uniformly specified in n.

Canonical bounded construction: n>=7, J=1..4, positive H with JH<=4.
Every edge retains its actual child types and all integral coordinates.
FIRST/RUN decrement and two base templates end at the first integral zero.
The recurrence and arbitrary-source entrance are separate obligations.
Pre-code gate: docs/bh-class-a-plus-upper-cycles-stop-go-2026-11-15.md.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, _run, _prefix, _letter, geometric_state,
)
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import (
    SeedOverlapTables, interior_overlap, selected_overlap_child,
)
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_sub_checked, cubic_scale_checked,
    cubic_mul_beta, sign_at_perron,
)


def _parameters(n: Int, J: Int) raises -> Int:
    if n < 7 or J < 1 or J > 4:
        raise Error("upper cycles require n>=7 and J in 1..4")
    var d = checked_sub(checked_add(checked_mul(2, n), 12), J)
    _ = checked_add(checked_add(n, d), 2)
    return d


def _zero(w: BoundaryLabel) -> Bool:
    return w.x == 0 and w.c == 0 and w.y == 0


def cycle_source(J: Int, H: Int, flip: Bool = False) raises -> BoundaryLabel:
    if J < 1 or J > 4 or H < 1 or checked_mul(J, H) > 4:
        raise Error("outside the eight upper-cycle cases")
    var w = BoundaryLabel(2, 2, H, checked_mul(3, H), checked_mul(-6, H))
    return reversed_label(w) if flip else w


def _bind(tables: SeedOverlapTables, n: Int, J: Int) raises:
    """Bind all literal words, field, positive scaling and original prefixes."""
    var d = _parameters(n, J)
    if len(tables.sigma) != 3:
        raise Error("upper cycle literal word mismatch")
    for a in range(3):
        var run = _run(1, n, d, a)
        if len(tables.sigma[a]) != checked_add(run, 2):
            raise Error("upper cycle literal word mismatch")
        for i in range(checked_add(run, 2)):
            if tables.sigma[a][i] != _letter(1, n, d, a, i):
                raise Error("upper cycle literal word mismatch")
    if (tables.field.chi0 != -2 or
        tables.field.chi1 != checked_sub(checked_sub(J, n), 7) or
        tables.field.chi2 != checked_sub(0, checked_add(n, 4))):
        raise Error("upper cycle field mismatch")
    if (sign_at_perron(tables.field,
            CubicElt(checked_sub(0, checked_add(n, 4)), 1, 0)) <= 0 or
        sign_at_perron(tables.field,
            CubicElt(checked_sub(0, checked_add(n, 6)), 1, 0)) >= 0):
        raise Error("upper cycle root chamber mismatch")
    if len(tables.prefix_starts) != 4:
        raise Error("upper cycle prefix starts mismatch")
    var total = 0
    for a in range(3):
        total = checked_add(total, len(tables.sigma[a]))
    if len(tables.prefix_positions) != total:
        raise Error("upper cycle prefix count mismatch")
    var start = 0
    for a in range(3):
        if sign_at_perron(tables.field, tables.lengths.at(a)) <= 0:
            raise Error("upper cycle nonpositive length")
        if tables.prefix_starts[a] != start:
            raise Error("upper cycle prefix starts mismatch")
        var cursor = CubicElt()
        for i in range(len(tables.sigma[a])):
            if tables.prefix_positions[checked_add(start, i)] != cursor:
                raise Error("upper cycle original prefix mismatch")
            cursor = cubic_add_checked(cursor, tables.lengths.at(tables.sigma[a][i]))
        if cursor != cubic_mul_beta(tables.field, tables.lengths.at(a)):
            raise Error("upper cycle exact scaling mismatch")
        start = checked_add(start, len(tables.sigma[a]))
    if tables.prefix_starts[3] != start:
        raise Error("upper cycle prefix starts mismatch")


def member_transport(n: Int, J: Int, parent: BoundaryLabel,
                     i: Int, j: Int) raises -> BoundaryLabel:
    var d = _parameters(n, J)
    var top = _prefix(1, n, d, parent.top, i)
    var bottom = _prefix(1, n, d, parent.bottom, j)
    var x = checked_add(checked_add(checked_mul(2, parent.x), parent.c), parent.y)
    var c = checked_add(parent.c, parent.y)
    var y = checked_add(checked_add(checked_mul(checked_add(n, d), parent.x),
                                  checked_mul(n, parent.c)),
                        checked_mul(checked_add(n, 1), parent.y))
    return BoundaryLabel(_letter(1, n, d, parent.top, i),
        _letter(1, n, d, parent.bottom, j),
        checked_add(x, checked_sub(bottom[0], top[0])),
        checked_add(c, checked_sub(bottom[1], top[1])),
        checked_add(y, checked_sub(bottom[2], top[2])))


def _verify_bound_edge(tables: SeedOverlapTables, n: Int, J: Int,
                       parent: BoundaryLabel, i: Int, j: Int,
                       target: BoundaryLabel) raises:
    if member_transport(n, J, parent, i, j) != target:
        raise Error("upper cycle child type or complete offset mismatch")
    var source = geometric_state(tables, parent)
    if not interior_overlap(tables, source):
        raise Error("upper cycle parent is not strict")
    var actual = selected_overlap_child(tables, source, i, j)
    if actual != geometric_state(tables, target):
        raise Error("upper cycle geometric transport mismatch")
    if not interior_overlap(tables, actual):
        raise Error("upper cycle child is not strict")


def verify_member_edge(tables: SeedOverlapTables, n: Int, J: Int,
                       parent: BoundaryLabel, i: Int, j: Int,
                       target: BoundaryLabel) raises:
    _bind(tables, n, J)
    _verify_bound_edge(tables, n, J, parent, i, j, target)


def verify_cycle_path(tables: SeedOverlapTables, n: Int, J: Int, H: Int,
                      flip: Bool, source: BoundaryLabel,
                      path: List[BoundaryEdge], step_cap: Int = 7) raises:
    _bind(tables, n, J)
    if source != cycle_source(J, H, flip):
        raise Error("upper cycle source mismatch")
    if step_cap < 0 or len(path) > step_cap:
        raise Error("upper cycle step cap exhausted: no verdict")
    var shift = geometric_state(tables, source).shift
    if sign_at_perron(tables.field, shift) < 0:
        shift = cubic_scale_checked(shift, -1)
    if sign_at_perron(tables.field, cubic_sub_checked(
            tables.lengths.l2, cubic_scale_checked(shift, 2))) <= 0:
        raise Error("upper cycle amplitude is not below one half")
    var w = source
    for edge in path:
        if _zero(w):
            raise Error("upper cycle continued after integral zero")
        _verify_bound_edge(tables, n, J, w, edge.i, edge.j, edge.target)
        w = edge.target
    if not _zero(w) or w.top != 2 or w.bottom != 2:
        raise Error("upper cycle path is incomplete or not typed y/y zero")


def _append(tables: SeedOverlapTables, n: Int, J: Int,
            mut path: List[BoundaryEdge], mut source: BoundaryLabel,
            i: Int, j: Int, expected: BoundaryLabel, flip: Bool,
            step_cap: Int) raises:
    if _zero(source):
        raise Error("upper cycle continued after integral zero")
    if step_cap < 0 or len(path) >= step_cap:
        raise Error("upper cycle step cap exhausted: no verdict")
    var top = j if flip else i
    var bottom = i if flip else j
    var target = reversed_label(expected) if flip else expected
    _verify_bound_edge(tables, n, J, source, top, bottom, target)
    path.append(BoundaryEdge(top, bottom, target))
    source = target


def cycle_escape(tables: SeedOverlapTables, n: Int, J: Int, H: Int,
                 flip: Bool = False, step_cap: Int = 7) raises -> List[BoundaryEdge]:
    _bind(tables, n, J)
    var initial = cycle_source(J, H, flip)
    var source = initial
    var path = List[BoundaryEdge]()
    var height = H
    while checked_mul(J, height) >= 3:
        var s = checked_mul(J, height)
        var lower = checked_sub(height, 1)
        _append(tables, n, J, path, source, 0, checked_sub(s, 2),
            BoundaryLabel(0, 2, checked_sub(1, height), checked_mul(-3, height),
                          checked_sub(checked_mul(6, height), 3)), flip, step_cap)
        _append(tables, n, J, path, source, checked_add(checked_sub(s, J), 4), 1,
            BoundaryLabel(2, 2, lower, checked_mul(3, lower), checked_mul(-6, lower)),
            flip, step_cap)
        height = lower
    if height > 0:
        if J == 1:
            _append(tables, n, J, path, source, 0, 0,
                BoundaryLabel(0, 0, checked_sub(0, height), checked_mul(-3, height),
                              checked_mul(5, height)), flip, step_cap)
            _append(tables, n, J, path, source, 1,
                checked_add(1, checked_mul(checked_add(n, 4), height)),
                BoundaryLabel(2, 2, 0, checked_mul(2, height), checked_mul(-2, height)),
                flip, step_cap)
            _append(tables, n, J, path, source, 1, checked_add(checked_mul(2, height), 1),
                BoundaryLabel(2, 2, 0, 0, 0), flip, step_cap)
        elif J == 2 and height == 1:
            _append(tables, n, J, path, source, 0, 0,
                BoundaryLabel(0, 0, -1, -3, 4), flip, step_cap)
            _append(tables, n, J, path, source, 0, checked_add(checked_mul(2, n), 6),
                BoundaryLabel(0, 2, 0, 1, -1), flip, step_cap)
            _append(tables, n, J, path, source, 1, 2,
                BoundaryLabel(2, 2, 0, 0, 0), flip, step_cap)
        else:
            raise Error("uncovered upper cycle base: no verdict")
    verify_cycle_path(tables, n, J, H, flip, initial, path, step_cap)
    return path^


def _image_count(n: Int, d: Int, p: List[Int]) raises -> List[Int]:
    if len(p) != 3:
        raise Error("upper prefix requires a complete integral vector")
    return [checked_add(checked_add(checked_mul(2, p[0]), p[1]), p[2]),
            checked_add(p[1], p[2]),
            checked_add(checked_add(checked_mul(checked_add(n, d), p[0]),
                                    checked_mul(n, p[1])),
                        checked_mul(checked_add(n, 1), p[2]))]


def original_prefixes(n: Int, J: Int, source: BoundaryLabel,
                      path: List[BoundaryEdge]) raises -> List[List[Int]]:
    """Checked nested original prefix counts and every affine identity.

    The caller separately uses verify_cycle_path for exact physical strictness.
    Prefix-coordinate overflow refuses even when all small offsets still fit.
    """
    var d = _parameters(n, J)
    var P: List[Int] = [0, 0, 0]
    var Q: List[Int] = [0, 0, 0]
    var power: List[Int] = [source.x, source.c, source.y]
    var w = source
    for edge in path:
        if _zero(w):
            raise Error("upper cycle continued after integral zero")
        if member_transport(n, J, w, edge.i, edge.j) != edge.target:
            raise Error("upper cycle child type or complete offset mismatch")
        var p = _prefix(1, n, d, w.top, edge.i)
        var q = _prefix(1, n, d, w.bottom, edge.j)
        P = _image_count(n, d, P)
        Q = _image_count(n, d, Q)
        power = _image_count(n, d, power)
        var actual: List[Int] = [edge.target.x, edge.target.c, edge.target.y]
        for k in range(3):
            P[k] = checked_add(P[k], p[k])
            Q[k] = checked_add(Q[k], q[k])
            if actual[k] != checked_add(power[k], checked_sub(Q[k], P[k])):
                raise Error("upper cycle complete original prefix identity failed")
        w = edge.target
    if not _zero(w) or w.top != 2 or w.bottom != 2:
        raise Error("upper cycle path is incomplete or not typed y/y zero")
    var result = List[List[Int]]()
    result.append(P^)
    result.append(Q^)
    return result^
