"""Bounded literal central-selector construction for upper plus Class A.

For n>=7 and 1<=J<=n+7, keep actual ordered words, checked full offsets,
strict Perron-field signs and unbounded original-prefix counts. A step cap
or checked-arithmetic failure refuses; finite execution is not the uniform
recurrence proof. See the dated upper-recurrence stop/go and proof notes.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from finite_exact.bigint_z import (
    BigZ, bigz_from_i64, bigz_add, bigz_sub, bigz_mul, bigz_eq,
)
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


struct CentralEscape(Copyable, Movable):
    var path: List[BoundaryEdge]
    var central_depth: Int
    var reserve: Int

    def __init__(out self, path: List[BoundaryEdge], central_depth: Int, reserve: Int):
        self.path = path.copy()
        self.central_depth = central_depth
        self.reserve = reserve


def parameters(n: Int, J: Int) raises -> Int:
    if n < 7 or J < 1 or J > checked_add(n, 7):
        raise Error("upper recurrence requires n>=7 and 1<=J<=n+7")
    var d = checked_sub(checked_add(checked_mul(2, n), 12), J)
    _ = checked_add(checked_add(n, d), 2)
    return d


def _abs(value: Int) raises -> Int:
    return checked_sub(0, value) if value < 0 else value


def is_zero(w: BoundaryLabel) -> Bool:
    return w.x == 0 and w.c == 0 and w.y == 0


def is_cycle(w: BoundaryLabel) raises -> Bool:
    return (w.top == 2 and w.bottom == 2 and w.x != 0 and
            w.c == checked_mul(3, w.x) and w.y == checked_mul(-6, w.x))


def bind_upper(tables: SeedOverlapTables, n: Int, J: Int) raises:
    """Authenticate words, cubic/root chamber, every prefix and scaling."""
    var d = parameters(n, J)
    if len(tables.sigma) != 3:
        raise Error("upper recurrence literal word mismatch")
    var total = 0
    for a in range(3):
        var length = checked_add(_run(1, n, d, a), 2)
        if len(tables.sigma[a]) != length:
            raise Error("upper recurrence literal word mismatch")
        for i in range(length):
            if tables.sigma[a][i] != _letter(1, n, d, a, i):
                raise Error("upper recurrence literal word mismatch")
        total = checked_add(total, length)
    if (tables.field.chi0 != -2 or
        tables.field.chi1 != checked_sub(checked_sub(J, n), 7) or
        tables.field.chi2 != checked_sub(0, checked_add(n, 4))):
        raise Error("upper recurrence field mismatch")
    if (sign_at_perron(tables.field, CubicElt(-checked_add(n, 4), 1, 0)) <= 0 or
        sign_at_perron(tables.field, CubicElt(-checked_add(n, 6), 1, 0)) >= 0):
        raise Error("upper recurrence root chamber mismatch")
    if len(tables.prefix_starts) != 4 or len(tables.prefix_positions) != total:
        raise Error("upper recurrence prefix layout mismatch")
    var start = 0
    for a in range(3):
        if sign_at_perron(tables.field, tables.lengths.at(a)) <= 0:
            raise Error("upper recurrence nonpositive length")
        if tables.prefix_starts[a] != start:
            raise Error("upper recurrence prefix layout mismatch")
        var cursor = CubicElt()
        for i in range(len(tables.sigma[a])):
            if tables.prefix_positions[checked_add(start, i)] != cursor:
                raise Error("upper recurrence original prefix mismatch")
            cursor = cubic_add_checked(cursor, tables.lengths.at(tables.sigma[a][i]))
        if cursor != cubic_mul_beta(tables.field, tables.lengths.at(a)):
            raise Error("upper recurrence exact scaling mismatch")
        start = checked_add(start, len(tables.sigma[a]))
    if tables.prefix_starts[3] != start:
        raise Error("upper recurrence prefix layout mismatch")
    # Positive denominators beta(beta+1) are already bound to the root.
    if J >= 5:
        if sign_at_perron(tables.field, CubicElt(-4, checked_sub(J, 4), 0)) <= 0:
            raise Error("upper recurrence contraction chamber mismatch")
    else:
        if sign_at_perron(tables.field,
                CubicElt(-4, -checked_add(checked_mul(2, J), 3), 1)) <= 0:
            raise Error("upper recurrence shear chamber mismatch")


def is_central(tables: SeedOverlapTables, w: BoundaryLabel) raises -> Bool:
    if w.top != 2 or w.bottom != 2:
        return False
    var twice = cubic_scale_checked(geometric_state(tables, w).shift, 2)
    return (sign_at_perron(tables.field,
                cubic_add_checked(twice, tables.lengths.l2)) > 0 and
            sign_at_perron(tables.field,
                cubic_sub_checked(twice, tables.lengths.l2)) < 0)


def nearest_twice(tables: SeedOverlapTables, twice: CubicElt,
                  lower: Int, upper: Int) raises -> Int:
    """Strict exact nearest integer in a supplied finite search interval.

    `twice` is twice the physical value; unit size is the actual y length.
    A half tie refuses, including synthetic inputs outside the family.
    """
    var lo = lower
    var hi = upper
    while lo <= hi:
        var mid = checked_add(lo, checked_sub(hi, lo) // 2)
        var residual = cubic_sub_checked(twice,
            cubic_scale_checked(tables.lengths.l2, checked_mul(2, mid)))
        var left = sign_at_perron(tables.field,
            cubic_add_checked(residual, tables.lengths.l2))
        var right = sign_at_perron(tables.field,
            cubic_sub_checked(residual, tables.lengths.l2))
        if left == 0 or right == 0:
            raise Error("upper recurrence half-integer tie: no verdict")
        if left < 0:
            hi = checked_sub(mid, 1)
        elif right > 0:
            lo = checked_add(mid, 1)
        else:
            return mid
    raise Error("upper recurrence nearest search cap: no verdict")


def central_source(tables: SeedOverlapTables, n: Int, J: Int,
                   p: Int, q: Int) raises -> BoundaryLabel:
    """Finite fixture adapter: unique central r for specified integral p,q."""
    bind_upper(tables, n, J)
    var bound = checked_add(checked_add(checked_mul(4, _abs(p)), _abs(q)), 1)
    var target = cubic_scale_checked(cubic_add_checked(
        cubic_scale_checked(tables.lengths.l0, p),
        cubic_scale_checked(tables.lengths.l1, q)), -2)
    var r = nearest_twice(tables, target, checked_sub(0, bound), bound)
    var source = BoundaryLabel(2, 2, p, q, r)
    if not is_central(tables, source):
        raise Error("upper recurrence fixture is not central")
    return source


def transport(n: Int, J: Int, source: BoundaryLabel, i: Int, j: Int) raises -> BoundaryLabel:
    var d = parameters(n, J)
    var top = _prefix(1, n, d, source.top, i)
    var bottom = _prefix(1, n, d, source.bottom, j)
    var p = checked_add(checked_add(checked_mul(2, source.x), source.c), source.y)
    var q = checked_add(source.c, source.y)
    var r = checked_add(checked_add(checked_mul(checked_add(n, d), source.x),
                                  checked_mul(n, source.c)),
                        checked_mul(checked_add(n, 1), source.y))
    return BoundaryLabel(_letter(1, n, d, source.top, i),
        _letter(1, n, d, source.bottom, j),
        checked_add(p, checked_sub(bottom[0], top[0])),
        checked_add(q, checked_sub(bottom[1], top[1])),
        checked_add(r, checked_sub(bottom[2], top[2])))


def _verify_edge(tables: SeedOverlapTables, n: Int, J: Int,
                 source: BoundaryLabel, edge: BoundaryEdge) raises:
    if transport(n, J, source, edge.i, edge.j) != edge.target:
        raise Error("upper recurrence child type or full offset mismatch")
    var parent = geometric_state(tables, source)
    if not interior_overlap(tables, parent):
        raise Error("upper recurrence parent is not strict")
    var actual = selected_overlap_child(tables, parent, edge.i, edge.j)
    if actual != geometric_state(tables, edge.target) or not interior_overlap(tables, actual):
        raise Error("upper recurrence literal overlap mismatch")


def _nearest_edge(tables: SeedOverlapTables, n: Int, J: Int,
                  source: BoundaryLabel) raises -> BoundaryEdge:
    if not is_central(tables, source):
        raise Error("upper recurrence source is not central y/y")
    var inflated = cubic_mul_beta(tables.field, geometric_state(tables, source).shift)
    var e = nearest_twice(tables, cubic_scale_checked(inflated, 2), -n, n)
    if _abs(e) >= n:
        raise Error("upper recurrence nearest gap exceeds proven range")
    var i = checked_add(1, max(e, 0))
    var j = checked_add(1, max(checked_sub(0, e), 0))
    var target = transport(n, J, source, i, j)
    var edge = BoundaryEdge(i, j, target)
    _verify_edge(tables, n, J, source, edge)
    if not is_central(tables, target):
        raise Error("upper recurrence selected child is not central")
    return edge


def nearest_edge(tables: SeedOverlapTables, n: Int, J: Int,
                 source: BoundaryLabel) raises -> BoundaryEdge:
    bind_upper(tables, n, J)
    return _nearest_edge(tables, n, J, source)


def reserve(n: Int, source: BoundaryLabel) raises -> Int:
    var z1 = checked_add(checked_add(checked_mul(2, source.x), source.c), source.y)
    return checked_mul(checked_add(n, 7), checked_add(checked_add(_abs(source.x), _abs(z1)), 1))


def _verify_reserve(tables: SeedOverlapTables, J: Int, B: Int,
                    source: BoundaryLabel) raises:
    var z1 = checked_add(checked_add(checked_mul(2, source.x), source.c), source.y)
    if _abs(source.x) > B or _abs(z1) > B:
        raise Error("upper recurrence initial-coordinate bound violated")
    if J <= 4:
        if _abs(checked_add(checked_mul(2, z1), source.x)) > B:
            raise Error("upper recurrence sheared-coordinate bound violated")
        if sign_at_perron(tables.field,
                CubicElt(checked_sub(checked_mul(checked_mul(2, J), B), 1), -1, 0)) <= 0:
            raise Error("upper recurrence shear reserve insufficient")
    else:
        if sign_at_perron(tables.field, CubicElt(checked_mul(-8, B),
                checked_sub(checked_mul(checked_mul(2, B), checked_sub(J, 4)), 1), -1)) <= 0:
            raise Error("upper recurrence contraction reserve insufficient")


def _append(tables: SeedOverlapTables, n: Int, J: Int,
            mut path: List[BoundaryEdge], mut source: BoundaryLabel,
            i: Int, j: Int, target: BoundaryLabel, flip: Bool, step_cap: Int) raises:
    if is_zero(source):
        raise Error("upper recurrence continued after integral zero")
    if len(path) >= step_cap:
        raise Error("upper recurrence step cap: no verdict")
    var edge = BoundaryEdge(j if flip else i, i if flip else j,
                           reversed_label(target) if flip else target)
    _verify_edge(tables, n, J, source, edge)
    path.append(edge)
    source = edge.target


def _exit_cycle(tables: SeedOverlapTables, n: Int, J: Int,
                mut path: List[BoundaryEdge], mut source: BoundaryLabel, step_cap: Int) raises:
    if not is_cycle(source) or not is_central(tables, source):
        raise Error("upper recurrence exit source is not an admitted cycle")
    var H = _abs(source.x)
    var flip = source.x < 0
    while checked_mul(J, H) >= 3:
        var s = checked_mul(J, H)
        if s > checked_sub(n, 1):
            raise Error("upper recurrence cycle ordinal bound violated")
        var lower = checked_sub(H, 1)
        _append(tables, n, J, path, source, 0, checked_sub(s, 2),
            BoundaryLabel(0, 2, checked_sub(1, H), checked_mul(-3, H),
                          checked_sub(checked_mul(6, H), 3)), flip, step_cap)
        _append(tables, n, J, path, source, checked_add(checked_mul(J, lower), 4), 1,
            BoundaryLabel(2, 2, lower, checked_mul(3, lower), checked_mul(-6, lower)), flip, step_cap)
        H = lower
    if H > 0:
        if J == 1:
            _append(tables, n, J, path, source, 0, 0,
                BoundaryLabel(0, 0, -H, checked_mul(-3, H), checked_mul(5, H)), flip, step_cap)
            _append(tables, n, J, path, source, 1, checked_add(1, checked_mul(checked_add(n, 4), H)),
                BoundaryLabel(2, 2, 0, checked_mul(2, H), checked_mul(-2, H)), flip, step_cap)
            _append(tables, n, J, path, source, 1, checked_add(checked_mul(2, H), 1),
                BoundaryLabel(2, 2, 0, 0, 0), flip, step_cap)
        elif J == 2 and H == 1:
            _append(tables, n, J, path, source, 0, 0,
                BoundaryLabel(0, 0, -1, -3, 4), flip, step_cap)
            _append(tables, n, J, path, source, 0, checked_add(checked_mul(2, n), 6),
                BoundaryLabel(0, 2, 0, 1, -1), flip, step_cap)
            _append(tables, n, J, path, source, 1, 2,
                BoundaryLabel(2, 2, 0, 0, 0), flip, step_cap)
        else:
            raise Error("upper recurrence uncovered cycle base: no verdict")


def verify_central_path(tables: SeedOverlapTables, n: Int, J: Int,
                        source: BoundaryLabel, cert: CentralEscape, step_cap: Int = 256) raises:
    bind_upper(tables, n, J)
    if not is_central(tables, source):
        raise Error("upper recurrence source is not central y/y")
    if step_cap < 0 or len(cert.path) > step_cap:
        raise Error("upper recurrence step cap: no verdict")
    if cert.central_depth < 0 or cert.central_depth > len(cert.path):
        raise Error("upper recurrence central phase mismatch")
    if cert.reserve != reserve(n, source):
        raise Error("upper recurrence source reserve mismatch")
    var w = source
    _verify_reserve(tables, J, cert.reserve, w)
    for index in range(len(cert.path)):
        if is_zero(w):
            raise Error("upper recurrence continued after integral zero")
        var edge = cert.path[index]
        if index < cert.central_depth:
            if is_cycle(w):
                raise Error("upper recurrence central phase continues past cycle")
            var expected = _nearest_edge(tables, n, J, w)
            if edge.i != expected.i or edge.j != expected.j or edge.target != expected.target:
                raise Error("upper recurrence selected nearest edge mismatch")
        elif index == cert.central_depth:
            if not is_cycle(w) or not is_central(tables, w):
                raise Error("upper recurrence central phase does not end at cycle")
        _verify_edge(tables, n, J, w, edge)
        w = edge.target
        if index < cert.central_depth:
            _verify_reserve(tables, J, cert.reserve, w)
    if not is_zero(w) or w.top != 2 or w.bottom != 2:
        raise Error("upper recurrence path is incomplete or not typed y/y zero")


def central_escape(tables: SeedOverlapTables, n: Int, J: Int,
                   source: BoundaryLabel, step_cap: Int = 256) raises -> CentralEscape:
    bind_upper(tables, n, J)
    if step_cap < 0:
        raise Error("upper recurrence step cap: no verdict")
    if not is_central(tables, source):
        raise Error("upper recurrence source is not central y/y")
    var B = reserve(n, source)
    var w = source
    var path = List[BoundaryEdge]()
    _verify_reserve(tables, J, B, w)
    while not is_zero(w) and not is_cycle(w):
        if len(path) >= step_cap:
            raise Error("upper recurrence step cap: no verdict")
        var edge = _nearest_edge(tables, n, J, w)
        path.append(edge)
        w = edge.target
        _verify_reserve(tables, J, B, w)
    var central_depth = len(path)
    if not is_zero(w):
        _exit_cycle(tables, n, J, path, w, step_cap)
    var cert = CentralEscape(path, central_depth, B)
    verify_central_path(tables, n, J, source, cert, step_cap)
    return cert^


def _z(value: Int) -> BigZ:
    return bigz_from_i64(Int64(value))


def _image(n: Int, d: Int, v: List[BigZ]) raises -> List[BigZ]:
    if len(v) != 3:
        raise Error("upper recurrence prefix requires three coordinates")
    var out = List[BigZ]()
    out.append(bigz_add(bigz_add(bigz_mul(_z(2), v[0]), v[1]), v[2]))
    out.append(bigz_add(v[1], v[2]))
    out.append(bigz_add(bigz_add(bigz_mul(_z(checked_add(n, d)), v[0]),
                               bigz_mul(_z(n), v[1])),
                       bigz_mul(_z(checked_add(n, 1)), v[2])))
    return out^


def original_prefixes(n: Int, J: Int, source: BoundaryLabel,
                      path: List[BoundaryEdge], limb_cap: Int = 1024) raises -> List[List[BigZ]]:
    """Unbounded signed integers, bounded resources, both original marks.

    Verify M^k*w0+Q_k-P_k=w_k at EVERY edge, with actual proper prefixes.
    This function does not replace the independent geometric path verifier.
    """
    var d = parameters(n, J)
    if source.top < 0 or source.top > 2 or source.bottom < 0 or source.bottom > 2:
        raise Error("upper recurrence source letter outside alphabet")
    if limb_cap < 1:
        raise Error("upper recurrence prefix limb cap: no verdict")
    var P = List[BigZ]()
    var Q = List[BigZ]()
    for _ in range(3):
        P.append(BigZ())
        Q.append(BigZ())
    var scaled = List[BigZ]()
    scaled.append(_z(source.x))
    scaled.append(_z(source.c))
    scaled.append(_z(source.y))
    var w = source
    for edge in path:
        if is_zero(w):
            raise Error("upper recurrence continued after integral zero")
        if transport(n, J, w, edge.i, edge.j) != edge.target:
            raise Error("upper recurrence child type or full offset mismatch")
        var top = _prefix(1, n, d, w.top, edge.i)
        var bottom = _prefix(1, n, d, w.bottom, edge.j)
        P = _image(n, d, P)
        Q = _image(n, d, Q)
        scaled = _image(n, d, scaled)
        var values = [edge.target.x, edge.target.c, edge.target.y]
        for coordinate in range(3):
            P[coordinate] = bigz_add(P[coordinate], _z(top[coordinate]))
            Q[coordinate] = bigz_add(Q[coordinate], _z(bottom[coordinate]))
            if (P[coordinate].limb_count() > limb_cap or Q[coordinate].limb_count() > limb_cap or
                scaled[coordinate].limb_count() > limb_cap):
                raise Error("upper recurrence prefix limb cap: no verdict")
            if not bigz_eq(bigz_sub(bigz_add(scaled[coordinate], Q[coordinate]), P[coordinate]),
                           _z(values[coordinate])):
                raise Error("upper recurrence original prefix identity mismatch")
        w = edge.target
    if not is_zero(w) or w.top != 2 or w.bottom != 2:
        raise Error("upper recurrence path is incomplete or not typed y/y zero")
    var result = List[List[BigZ]]()
    result.append(P^)
    result.append(Q^)
    return result^
