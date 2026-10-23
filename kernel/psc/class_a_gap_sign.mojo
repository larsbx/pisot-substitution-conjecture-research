"""Exact positive-box sign certificates for class-A gap margins (step (b)).

QX rows are u powers, columns h powers. Reuse the existing polynomial and
unbounded rational carriers. Standard tensor Bernstein conversion followed
by bounded, iterative dyadic subdivision; refusal never means non-hitting.
See docs/class-a-gap-sign-2026-10-23.md, especially closed-boundary strictness.
"""
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int, q_is_zero
from psc.exact import require_q
from psc.param_poly import QX, qx_norm

comptime DEGREE_BUDGET = 8


def _choose(n: Int, k: Int) -> Int:
    # All callers have 0<=k<=n<=8, so intermediate products fit Int.
    var out = 1
    for i in range(k):
        out = out * (n - i) // (i + 1)
    return out


def _grid(rows: Int, cols: Int) -> QX:
    var out = QX()
    for _ in range(rows):
        var row = List[Q]()
        for _ in range(cols):
            row.append(Q.zero())
        out.append(row^)
    return out^


def _validated(p: QX) raises -> QX:
    if len(p) > DEGREE_BUDGET + 1:
        raise Error("gap-sign u-degree budget exceeded")
    for row in p:
        if len(row) > DEGREE_BUDGET + 1:
            raise Error("gap-sign h-degree budget exceeded")
        for c in row:
            _ = require_q(c, "gap-sign coefficient")
    return qx_norm(p)


def bernstein_box(p: QX, H: Q, U: Q) raises -> QX:
    """Exact rectangular coefficients on [0,H] x [0,U], without factoring.

    Returned grid retains its full bidegree, including zero boundary rows.
    """
    _ = require_q(H, "gap-sign H")
    _ = require_q(U, "gap-sign U")
    if not Q.zero().lt(H) or not Q.zero().lt(U):
        raise Error("gap-sign bounds must be strictly positive")
    var f = _validated(p)
    var n = max(0, len(f) - 1)
    var m = 0
    for row in f:
        m = max(m, len(row) - 1)
    var horizontal = _grid(n + 1, m + 1)
    var upower = Q.one()
    for j in range(n + 1):
        var row = List[Q]()
        if j < len(f):
            row = f[j].copy()
        var hpower = Q.one()
        for k in range(len(row)):
            var c = row[k].mul(hpower).mul(upower)
            for i in range(k, m + 1):
                var weight = Q(Int64(_choose(i, k)), Int64(_choose(m, k)))
                horizontal[j][i] = horizontal[j][i].add(c.mul(weight))
            hpower = hpower.mul(H)
        upower = upower.mul(U)
    var out = _grid(n + 1, m + 1)
    for j in range(n + 1):
        for k in range(j + 1):
            var weight = Q(Int64(_choose(j, k)), Int64(_choose(n, k)))
            for i in range(m + 1):
                out[j][i] = out[j][i].add(horizontal[k][i].mul(weight))
    return out^


def _split(g: QX, axis: Int) raises -> Tuple[QX, QX]:
    """De Casteljau at 1/2 along exactly one tensor direction."""
    var rows = len(g)
    var cols = len(g[0])
    var left = _grid(rows, cols)
    var right = _grid(rows, cols)
    var count = rows if axis == 0 else cols
    var degree = cols - 1 if axis == 0 else rows - 1
    for line in range(count):
        var v = List[Q]()
        for k in range(degree + 1):
            v.append(g[line][k].copy() if axis == 0 else g[k][line].copy())
        for level in range(degree + 1):
            if axis == 0:
                left[line][level] = v[0].copy()
                right[line][degree - level] = v[degree - level].copy()
            else:
                left[level][line] = v[0].copy()
                right[degree - level][line] = v[degree - level].copy()
            for k in range(degree - level):
                v[k] = v[k].add(v[k + 1]).div(q_int(2))
    return left^, right^


struct GapSignCertificate(ImplicitlyCopyable, Copyable, Movable):
    var h_factor: Int
    var u_factor: Int
    var leaves: Int
    var visited: Int
    var depth: Int

    def __init__(out self, h_factor: Int, u_factor: Int):
        self.h_factor = h_factor
        self.u_factor = u_factor
        self.leaves = 0
        self.visited = 0
        self.depth = 0


def certify_gap_margin(p: QX, H: Q, U: Q, max_depth: Int = 8, max_cells: Int = 1023) raises -> GapSignCertificate:
    """Prove p>0 on (0,H]x(0,U], or refuse. Never returns a partial cover."""
    if max_depth < 0 or max_depth > 12 or max_cells < 1 or max_cells > 8191:
        raise Error("invalid gap-sign subdivision budget")
    var f = _validated(p)
    if len(f) == 0:
        raise Error("zero gap-sign margin cannot be strict")
    var h_factor = DEGREE_BUDGET + 1
    var u_factor = len(f)
    for j in range(len(f)):
        for i in range(len(f[j])):
            if not q_is_zero(f[j][i]):
                h_factor = min(h_factor, i)
                u_factor = min(u_factor, j)
    var residual = QX()
    for j in range(u_factor, len(f)):
        var row = List[Q]()
        for i in range(h_factor, len(f[j])):
            row.append(f[j][i].copy())
        residual.append(row^)
    var stack = List[QX]()
    var depths = List[Int]()
    stack.append(bernstein_box(residual, H, U))
    depths.append(0)
    var cert = GapSignCertificate(h_factor, u_factor)
    while len(stack) > 0:
        if cert.visited >= max_cells:
            raise Error("gap-sign cell budget exhausted: no certificate")
        var g = stack.pop()
        var depth = depths.pop()
        cert.visited += 1
        cert.depth = max(cert.depth, depth)
        var strict = True
        for row in g:
            for c in row:
                _ = require_q(c, "gap-sign Bernstein coefficient")
                if not Q.zero().lt(c):
                    strict = False
        if strict:
            cert.leaves += 1
            continue
        # The four tensor corner coefficients are exact corner values.
        # A zero even at a retained upper endpoint must not be certified.
        for j in [0, len(g) - 1]:
            for i in [0, len(g[0]) - 1]:
                if not Q.zero().lt(g[j][i]):
                    raise Error("gap-sign residual has a nonpositive closed-box corner")
        if depth >= max_depth:
            raise Error("gap-sign depth budget exhausted: no certificate")
        var axis = depth % 2
        if len(g) == 1:
            axis = 0
        elif len(g[0]) == 1:
            axis = 1
        var children = _split(g, axis)
        stack.append(children[1].copy())
        depths.append(depth + 1)
        stack.append(children[0].copy())
        depths.append(depth + 1)
    return cert
