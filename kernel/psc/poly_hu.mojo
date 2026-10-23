"""Integer polynomials in (h, u) and exact signs on the gap family's parameter box (#139, gaps d >= 5).

For a member `(d, n)` of a class-A line, `h = 1/(beta-1)` and `u = d h`. Every
Perron margin of the uniform certificate is `A + n B + (r h) C` with
`A, B, C` in `Z[h, u]` (`AffHU`); its sign is the sign of
`A h(1+h) + E B + (r h) C h(1+h)` where `E = n h(1+h) = 1 - eps h -
(1-eps) h^2 - u h - u h^2` (Lemma 4 of the design note), and `r h` is the
regime's value (`j h`, `u - j h`, or both for the middle regime).

Lemma 3 (docs/class-a-gap-uniform-certificate-design-2026-10-23.md): with
`t = 1/d`, every member of a regime with `l >= l0`, `d >= d0` has
`(u, t)` in the box `B = (0, 1/l0) x (0, 1/d0]` and `h = u t`. `sign_on_box`
substitutes `h = u t`, maps `B` onto the unit square, converts to the
Bernstein basis over the exact rationals of `finite_exact`, and bisects until
every cell certifies the same sign by the sub-face criterion (all coefficients
`>= 0`, and a positive governing coefficient on every sub-face of the cell
that lies inside `B`), or refuses (`UNDECIDED`). It never evaluates at a root
and never uses floating point.
"""
from finite_exact.rat_q import Q
from psc.exact import q_sign


struct PolyHU(Copyable, Movable, Equatable, Writable):
    """Dense coefficients `c[i][j]` of `h^i u^j`, trimmed so that the last row
    and the last column each hold a nonzero entry (the zero polynomial is `[]`)."""
    var c: List[List[Int]]

    def __init__(out self):
        self.c = List[List[Int]]()

    def __init__(out self, var c: List[List[Int]]):
        self.c = c^
        self._trim()

    @staticmethod
    def zero() -> PolyHU:
        return PolyHU()

    @staticmethod
    def monomial(i: Int, j: Int, coef: Int) -> PolyHU:
        var c = List[List[Int]]()
        for a in range(i + 1):
            c.append(List[Int](length=j + 1, fill=0))
        if coef != 0:
            c[i][j] = coef
        return PolyHU(c^)

    @staticmethod
    def const(x: Int) -> PolyHU:
        return PolyHU.monomial(0, 0, x)

    def _trim(mut self):
        # Drop zero rows from the top, then zero columns from the right.
        while len(self.c) > 0:
            var last = self.c[len(self.c) - 1].copy()
            var all_zero = True
            for x in last:
                if x != 0:
                    all_zero = False
            if not all_zero:
                break
            _ = self.c.pop()
        if len(self.c) == 0:
            return
        var width = 0
        for row in self.c:
            for j in range(len(row)):
                if row[j] != 0:
                    width = max(width, j + 1)
        for i in range(len(self.c)):
            var row = List[Int]()
            for j in range(width):
                row.append(self.c[i][j] if j < len(self.c[i]) else 0)
            self.c[i] = row^

    def is_zero(self) -> Bool:
        return len(self.c) == 0

    def deg_h(self) -> Int:
        return len(self.c) - 1

    def deg_u(self) -> Int:
        return (len(self.c[0]) - 1) if len(self.c) > 0 else -1

    def coefficient(self, i: Int, j: Int) -> Int:
        if i < 0 or i >= len(self.c) or j < 0 or j >= len(self.c[i]):
            return 0
        return self.c[i][j]

    def add(self, o: PolyHU) -> PolyHU:
        var rows = max(len(self.c), len(o.c))
        var cols = max(self.deg_u(), o.deg_u()) + 1
        var c = List[List[Int]]()
        for i in range(rows):
            var row = List[Int]()
            for j in range(cols):
                row.append(self.coefficient(i, j) + o.coefficient(i, j))
            c.append(row^)
        return PolyHU(c^)

    def scale(self, k: Int) -> PolyHU:
        var c = List[List[Int]]()
        for row in self.c:
            var out = List[Int]()
            for x in row:
                out.append(k * x)
            c.append(out^)
        return PolyHU(c^)

    def sub(self, o: PolyHU) -> PolyHU:
        return self.add(o.scale(-1))

    def mul(self, o: PolyHU) -> PolyHU:
        if self.is_zero() or o.is_zero():
            return PolyHU.zero()
        var rows = self.deg_h() + o.deg_h() + 1
        var cols = self.deg_u() + o.deg_u() + 1
        var c = List[List[Int]]()
        for _ in range(rows):
            c.append(List[Int](length=cols, fill=0))
        for i in range(len(self.c)):
            for j in range(len(self.c[i])):
                if self.c[i][j] == 0:
                    continue
                for p in range(len(o.c)):
                    for q in range(len(o.c[p])):
                        c[i + p][j + q] += self.c[i][j] * o.c[p][q]
        return PolyHU(c^)

    def __eq__(self, o: PolyHU) -> Bool:
        return self.sub(o).is_zero()

    def __ne__(self, o: PolyHU) -> Bool:
        return not (self == o)

    def write_to(self, mut w: Some[Writer]):
        var first = True
        for i in range(len(self.c)):
            for j in range(len(self.c[i])):
                if self.c[i][j] == 0:
                    continue
                if not first:
                    w.write(" + ")
                first = False
                w.write(self.c[i][j], "*h^", i, "*u^", j)
        if first:
            w.write("0")


def elimination_hu(eps: Int) -> PolyHU:
    """`E = n h(1+h) = 1 - eps h - (1-eps) h^2 - u h - u h^2`."""
    return (PolyHU.const(1).add(PolyHU.monomial(1, 0, -eps)).add(PolyHU.monomial(2, 0, eps - 1))
            .add(PolyHU.monomial(1, 1, -1)).add(PolyHU.monomial(2, 1, -1)))


def h_one_h() -> PolyHU:
    """`h (1 + h)`."""
    return PolyHU.monomial(1, 0, 1).add(PolyHU.monomial(2, 0, 1))


struct AffHU(Copyable, Movable):
    """`a + n b + (r h) c` over `Z[h, u]`."""
    var a: PolyHU
    var b: PolyHU
    var c: PolyHU

    def __init__(out self, var a: PolyHU, var b: PolyHU, var c: PolyHU):
        self.a = a^
        self.b = b^
        self.c = c^

    def add(self, o: AffHU) -> AffHU:
        return AffHU(self.a.add(o.a), self.b.add(o.b), self.c.add(o.c))

    def sub(self, o: AffHU) -> AffHU:
        return AffHU(self.a.sub(o.a), self.b.sub(o.b), self.c.sub(o.c))

    def is_zero(self) -> Bool:
        return self.a.is_zero() and self.b.is_zero() and self.c.is_zero()

    def numerator(self, rh: PolyHU, eps: Int) -> PolyHU:
        """`a h(1+h) + E b + rh c h(1+h)`: the sign of `a + n b + (r h) c` at `r h = rh`."""
        var hh = h_one_h()
        return self.a.mul(hh).add(elimination_hu(eps).mul(self.b)).add(rh.mul(self.c).mul(hh))


# ---------------------------------------------------------------------------
# Bernstein signs on the box (0, 1/l0) x (0, 1/d0] in (u, t), h = u t.
# ---------------------------------------------------------------------------

def _binomial(n: Int, k: Int) -> Int:
    if k < 0 or k > n:
        return 0
    var out = 1
    for i in range(k):
        out = out * (n - i) // (i + 1)
    return out


struct _Cell(Copyable, Movable):
    """Bernstein coefficients `b[i][j]` (`i` along `x` in `0..P`, `j` along `y` in `0..Q`)
    on the rectangle `[x0, x1] x [y0, y1]` of the unit square, with its position
    recorded by whether it meets the open faces `x = 0`, `x = 1`, `y = 0`."""
    var b: List[List[Q]]
    var s: List[List[Q]]
    var on_x0: Bool
    var on_x1: Bool
    var on_y0: Bool
    var depth: Int

    def __init__(out self, var b: List[List[Q]], var s: List[List[Q]], on_x0: Bool, on_x1: Bool, on_y0: Bool, depth: Int):
        """`b`: Bernstein coefficients of the polynomial; `s`: those of the side
        condition on the same cell (empty when there is none)."""
        self.b = b^
        self.s = s^
        self.on_x0 = on_x0
        self.on_x1 = on_x1
        self.on_y0 = on_y0
        self.depth = depth


def _to_bernstein(a: List[List[Q]]) -> List[List[Q]]:
    """Power coefficients `a[p][q]` of `x^p y^q` on `[0,1]^2` to Bernstein
    coefficients of the same bidegree: `b_ij = sum_{p<=i, q<=j} C(i,p)C(j,q)/(C(P,p)C(Q,q)) a_pq`."""
    var P = len(a) - 1
    var Qd = len(a[0]) - 1
    var b = List[List[Q]]()
    for i in range(P + 1):
        var row = List[Q]()
        for j in range(Qd + 1):
            var acc = Q.zero()
            for p in range(i + 1):
                for q in range(j + 1):
                    var num = Int64(_binomial(i, p) * _binomial(j, q))
                    var den = Int64(_binomial(P, p) * _binomial(Qd, q))
                    acc = acc.add(a[p][q].mul(Q(num, den)))
            row.append(acc^)
        b.append(row^)
    return b^


def _bisect(b: List[List[Q]], along_x: Bool) -> List[List[List[Q]]]:
    """de Casteljau bisection of one Bernstein table at the midpoint, in `x`
    (columns) or `y` (rows): `[left, right]`."""
    var P = len(b) - 1
    var Qd = len(b[0]) - 1
    var half = Q(1, 2)
    var left = List[List[Q]]()
    var right = List[List[Q]]()
    if along_x:
        for _ in range(P + 1):
            left.append(List[Q]())
            right.append(List[Q]())
        for j in range(Qd + 1):
            var cur = List[Q]()
            for i in range(P + 1):
                cur.append(b[i][j].copy())
            var lo = List[Q]()
            var hi = List[Q]()
            lo.append(cur[0].copy())
            hi.append(cur[P].copy())
            for _ in range(P):
                var nxt = List[Q]()
                for i in range(len(cur) - 1):
                    nxt.append(cur[i].add(cur[i + 1]).mul(half))
                cur = nxt^
                lo.append(cur[0].copy())
                hi.append(cur[len(cur) - 1].copy())
            for i in range(P + 1):
                left[i].append(lo[i].copy())
                right[i].append(hi[P - i].copy())
        return [left^, right^]
    for i in range(P + 1):
        var cur = b[i].copy()
        var lo = List[Q]()
        var hi = List[Q]()
        lo.append(cur[0].copy())
        hi.append(cur[Qd].copy())
        for _ in range(Qd):
            var nxt = List[Q]()
            for j in range(len(cur) - 1):
                nxt.append(cur[j].add(cur[j + 1]).mul(half))
            cur = nxt^
            lo.append(cur[0].copy())
            hi.append(cur[len(cur) - 1].copy())
        var hi_row = List[Q]()
        for j in range(Qd + 1):
            hi_row.append(hi[Qd - j].copy())
        left.append(lo^)
        right.append(hi_row^)
    return [left^, right^]


def _split(cell: _Cell, along_x: Bool) -> List[_Cell]:
    """Bisect the cell, carrying the side table along."""
    var halves = _bisect(cell.b, along_x)
    var sides = List[List[List[Q]]]()
    if len(cell.s) > 0:
        sides = _bisect(cell.s, along_x)
    else:
        sides = [List[List[Q]](), List[List[Q]]()]
    if along_x:
        return [_Cell(halves[0].copy(), sides[0].copy(), cell.on_x0, False, cell.on_y0, cell.depth + 1),
                _Cell(halves[1].copy(), sides[1].copy(), False, cell.on_x1, cell.on_y0, cell.depth + 1)]
    return [_Cell(halves[0].copy(), sides[0].copy(), cell.on_x0, cell.on_x1, cell.on_y0, cell.depth + 1),
            _Cell(halves[1].copy(), sides[1].copy(), cell.on_x0, cell.on_x1, False, cell.depth + 1)]


def _outside_hull(cell: _Cell) -> Bool:
    """Every Bernstein coefficient of the side condition is negative on the cell,
    so the side condition is `< 0` on the whole closed cell and no member maps
    into it."""
    if len(cell.s) == 0:
        return False
    for i in range(len(cell.s)):
        for j in range(len(cell.s[i])):
            if q_sign(cell.s[i][j]) >= 0:
                return False
    return True


def _column_positive(cell: _Cell, i: Int, want: Int) -> Bool:
    for j in range(len(cell.b[0])):
        if q_sign(cell.b[i][j]) * want > 0:
            return True
    return False


def _row_positive(cell: _Cell, j: Int, want: Int) -> Bool:
    for i in range(len(cell.b)):
        if q_sign(cell.b[i][j]) * want > 0:
            return True
    return False


def _certify(cell: _Cell, want: Int) -> Bool:
    """The sub-face criterion for sign `want` (`+1` or `-1`) on the cell's part inside `B`."""
    var P = len(cell.b) - 1
    var Qd = len(cell.b[0]) - 1
    var any_pos = False
    for i in range(P + 1):
        for j in range(Qd + 1):
            var s = q_sign(cell.b[i][j]) * want
            if s < 0:
                return False
            if s > 0:
                any_pos = True
    if not any_pos:
        return False
    # Edges inside B: left column i=0 unless on x=0; right column i=P unless on x=1;
    # bottom row j=0 unless on y=0; top row j=Qd always (t = 1/d0 belongs to B).
    if not cell.on_x0 and not _column_positive(cell, 0, want):
        return False
    if not cell.on_x1 and not _column_positive(cell, P, want):
        return False
    if not cell.on_y0 and not _row_positive(cell, 0, want):
        return False
    if not _row_positive(cell, Qd, want):
        return False
    # Corners inside B: (0,0) unless on x=0 or y=0; (P,0) unless on x=1 or y=0;
    # (0,Qd) unless on x=0; (P,Qd) unless on x=1.
    if not cell.on_x0 and not cell.on_y0 and q_sign(cell.b[0][0]) * want <= 0:
        return False
    if not cell.on_x1 and not cell.on_y0 and q_sign(cell.b[P][0]) * want <= 0:
        return False
    if not cell.on_x0 and q_sign(cell.b[0][Qd]) * want <= 0:
        return False
    if not cell.on_x1 and q_sign(cell.b[P][Qd]) * want <= 0:
        return False
    return True


def box_polynomial(f: PolyHU, l0: Int, d0: Int, strip: Bool = True) -> List[List[Q]]:
    """`G(u,t) = f(u t, u)` with common monomial factors `u^a t^b` removed (unless
    `strip` is false), as power coefficients in `x = l0 u`, `y = d0 t` on the unit square."""
    # g[p][q] is the coefficient of u^p t^q: h^i u^j -> u^(i+j) t^i.
    var P = f.deg_h() + f.deg_u()
    var Qd = f.deg_h()
    var g = List[List[Int]]()
    for _ in range(P + 1):
        g.append(List[Int](length=Qd + 1, fill=0))
    for i in range(len(f.c)):
        for j in range(len(f.c[i])):
            g[i + j][i] += f.c[i][j]
    var p_min = P + 1
    var q_min = Qd + 1
    for p in range(P + 1):
        for q in range(Qd + 1):
            if g[p][q] != 0:
                p_min = min(p_min, p)
                q_min = min(q_min, q)
    if not strip:
        p_min = 0
        q_min = 0
    var p_max = 0
    var q_max = 0
    for p in range(P + 1):
        for q in range(Qd + 1):
            if g[p][q] != 0:
                p_max = max(p_max, p)
                q_max = max(q_max, q)
    var a = List[List[Q]]()
    var lp = Int64(1)
    for p in range(p_min, p_max + 1):
        var row = List[Q]()
        var dq = Int64(1)
        for q in range(q_min, q_max + 1):
            # u^p t^q = x^p y^q / (l0^p d0^q)
            row.append(Q(Int64(g[p][q]), lp * dq))
            dq *= Int64(d0)
        a.append(row^)
        lp *= Int64(l0)
    return a^


def sign_on_box(f: PolyHU, l0: Int, d0: Int, max_depth: Int = 12) raises -> Int:
    """Lemma 3: the sign of `f(h, u)` at every `(h, u) = (u t, u)` with `(u, t)` in
    `(0, 1/l0) x (0, 1/d0]`: `0` for the zero polynomial, `+-1` when every
    cell of the bisection certifies that sign, else raises `UNDECIDED sign`."""
    return sign_within_hull(f, PolyHU.zero(), l0, d0, max_depth)


def strip_hu(f: PolyHU) -> PolyHU:
    """`f` divided by the largest monomial `h^a u^b` dividing it (positive on the box)."""
    if f.is_zero():
        return f.copy()
    var a_min = 1000000
    var b_min = 1000000
    for i in range(len(f.c)):
        for j in range(len(f.c[i])):
            if f.c[i][j] != 0:
                a_min = min(a_min, i)
                b_min = min(b_min, j)
    var out = PolyHU.zero()
    for i in range(len(f.c)):
        for j in range(len(f.c[i])):
            if f.c[i][j] != 0:
                out = out.add(PolyHU.monomial(i - a_min, j - b_min, f.c[i][j]))
    return out^


def _h_free(f: PolyHU) -> List[Int]:
    """The coefficients of `f(0, u)` in `u`."""
    var out = List[Int]()
    if len(f.c) > 0:
        for j in range(len(f.c[0])):
            out.append(f.c[0][j])
    while len(out) > 0 and out[len(out) - 1] == 0:
        _ = out.pop()
    return out^


def _constant_ratio(pf: List[Int], ps: List[Int]) -> List[Int]:
    """`[num, den]` with `den > 0` when `pf = (num/den) ps` as polynomials and
    `ps != 0`; `[0, 0]` otherwise (including `pf = 0`, which needs no multiple)."""
    if len(ps) == 0 or len(pf) == 0 or len(pf) != len(ps):
        return [0, 0]
    var num = pf[len(pf) - 1]
    var den = ps[len(ps) - 1]
    for j in range(len(pf)):
        if pf[j] * den != ps[j] * num:
            return [0, 0]
    if den < 0:
        num = -num
        den = -den
    return [num, den]


def _bernstein_sign(f: PolyHU, side: PolyHU, l0: Int, d0: Int, max_depth: Int) raises -> Int:
    """Lemma 3 with Lemma 3' cell skipping, on `f` alone."""
    var a = box_polynomial(f, l0, d0)
    var sb = List[List[Q]]()
    if not side.is_zero():
        sb = _to_bernstein(box_polynomial(side, l0, d0, False))
    var root = _Cell(_to_bernstein(a), sb^, True, True, True, 0)
    var stack = List[_Cell]()
    stack.append(root^)
    var sign = 0
    var skipped = 0
    while len(stack) > 0:
        var cell = stack.pop()
        if _outside_hull(cell):
            skipped += 1
            continue
        var s = 0
        if _certify(cell, 1):
            s = 1
        elif _certify(cell, -1):
            s = -1
        if s != 0:
            if sign == 0:
                sign = s
            elif sign != s:
                raise Error("UNDECIDED sign: the polynomial changes sign on the (u, t) box")
            continue
        if cell.depth >= max_depth:
            raise Error("UNDECIDED sign: a box cell is still mixed at depth " + String(max_depth))
        var P = len(cell.b) - 1
        var Qd = len(cell.b[0]) - 1
        var along_x = (cell.depth % 2 == 0 and P > 0) or Qd == 0
        if P == 0 and Qd == 0:
            raise Error("UNDECIDED sign: a constant cell failed the criterion")
        var kids = _split(cell, along_x)
        for k in range(len(kids)):
            stack.append(kids[k].copy())
    if sign == 0:
        raise Error("UNDECIDED sign: no cell certified" + (" (every cell lies outside the hull)" if skipped > 0 else ""))
    return sign


def sign_within_hull(f: PolyHU, side: PolyHU, l0: Int, d0: Int, max_depth: Int = 12) raises -> Int:
    """`sign_on_box` restricted to the part of the box where `side(h, u) >= 0`
    (Lemma 3'), in two steps. First, cells on which every Bernstein coefficient
    of `side` is negative contain no point with `side >= 0` and are skipped.
    Second, when that is still undecided and `f(0, u) = q side(0, u)` for one
    rational `q`, the sign of `g = den f - num side` (whose `h`-free part
    vanishes, so a factor `h` strips) is certified instead: `side >= 0` and
    `den > 0` give `f > 0` wherever `g > 0` and `q >= 0`, and `f < 0` wherever
    `g < 0` and `q <= 0`. With `side = E - l0 u(1+h)` (`E = n h(1+h)`), which
    is `>= 0` at every member `n >= d l0`, the certified sign holds at every
    member. The zero polynomial as `side` means no restriction."""
    if l0 < 1 or d0 < 1:
        raise Error("box floors must be positive")
    if f.is_zero():
        return 0
    var direct = 0
    var first = String("")
    try:
        direct = _bernstein_sign(f, side, l0, d0, max_depth)
        return direct
    except e:
        first = String(e)
    if side.is_zero():
        raise Error(first)
    var f1 = strip_hu(f)
    var ratio = _constant_ratio(_h_free(f1), _h_free(side))
    if ratio[1] == 0:
        raise Error(first + "; no hull multiple cancels the h-free part")
    var g = strip_hu(f1.scale(ratio[1]).sub(side.scale(ratio[0])))
    if g.is_zero():
        raise Error(first + "; f is a multiple of the hull condition")
    var sg = _bernstein_sign(g, side, l0, d0, max_depth)
    if ratio[0] >= 0 and sg > 0:
        return 1
    if ratio[0] <= 0 and sg < 0:
        return -1
    raise Error(first + "; the hull multiple (" + String(ratio[0]) + "/" + String(ratio[1]) + ") leaves the sign undecided")
