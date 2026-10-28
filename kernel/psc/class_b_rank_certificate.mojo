"""Exact all-parameter check of a class-B piecewise-affine rank with symbolic edges.

A certificate fixes a residue ray q = q0 + t (t >= 0 an integer), typed pieces
P = (top,bottom,s,d; lo(q) <= k <= hi(q)), an integer potential
X_P(q,k) = a*q + b*k + c per piece, and symbolic edges (P -> Q, dx) on parent
domains lo_e(q) <= k <= hi_e(q). An edge sends parent k to child k' = s_P + dx - k
in Q (the exact occurrence identity k' = s - k + Δx). Every endpoint is
integer-affine in t. This module proves, for every integer t >= 0:

  * pieces are nonempty, X_P >= 0 on them, and same-type pieces are disjoint;
  * each edge domain is nonempty, lies in P, and its image lies in Q;
  * X_Q(q, k') <= X_P(q, k) - 1 on every edge domain;
  * the edge domains of each non-target piece cover that piece.

Linear inequalities are checked at the two vertices of the polyhedron
{t >= 0, lo(t) <= k <= hi(t)} and on its two recession rays (1, slope), which
is exact for an affine function on that polyhedron. Coverage is checked by an
exact sweep at every t up to one past the last crossing of any two endpoint
functions, after which every comparison the sweep makes is constant.

It does NOT prove the hypotheses that make this a boundary-hitting statement:
that every graph vertex lies in some piece, and that each symbolic edge is an
actual legal overlap edge at every lattice point of its domain. `replay`
checks those two hypotheses on one finite member only.
"""

comptime COVERAGE_HORIZON = 1000000
# Every certificate value (header, ends, potentials) and every replayed q lies in
# [-VALUE_BUDGET, VALUE_BUDGET], so each checked product and sum stays below 2^62
# in magnitude; a value outside refuses rather than risking Int wrap-around.
comptime VALUE_BUDGET = 1000000


struct Affine(ImplicitlyCopyable, Copyable, Movable):
    """v0 + slope*t."""
    var slope: Int
    var v0: Int

    def __init__(out self, slope: Int, v0: Int):
        self.slope = slope
        self.v0 = v0

    def at(self, t: Int) -> Int:
        return self.v0 + self.slope * t

    def shifted(self, c: Int) -> Affine:
        return Affine(self.slope, self.v0 + c)


def always_le(f: Affine, g: Affine) -> Bool:
    """f(t) <= g(t) for every integer t >= 0."""
    return f.v0 <= g.v0 and f.slope <= g.slope


struct Piece(ImplicitlyCopyable, Copyable, Movable):
    var top: Int
    var bottom: Int
    var s: Int
    var d: Int
    var lo: Affine
    var hi: Affine
    var a: Int
    var b: Int
    var c: Int
    var target: Bool

    def __init__(out self, row: List[Int]) raises:
        if len(row) != 12 or row[11] < 0 or row[11] > 1:
            raise Error("invalid piece row")
        self.top = row[0]
        self.bottom = row[1]
        self.s = row[2]
        self.d = row[3]
        self.lo = Affine(row[4], row[5])
        self.hi = Affine(row[6], row[7])
        self.a = row[8]
        self.b = row[9]
        self.c = row[10]
        self.target = row[11] == 1


struct Edge(ImplicitlyCopyable, Copyable, Movable):
    var parent: Int
    var child: Int
    var dx: Int
    var lo: Affine
    var hi: Affine

    def __init__(out self, row: List[Int]) raises:
        if len(row) != 7:
            raise Error("invalid edge row")
        self.parent = row[0]
        self.child = row[1]
        self.dx = row[2]
        self.lo = Affine(row[3], row[4])
        self.hi = Affine(row[5], row[6])


struct RankCertificate(Copyable, Movable):
    var plus: Bool
    var gap: Int
    var residue: Int
    var q0: Int
    var pieces: List[Piece]
    var edges: List[Edge]

    def __init__(out self, text: String) raises:
        var lines = text.splitlines()
        if len(lines) < 2:
            raise Error("empty certificate")
        var h = lines[0].split(" ")
        if len(h) != 5 or String(h[0]) != "C" or (String(h[1]) != "plus" and String(h[1]) != "minus"):
            raise Error("invalid certificate header")
        self.plus = String(h[1]) == "plus"
        self.gap = Int(h[2])
        self.residue = Int(h[3])
        self.q0 = Int(h[4])
        if self.gap > VALUE_BUDGET or self.q0 > VALUE_BUDGET:
            raise Error("certificate coefficient budget exhausted")
        if self.gap < 1 or self.residue < 0 or self.residue >= self.gap or self.q0 < 1 or self.q0 % self.gap != self.residue:
            raise Error("invalid residue ray")
        self.pieces = List[Piece]()
        self.edges = List[Edge]()
        for line in lines[1:]:
            var p = line.split(" ")
            var row = List[Int]()
            for x in p[1:]:
                var v = Int(x)
                if v < -VALUE_BUDGET or v > VALUE_BUDGET:
                    raise Error("certificate coefficient budget exhausted")
                row.append(v)
            if String(p[0]) == "P":
                self.pieces.append(Piece(row))
            elif String(p[0]) == "E":
                self.edges.append(Edge(row))
            else:
                raise Error("unknown certificate row")

    def q(self, t: Int) -> Int:
        return self.q0 + self.gap * t

    def potential(self, i: Int, t: Int, k: Int) -> Int:
        ref p = self.pieces[i]
        return p.a * self.q(t) + p.b * k + p.c


def _piece_checks(cert: RankCertificate) raises:
    var n = len(cert.pieces)
    if n == 0:
        raise Error("certificate without pieces")
    for i in range(n):
        ref p = cert.pieces[i]
        if not always_le(p.lo, p.hi):
            raise Error("piece empty for some parameter")
        if p.target and (p.s != 0 or p.d != 0 or p.lo.slope != 0 or p.lo.v0 != 0 or p.hi.slope != 0 or p.hi.v0 != 0):
            raise Error("target piece is not the offset-zero label")
        # X >= 0: two vertices at t=0, two rays (1, slope).
        for f in [p.lo, p.hi]:
            if cert.potential(i, 0, f.v0) < 0 or p.a * cert.gap + p.b * f.slope < 0:
                raise Error("negative potential on piece")
        if i > 0:
            ref r = cert.pieces[i - 1]
            if r.top == p.top and r.bottom == p.bottom and r.s == p.s and r.d == p.d:
                if not always_le(r.hi.shifted(1), p.lo):
                    raise Error("same-type pieces overlap or are unordered")
            elif not (r.top < p.top or (r.top == p.top and (r.bottom < p.bottom or (r.bottom == p.bottom and (r.s < p.s or (r.s == p.s and r.d < p.d)))))):
                raise Error("pieces not in type order")


def _edge_checks(cert: RankCertificate) raises:
    var n = len(cert.pieces)
    for e in cert.edges:
        if e.parent < 0 or e.parent >= n or e.child < 0 or e.child >= n or e.dx < -1 or e.dx > 1:
            raise Error("invalid edge endpoints")
        ref p = cert.pieces[e.parent]
        ref c = cert.pieces[e.child]
        if p.target:
            raise Error("target pieces need no descent edge")
        if not (always_le(e.lo, e.hi) and always_le(p.lo, e.lo) and always_le(e.hi, p.hi)):
            raise Error("edge domain not a nonempty part of its piece")
        # Image of [lo,hi] under k -> s+dx-k is [s+dx-hi, s+dx-lo].
        var base = p.s + e.dx
        var img_lo = Affine(-e.hi.slope, base - e.hi.v0)
        var img_hi = Affine(-e.lo.slope, base - e.lo.v0)
        if not (always_le(c.lo, img_lo) and always_le(img_hi, c.hi)):
            raise Error("edge image leaves its child piece")
        # f(t,k) = X_P(q,k) - X_Q(q, base-k) - 1 >= 0 at both vertices and on both rays.
        for f in [e.lo, e.hi]:
            if cert.potential(e.parent, 0, f.v0) - cert.potential(e.child, 0, base - f.v0) < 1:
                raise Error("potential does not decrease at an edge vertex")
            if (p.a - c.a) * cert.gap + (p.b + c.b) * f.slope < 0:
                raise Error("potential does not decrease along an edge ray")


def _last_crossing(fs: List[Affine]) raises -> Int:
    var last = 0
    for i in range(len(fs)):
        for j in range(i + 1, len(fs)):
            var ds = fs[i].slope - fs[j].slope
            if ds == 0:
                continue
            var dv = fs[j].v0 - fs[i].v0
            # Integer t past which sign(f_i - f_j) is constant: floor(dv/ds) + 1.
            last = max(last, dv // ds + 1)  # floor division
    if last > COVERAGE_HORIZON:
        raise Error("coverage crossing horizon exhausted")
    return last


def _covered_at(cert: RankCertificate, i: Int, owned: List[Int], t: Int) -> Bool:
    ref p = cert.pieces[i]
    var los = List[Int]()
    var his = List[Int]()
    for e in owned:
        var lo = cert.edges[e].lo.at(t)
        var hi = cert.edges[e].hi.at(t)
        var h = len(los)
        los.append(lo)
        his.append(hi)
        while h > 0 and los[h - 1] > lo:
            los[h] = los[h - 1]
            his[h] = his[h - 1]
            h -= 1
        los[h] = lo
        his[h] = hi
    var reach = p.lo.at(t) - 1
    for h in range(len(los)):
        if los[h] > reach + 1:
            return False
        reach = max(reach, his[h])
    return reach >= p.hi.at(t)


def _coverage_checks(cert: RankCertificate) raises -> Int:
    var horizon = 0
    for i in range(len(cert.pieces)):
        if cert.pieces[i].target:
            continue
        var owned = List[Int]()
        var fs: List[Affine] = [cert.pieces[i].lo, cert.pieces[i].hi]
        for e in range(len(cert.edges)):
            if cert.edges[e].parent == i:
                owned.append(e)
                fs.append(cert.edges[e].lo)
                fs.append(cert.edges[e].hi.shifted(1))
                fs.append(cert.edges[e].hi)
        if len(owned) == 0:
            raise Error("non-target piece without a descent edge")
        var last = _last_crossing(fs)
        horizon = max(horizon, last)
        for t in range(last + 1):
            if not _covered_at(cert, i, owned, t):
                raise Error("descent edges leave a lattice point of a piece uncovered")
    return horizon


def check_rank_certificate(cert: RankCertificate) raises -> Int:
    """Raises unless every all-parameter condition holds; returns the coverage horizon."""
    _piece_checks(cert)
    _edge_checks(cert)
    return _coverage_checks(cert)


def piece_of(cert: RankCertificate, t: Int, label: List[Int]) -> Int:
    """Index of the piece holding `label` = [top,bottom,k,c,y] at parameter t, or -1."""
    var k = label[2]
    var s = 3 * k + label[3] + label[4]
    var d = label[3] - 3 * k
    for i in range(len(cert.pieces)):
        ref p = cert.pieces[i]
        if p.top == label[0] and p.bottom == label[1] and p.s == s and p.d == d and p.lo.at(t) <= k and k <= p.hi.at(t):
            return i
    return -1


def child_label(cert: RankCertificate, e: Int, k: Int) -> List[Int]:
    """The label edge `e` assigns to parent coordinate k: c = 3k'+d, y = s-6k'-d."""
    ref p = cert.pieces[cert.edges[e].parent]
    ref c = cert.pieces[cert.edges[e].child]
    var kk = p.s + cert.edges[e].dx - k
    return [c.top, c.bottom, kk, 3 * kk + c.d, c.s - 6 * kk - c.d]
