"""Theorems T_C and T_C2: class-C pieces on the symbolic cone engine.

docs/class-c-tail-theorem-2026-10-28.md (T_C, the frozen tail) and
docs/class-c-strip-stopgo-2026-10-29.md (T_C2, the strip `3d <= n` below the
onset). The lines are

    sigma(x) = x y^(n+d) x,   sigma(c) = c y^n x,   sigma(y) = c y^(n-d+eps) c,   eps = +-1,

and a *piece* is a set of members `(d, n)` parametrized by `s = (s1, s2)` in
one of two unimodular frames: `TAIL`, `s = (d, m)` with `n = 4d + c + m`, and
`STRIP`, `s = (k, j) = (n - 3d, 4d - n)`, i.e. `d = k + j`, `n = 4k + 3j`. A
piece is a cone (`s1 >= a0`, `s2 >= b0`), a diagonal line (`s2 = b0` fixed,
`s1 >= a0`; `s2` does not occur) or a gap line (`s1 = a0` fixed, `s2 >= b0`;
`s1` does not occur). Every
run length is affine in `s`, so `psc.symbolic_cone` decides the whole piece at
once: it certifies that every member is PIP with `beta` in the supplied
brackets, then builds the swap-seed overlap graph with every child decided on
the piece (Lemma S of docs/p1b-symbolic-line-2026-10-07.md). `certify_piece`
adds three checks the theorem needs: every vertex has an offset-zero
descendant, every offset is a constant (so the label set does not depend on
`s`), and, as a cross-check only, the graph equals the exact graph at one
member of the piece.
"""
from psc.class_a_gap_dataset import typed_intervals
from psc.class_c_gap_profile import c_block, c_member, rows_of, vertices_of
from psc.exact import q_string
from psc.param_poly import QX, qx_add, qx_affine2, qx_at, qx_const, qx_const_term, qx_deg, qx_sub
from psc.symbolic_cone import (
    Bracket, Cone, ConeGraph, Frac2, Region, cone_offset_zero_reachable, r2_add, r2_const, r2_div, r2_sub,
    symbolic_cone_graph,
)
from symbolic_line_certificate import exact_vertex_keys, same_set


comptime CONE = 0
comptime DIAGONAL = 1  # s2 = b0 fixed
comptime GAP = 2  # s1 = a0 fixed
comptime TAIL = 0  # s = (d, m), n = 4d + c + m
comptime STRIP = 1  # s = (k, j) = (n - 3d, 4d - n)


struct Piece(ImplicitlyCopyable, Copyable, Movable):
    """Members with `s1 >= a0`, `s2 >= b0` (`CONE`), `s2 = b0` (`DIAGONAL`) or
    `s1 = a0` (`GAP`), in the `TAIL` frame (`a0 = d0`, `b0 = m0`, offset `c`)
    or the `STRIP` frame (`a0 = k0`, `b0 = j0`; `c` must be 0)."""
    var eps: Int
    var c: Int
    var d0: Int  # a0
    var m0: Int  # b0
    var kind: Int
    var frame: Int

    def __init__(out self, eps: Int, c: Int, d0: Int, m0: Int, kind: Int, frame: Int = TAIL) raises:
        if eps != 1 and eps != -1:
            raise Error("class-C piece requires eps = +-1")
        if kind < CONE or kind > GAP or frame < TAIL or frame > STRIP:
            raise Error("class-C piece requires a known kind and frame")
        if frame == TAIL and (m0 < 0 or d0 < 2 or d0 > 64):
            raise Error("class-C piece requires m0 >= 0, 2 <= d0 <= 64 and a known kind")
        if frame == STRIP and (c != 0 or d0 < -64 or d0 > 64 or m0 < -64 or m0 > 64 or d0 + m0 < 1):
            raise Error("class-C strip piece requires c = 0, |k0|, |j0| <= 64 and d = k0 + j0 >= 1")
        self.eps = eps
        self.c = c
        self.d0 = d0
        self.m0 = m0
        self.kind = kind
        self.frame = frame
        var y = self.coeffs(2)
        if y[0] + y[1] * self.d0 + y[2] * self.m0 < 1:
            raise Error("class-C piece leaves the normal form: n - d + eps < 1 at its corner")

    def coeffs(self, a: Int) -> List[Int]:
        """Run length of `sigma(a)` (`n + d`, `n`, `n - d + eps`) as `[c0, k1, k2]`,
        `c0 + k1 s1 + k2 s2`, with a fixed coordinate folded into `c0`."""
        var sd = 1 if a == 0 else (0 if a == 1 else -1)  # coefficient of d
        # d = d1 s1 + d2 s2, n = c + n1 s1 + n2 s2
        var d1 = 1
        var d2 = 0 if self.frame == TAIL else 1
        var n1 = 4
        var n2 = 1 if self.frame == TAIL else 3
        var out = List[Int]([self.c + (self.eps if a == 2 else 0), n1 + sd * d1, n2 + sd * d2])
        if self.kind == DIAGONAL:
            out[0] += out[2] * self.m0
            out[2] = 0
        elif self.kind == GAP:
            out[0] += out[1] * self.d0
            out[1] = 0
        return out^

    def run(self, a: Int) -> QX:
        var k = self.coeffs(a)
        return qx_affine2(k[0], k[2], k[1])

    def region(self) -> Region:
        return Region(0 if self.kind == GAP else self.d0, 0 if self.kind == DIAGONAL else self.m0)

    def member(self, s1: Int, s2: Int) -> List[Int]:
        """`(d, n)` at `s`."""
        var a = self.d0 if self.kind == GAP else s1
        var b = self.m0 if self.kind == DIAGONAL else s2
        if self.frame == STRIP:
            return [a + b, 4 * a + 3 * b]
        return [a, 4 * a + self.c + b]

    def name(self) -> String:
        if self.frame == STRIP:
            var k = (" n-3d=" if self.kind == GAP else " n-3d>=") + String(self.d0)
            var j = (" 4d-n=" if self.kind == DIAGONAL else " 4d-n>=") + String(self.m0)
            return "eps=" + String(self.eps) + k + j
        var d = (" d=" if self.kind == GAP else " d>=") + String(self.d0)
        var m = (" n-4d=" if self.kind == DIAGONAL else " n-4d>=") + String(self.c + self.m0)
        return "eps=" + String(self.eps) + d + m


def tail_cone(p: Piece) raises -> Cone:
    """The cone of a piece, with brackets of beta from the fixed-point form
    `beta = r + 2 (q + p_x / (beta - 2)) / (beta - 1)` of `ell M = beta ell`
    (`ell_y = 1`, `ell_c = (ell_x + q) / (beta - 1)`, `ell_x = p_x / (beta - 2)`,
    with `(p_x, q, r)` the three run lengths): iterates from `x0 = r + 2`,
    alternating sides of beta. They are proposals; `certify_cone` certifies them."""
    var runs = List[QX]([p.run(0), p.run(1), p.run(2)])
    var x0 = r2_const(qx_add(runs[2], qx_const(2)))
    var xs = List[Frac2]()
    xs.append(x0.copy())
    for _ in range(3):
        ref x = xs[len(xs) - 1]
        var inner = r2_add(r2_const(runs[1]), r2_div(r2_const(runs[0]), r2_sub(x, r2_const(qx_const(2)))))
        var two_inner = r2_add(inner, inner)
        var nxt = r2_add(r2_const(runs[2]), r2_div(two_inner, r2_sub(x, r2_const(qx_const(1)))))
        xs.append(nxt^)
    var brs = List[Bracket]()
    brs.append(Bracket(xs[0].copy(), xs[1].copy()))
    brs.append(Bracket(xs[2].copy(), xs[1].copy()))
    brs.append(Bracket(xs[2].copy(), xs[3].copy()))
    return Cone([0, 1, 1], [0, 0, 1], runs^, 2, brs^)


def _int_of(p: QX) raises -> Int:
    if qx_deg(p) > 0:
        raise Error("an offset depends on s: the label set is not frozen on the piece")
    var s = q_string(qx_const_term(p))
    if "/" in s:
        raise Error("a non-integer offset")
    return Int(s)


def labels(g: ConeGraph) raises -> List[List[Int]]:
    """`[top, bottom, k, c, y]` per vertex; raises unless every offset is a constant integer."""
    var out = List[List[Int]]()
    for v in g.vertices:
        out.append([v.top, v.bottom, _int_of(v.w[0]), _int_of(v.w[1]), _int_of(v.w[2])])
    return out^


def rows(g: ConeGraph) raises -> String:
    """The label set as typed rows `R top bottom s y k_lo k_hi`, the profile packet's format."""
    var keyed = List[List[Int]]()
    for l in labels(g):
        keyed.append([l[0], l[1], l[2] + l[3] + l[4], l[4], l[2]])
    var out = String()
    for r in typed_intervals(keyed^):
        out += "R " + String(r[0]) + " " + String(r[1]) + " " + String(r[2]) + " " + String(r[3]) + " " + String(r[4]) + " " + String(r[5]) + "\n"
    return out^


def vertex_keys(g: ConeGraph, s1: Int, s2: Int) -> List[String]:
    """Vertex keys at `s`, in `exact_vertex_keys`' format."""
    var out = List[String]()
    for v in g.vertices:
        var key = String(v.top) + "|" + String(v.bottom) + "|"
        for k in range(3):
            key += q_string(qx_at(v.w[k], s2, s1)) + ("," if k < 2 else "")
        out.append(key^)
    return out^


def certify_piece(p: Piece) raises -> ConeGraph:
    """The piece's symbolic graph; raises unless PIP, every vertex hits offset zero,
    every offset is constant, and the graph equals the exact one at a sample member."""
    var g = symbolic_cone_graph(tail_cone(p), p.region())
    if not g.pip:
        raise Error("the piece is not certified PIP: " + g.reason)
    var good = cone_offset_zero_reachable(g)
    for i in range(len(good)):
        if not good[i]:
            raise Error("a symbolic seed-reachable vertex has no offset-zero descendant on " + p.name())
    _ = labels(g)
    var s1 = 0 if p.kind == GAP else p.d0 + 1
    var s2 = 0 if p.kind == DIAGONAL else p.m0 + 2
    var dn = p.member(s1, s2)
    if not same_set(vertex_keys(g, s1, s2), exact_vertex_keys(c_member(dn[0], p.eps, dn[1]))):
        raise Error("cross-check: the symbolic graph differs from the exact graph on " + p.name())
    return g^


def shifts() -> List[Int]:
    """The shifts tried, in order, before a piece is split."""
    return [0, 1, 2, 3, 4, 6, 8]


struct Cover(Copyable, Movable):
    """What `cover` certified: symbolic pieces, exact members, and their label
    sets. With `one_set` (T_C) a second label set raises; without it (T_C2)
    the distinct sets are collected."""
    var rows: String  # the first label set; empty until the first piece or member
    var sets: List[String]  # the distinct label sets, in order of appearance
    var one_set: Bool
    var pieces: List[String]
    var members: Int
    var log: List[String]
    var verbose: Bool

    def __init__(out self, verbose: Bool = False, one_set: Bool = True):
        self.rows = String()
        self.sets = List[String]()
        self.one_set = one_set
        self.pieces = List[String]()
        self.members = 0
        self.log = List[String]()
        self.verbose = verbose

    def note(mut self, line: String):
        self.log.append(line)
        if self.verbose:
            print(line, flush=True)

    def agree(mut self, rows: String, where: String) raises:
        if self.rows.byte_length() == 0:
            self.rows = rows
        elif rows != self.rows and self.one_set:
            raise Error("the label set differs on " + where)
        for s in self.sets:
            if s == rows:
                return
        self.sets.append(rows)


def _try_piece(p: Piece, mut out: Cover) raises -> Bool:
    var g: ConeGraph
    try:
        g = certify_piece(p)
    except e:
        var msg = String(e)
        if not msg.startswith("a sign") and not msg.startswith("a fitted") and not msg.startswith("a run-position"):
            raise e^  # only an undecided sign or fit is a reason to shift; anything else is a refusal
        out.note(p.name() + ": undecided, " + String(msg[byte=0 : min(msg.byte_length(), 120)]))
        return False
    out.agree(rows(g), p.name())
    out.pieces.append(p.name() + ", " + String(g.size()) + " vertices")
    out.note(p.name() + ": certified, " + String(g.size()) + " vertices")
    return True


def _member(eps: Int, d: Int, n: Int, mut out: Cover) raises:
    var block = c_block(d, eps, n)
    if block.startswith("S "):
        raise Error("a member of the tail is screened out: d=" + String(d) + " n=" + String(n))
    out.agree(rows_of(block), "the exact member d=" + String(d) + " n=" + String(n))
    out.members += 1
    out.note("eps=" + String(eps) + " d=" + String(d) + " n=" + String(n) + ": exact, " + String(vertices_of(block)) + " vertices")


def cover(p: Piece, mut out: Cover) raises:
    """Every member of `p` is PIP and every label of its graph hits offset zero;
    the label sets are recorded in `out` (one only, if `out.one_set`).

    A cone is certified at the first shift `k` of `shifts()` on `s1 >= a0 + k`,
    `s2 >= b0 + k`; the strips it leaves (gap lines `s1 = a0 + j`, `s2 >= b0`,
    and diagonals `s2 = b0 + j`, `s1 >= a0 + k`, for `j < k`) are covered
    recursively. A line is certified from its first shift on; the members
    below are decided exactly. No shift certifying raises."""
    for k in shifts():
        var q = Piece(p.eps, p.c, p.d0 + (0 if p.kind == GAP else k), p.m0 + (0 if p.kind == DIAGONAL else k), p.kind, p.frame)
        if not _try_piece(q, out):
            continue
        for j in range(k):
            if p.kind == CONE:
                cover(Piece(p.eps, p.c, p.d0 + j, p.m0, GAP, p.frame), out)
                cover(Piece(p.eps, p.c, p.d0 + k, p.m0 + j, DIAGONAL, p.frame), out)
            else:
                var dn = p.member(p.d0 + j, p.m0) if p.kind == DIAGONAL else p.member(p.d0, p.m0 + j)
                _member(p.eps, dn[0], dn[1], out)
        return
    raise Error("no shift certifies " + p.name())
