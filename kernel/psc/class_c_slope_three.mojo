"""Coverage plan for a class-C slope-three BH certificate.

The graph certificates are independently replayed pieces, with no imposed
common label set. This module checks their integer cover at a finite grid;
the unbounded coverage proof is in the dated slope-three note.
"""
from psc.class_c_gap_profile import frozen_onset
from psc.param_poly import qx_add, qx_affine2, qx_const, qx_sub
from psc.class_c_lower_strip import make_cone
from psc.class_c_tail_certificate import labels, vertex_keys
from psc.class_c_gap_profile import c_member
from psc.symbolic_cone import ConeGraph, Region, cone_offset_zero_reachable, symbolic_cone_graph
from symbolic_line_certificate import exact_vertex_keys, same_set


comptime BELOW = 0
comptime FINITE = 1
comptime MIDDLE = 2
comptime DIAGONAL = 3
comptime INHERITED_TOP = 4
comptime TAIL = 5
comptime LOWER_LINE = 6
comptime GAP_SPLIT = 24


struct SlopePlan(ImplicitlyCopyable, Copyable, Movable):
    var eps: Int
    var a: Int
    var b: Int
    var middle_a: Int

    def __init__(out self, eps: Int, a: Int) raises:
        if eps != 1 and eps != -1:
            raise Error("slope-three sign must be +-1")
        if a < 1 or a > 16:
            raise Error("slope-three intercept budget: 1<=a<=16")
        self.eps = eps
        self.a = a
        self.b = 16
        self.middle_a = max(a, 8) if eps == -1 else a

    def target(self, d: Int) -> Int:
        return 3 * d + self.a

    def diagonal_floor(self) -> Int:
        return 1 - self.b

    def diagonal_last(self) -> Int:
        return -5 if self.eps == 1 else -1

    def piece(self, d: Int, n: Int) raises -> Int:
        """Finite audit only: bounded inputs prevent machine-Int wraparound.
        The mathematical partition itself is stated without this audit budget."""
        if d < 6 or d > 64 or n < 0 or n > 400:
            raise Error("coverage audit budget: 6<=d<=64, 0<=n<=400")
        if n < self.target(d):
            return BELOW
        if n >= frozen_onset(d, self.eps):
            return TAIL
        if d < GAP_SPLIT:
            return FINITE
        if n <= 4 * d - self.b:
            return LOWER_LINE if n < 3 * d + self.middle_a else MIDDLE
        if n - 4 * d <= self.diagonal_last():
            return DIAGONAL
        return INHERITED_TOP


def coverage_audit(p: SlopePlan) raises -> String:
    var counts = List[Int](length=7, fill=0)
    for d in range(6, 65):
        for n in range(401):
            var k = p.piece(d, n)
            counts[k] += 1
            if k == BELOW:
                if n >= p.target(d):
                    raise Error("coverage lost a target member")
            elif k == FINITE:
                if d >= GAP_SPLIT or n < p.target(d) or n >= frozen_onset(d, p.eps):
                    raise Error("finite end-piece coverage mismatch")
            elif k == MIDDLE:
                var u = n - 3 * d - p.middle_a
                var v = 4 * d - p.b - n
                if u < 0 or v < 0 or d != p.middle_a + p.b + u + v or n != 4 * p.middle_a + 3 * p.b + 4 * u + 3 * v:
                    raise Error("middle-cone inverse mismatch")
            elif k == LOWER_LINE:
                var c = n - 3 * d
                if p.eps != -1 or c < p.a or c >= p.middle_a or n > 4 * d - p.b:
                    raise Error("lower-edge line coverage mismatch")
            elif k == DIAGONAL:
                var c = n - 4 * d
                if d < GAP_SPLIT or c < p.diagonal_floor() or c > p.diagonal_last():
                    raise Error("diagonal coverage mismatch")
            elif k == INHERITED_TOP:
                var c = n - 4 * d
                if d < 6 or c < (-4 if p.eps == 1 else 0) or c > (-1 if p.eps == 1 else 3):
                    raise Error("inherited top coverage mismatch")
            elif k == TAIL:
                if n < frozen_onset(d, p.eps):
                    raise Error("tail coverage mismatch")
    var out = "COVERAGE_AUDIT eps=" + String(p.eps) + " a=" + String(p.a) + " d=6..64 n=0..400"
    for k in range(7):
        out += " kind" + String(k) + "=" + String(counts[k])
    return out^


def refusal_controls() raises -> String:
    """Exact finite sign changes in all five refused candidate cones.
    A changing intermediate comparison refutes that unsplit decision path,
    not BH or even constant labels on the region."""
    from finite_linear_algebra.scalar import q_int
    from psc.real_root_sign import count_real_roots, tarski_query
    var out = String()
    for which in range(5):
        var eps = 1 if which < 2 else -1
        var a = 4 if which == 0 else (8 if which == 1 or which == 3 else 6)
        var b = 10 if eps == 1 else (16 if which == 4 else 4)
        for side in range(2):
            var u = 20 if (which == 2 or which == 4) and side == 1 else 0
            var v = 20 if which != 2 and which != 4 and side == 1 else 0
            var d = a + b + u + v
            var n = 4 * a + 3 * b + 4 * u + 3 * v
            var c1 = n - 3 * d + 3 * eps + 2
            var c2 = -(n - d + eps + 3)
            var poly = List([q_int(-2 * eps), q_int(c1), q_int(c2), q_int(1)])
            var g0: Int
            var g1: Int
            var g2: Int
            if eps == 1:
                g0 = (-110 if a == 4 else -150) - 8 * v - 10 * u
                g1 = (185 if a == 4 else 245) + 14 * v + 15 * u
                g2 = -5 - v
            elif a == 6:
                g0 = (88 if b == 16 else 40) + 4 * v + 6 * u
                g1 = (-44 if b == 16 else -20) - 2 * v - 5 * u
                g2 = u
            else:
                g0 = 114 + 8 * v + 10 * u
                g1 = -179 - 14 * v - 15 * u
                g2 = 5 + v
            var gp = List([q_int(g0), q_int(g1), q_int(g2)])
            var high = 1 + max(2, max(abs(c1), abs(c2)))
            if count_real_roots(poly, q_int(2), q_int(high)) != 1:
                raise Error("refusal control did not isolate one Perron root")
            var sign = tarski_query(poly, gp, q_int(2), q_int(high))
            var expected = (1 if side == 0 else -1) if eps == 1 else (-1 if side == 0 else 1)
            if sign != expected:
                raise Error("refusal polynomial sign-change control failed")
            out += "SIGN_CONTROL eps=" + String(eps) + " a=" + String(a) + " b=" + String(b) + " u=" + String(u) + " v=" + String(v) + " d=" + String(d) + " n=" + String(n) + " g=" + String(g0) + "," + String(g1) + "," + String(g2) + " sign=" + String(sign) + "\n"
    return out^


def lower_line(c: Int) raises -> ConeGraph:
    """Minus n=3d+c, every d>=24; all hypotheses certified from scratch."""
    if c < 6 or c > 7:
        raise Error("lower-line budget: minus c=6 or 7 only")
    var d = qx_affine2(0, 0, 1)
    var n = qx_affine2(c, 0, 3)
    var cone = make_cone([qx_add(n, d), n.copy(), qx_add(qx_sub(n, d), qx_const(-1))])
    var g = symbolic_cone_graph(cone^, Region(GAP_SPLIT, 0))
    if not g.pip:
        raise Error("lower-edge line not certified PIP: " + g.reason)
    for good in cone_offset_zero_reachable(g):
        if not good:
            raise Error("lower-edge line has a vertex without offset-zero descendant")
    _ = labels(g)
    if not same_set(vertex_keys(g, 25, 0), exact_vertex_keys(c_member(25, -1, 75 + c))):
        raise Error("lower-edge line exact-member label mismatch")
    return g^
