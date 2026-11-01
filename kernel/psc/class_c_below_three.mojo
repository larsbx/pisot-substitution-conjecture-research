"""Class-C sector/line certificates below slope three; all labels are outputs."""
from psc.param_poly import QX, qx_add, qx_affine2, qx_const, qx_sub
from psc.class_c_lower_strip import check_sign, make_cone
from psc.class_c_tail_certificate import labels, vertex_keys
from psc.class_c_gap_profile import c_member
from psc.symbolic_cone import Cone, ConeGraph, Region, cone_offset_zero_reachable, symbolic_cone_graph
from symbolic_line_certificate import exact_vertex_keys, same_set

comptime LINE_FLOOR = 32


def sector_cone(eps: Int, a: Int, b: Int) raises -> Cone:
    """u=2n-5d-a, v=3d-n-b; d=a+2b+u+2v,n=3a+5b+3u+5v."""
    check_sign(eps)
    if (a != 8 and a != 16) or (b != 8 and b != 16):
        raise Error("sector proposal budget: a,b in {8,16}")
    var d = qx_affine2(a + 2 * b, 2, 1)
    var n = qx_affine2(3 * a + 5 * b, 5, 3)
    return make_cone([qx_add(n, d), n.copy(), qx_add(qx_sub(n, d), qx_const(eps))])


def line_cone(eps: Int, c: Int) raises -> Cone:
    check_sign(eps)
    if c < -15 or c > (3 if eps == 1 else 5):
        raise Error("line budget: -15<=c<=3 plus / 5 minus")
    var d = qx_affine2(0, 0, 1)
    var n = qx_affine2(c, 0, 3)
    return make_cone([qx_add(n, d), n.copy(), qx_add(qx_sub(n, d), qx_const(eps))])


def certified(var cone: Cone, var region: Region, eps: Int, s1: Int, s2: Int, d: Int, n: Int) raises -> ConeGraph:
    var g = symbolic_cone_graph(cone^, region^)
    if not g.pip:
        raise Error("below-three piece not certified PIP: " + g.reason)
    for good in cone_offset_zero_reachable(g):
        if not good:
            raise Error("below-three piece has a vertex without offset-zero descendant")
    _ = labels(g)  # extra export restriction, not a premise of closure or hitting
    if not same_set(vertex_keys(g, s1, s2), exact_vertex_keys(c_member(d, eps, n))):
        raise Error("below-three exact-member label cross-check failed")
    return g^


def certify_sector(eps: Int, a: Int, b: Int) raises -> ConeGraph:
    # At (u,v)=(1,2), every proposal is within d<=64,n<=400.
    return certified(sector_cone(eps, a, b), Region(0, 0), eps, 1, 2, a + 2 * b + 5, 3 * a + 5 * b + 13)


def certify_line(eps: Int, c: Int, d0: Int = LINE_FLOOR) raises -> ConeGraph:
    if d0 < LINE_FLOOR or d0 > 48:
        raise Error("line-floor replay budget: 32<=d0<=48")
    return certified(line_cone(eps, c), Region(d0, 0), eps, d0 + 1, 0, d0 + 1, 3 * (d0 + 1) + c)


def target_line_floor(c: Int, a: Int) raises -> Int:
    if c < -15 or c > 5 or (a != 8 and a != 16):
        raise Error("target-line budget: c=-15..5, a in {8,16}")
    return max(LINE_FLOOR, a - 2 * c)


def finite_start(eps: Int, d: Int, a: Int) raises -> Int:
    check_sign(eps)
    if d < 6 or d >= LINE_FLOOR or (a != 8 and a != 16):
        raise Error("finite-end budget: d=6..31, a in {8,16}")
    var domain = 2 * d + (-5 if eps == 1 else 1)
    return max(domain, (5 * d + a + 1) // 2)


def finite_stop(eps: Int, d: Int) raises -> Int:
    check_sign(eps)
    if d < 6 or d >= LINE_FLOOR:
        raise Error("finite-end gap budget: d=6..31")
    return 3 * d + (4 if eps == 1 else 6)


def coverage_audit(eps: Int, a: Int, b: Int) raises -> String:
    """Finite endpoint/inverse audit, not a proof outside its bounded grid."""
    check_sign(eps)
    if (a != 8 and a != 16) or (b != 8 and b != 16):
        raise Error("coverage proposal budget: a,b in {8,16}")
    var counts = List[Int](length=5, fill=0)
    for d in range(6, 65):
        for n in range(401):
            if 2 * n < 5 * d + a:
                counts[0] += 1
            elif n >= 3 * d + (4 if eps == 1 else 6):
                counts[4] += 1
            elif d < LINE_FLOOR:
                if n < finite_start(eps, d, a) or n >= finite_stop(eps, d):
                    raise Error("finite-end coverage mismatch")
                counts[1] += 1
            elif n <= 3 * d - b:
                var u = 2 * n - 5 * d - a
                var v = 3 * d - n - b
                if u < 0 or v < 0 or d != a + 2 * b + u + 2 * v or n != 3 * a + 5 * b + 3 * u + 5 * v:
                    raise Error("sector inverse coverage mismatch")
                counts[2] += 1
            else:
                var c = n - 3 * d
                if c < -15 or c > (3 if eps == 1 else 5) or d < target_line_floor(c, a):
                    raise Error("bridging-line coverage mismatch")
                counts[3] += 1
    var out = "COVERAGE eps=" + String(eps) + " a=" + String(a) + " b=" + String(b) + " d=6..64 n=0..400"
    for k in range(5):
        out += " kind" + String(k) + "=" + String(counts[k])
    return out^
