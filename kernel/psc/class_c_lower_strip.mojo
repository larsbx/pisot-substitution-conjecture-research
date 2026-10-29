"""Lower class-C certificates; no PIP or fixed-label premise. See the dated note."""
from psc.param_poly import QX, qx_add, qx_affine2, qx_const, qx_key, qx_scale, qx_sub, tp_homog_at
from finite_linear_algebra.scalar import q_int
from psc.symbolic_cone import Bracket, Cone, ConeGraph, Frac2, Region, cone_offset_zero_reachable, r2_add, r2_const, r2_div, r2_sub, symbolic_cone_graph
from psc.class_c_tail_certificate import labels, vertex_keys
from psc.class_c_gap_profile import c_member
from symbolic_line_certificate import exact_vertex_keys, same_set


def check_sign(eps: Int) raises:
    if eps != 1 and eps != -1:
        raise Error("class-C sign must be +-1")


def make_cone(runs: List[QX]) raises -> Cone:
    """T_C fixed-point brackets, proposed only; each use certifies them afresh."""
    var xs = List[Frac2]()
    xs.append(r2_const(qx_add(runs[2], qx_const(2))))
    for _ in range(3):
        ref x = xs[len(xs) - 1]
        var inner = r2_add(r2_const(runs[1]), r2_div(r2_const(runs[0]), r2_sub(x, r2_const(qx_const(2)))))
        xs.append(r2_add(r2_const(runs[2]), r2_div(r2_add(inner, inner), r2_sub(x, r2_const(qx_const(1))))))
    var brs = List[Bracket]()
    brs.append(Bracket(xs[0].copy(), xs[1].copy()))
    brs.append(Bracket(xs[2].copy(), xs[1].copy()))
    brs.append(Bracket(xs[2].copy(), xs[3].copy()))
    return Cone([0, 1, 1], [0, 0, 1], runs.copy(), 2, brs^)


def middle_cone(eps: Int, a: Int, b: Int) raises -> Cone:
    """Exactly 3d+a<=n<=4d-b, d=a+b+u+v, n=4a+3b+4u+3v."""
    check_sign(eps)
    if a < 1 or b < 1 or a > 24 or b > 24:
        raise Error("middle-cone budget: 1<=a,b<=24")
    var d = qx_affine2(a + b, 1, 1)
    var n = qx_affine2(4 * a + 3 * b, 3, 4)
    return make_cone([qx_add(n, d), n.copy(), qx_add(qx_sub(n, d), qx_const(eps))])


def certify_middle(eps: Int, a: Int, b: Int) raises -> ConeGraph:
    var g = symbolic_cone_graph(middle_cone(eps, a, b), Region(0, 0))
    if not g.pip:
        raise Error("middle cone not certified PIP: " + g.reason)
    for good in cone_offset_zero_reachable(g):
        if not good:
            raise Error("middle cone has a vertex without offset-zero descendant")
    _ = labels(g)  # extra export restriction, checked after closure/hitting
    # Cross-check at u=1,v=2, inside c_member's finite replay budget.
    var d = a + b + 3
    var n = 4 * a + 3 * b + 10
    if not same_set(vertex_keys(g, 1, 2), exact_vertex_keys(c_member(d, eps, n))):
        raise Error("middle cone exact-member label cross-check failed")
    return g^


def domain_identities(eps: Int) raises -> String:
    """Polynomial premises of the hand PIP proof; d=6+u,n=2d+c+v,u,v>=0.
    This certifies identities and signs, not a second root-screen algorithm."""
    check_sign(eps)
    var c = -5 if eps == 1 else 1
    var d = qx_affine2(6, 0, 1)
    var n = qx_affine2(12 + c, 1, 2)
    var cone = make_cone([qx_add(n, d), n.copy(), qx_add(qx_sub(n, d), qx_const(eps))])
    var expected = List[QX]()
    expected.append(qx_scale(d, q_int(-2)))
    expected.append(qx_scale(qx_add(qx_sub(n, qx_scale(d, q_int(2))), qx_const(3 * eps + 3)), q_int(-2)))
    expected.append(qx_scale(qx_add(n, d), q_int(-2)))
    expected.append(qx_add(qx_sub(qx_scale(d, q_int(10)), qx_scale(n, q_int(6))), qx_const(-12 * eps - 24)))
    var at = List[Int]([1, -1, 2, -2])
    var region = Region(0, 0)
    var out = "DOMAIN eps=" + String(eps) + " d>=6 n>=2d" + ("-5" if eps == 1 else "+1") + "\n"
    if qx_key(cone.chi[0]) != qx_key(qx_const(-2 * eps)):
        raise Error("domain determinant identity failed")
    for i in range(4):
        var actual = tp_homog_at(cone.chi, qx_const(at[i]), qx_const(1), 3)
        if qx_key(actual) != qx_key(expected[i]) or region.sign(actual) != -1:
            raise Error("domain identity/sign failed")
        out += "chi(" + String(at[i]) + ")=" + qx_key(actual) + " <0\n"
    return out^


def boundary_identities(eps: Int) raises:
    """One below the start has root -1; two below has chi(-1)=2."""
    check_sign(eps)
    var d = qx_affine2(6, 0, 1)
    for delta in [1, 2]:
        var n = qx_add(qx_scale(d, q_int(2)), qx_const((-5 if eps == 1 else 1) - delta))
        var cone = make_cone([qx_add(n, d), n.copy(), qx_add(qx_sub(n, d), qx_const(eps))])
        var at_minus_one = tp_homog_at(cone.chi, qx_const(-1), qx_const(1), 3)
        if qx_key(at_minus_one) != qx_key(qx_const(2 * (delta - 1))):
            raise Error("Pisot boundary negative control failed")
