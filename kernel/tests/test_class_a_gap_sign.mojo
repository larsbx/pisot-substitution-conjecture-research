"""Soundness controls and independent-conversion fixtures for gap sign step (b)."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from psc.exact import q_string
from psc.param_poly import QX, qx_const, qx_affine2
from psc.class_a_gap_sign import bernstein_box, certify_gap_margin


def poly(rows: QX) -> QX:
    return rows.copy()


def refused(p: QX, H: Q = Q.one(), U: Q = Q.one(), depth: Int = 8, cells: Int = 1023) raises:
    var failed = False
    try:
        _ = certify_gap_margin(p, H, U, depth, cells)
    except:
        failed = True
    assert_true(failed)


def main() raises:
    # Strictly positive but has negative root-box Bernstein coefficients.
    var bowl = poly([[Q(9, 16), q_int(-1), Q.one()], [q_int(-1)], [Q.one()]])
    var c = certify_gap_margin(bowl, Q.one(), Q.one())
    assert_equal(c.leaves, 4)
    assert_equal(c.visited, 7)
    assert_equal(c.depth, 2)
    refused(bowl, Q.one(), Q.one(), 1, 1023)
    refused(bowl, Q.one(), Q.one(), 8, 2)
    refused(qx_const(1), Q.one(), Q.one(), -1)
    refused(qx_const(1), Q.one(), Q.one(), 13)
    refused(qx_const(1), Q.one(), Q.one(), 8, 0)
    refused(qx_const(1), Q.one(), Q.one(), 8, 8192)
    refused(QX())
    refused(qx_const(-1))
    refused(poly([[Q(1, 0)]]))
    refused(qx_const(1), Q(1, 0), Q.one())
    refused(qx_const(1), Q.zero(), Q.one())
    refused(qx_const(1), Q.one(), q_int(-1))
    refused(poly([[Q.one(), q_int(-2)]]))
    refused(poly([[Q(1, 4), q_int(-1), Q.one()]]))  # interior zero
    refused(poly([[Q(3, 16), q_int(-1), Q.one()]]))  # hidden negative interval
    refused(poly([[Q.zero(), Q.one(), q_int(-1)]]))  # h*(1-h), retained upper zero
    refused(qx_affine2(0, 1, 1))  # positive on open axes, conservative refusal
    var too_wide = List[Q]()
    for _ in range(10):
        too_wide.append(Q.one())
    refused(poly([too_wide^]))
    var too_tall = QX()
    for _ in range(10):
        too_tall.append([Q.one()])
    refused(too_tall)
    var axis = poly([List[Q](), [Q.zero(), Q.zero(), Q.one()]])  # h^2*u
    c = certify_gap_margin(axis, Q(1, 25), Q(1, 5))
    assert_equal(c.h_factor, 2)
    assert_equal(c.u_factor, 1)
    assert_equal(c.leaves, 1)
    var padded = poly([[Q.one(), Q.zero()], [Q.zero()]])
    c = certify_gap_margin(padded, Q.one(), Q.one())
    assert_equal(c.leaves, 1)
    # Actual existing PSC elimination and tile-length margins on the proposed box.
    for eps in [1, -1]:
        var R = poly([[Q.one(), q_int(-eps), q_int(eps - 1)], [Q.zero(), q_int(-1), q_int(-1)]])
        c = certify_gap_margin(R, Q(1, 25), Q(1, 5))
        assert_equal(c.leaves, 1)
        var lengths = List[QX]()
        lengths.append([[Q.one(), q_int(1 - eps)], [Q.one(), Q.one()]])
        lengths.append([[Q.one(), q_int(1 - eps)]])
        lengths.append([[Q.one(), Q.one()]])
        for ell in lengths:
            c = certify_gap_margin(ell, Q(1, 25), Q(1, 5))
            assert_equal(c.leaves, 1)
        print("GAP_SIGN_PSC eps=", eps, "margins=4 H=1/25 U=1/5 closed_residual=true closure_proved=false")
    # Independent oracle checks every accepted bilinear against exact corner logic.
    for a in range(-1, 2):
        for b in range(-1, 2):
            for c0 in range(-1, 2):
                for d in range(-1, 2):
                    var accepted = False
                    try:
                        _ = certify_gap_margin([[q_int(a), q_int(b)], [q_int(c0), q_int(d)]], Q.one(), Q.one(), 2, 7)
                        accepted = True
                    except:
                        pass
                    print("GAP_SIGN_BILINEAR", a, b, c0, d, Int(accepted))
    # Nonzero coefficients ensure that dimensions do not normalize away.
    for m in range(5):
        for n in range(5):
            var p = QX()
            var seed = 5 * m + n
            for j in range(n + 1):
                var row = List[Q]()
                for i in range(m + 1):
                    var coefficient = 1 + (3 * i + 5 * j + seed) % 7
                    if (i + j) % 2 == 1:
                        coefficient = -coefficient
                    row.append(q_int(coefficient))
                p.append(row^)
            var b = bernstein_box(p, Q(2, 7), Q(3, 5))
            assert_equal(len(b), n + 1)
            assert_equal(len(b[0]), m + 1)
            for j in range(n + 1):
                for i in range(m + 1):
                    print("GAP_SIGN_COEFF", m, n, j, i, q_string(b[j][i]))
    require_contract("class-A gap sign step (b): exact tensor Bernstein conversion and bounded closed-box subdivision; strict upper boundaries, positive-axis factors, hidden zeros/negatives, rejected rationals, degree/depth/cell refusals; actual PSC margin calibrations do not certify graph closure or universal boundary hitting")
