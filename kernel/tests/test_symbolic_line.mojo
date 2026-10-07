"""Exact regressions for the symbolic line overlap graph (psc.symbolic_line) and
the class B line certificate (symbolic_line_certificate).

docs/p1b-symbolic-line-2026-10-07.md. The parametric sign reader is checked
against the same query at concrete `q`, the pseudo-remainder against its
sign-preservation contract, the PIP certificate on a member and a non-member
line, and the certificate itself is pinned.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from mojo_smoke.claims import require_contract
from psc.symbolic_line import (
    Eventual,
    Line,
    LineField,
    certify_line,
    qx_affine,
    qx_const,
    tp_add,
    tp_at_q,
    tp_const,
    tp_prem,
    tp_scale,
    tp_sub,
    tp_t,
)
from symbolic_line_certificate import class_b_line, certify_class_b_line


def test_eventual_sign_records_the_largest_root() raises:
    var ev = Eventual()
    # (q - 10)(q - 3) = q^2 - 13 q + 30
    var s = ev.sign([q_int(30), q_int(-13), q_int(1)])
    assert_equal(s, 1)
    assert_true(q_int(10).le(ev.threshold))
    assert_equal(ev.sign(qx_const(-4)), -1)
    assert_equal(ev.sign(List[Q]()), 0)


def test_parametric_signs_agree_with_concrete_signs() raises:
    """beta = q + 4 - 3/q + ...: below q + 4, above q + 3, for every large q;
    the same queries at q = 60 with constant coefficients agree."""
    var line = class_b_line()
    var ev = Eventual()
    var cert = certify_line(line, ev)
    assert_true(cert.holds)
    var below = tp_sub(tp_t(), tp_const(qx_affine(4, 1)))  # t - (q + 4)
    var above = tp_sub(tp_t(), tp_const(qx_affine(3, 1)))  # t - (q + 3)
    assert_equal(line.field.sign_at_beta(below, ev), -1)
    assert_equal(line.field.sign_at_beta(above, ev), 1)
    var at60 = LineField(tp_at_q(line.field.chi, 60))
    var ev60 = Eventual()
    assert_equal(at60.sign_at_beta(tp_at_q(below, 60), ev60), -1)
    assert_equal(at60.sign_at_beta(tp_at_q(above, 60), ev60), 1)
    # ell_x / ell_y -> 2 from below: 2 ell_y - ell_x > 0 with the tile lengths oriented positive
    var gap = tp_scale(tp_sub(tp_scale(line.ell[2], qx_const(2)), line.ell[0]), qx_const(cert.ell_sign))
    assert_equal(line.field.sign_at_beta(gap, ev), 1)
    assert_equal(at60.sign_at_beta(tp_at_q(gap, 60), ev60), 1)


def test_pseudo_remainder_keeps_the_sign_at_beta() raises:
    var line = class_b_line()
    var ev = Eventual()
    _ = certify_line(line, ev)
    var g = tp_add(tp_scale(tp_t(), qx_affine(-1, 2)), tp_const(qx_affine(5, -3)))
    var g3 = tp_add(g, tp_scale(line.field.chi, qx_const(7)))  # same value at beta
    var r = tp_prem(g3, line.field.chi)
    assert_equal(line.field.sign_at_beta(r, ev), line.field.sign_at_beta(g, ev))


def test_a_line_with_determinant_zero_is_not_certified() raises:
    """runs q, q, q with endings (x, x, c, x): det M = 2 (r - q) = 0."""
    var line = Line([0, 1, 1], [0, 0, 0], [qx_affine(0, 1), qx_affine(0, 1), qx_affine(0, 1)], 2)
    var ev = Eventual()
    assert_false(certify_line(line, ev).holds)


def test_the_class_b_line_certificate() raises:
    var v = certify_class_b_line()
    assert_equal(v.q0, 52)
    assert_equal(v.symbolic_vertices, 119)
    assert_equal(v.finite_members, 52)
    assert_equal(v.finite_non_pip, 0)


def main() raises:
    test_eventual_sign_records_the_largest_root()
    print("[PASS] test_eventual_sign_records_the_largest_root")
    test_parametric_signs_agree_with_concrete_signs()
    print("[PASS] test_parametric_signs_agree_with_concrete_signs")
    test_pseudo_remainder_keeps_the_sign_at_beta()
    print("[PASS] test_pseudo_remainder_keeps_the_sign_at_beta")
    test_a_line_with_determinant_zero_is_not_certified()
    print("[PASS] test_a_line_with_determinant_zero_is_not_certified")
    test_the_class_b_line_certificate()
    print("[PASS] test_the_class_b_line_certificate")
    require_contract("Theorem L certificate (class B line sigma_q: x -> x y^(2q+2) x, c -> c y^q x, y -> c y^(q+1) x): the symbolic swap-seed overlap graph, decided by parametric Sturm-Tarski queries over Q[q] with certified threshold, has 119 vertices for every q >= 52, all with an offset-zero descendant, and the line is certified PIP there; every q in 0..51 is PIP and its exact seed-reachable graph (screened kernel) has every vertex hitting; at q = 52 and 57 the symbolic graph with q substituted equals the exact graph; parametric signs agree with concrete signs at q = 60; pseudo-remainders keep the sign at beta; a det-0 line is refused")
