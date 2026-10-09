"""Regression tests for psc.param_poly, the algebra shared by the symbolic line
and cone engines.

Every identity is checked through evaluation at a grid of integer parameter
points, so it tests the polynomials, not their representation; the keys are
checked to be canonical, since both engines intern vertices and memoize signs
by them.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from mojo_smoke.claims import require_contract
from psc.param_poly import (
    QX,
    TPoly,
    qx_add,
    qx_affine,
    qx_affine2,
    qx_at,
    qx_const,
    qx_const_term,
    qx_deg,
    qx_is_const,
    qx_key,
    qx_mul,
    qx_neg,
    qx_shift,
    qx_sub,
    tp_at_t,
    tp_const,
    tp_homog_at,
    tp_mod_monic,
    tp_mul,
    tp_norm,
    tp_sub,
    tp_t,
)


def _samples() -> List[QX]:
    """`3 - 2a + b`, `a b - 1`, `(1 + a)^2`, `5`, `0`."""
    var a1 = qx_affine(1, 1)
    return [
        qx_affine2(3, -2, 1),
        qx_sub(qx_mul(qx_affine(0, 1), qx_affine2(0, 0, 1)), qx_const(1)),
        qx_mul(a1, a1),
        qx_const(5),
        QX(),
    ]


def _grid() -> List[Tuple[Int, Int]]:
    var out = List[Tuple[Int, Int]]()
    for a in range(-2, 4):
        for b in range(-1, 3):
            out.append((a, b))
    return out^


def test_ring_operations_commute_with_evaluation() raises:
    var ps = _samples()
    for i in range(len(ps)):
        for j in range(len(ps)):
            for pt in _grid():
                var x = qx_at(ps[i], pt[0], pt[1])
                var y = qx_at(ps[j], pt[0], pt[1])
                assert_true(qx_at(qx_add(ps[i], ps[j]), pt[0], pt[1]).eq(x.add(y)))
                assert_true(qx_at(qx_sub(ps[i], ps[j]), pt[0], pt[1]).eq(x.sub(y)))
                assert_true(qx_at(qx_mul(ps[i], ps[j]), pt[0], pt[1]).eq(x.mul(y)))


def test_affine_and_shift_follow_the_coordinates() raises:
    """`qx_affine2(c0, ca, cb) = c0 + ca a + cb b`, and `qx_shift` translates
    `(a, b)`. The cone engine reads `s1 = b`, `s2 = a` through exactly these."""
    var ps = _samples()
    for pt in _grid():
        var a = pt[0]
        var b = pt[1]
        assert_true(qx_at(qx_affine2(7, -3, 2), a, b).eq(q_int(7 - 3 * a + 2 * b)))
        for i in range(len(ps)):
            assert_true(qx_at(qx_shift(ps[i], 4, -3), a, b).eq(qx_at(ps[i], a + 4, b - 3)))


def test_keys_are_canonical() raises:
    var a = qx_affine(0, 1)
    var b = qx_affine2(0, 0, 1)
    var s = qx_add(a, b)
    var expanded = qx_add(qx_add(qx_mul(a, a), qx_mul(qx_const(2), qx_mul(a, b))), qx_mul(b, b))
    assert_equal(qx_key(qx_mul(s, s)), qx_key(expanded))
    assert_equal(qx_key(qx_sub(expanded, expanded)), qx_key(QX()))
    assert_equal(qx_key(qx_neg(qx_neg(expanded))), qx_key(expanded))


def test_degree_and_constants() raises:
    var ps = _samples()
    assert_equal(qx_deg(ps[0]), 1)
    assert_equal(qx_deg(ps[1]), 2)
    assert_equal(qx_deg(ps[2]), 2)
    assert_equal(qx_deg(ps[3]), 0)
    assert_equal(qx_deg(ps[4]), -1)
    assert_true(qx_const_term(ps[1]).eq(q_int(-1)))
    assert_true(qx_is_const(ps[3]) and qx_is_const(ps[4]))
    assert_false(qx_is_const(ps[0]))


def _cubic() -> TPoly:
    """`t^3 - (a + 1) t^2 - b t - 2`, monic in `t`."""
    return tp_norm([qx_const(-2), qx_affine2(0, 0, -1), qx_affine(-1, -1), qx_const(1)])


def test_reduction_modulo_a_monic_cubic() raises:
    var chi = _cubic()
    var t = tp_t()
    var t5 = tp_mul(tp_mul(tp_mul(t, t), tp_mul(t, t)), t)
    var r = tp_mod_monic(t5, chi)
    assert_true(len(r) <= 3)
    # t^5 - r is a multiple of chi: it reduces to zero.
    assert_equal(len(tp_mod_monic(tp_sub(t5, r), chi)), 0)
    var raised = False
    try:
        _ = tp_mod_monic(t5, tp_norm([qx_const(1), qx_affine(2, 1)]))
    except:
        raised = True
    assert_true(raised)


def test_homogenized_value_is_den_power_times_value() raises:
    """`den^d p(num / den)` at integer points equals the rational evaluation."""
    var p = _cubic()
    var num = qx_affine2(1, 2, 0)  # 1 + 2a
    var den = qx_affine2(1, 0, 1)  # 1 + b
    var h = tp_homog_at(p, num, den, 3)
    for pt in _grid():
        var a = pt[0]
        var b = pt[1]
        if b == -1:
            continue
        var x = Q(Int64(1 + 2 * a), Int64(1 + b))
        var value = qx_at(tp_at_t(p, x), a, b)
        var d3 = q_int((1 + b) * (1 + b) * (1 + b))
        assert_true(qx_at(h, a, b).eq(value.mul(d3)))
    assert_equal(qx_key(tp_homog_at(tp_const(qx_const(4)), num, den, 0)), qx_key(qx_const(4)))


def main() raises:
    test_ring_operations_commute_with_evaluation()
    print("[PASS] test_ring_operations_commute_with_evaluation")
    test_affine_and_shift_follow_the_coordinates()
    print("[PASS] test_affine_and_shift_follow_the_coordinates")
    test_keys_are_canonical()
    print("[PASS] test_keys_are_canonical")
    test_degree_and_constants()
    print("[PASS] test_degree_and_constants")
    test_reduction_modulo_a_monic_cubic()
    print("[PASS] test_reduction_modulo_a_monic_cubic")
    test_homogenized_value_is_den_power_times_value()
    print("[PASS] test_homogenized_value_is_den_power_times_value")
    require_contract("Parameter polynomials (psc.param_poly, shared by the symbolic line and cone engines): sum, difference and product commute with evaluation on an integer grid; qx_affine2 and qx_shift follow the (a, b) coordinates; equal polynomials have equal keys; total degree and constant term; reduction modulo a monic cubic leaves a multiple of it and refuses a non-monic modulus; den^d p(num / den) matches rational evaluation")
