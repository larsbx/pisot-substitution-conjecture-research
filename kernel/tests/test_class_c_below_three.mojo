"""Exact affine sector identities and finite-end parity/domain guards."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from finite_linear_algebra.scalar import q_int
from psc.class_c_below_three import finite_start, finite_stop, coverage_audit, target_line_floor, line_cone, sector_cone
from psc.param_poly import qx_add, qx_affine2, qx_const, qx_key, qx_scale, qx_sub


def main() raises:
    for eps in [1, -1]:
        for a in [8, 16]:
            for b in [8, 16]:
                var cone = sector_cone(eps, a, b)
                var n = cone.run[1].copy()
                var d = qx_sub(cone.run[0], n)
                var u = qx_sub(qx_sub(qx_scale(n, q_int(2)), qx_scale(d, q_int(5))), qx_const(a))
                var v = qx_sub(qx_sub(qx_scale(d, q_int(3)), n), qx_const(b))
                assert_equal(qx_key(u), qx_key(qx_affine2(0, 0, 1)))
                assert_equal(qx_key(v), qx_key(qx_affine2(0, 1, 0)))
                assert_equal(qx_key(cone.run[2]), qx_key(qx_add(qx_sub(n, d), qx_const(eps))))
    assert_equal(target_line_floor(-15, 8), 38)
    assert_equal(target_line_floor(-14, 8), 36)
    assert_equal(target_line_floor(-13, 8), 34)
    assert_equal(target_line_floor(-15, 16), 46)
    assert_equal(target_line_floor(-8, 8), 32)
    # Ceil((5d+8)/2), including odd gap and exact even boundary.
    assert_equal(finite_start(1, 6, 8), 19)
    assert_equal(finite_start(-1, 7, 8), 22)
    assert_equal(finite_stop(1, 7), 25)
    assert_equal(finite_stop(-1, 7), 27)
    assert_true(coverage_audit(1, 8, 16).startswith("COVERAGE"))
    assert_true(coverage_audit(-1, 16, 8).startswith("COVERAGE"))
    var refused = False
    try:
        _ = finite_start(1, 1000000000000000000, 8)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = sector_cone(1, 0, 8)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = line_cone(-1, -16)
    except:
        refused = True
    assert_true(refused)
    require_contract("class C below-three pieces: exact unimodular sector inverse with no missing parity class; integral run lengths; finite-end ceiling/domain bounds and target-line intersection floors; oversized or out-of-budget inputs refuse before arithmetic; graph certificates replay separately")
