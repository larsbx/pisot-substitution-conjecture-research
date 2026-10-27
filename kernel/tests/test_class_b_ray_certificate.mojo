"""Boundary hitting on class B's top-layer residue rays: certificate, replay and refusals."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_b_ray_line import BRay, check_line_identity, check_bound
from psc.class_b_ray_certificate import certify_ray_rows, replay_finite
from psc.class_b_ray_tables import ray_specs, ray_rows, ray_potentials


def refuses(ray: BRay, q0: Int, rows: List[List[Int]], pot: List[List[Int]]) -> Bool:
    try:
        _ = certify_ray_rows(ray, q0, rows, pot)
        return False
    except:
        return True


def without(rows: List[List[Int]], drop: Int) -> List[List[Int]]:
    var out = List[List[Int]]()
    for i in range(len(rows)):
        if i != drop:
            out.append(rows[i].copy())
    return out^


def main() raises:
    # Ray parameters: eps = +-1, 0 <= r < g; a member off its ray or outside the top layer refuses.
    var refused = False
    try:
        check_line_identity(BRay(0, 1, 0))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = BRay(1, 3, 1).l_of(15)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        BRay(1, 5, 0).check_domain(5)    # p = 22 is not above 2q+13 = 23
    except:
        refused = True
    assert_true(refused)
    # The Perron lower bound is checked, not assumed: beta_low = q0+4 lies below beta_9.
    check_bound(BRay(1, 1, 0), 9)

    # Every tabulated ray: closure and descent for every q >= q0.
    var specs = ray_specs()
    assert_equal(len(specs), 83)
    for i in range(len(specs)):
        var ray = BRay(specs[i][0], specs[i][1], specs[i][2])
        var stats = certify_ray_rows(ray, specs[i][3], ray_rows(i), ray_potentials(i))
        assert_equal(stats[0], specs[i][5])
        assert_equal(stats[2], 9)     # real swap seeds
        assert_equal(stats[3], 3)     # non-strict seed candidates
        assert_equal(stats[11], 8)    # offset-zero target pieces

    # Differential replay: native complete graph = carrier, and the potential
    # strictly descends along a native edge, at the floor of three rays.
    var ray0 = BRay(1, 1, 0)
    assert_equal(replay_finite(ray0, 9, ray_rows(0), ray_potentials(0)), 2765)
    assert_true(replay_finite(BRay(1, 3, 1), 16, ray_rows(4), ray_potentials(4)) > 0)
    assert_true(replay_finite(BRay(-1, 2, 1), 17, ray_rows(17), ray_potentials(17)) > 0)

    # Negative controls on plus g=1.
    var rows = ray_rows(0)
    var pot = ray_potentials(0)
    # (1) a removed carrier row escapes;
    assert_true(refuses(ray0, 9, without(rows, 68), pot))
    assert_true(refuses(ray0, 9, without(rows, 0), pot))
    # (2) a lowered positive potential constant has no covering descent;
    for i in range(len(pot)):
        if pot[i][5] > 0:
            var low = pot.copy()
            low[i][5] -= 1
            assert_true(refuses(ray0, 9, rows, low))
            break
    # (3) the all-zero potential refuses, and so does a missing potential row;
    var zero = pot.copy()
    for i in range(len(zero)):
        zero[i][5] = 0
    assert_true(refuses(ray0, 9, rows, zero))
    assert_true(refuses(ray0, 9, rows, without(pot, 0)))
    # (4) another ray's carrier does not fit;
    assert_true(refuses(ray0, 9, ray_rows(15), ray_potentials(15)))
    assert_true(refuses(BRay(-1, 1, 0), 15, rows, pot))
    # (5) below its floor the certificate refuses rather than concluding.
    assert_true(refuses(ray0, 8, rows, pot))
    assert_true(refuses(BRay(-1, 3, 1), 19, ray_rows(19), ray_potentials(19)))

    require_contract("class-B top-layer residue rays q = g l + r (plus g<=5, minus g<=3): uniform forward closure of l-affine typed carriers in (u,v,k) coordinates and strict descent of X = |k| + b by exact Sturm signs on beta >= q0+3+eps, per tabulated ray from its floor; native graph = carrier and native descent at three floors; removed row, lowered/zero/missing potential, another ray's carrier and sub-floor certificates refuse; other gaps, universal BH, G1 and PSC open")
