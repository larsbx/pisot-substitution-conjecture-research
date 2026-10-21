"""Polynomial identities, fixed-cycle agreement, and malformed closure refusal."""
from std.testing import assert_true
from finite_linear_algebra.scalar import q_int
from mojo_smoke.claims import require_contract, require_claim
from psc.param_poly import qx_add, qx_const, qx_at
from psc.class_d_minus_cycle_family import (
    six_edge_family, six_edge_family_forms, verify_six_edge_family,
)
from psc.class_d_minus_shared_cycles import cycle_forms, negative_cycle, negative_segments


def main() raises:
    verify_six_edge_family()
    var rows = six_edge_family()
    var forms = six_edge_family_forms(rows)
    var golden = negative_cycle()
    var guards = cycle_forms(golden,negative_segments())
    for i in range(6):
        assert_true(qx_at(rows[i][0],2).eq(q_int(golden[i].x)))
        assert_true(qx_at(rows[i][1],2).eq(q_int(golden[i].c)))
        assert_true(qx_at(rows[i][2],2).eq(q_int(golden[i].y)))
    for i in range(12):
        for d in range(3):
            assert_true(qx_at(forms[i][d],2).eq(q_int(guards[i][d])))
    # Damage the source of the closing edge. It must refuse before certifying.
    rows[5][2] = qx_add(rows[5][2],qx_const(1))
    var refused = False
    try:
        _ = six_edge_family_forms(rows)
    except:
        refused = True
    assert_true(refused)
    require_contract("minus six-edge family: symbolic closure and occurrence guards for all integer k>=2; two nonnegative unit multipliers cancel k and v to -7-u; no k cap and no claim of coverage of every higher-sum cycle")
    require_claim("MinusSixEdgeFamilyExclusion")
