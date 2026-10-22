"""Conditional cycle reduction for the minus positive-b residual."""
from std.testing import assert_equal
from mojo_smoke.claims import require_contract, require_claim
from psc.class_d_minus_cycle_superset import verify_minus_cycle_superset
from psc.class_d_minus_exceptional_cycles import verify_minus_exceptional_productivity


def main() raises:
    var sup = verify_minus_cycle_superset()
    assert_equal(sup[0],1971)
    assert_equal(sup[1],145)
    assert_equal(sup[2],131)
    assert_equal(sup[3],2)
    assert_equal(sup[4],8)
    assert_equal(sup[5],4)

    var exc = verify_minus_exceptional_productivity()
    assert_equal(exc[0],4)
    assert_equal(exc[1],8)
    assert_equal(exc[2],4)
    assert_equal(exc[3],2)

    require_claim("MinusClassDPositiveBBoundaryHitting")
    require_contract("minus class-D positive-b conditional cycle reduction: assuming every genuine cyclic overlap has |1^T w|<=1, the exact guarded 1971-state superset has 145 recurrent vertices classified as 131 sealed-carrier states, two offset-zero states, eight boundary-only impossible states, and four explicitly productive exceptions with verified exits into carrier rank<=2; the cycle-sum premise is discharged separately by the uniform seed-carrier certificate")
