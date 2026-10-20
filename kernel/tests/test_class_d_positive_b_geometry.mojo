"""Conditional geometry for every #287 minus positive-b descent."""
from std.testing import assert_equal
from mojo_smoke.claims import require_contract
from psc.class_d_positive_b_geometry import verify_minus_positive_b_conditional_geometry


def main() raises:
    var out = verify_minus_positive_b_conditional_geometry()
    assert_equal(out[0],145)
    assert_equal(out[1],6)
    assert_equal(out[2],141)
    assert_equal(out[3],282)
    assert_equal(out[4],1)
    assert_equal(out[5],10)
    require_contract("minus class-D positive-b conditional geometry: on 2<d<3 and 0<1/beta<1/10, realness of every sealed source implies both realness margins of its #287 selected lower-rank target exceed 1/10; 141 source/branch cases and 282 checked Farkas implications; carrier closure remains separate")
