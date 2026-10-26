"""Exact coefficient proof of the plus row-12 lattice chamber."""
from std.testing import assert_equal
from mojo_smoke.claims import require_contract
from psc.class_d_plus_row12_chamber import verify_plus_row12_integer_chamber


def main() raises:
    var out = verify_plus_row12_integer_chamber()
    assert_equal(out[0],4)
    assert_equal(out[1],5)
    assert_equal(out[2],7)
    assert_equal(out[3],5)
    assert_equal(out[4],6)
    require_contract("plus class-D row 12: exact threshold squeeze leaves one integer interface b=5a+7, equivalently c=b-1=5a+6; four cross-multiplied quadratic numerators and both denominator bases are coefficient-positive for D=a+2>=2")
