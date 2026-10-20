"""Lattice calibration for the plus positive-b chamber decomposition."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from class_d_plus_positive_b_chambers import classify_plus_chamber, _low_wedge, _high_wedge, _interface_line
from a1_normal_form_census import CLASS_D, class_member


def _expected(a: Int, c: Int) raises -> List[List[Int]]:
    # c=b-1: plus residual p=4+3a+c, q=3+3a+c, r=1+2a+c.
    return class_member(CLASS_D,4+3*a+c,3+3*a+c,1+2*a+c)


def main() raises:
    var low = 0
    var line = 0
    var high = 0
    for a in range(41):
        for c in range(241):
            var cls = classify_plus_chamber(a,c)
            var got = List[List[Int]]()
            if cls[0] == 0:
                low += 1
                got = _low_wedge(cls[1]).member(cls[2],cls[3])
            elif cls[0] == 1:
                line += 1
                got = _interface_line(cls[1]).member(cls[2])
            elif cls[0] == 2:
                high += 1
                got = _high_wedge().member(cls[2],cls[3])
            else:
                raise Error("unknown plus chamber kind")
            assert_equal(got,_expected(a,c))
    assert_true(low > 0 and line > 0 and high > 0)
    require_contract("plus class-D positive-b chamber partition: c<=5a is covered by five unimodular wedges, c=5a+j for j=1..6 by six exact lines, and c>=5a+7 by one unimodular high wedge; sampled lattice reconstruction agrees exactly with the residual substitution formulas")
