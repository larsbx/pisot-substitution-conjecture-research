"""Complete minus residual: initial boundary, two strips, and seed carrier."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract, require_claim
from psc.class_d_minus_boundary_strips import minus_strip
from psc.class_d_minus_complete import minus_residual_region, certify_minus_residual


def main() raises:
    for a in [0,1]:
        var line = minus_strip(a)
        assert_equal(line.run(0,0),6+3*a)
        assert_equal(line.run(1,0),7+3*a)
        assert_equal(line.run(2,0),5+2*a)
    for a in [0,1,2,Int.MAX]:
        assert_equal(minus_residual_region(a,0),0)
    assert_equal(minus_residual_region(0,1),1)
    assert_equal(minus_residual_region(1,Int.MAX),2)
    assert_equal(minus_residual_region(Int.MAX,Int.MAX),3)
    for bad in [-1,2,Int.MAX]:
        var refused = False
        try:
            _ = minus_strip(bad)
        except:
            refused = True
        assert_true(refused)
    var refused = False
    try:
        _ = minus_residual_region(0,-1)
    except:
        refused = True
    assert_true(refused)
    var result = certify_minus_residual()
    assert_equal(result[0],145)
    assert_equal(result[3],145)
    assert_equal(result[4],4)
    require_contract("minus class-D a,b>=0: complete b=0 symbolic tail and finite prefix, both a=0,1 positive-b symbolic line tails with every finite prefix member and exact graph agreement, then a>=2 positive-b all-seed/all-child carrier plus exact rank descent and conditional geometry; no omitted strip or parameter cap; universal #139 and PSC remain open")
    require_claim("MinusClassDBoundaryLine")
    require_claim("MinusClassDBoundaryStrips")
    require_claim("MinusClassDResidualBoundaryHitting")
