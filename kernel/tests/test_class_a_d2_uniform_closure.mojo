"""Exact all-n d2 forward closure: four residue rays, finite prefix, refusals."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_d2_parity_carrier import inferred_template
from psc.class_a_d2_uniform_closure import (
    certify_d2_all_n_closure,certify_residue,_nonnegative,_a,
    _ceil_aff_half,_floor_aff_half,
)


def main() raises:
    assert_equal(certify_d2_all_n_closure(),List[Int]([2483,2363,2483,2363]))
    var even=inferred_template(8,12)
    var odd=inferred_template(9,13)
    assert_equal(certify_residue(even,0),List[Int]([3005,2483,1249,1234,1710]))
    assert_equal(certify_residue(odd,1),List[Int]([2845,2363,1189,1174,1602]))
    assert_equal(certify_residue(even,2),List[Int]([3005,2483,1249,1234,1710]))
    assert_equal(certify_residue(odd,3),List[Int]([2845,2363,1189,1174,1602]))
    assert_equal(_ceil_aff_half(_a(-4,-1)),List[Int]([-2,0]))
    assert_equal(_floor_aff_half(_a(4,-1)),List[Int]([2,-1]))
    assert_true(_nonnegative([0,0,0,0],13)) # equality excludes strict overlap
    assert_true(_nonnegative([0,1,0,0],13))
    assert_true(not _nonnegative([0,-1,0,0],13))
    # Remove one endpoint member. At least one actual positive-interior
    # occurrence must now escape: the geometry cannot certify that gap.
    var damaged=even.copy()
    var first=damaged[0].copy()
    first[7]-=1
    damaged[0]=first.copy()
    var refused=False
    try:
        _=certify_residue(damaged,0)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=certify_residue(even,4)
    except:
        refused=True
    assert_true(refused)
    # The child-y window derivation assumes a small coordinate sum.
    var wrong=even.copy()
    var item=wrong[0].copy()
    item[2]=2
    wrong[0]=item.copy()
    refused=False
    try:
        _=certify_residue(wrong,0)
    except:
        refused=True
    assert_true(refused)
    require_contract("class-A d2 every n>=4 parity carrier forward-closed: n4..11 exact finite bases, four n mod4 all-n affine transfer partitions, 6624 endpoint-window checks and 9692 strict-geometry-excluded gaps, exact ceil/floor integer run indices, corrupted row, source-sum and crossing-order refusals; no universal d2 hitting or #139 promotion")
