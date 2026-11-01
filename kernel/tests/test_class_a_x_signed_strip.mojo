"""Signed strip: bounded pumps, all four exits and exact occurrence controls."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_boundary_children import BoundaryLabel, verify_member_edge
from psc.class_a_x_transfer_plane import plane_middle
from psc.class_a_x_signed_strip import signed_strip_path, strip_source, verify_signed_strip


def main() raises:
    var members=List[List[Int]]()
    for k in range(13):
        for t in range(9):
            members.append([k,t])
    members.append([0,20])
    members.append([0,64])
    members.append([32,0])
    var paths=0
    var edges=0
    for pair in members:
        var k=pair[0]
        var t=pair[1]
        var n=k+t+3
        var d=k+2*t+5
        var radius=(n-1)//(k+1)
        var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n-1))
        for p in range(-radius,radius+1):
            for flip in [False,True]:
                var count=verify_signed_strip(tables,k,t,p,flip)
                assert_true(count<=4*radius+6)
                paths+=1
                edges+=count
        for bad_p in [-radius-1,radius+1]:
            var refused=False
            try:
                _=signed_strip_path(k,t,bad_p)
            except:
                refused=True
            assert_true(refused)
    assert_true(paths==1464 and edges==46462)
    # A tempting immediate fold at (0,8) asks for y ordinal 19;
    # sigma(y) has only ordinals 0..11. Refuse the nonexistent occurrence.
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,32,11,10))
    var refused=False
    try:
        verify_member_edge(tables,-1,0,11,21,strip_source(-1),33,19,
                           BoundaryLabel(0,2,2,4,-8))
    except:
        refused=True
    assert_true(refused)
    # At a=t-1, the negative transfer really ends in LAST x, not RUN y.
    tables=build_seed_overlap_tables_screened(class_member(CLASS_A,14,5,4))
    refused=False
    try:
        verify_member_edge(tables,-1,0,5,9,plane_middle(1,0,-1),0,15,strip_source(-2))
    except:
        refused=True
    assert_true(refused)
    assert_true(signed_strip_path(0,2,-1)[1].target==BoundaryLabel(0,0,-2,-5,12))
    refused=False
    try:
        _=signed_strip_path(0,8,-1,False,2)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=signed_strip_path(0,0,Int.MIN)
    except:
        refused=True
    assert_true(refused)
    print("CLASS_A_SIGNED_STRIP oriented_paths=",paths,"indexed_edges=",edges)
    require_contract("ClassASignedUnitStripBoundedNegativePumpAndFourTypedExits")
