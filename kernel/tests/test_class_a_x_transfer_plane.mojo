"""Actual unit descent, all parameter faces, generic transfer refusals."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, interior_overlap
from psc.class_a_boundary_children import geometric_state, verify_member_edge
from psc.class_a_x_transfer_plane import (
    plane_source, plane_middle, plane_indices, verify_plane_transfer,
    unit_descent_path, verify_unit_descent, verify_exception_base,
)


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
    var exception_paths=0
    for pair in members:
        var k=pair[0]
        var t=pair[1]
        var n=k+t+3
        var d=k+2*t+5
        var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n-1))
        for flip in [False,True]:
            verify_exception_base(tables,k,t,flip)
            exception_paths+=1
        for p in range((n+3)//(k+1)+1):
            for flip in [False,True]:
                var count=verify_unit_descent(tables,k,t,p,flip)
                assert_true(count==2*p+2)
                paths+=1
                edges+=count
            if p>=1 and not(k==0 and t==0 and p==1):
                verify_plane_transfer(tables,k,t,1,0,p)
        # z=2,s=0 recovers #436's original two-index-step ladder.
        if 2*k+t>=2:
            for m in range(2,(n+3)//(k+1)+1):
                verify_plane_transfer(tables,k,t,2,0,2*m)
        var refused=False
        try:
            _=unit_descent_path(k,t,(n+3)//(k+1)+1)
        except:
            refused=True
        assert_true(refused)
    # An actual strict X descendant on the SAME affine plane, but s=1.
    # Its algebraic second ordinal is A+3: the generic rule must refuse.
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    assert_true(interior_overlap(tables,geometric_state(tables,plane_source(1,1,1))))
    assert_true(interior_overlap(tables,geometric_state(tables,plane_middle(1,1,1))))
    assert_true(interior_overlap(tables,geometric_state(tables,plane_source(1,1,0))))
    verify_member_edge(tables,-1,0,3,5,plane_source(1,1,1),3,0,plane_middle(1,1,1))
    var refused=False
    try:
        verify_plane_transfer(tables,0,0,1,1,1)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=unit_descent_path(Int.MAX,0,0)
    except:
        refused=True
    assert_true(refused)
    # The origin's LAST edge is mathematically real; only its RUN label fails.
    refused=False
    try:
        verify_plane_transfer(tables,0,0,1,0,1)
    except:
        refused=True
    assert_true(refused)
    assert_true(verify_unit_descent(tables,0,0,1)==4)
    assert_true(plane_indices(0,0,1,0,1)[1]==9)
    assert_true(plane_indices(0,1,1,0,1)[1]==11)
    assert_true(plane_indices(0,0,1,0,6)[0]==1)
    refused=False
    try:
        _=unit_descent_path(0,0,6,False,13)
    except:
        refused=True
    assert_true(refused)
    print("CLASS_A_X_UNIT_DESCENT oriented_paths=",paths,"selected_edges=",edges)
    print("CLASS_A_X_EXCEPTION_BASE oriented_paths=",exception_paths,"selected_edges=",2*exception_paths)
    require_contract("ClassAXOddPlaneGuardedTransferAndUnitDescent")
