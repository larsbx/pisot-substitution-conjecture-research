"""Indexed ladder, endpoint faces, genuine reversals and cap refusal."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_boundary_children import BoundaryLabel, verify_member_edge
from psc.class_a_x_ladder import ladder_a, ladder_path, verify_ladder


def main() raises:
    var checks=0
    for k in range(9):
        for t in range(9):
            if 2*k+t<2:
                var refused=False
                try:
                    _=ladder_path(k,t,1)
                except:
                    refused=True
                assert_true(refused)
                continue
            var n=k+t+3
            var d=k+2*t+5
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n-1))
            for m in range(1,(k+t+6)//(k+1)+1):
                for flip in [False,True]:
                    assert_true(verify_ladder(tables,k,t,m,flip)==2*m+4)
                    checks+=1
            var refused=False
            try:
                _=ladder_path(k,t,(k+t+6)//(k+1)+1)
            except:
                refused=True
            assert_true(refused)
    # The first excluded face has a genuine LAST x instead of the claimed RUN y.
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,11,4,3))
    var refused=False
    try:
        verify_member_edge(tables,-1,0,4,7,ladder_a(1),12,0,BoundaryLabel(2,0,-1,-4,6))
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=ladder_path(0,2,8,False,19)
    except:
        refused=True
    assert_true(refused)
    print("CLASS_A_X_LADDER member_paths=",checks,"universal_X_productivity=false")
    require_contract("ClassAXIndexedLadderActualTypedPaths")
