"""H5: all-chamber k=0/1/>=2 actual short typed-coincidence exits."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge,
)
from psc.class_a_boundary_h4_children import h4_source, verify_h4_packet
from psc.class_a_boundary_h5_exit import (
    certify_h5_exits, h5_source, h5_path, verify_h5_path,
)
from psc.overlap_seed_patch import build_seed_overlap_tables_screened


def main() raises:
    certify_h5_exits()
    var members=0
    var path_edges=0
    for k in range(11):
        for t in [0,1,2,3,5,9]:
            members+=1
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(
                class_member(CLASS_A,A,n,n-1))
            var source=h5_source()
            var ancestry=member_transport(-1,k,n,d,h4_source(),A+1,t+2)
            assert_true(ancestry==source)
            verify_h4_packet(tables,k,t,BoundaryEdge(A+1,t+2,source))
            var steps=h5_path(k,t)
            assert_true(len(steps)==(3 if k==0 else 2))
            verify_h5_path(tables,k,t,steps)
            path_edges+=len(steps)
            var first=steps[0]
            if k==0:
                assert_true(first.target==BoundaryLabel(0,0,0,-3,4))
            elif k==1:
                assert_true(first.target==BoundaryLabel(0,0,0,-3,3))
            else:
                assert_true(first.target==BoundaryLabel(2,0,0,-3,3))
                assert_true(first.i==A+2-k)
            assert_true(steps[len(steps)-1].target==BoundaryLabel(2,2,0,0,0))
    var failed=False
    try:
        certify_h5_exits(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=h5_path(-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=h5_path(0,-1)
    except:
        failed=True
    assert_true(failed)

    # A forged intermediate label fails even though the final target C
    # and the word occurrence indices were left unchanged.
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var correct=h5_path(0,0)
    var bad=List[BoundaryEdge]()
    for e in correct:
        bad.append(BoundaryEdge(e.i,e.j,e.target))
    var middle=bad[1].target
    bad[1]=BoundaryEdge(bad[1].i,bad[1].j,
        BoundaryLabel(middle.top,middle.bottom,middle.x,middle.c,middle.y+1))
    failed=False
    try:
        verify_h5_path(tables,0,0,bad)
    except:
        failed=True
    assert_true(failed)
    # For k=2 the formal LAST index cannot be used as the intended
    # RUN route with the claimed (y,x,0,-3,3) target.
    var p=2
    var n=p+3
    var d=2*n-1-p
    var A=n+d
    var tab=build_seed_overlap_tables_screened(
        class_member(CLASS_A,A,n,n-1))
    failed=False
    try:
        verify_member_edge(tab,-1,p,n,d,h5_source(),A+1,0,
            BoundaryLabel(2,0,0,-3,3))
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_H5_FINITE members",members,
          "selected_edges",path_edges,"typed_terminal=true",
          "k0_depth=3","k_ge_1_depth=2","global_BH=false")
    require_contract("minus boundary H5=(x,y,2,2,-5) actual H4 last/run descendant with k0 length-three and k>=1 length-two genuine typed coincidence exits, symbolic Q[t,k] word/Parikh identities, full strict Perron replay, invalid index and forged packet refusals; not closed BH")
