"""Every entrance is indexed; identical suffixes are checked once and compared."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_boundary_children import BoundaryLabel, verify_member_edge
from psc.class_a_x_ladder import reversed_label
from psc.class_a_x_signed_strip import signed_strip_path
from psc.class_a_x_transfer_plane import plane_middle
from psc.class_a_x_cross_strip import cross_strip_source, cross_strip_path


def main() raises:
    var members=List[List[Int]]()
    for k in range(13):
        for t in range(9):
            members.append([k,t])
    members.append([0,20])
    members.append([0,64])
    members.append([32,0])
    var paths=0
    var projected_edges=0
    var shared_checks=0
    var entrance_checks=0
    for pair in members:
        var k=pair[0]
        var t=pair[1]
        var n=k+t+3
        var d=k+2*t+5
        var K=k+1
        var radius=(n-1)//K
        var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n-1))
        for p in range(-(t//K),radius+1):
            for flip in [False,True]:
                var baseline=signed_strip_path(k,t,p,flip)
                var parent=baseline[0].target
                for q in range(1,len(baseline)):
                    var e=baseline[q]
                    verify_member_edge(tables,-1,k,n,d,parent,e.i,e.j,e.target)
                    parent=e.target
                    shared_checks+=1
                assert_true(parent==BoundaryLabel(2,2,0,0,0))
                for s in range(-3,2 if p<0 else 4):
                    var packet=cross_strip_path(k,t,p,s,flip)
                    var root=cross_strip_source(p,s)
                    if flip:
                        root=reversed_label(root)
                    assert_true(len(packet)==len(baseline) and len(packet)<=4*radius+6)
                    if p>=0:
                        assert_true(len(packet)==2*p+2)
                    var first=packet[0]
                    verify_member_edge(tables,-1,k,n,d,root,first.i,first.j,first.target)
                    assert_true(first.target==baseline[0].target)
                    # Equality against the actual checked suffix certifies
                    # all repeated paths without repeating field geometry.
                    for q in range(1,len(packet)):
                        assert_true(packet[q].i==baseline[q].i and packet[q].j==baseline[q].j)
                        assert_true(packet[q].target==baseline[q].target)
                    entrance_checks+=1
                    paths+=1
                    projected_edges+=len(packet)
    assert_true(paths==7574 and projected_edges==243888)
    assert_true(entrance_checks==7574 and shared_checks==42234)
    # Actual strict X descendant W=Z(2,-4,1): formal entrance index 0
    # is FIRST x, not RUN y. The full target Q_2 must be refused.
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var refused=False
    try:
        verify_member_edge(tables,-1,0,3,5,cross_strip_source(2,-4),0,0,plane_middle(1,0,2))
    except:
        refused=True
    assert_true(refused)
    # The actual FIRST child has a different type and full offset.
    verify_member_edge(tables,-1,0,3,5,cross_strip_source(2,-4),0,0,
                       BoundaryLabel(0,0,-1,-5,8))
    for pair in [[0,-4],[0,4],[3,0],[-1,0]]:
        var p=pair[0]
        var s=pair[1]
        refused=False
        try:
            _=cross_strip_path(0,0,p,s)
        except:
            refused=True
        assert_true(refused)
    refused=False
    try:
        _=cross_strip_path(0,0,Int.MIN,0)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=cross_strip_path(0,0,1,0,False,2)
    except:
        refused=True
    assert_true(refused)
    refused=False
    var first=cross_strip_path(0,0,1,-3)[0]
    try:
        verify_member_edge(tables,-1,0,3,5,reversed_label(cross_strip_source(1,-3)),
                           first.i,first.j,reversed_label(first.target))
    except:
        refused=True
    assert_true(refused)
    print("CLASS_A_CROSS_STRIP oriented_paths=",paths,"selected_edges=",projected_edges)
    print("CLASS_A_CROSS_STRIP entrance_checks=",entrance_checks,"shared_suffix_checks=",shared_checks)
    require_contract("ClassACrossStripTypedRunShearProductiveSectors")
