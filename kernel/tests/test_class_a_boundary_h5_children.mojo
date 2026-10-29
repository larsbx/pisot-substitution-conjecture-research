"""All H5 first/run/last pairs and orientations; strict t separator and exits."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_h4_children import verify_h4_packet
from psc.class_a_boundary_h5_children import (
    certify_h5_children, h5_child_source, h5_child_allowed, h5_child_star,
    h5_image, verify_h5_child_packet, h5_child_path, h5_child_rank, verify_h5_child_path,
)
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_h5_children()
    var envelope=h5_image()
    assert_true(len(envelope)==30)
    var attained=List[Bool]()
    for _ in envelope:
        attained.append(False)
    var pairs=0
    var accepted=0
    var path_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            verify_h4_packet(tables,k,t,BoundaryEdge(A+1,t+2,h5_child_source(0)))
            for flip in range(2):
                var w=h5_child_source(flip)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=A if flip==0 else N
                var B=N if flip==0 else A
                var star=h5_child_star(flip,k,t)
                assert_true(len(star)==2*k+1)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_h5_child_packet(tables,flip,k,t,edge)
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    var found=False
                    for z in range(len(envelope)):
                        if edge.target==envelope[z]:
                            attained[z]=True
                            found=True
                    assert_true(found)
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==h5_child_allowed(flip,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var packet=h5_child_path(flip,k,t)
                verify_h5_child_path(tables,flip,k,t,packet)
                verify_h5_child_packet(tables,flip,k,t,packet[0])
                assert_true(len(packet)==(3 if k==0 else 2))
                path_edges+=len(packet)
                if k==0:
                    assert_true(len(star)==1)
    for reached in attained:
        assert_true(reached)
    var failed=False
    try:
        certify_h5_children(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=h5_child_allowed(2,0,0,0,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=h5_child_allowed(0,0,0,-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=h5_child_rank(BoundaryLabel(0,0,0,0,0),0,0)
    except:
        failed=True
    assert_true(failed)
    for t in [0,1,2]:
        var k=4
        var n=k+t+3
        var A=3*n-1-k
        var q=A+2-k
        assert_true(h5_child_allowed(0,k,t,q+2,0)==(t>=2))
    for t in [1,2]:
        var k=3
        var n=k+t+3
        var A=3*n-1-k
        assert_true(h5_child_allowed(0,k,t,A+1,0)==(t>=2))
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:
        verify_h5_child_packet(tables,0,0,0,BoundaryEdge(9,0,BoundaryLabel(0,0,0,-3,3)))
    except:
        failed=True
    assert_true(failed) # interior and in the image, but wrong full transport
    var packet=h5_child_path(0,0,0)
    packet[1]=BoundaryEdge(0,0,packet[1].target)
    failed=False
    try:
        verify_h5_child_path(tables,0,0,0,packet)
    except:
        failed=True
    assert_true(failed)
    packet=h5_child_path(1,0,0)
    packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,1,0,0,0))
    failed=False
    try:
        verify_h5_child_path(tables,1,0,0,packet)
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_H5_CHILDREN_FINITE members=56", "pairs",pairs,"accepted",accepted,
          "path_edges",path_edges,"union_labels=30", "occurrences_each=2k+1", "BH=false")
    require_contract("class-A minus H5 and actual reversal: complete nine-kind child tables, exact t0/1 versus t>=2 polynomial separator, 2k+1 true ordered occurrences and 30-label chamber union, full word/Parikh/Perron every-pair replay and reversed selected <=3-step typed exits; invalid ordinals, legal disjoint extra children at t1, rank escape, symbolic corruption and broken packets refuse; no global forward closure or BH")
