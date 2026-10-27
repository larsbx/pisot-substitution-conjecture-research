"""Both complete P3 stars: all literal pairs, endpoint changes and typed exits."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_f_children import verify_f_packet
from psc.class_a_boundary_w_children import selected_path_label
from psc.class_a_boundary_p3_children import (
    certify_p3_children, p3_source, p3_child_allowed, p3_child_star, p3_image,
    verify_p3_packet, p3_path, p3_rank, verify_p3_path,
)
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_p3_children()
    var envelope=p3_image()
    assert_true(len(envelope)==26)
    var attained=List[Bool]()
    for _ in envelope:attained.append(False)
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
            verify_f_packet(tables,4,k,t,BoundaryEdge(A+1,A-k-1,p3_source(0)))
            verify_f_packet(tables,5,k,t,BoundaryEdge(A-k-1,A+1,p3_source(1)))
            var disjoint=member_transport(-1,k,n,d,p3_source(0),d+2,0)
            assert_true(disjoint.top==2 and disjoint.bottom==0)
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,disjoint)))
            assert_true(p3_child_allowed(0,k,t,A+1,0)==(n<=5))
            for flip in range(2):
                var w=p3_source(flip)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=A if flip==0 else N
                var B=N if flip==0 else A
                var star=p3_child_star(flip,k,t)
                assert_true(len(star)==2*n-3)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_p3_packet(tables,flip,k,t,edge)
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
                        assert_true(overlaps==p3_child_allowed(flip,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:accepted+=1
                var packet=p3_path(flip,k,t)
                verify_p3_path(tables,flip,k,t,packet)
                verify_p3_packet(tables,flip,k,t,packet[0])
                assert_true(len(packet)==(4 if n==3 else 2))
                path_edges+=len(packet)
    for reached in attained:assert_true(reached)
    var failed=False
    try:certify_p3_children(True)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=p3_child_allowed(2,0,0,0,0)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=p3_child_allowed(0,0,0,-1,0)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=p3_child_star(0,-1,0)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=p3_rank(BoundaryLabel(0,0,0,0,0))
    except:failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:verify_p3_packet(tables,0,0,0,BoundaryEdge(8,0,selected_path_label(5)))
    except:failed=True
    assert_true(failed) # Q is interior and in the image; actual full target is V.
    var target=member_transport(-1,0,3,5,p3_source(0),9,0)
    assert_true(target.top==0 and target.bottom==0)
    assert_true(target!=selected_path_label(5)) # false unshifted short RUN.
    failed=False
    try:verify_p3_packet(tables,0,0,0,BoundaryEdge(9,0,selected_path_label(5)))
    except:failed=True
    assert_true(failed)
    var packet=p3_path(0,0,0)
    packet[1]=BoundaryEdge(0,0,packet[1].target)
    failed=False
    try:verify_p3_path(tables,0,0,0,packet)
    except:failed=True
    assert_true(failed)
    packet=p3_path(1,0,0)
    packet[len(packet)-1]=BoundaryEdge(2,1,BoundaryLabel(2,1,0,0,0))
    failed=False
    try:verify_p3_path(tables,1,0,0,packet)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_P3_FINITE members=56", "pairs",pairs,"accepted",accepted,
          "path_edges",path_edges,"union_labels=26", "BH=false")
    require_contract("class-A minus P3 and real reversal: complete nine-kind stars, exactly 2n-3 actual children each, 26-label chamber union, every word pair checked by full Parikh/Perron geometry, uniform E3 ancestry and selected typed exits <=4 with true n=3 endpoint; legal disjoint children, wrong interior targets, invalid ordinals/orientations, symbolic corruption, rank escape and malformed paths refused; no forward closure or global BH")
