"""Eight complete F-family stars; all three direct child exits and real two-cycle."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_h5_children import verify_h5_child_packet
from psc.class_a_boundary_f_children import (
    certify_f_children, f_source, f_child_allowed, f_child_star, f_image,
    verify_f_packet, f_path, f_rank, verify_f_path, f_child_exit, verify_f_child_exit,
)
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_f_children()
    var envelope=f_image()
    assert_true(len(envelope)==64)
    var attained=List[Bool]()
    for _ in envelope:
        attained.append(False)
    var pairs=0
    var accepted=0
    var path_edges=0
    var child_exit_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            if k>=1:
                verify_h5_child_packet(tables,0,k,t,BoundaryEdge(A+1,k,f_source(0)))
            verify_f_packet(tables,6,k,t,BoundaryEdge(A+1,k+2,f_source(0)))
            var disjoint=member_transport(-1,k,n,d,f_source(0),A-1,0)
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,disjoint)))
            for kind in range(8):
                var w=f_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=A if w.top==0 else N
                var B=A if w.bottom==0 else N
                var star=f_child_star(kind,k,t)
                var expected=3
                if kind//2==1:expected=2*k+6
                elif kind//2==2:expected=2*A-2*k-1
                elif kind//2==3:expected=2*k+5
                assert_true(len(star)==expected)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_f_packet(tables,kind,k,t,edge)
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
                        assert_true(overlaps==f_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var packet=f_path(kind,k,t)
                verify_f_path(tables,kind,k,t,packet)
                verify_f_packet(tables,kind,k,t,packet[0])
                assert_true(len(packet)==(2 if kind//2==3 else 3))
                path_edges+=len(packet)
            for flip in range(2):
                var first=Dict[Int,Bool]()
                var width=N+2 if flip==0 else A+2
                for branch in range(3):
                    var packet=f_child_exit(flip,branch,k,t)
                    verify_f_child_exit(tables,flip,branch,k,t,packet)
                    verify_f_packet(tables,flip,k,t,packet[0])
                    var key=packet[0].i*width+packet[0].j
                    assert_true(key not in first)
                    first[key]=True
                    assert_true(len(packet)==(3 if branch==2 else 4))
                    child_exit_edges+=len(packet)
                assert_true(len(first)==3)
    for reached in attained:
        assert_true(reached)
    var failed=False
    try:
        certify_f_children(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=f_child_allowed(8,0,0,0,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=f_child_allowed(0,0,0,-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=f_rank(BoundaryLabel(0,0,0,0,0))
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=f_child_exit(2,0,0,0)
    except:
        failed=True
    assert_true(failed) # a source kind is not an F orientation
    failed=False
    try:
        _=f_child_exit(0,3,0,0)
    except:
        failed=True
    assert_true(failed)
    assert_true(f_rank(f_source(0))>f_rank(f_source(6))) # actual return edge increases selected rank
    assert_true(f_child_allowed(2,0,0,0,0))
    assert_true(not f_child_allowed(2,0,1,0,0))
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:
        verify_f_packet(tables,0,0,0,BoundaryEdge(8,0,BoundaryLabel(2,0,0,-3,3)))
    except:
        failed=True
    assert_true(failed) # interior and in the image, but wrong full transport
    var packet=f_path(0,0,0)
    packet[1]=BoundaryEdge(0,0,packet[1].target)
    failed=False
    try:
        verify_f_path(tables,0,0,0,packet)
    except:
        failed=True
    assert_true(failed)
    packet=f_path(1,0,0)
    packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,1,0,0,0))
    failed=False
    try:
        verify_f_path(tables,1,0,0,packet)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        verify_h5_child_packet(tables,0,0,0,BoundaryEdge(9,0,f_source(0)))
    except:
        failed=True
    assert_true(failed) # ordinal zero exists, but it is FIRST x, not a RUN y
    print("CLASS_A_BOUNDARY_F_FINITE members=56", "pairs",pairs,"accepted",accepted,
          "path_edges",path_edges,"direct_F_child_exit_edges",child_exit_edges,"union_labels=64", "BH=false")
    require_contract("class-A minus F/Z/E3/G2 and real reversals: eight complete nine-kind stars, exact 64-label union, every literal word pair checked by Parikh/Perron geometry, all three F children with typed tails <=3, conditional H5 ancestry and genuine F/G2 two-cycle with exits; legal disjoint children, wrong interior target, rank escape, symbolic corruption and malformed paths refused; no global closure/BH")
