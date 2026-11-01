"""Six complete T/X/Y0 stars, real cycle and t=0 last-c controls."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_p3_children import verify_p3_packet
from psc.class_a_boundary_tx_children import certify_tx_children, tx_source, tx_child_allowed, tx_child_star, tx_image, verify_tx_packet, tx_path, tx_rank, verify_tx_path
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_tx_children()
    var image=tx_image()
    assert_true(len(image)==42)
    var attained=List[Bool]()
    for _ in image:attained.append(False)
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
            verify_p3_packet(tables,0,k,t,BoundaryEdge(A+1,n-2,tx_source(0)))
            verify_p3_packet(tables,1,k,t,BoundaryEdge(n-2,A+1,tx_source(1)))
            for flip in range(2):
                verify_tx_packet(tables,2+flip,k,t,BoundaryEdge(n+1 if flip==1 else A+1,A+1 if flip==1 else n+1,tx_source(flip)))
                verify_tx_packet(tables,2+flip,k,t,BoundaryEdge(1 if flip==1 else d+3,d+3 if flip==1 else 1,tx_source(4+flip)))
                assert_true(tx_rank(tx_source(flip))>tx_rank(tx_source(2+flip))) # actual return increases selected rank
            var disjoint=member_transport(-1,k,n,d,tx_source(0),A,0)
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,disjoint)))
            assert_true(tx_child_allowed(4,k,t,0,0)==(t<=1))
            assert_true(tx_child_allowed(4,k,t,n,n)==(t==0))
            for kind in range(6):
                var w=tx_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=N if w.top==2 else A
                var B=N if w.bottom==2 else A
                var star=tx_child_star(kind,k,t)
                var expected=1 if kind//2==0 else (2*n+3 if kind//2==1 else 2*k+8-(1 if t==0 else 0))
                assert_true(len(star)==expected)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_tx_packet(tables,kind,k,t,edge)
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    var found=False
                    for z in range(len(image)):
                        if edge.target==image[z]:
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
                        assert_true(overlaps==tx_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:accepted+=1
                var path=tx_path(kind,k,t)
                verify_tx_path(tables,kind,k,t,path)
                verify_tx_packet(tables,kind,k,t,path[0])
                assert_true(len(path)==(2 if kind//2==1 else 3))
                path_edges+=len(path)
    for reached in attained:assert_true(reached)
    var failed=False
    try:certify_tx_children(True)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=tx_child_allowed(6,0,0,0,0)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=tx_child_allowed(0,0,0,-1,0)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=tx_child_star(0,-1,0)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=tx_rank(BoundaryLabel(0,0,0,0,0))
    except:failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:verify_tx_packet(tables,0,0,0,BoundaryEdge(9,0,BoundaryLabel(0,0,0,-2,3)))
    except:failed=True
    assert_true(failed) # interior and in the image, but wrong full Parikh target
    var target=member_transport(-1,0,3,5,tx_source(4),3,3)
    assert_true(target==BoundaryLabel(1,1,0,-2,3))
    failed=False
    try:verify_tx_packet(tables,4,0,0,BoundaryEdge(3,3,BoundaryLabel(1,2,0,-2,3)))
    except:failed=True
    assert_true(failed) # a real LAST c cannot become a RUN y at the same offset
    var path=tx_path(0,0,0)
    path[1]=BoundaryEdge(0,0,path[1].target)
    failed=False
    try:verify_tx_path(tables,0,0,0,path)
    except:failed=True
    assert_true(failed)
    path=tx_path(5,0,0)
    path[len(path)-1]=BoundaryEdge(1,2,BoundaryLabel(2,1,0,0,0))
    failed=False
    try:verify_tx_path(tables,5,0,0,path)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_TX_FINITE members=56", "pairs",pairs,"accepted",accepted,"path_edges",path_edges,"union_labels=42", "BH=false")
    require_contract("class-A minus T/X/Y0 and real reversals: six complete nine-kind stars, exact counts 1/2n+3/2k+8-[t=0], 42-label chamber union, every literal word pair checked by full Parikh/Perron geometry, uniform P3 ancestry and X-to-Y0 child, true T/X cycle with an exit, typed paths <=3; t=0 c/c endpoint, legal disjoint children, wrong interior targets, invalid inputs, symbolic corruption, rank escape and malformed paths refused; no all-edge descent, forward closure or global BH")
