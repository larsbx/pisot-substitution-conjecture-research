"""Ten complete oriented P stars, typed endpoint control and short exits."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_h3_children import verify_chain_packet
from psc.class_a_boundary_p_children import (
    p_source, certify_p_children, p_child_allowed, p_child_star, verify_p_packet,
    p_image, p_path, verify_p_path, p_rank,
)
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt
from psc.class_a_boundary_occurrences import symbolic_child, RUN
from psc.param_poly import QX, qx_const


def main() raises:
    certify_p_children()
    var envelope=p_image()
    assert_true(len(envelope)==51)
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
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            verify_chain_packet(tables,6,k,t,BoundaryEdge(1,n,p_source(0)))
            verify_p_packet(tables,0,k,t,BoundaryEdge(0,t+2,p_source(8)))
            # The k=0 "run" ordinal t+3=n is really a last c.
            # A's legal (2,1) pair is endpoint contact, so no strict child.
            assert_true(not p_child_allowed(4,k,t,2,1))
            var half=member_transport(-1,k,n,d,p_source(4),n,n-2)
            assert_true(half==BoundaryLabel(1,2,0,0,0))
            verify_p_packet(tables,4,k,t,BoundaryEdge(n,n-2,half))
            for kind in range(10):
                var w=p_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=A if w.top==0 else n-1
                var B=A if w.bottom==0 else n-1
                var group=kind//2
                var expected=2*k+4
                if group==1:
                    expected=2*t+4
                elif group==2:
                    expected=n+2
                elif group==3:
                    expected=2
                elif group==4:
                    expected=2*n+3
                var star=p_child_star(kind,k,t)
                assert_true(len(star)==expected)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_p_packet(tables,kind,k,t,edge)
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,
                                       reverse_label(edge.target))
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
                        assert_true(overlaps==p_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var path=p_path(kind,k,t)
                verify_p_path(tables,kind,k,t,path)
                assert_true(len(path)<=5)
                path_edges+=len(path)
    for reached in attained:
        assert_true(reached)
    var failed=False
    try:
        certify_p_children(True)
    except:
        failed=True
    assert_true(failed)
    # This unshifted universal RUN(3) claim includes N=2 and must refuse.
    failed=False
    try:
        var old: List[QX]=[qx_const(0),qx_const(2),qx_const(-2)]
        _=symbolic_child(-1,2,2,old,RUN,qx_const(3),RUN,qx_const(1),2,2)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=p_child_allowed(10,0,0,0,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=p_child_allowed(0,0,0,-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=p_rank(BoundaryLabel(0,0,0,0,0),0,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=p_rank(BoundaryLabel(2,0,-1,0,2),1,0)
    except:
        failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var path=p_path(0,0,0)
    path[1]=BoundaryEdge(0,0,path[1].target)
    failed=False
    try:
        verify_p_path(tables,0,0,0,path)
    except:
        failed=True
    assert_true(failed)
    # Correct final C cannot excuse a corrupted intermediate, or a wrong terminal.
    path=p_path(0,0,0)
    path[len(path)-1]=BoundaryEdge(1,2,BoundaryLabel(2,1,0,0,0))
    failed=False
    try:
        verify_p_path(tables,0,0,0,path)
    except:
        failed=True
    assert_true(failed)
    # Same offset and overlap, wrong type: the n=3 (3,1) child is c/y.
    failed=False
    try:
        verify_p_packet(tables,4,0,0,BoundaryEdge(3,1,BoundaryLabel(2,2,0,0,0)))
    except:
        failed=True
    assert_true(failed)
    # P(1,t+3) exists at k=0, but is run/last, not the intended run/run B.
    failed=False
    try:
        verify_p_packet(tables,0,0,0,BoundaryEdge(1,3,p_source(6)))
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_P_FINITE members=56", "pairs",pairs,"accepted",accepted,
          "path_edges",path_edges,"union_labels=51", "all_ten_sources_exit_in_at_most_five=true", "BH=false")
    require_contract("class-A minus P/Pplus/A/B/D and real reversals: complete ten first/run/last stars, exact 51-label union, full Parikh/Perron every-pair replay and <=5-step typed coincidence paths; k0 last-occurrence and n3 unequal-type zero offset handled, disjoint contacts and corrupted intermediates refused; no global closure or universal BH")
