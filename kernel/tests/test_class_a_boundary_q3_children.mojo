"""Complete Q3 stars, real singleton X, five-edge exits and true two-cycle."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_p3_children import verify_p3_packet, in_p3_image, p3_image
from psc.class_a_boundary_w_children import verify_local_packet, X, typed_coincidence
from psc.class_a_boundary_q3_children import certify_q3_children, q3_source, q3_target, q3_child_allowed, q3_child_star, verify_q3_packet, q3_path, verify_q3_path
from psc.class_a_boundary_occurrences import symbolic_child, RUN, FIRST
from psc.class_a_boundary_e_children import _offset
from psc.param_poly import qx_const
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_q3_children()
    var old_image=p3_image()
    assert_true(len(old_image)==37)
    for kind in range(2):
        assert_true(in_p3_image(q3_source(kind)))
        assert_true(not in_p3_image(q3_target(kind)))
        var found=False
        for label in old_image:
            if label==q3_source(kind):
                found=True
            assert_true(label!=q3_target(kind))
        assert_true(found)
    var pairs=0
    var accepted=0
    var path_edges=0
    var cycle_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            for kind in range(2):
                var w=q3_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                verify_p3_packet(tables,kind,k,t,BoundaryEdge(n-2 if kind==1 else A+1,A+1 if kind==1 else n-2,w))
                var R=A if kind==0 else N
                var B=N if kind==0 else A
                var star=q3_child_star(kind,k,t)
                assert_true(len(star)==1)
                verify_q3_packet(tables,kind,k,t,star[0])
                assert_true(star[0].target==q3_target(kind))
                assert_true(not typed_coincidence(star[0].target))
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==q3_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i==star[0].i and j==star[0].j))
                        if overlaps:
                            accepted+=1
                            verify_member_edge(tables,-1,k,n,d,reverse_label(w),j,i,reverse_label(target))
                var packet=q3_path(kind,k,t)
                verify_q3_path(tables,kind,k,t,packet)
                verify_q3_packet(tables,kind,k,t,packet[0])
                path_edges+=len(packet)
                # X's return is real, with n+1 a RUN even at n=3.
                verify_member_edge(tables,-1,k,n,d,q3_target(kind),n+1 if kind==1 else A+1,A+1 if kind==1 else n+1,w)
                cycle_edges+=2
            verify_local_packet(tables,X,k,t,BoundaryEdge(A+1,n+1,q3_source(0)))
            verify_local_packet(tables,X,k,t,q3_path(0,k,t)[1])
            # Legal last/run pair has x/y types but shift 2a-1>a.
            var bad=member_transport(-1,k,n,d,q3_source(0),A+1,1)
            assert_true(bad.top==0 and bad.bottom==2)
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,bad)))
            # Old Q=(y,x,0,-1,1), different from Q3. Its FR(0,2)
            # is exact upper-endpoint contact, not strict intersection.
            var oldq=BoundaryLabel(2,0,0,-1,1)
            var endpoint=member_transport(-1,k,n,d,oldq,0,2)
            assert_true(endpoint==BoundaryLabel(0,2,1,0,0))
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,endpoint)))
            verify_member_edge(tables,-1,k,n,d,oldq,n,n+1,BoundaryLabel(1,2,0,0,0))
            assert_true(not typed_coincidence(BoundaryLabel(1,2,0,0,0)))
    var failed=False
    try:
        certify_q3_children(True)
    except:
        failed=True
    assert_true(failed)
    for mode in range(5):
        failed=False
        try:
            _=q3_child_allowed(2 if mode==0 else 0,-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),0)
        except:
            failed=True
        assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    # This wrong x/c target is interior and has all the correct offsets.
    var wrong=BoundaryLabel(0,1,1,0,-1)
    var cache=Dict[CubicElt,Int]()
    assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,wrong)))
    failed=False
    try:
        verify_q3_packet(tables,0,0,0,BoundaryEdge(9,0,wrong))
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=symbolic_child(-1,0,2,_offset(q3_source(0)),RUN,qx_const(9),FIRST,qx_const(0),2,0)
    except:
        failed=True
    assert_true(failed) # LAST 9 cannot be relabelled as RUN
    for mode in range(4):
        var packet=q3_path(0,0,0)
        if mode==0:
            packet[0]=BoundaryEdge(9,0,wrong)
        elif mode==1:
            packet[2]=BoundaryEdge(3,0,BoundaryLabel(1,0,0,1,0))
        elif mode==2:
            packet[4]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
        else:
            _=packet.pop()
        failed=False
        try:
            verify_q3_path(tables,0,0,0,packet)
        except:
            failed=True
        assert_true(failed)
    print("CLASS_A_BOUNDARY_Q3_FINITE members=56 source_cells=112", "pairs",pairs,"accepted",accepted,"path_edges",path_edges,"cycle_edges",cycle_edges,"union_labels=2", "BH=false")
    require_contract("class-A minus Q3 and real reversal: complete nine-kind stars with one actual X child per orientation; exact P3 ancestry and actual escape from P3's 37-label image; five-edge typed exit and four-edge tail for every direct Q3 child; every literal pair checked against full Parikh/Perron geometry; real two-cycle retained; invalid kinds/indices/types, disjoint pairs, endpoint contact and false coincidence refused; no all-edge descent/global closure/BH")
