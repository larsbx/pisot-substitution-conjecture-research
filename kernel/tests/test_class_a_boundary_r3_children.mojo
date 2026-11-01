"""R3/D3 complete stars, selected exits, source reconciliation and escapes."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_q3_children import q3_target
from psc.class_a_boundary_p3_children import p3_source, verify_p3_packet
from psc.class_a_boundary_p_children import p_source
from psc.class_a_boundary_r3_children import certify_r3_children, r3_source, enlarged_candidate, star_interface, has_registered_exit, r3_child_allowed, r3_child_star, r3_image, in_r3_image, verify_r3_packet, r3_path, verify_r3_path, _transition
from psc.class_a_boundary_occurrences import symbolic_child, RUN, FIRST
from psc.class_a_boundary_e_children import _offset
from psc.param_poly import qx_const
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_r3_children()
    for stage in range(2):
        var candidate=enlarged_candidate(stage==1)
        assert_true(len(candidate)==(39 if stage==0 else 41))
        var before=0
        var after=0
        var exits_before=0
        var exits_after=0
        for z in range(len(candidate)):
            var w=candidate[z]
            before+=1 if star_interface(w)!=0 else 0
            after+=1 if star_interface(w,True)!=0 else 0
            exits_before+=1 if has_registered_exit(w) else 0
            exits_after+=1 if has_registered_exit(w,True) else 0
            for j in range(z):
                assert_true(w!=candidate[j])
            for flip in range(2):
                assert_true(w!=r3_source(2+flip) or stage==1)
                assert_true(w!=p_source(flip))
        assert_true(before==17 and exits_before==15)
        assert_true(after==(19 if stage==0 else 21))
        assert_true(exits_after==(17 if stage==0 else 19))
    var image=r3_image()
    assert_true(len(image)==36)
    var attained=List[Bool]()
    var child_stars=0
    var child_exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_r3_image(image[z]))
        child_stars+=1 if star_interface(image[z],True)!=0 else 0
        child_exits+=1 if has_registered_exit(image[z],True) else 0
        for j in range(z):
            assert_true(image[z]!=image[j])
    assert_true(child_stars==16 and child_exits==14)
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
            for flip in range(2):
                verify_member_edge(tables,-1,k,n,d,q3_target(flip),n if flip==1 else A+1,A+1 if flip==1 else n,r3_source(flip))
                if n>=4:
                    verify_p3_packet(tables,flip,k,t,BoundaryEdge(n-3 if flip==1 else A+1,A+1 if flip==1 else n-3,r3_source(flip)))
            if n==3:
                assert_true(member_transport(-1,k,n,d,p3_source(0),A+1,0)==p3_source(4))
            for kind in range(4):
                var w=r3_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var run=N if kind//2==0 else n
                var R=A if kind%2==0 else run
                var B=run if kind%2==0 else A
                var star=r3_child_star(kind,k,t)
                assert_true(len(star)==(2*n+3 if kind//2==0 else 2*n+4+(1 if t>0 else 0)))
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_r3_packet(tables,kind,k,t,edge)
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    assert_true(edge.target.c!=0) # no immediate typed coincidence
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
                        assert_true(overlaps==r3_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var packet=r3_path(kind,k,t)
                verify_r3_path(tables,kind,k,t,packet)
                verify_r3_packet(tables,kind,k,t,packet[0])
                assert_true(len(packet)==(2 if kind//2==0 else (6 if k==0 else 4)))
                path_edges+=len(packet)
            # Two actual carrier escapes, not empirical nonmembership guesses.
            verify_r3_packet(tables,0,k,t,BoundaryEdge(A+1,n,r3_source(2)))
            verify_r3_packet(tables,0,k,t,BoundaryEdge(d+1,0,BoundaryLabel(2,0,0,-1,0)))
            verify_r3_packet(tables,2,k,t,BoundaryEdge(t+1,1,p_source(0)))
            var bad=member_transport(-1,k,n,d,r3_source(0),d-2,0)
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,bad)))
            assert_true(r3_child_allowed(2,k,t,0,0)==(t<=1))
            assert_true(r3_child_allowed(2,k,t,0,1)==(t==0))
    for found in attained:
        assert_true(found)
    var failed=False
    try:
        certify_r3_children(True)
    except:
        failed=True
    assert_true(failed)
    for mode in range(5):
        failed=False
        try:
            _=r3_child_allowed(4 if mode==0 else 0,-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),0)
        except:
            failed=True
        assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var cache=Dict[CubicElt,Int]()
    assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,p_source(2))))
    failed=False
    try:
        verify_r3_packet(tables,2,0,0,BoundaryEdge(1,1,p_source(2)))
    except:
        failed=True
    assert_true(failed) # wrong target is interior, same types, inside image
    failed=False
    try:
        _=symbolic_child(-1,0,2,_offset(p3_source(0)),2,qx_const(9),RUN,qx_const(0),0,2)
    except:
        failed=True
    assert_true(failed) # n=3 ancestry ordinal 0 is FIRST, never RUN
    failed=False
    try:
        _transition(qx_const(3),qx_const(5),qx_const(0),2,RUN,qx_const(0),FIRST,qx_const(0),BoundaryLabel(2,1,-1,-2,4))
    except:
        failed=True
    assert_true(failed) # t=0 clipped RF(t,0) cannot be supplied as RUN
    for mode in range(4):
        var packet=r3_path(2,0,0)
        if mode==0:
            packet[0]=BoundaryEdge(1,1,p_source(2))
        elif mode==1:
            packet[1]=BoundaryEdge(0,2,BoundaryLabel(0,2,1,2,-3))
        elif mode==2:
            packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
        else:
            _=packet.pop()
        failed=False
        try:
            verify_r3_path(tables,2,0,0,packet)
        except:
            failed=True
        assert_true(failed)
    print("CLASS_A_BOUNDARY_R3_FINITE members=56 source_cells=224", "pairs",pairs,"accepted",accepted,"path_edges",path_edges,"union_labels=36", "candidate39_registered_before=17_after=19", "candidate41_registered=21_unregistered=20", "BH=false")
    require_contract("class-A minus R3/D3 and real reversals: four complete nine-kind stars with t=0/1 clipping, exact 36-label union, literal all-pair Parikh/Perron checks, X ancestry and conditional n>=4 P3 ancestry, selected typed exits <=2 and <=6 via T/P0, explicit 39/41 carrier escapes and scoped source reconciliation; invalid ordinals/types/parameters, disjoint pairs, wrong interior targets, malformed paths and false coincidence refused; no all-direct-child/global closure/BH claim")
