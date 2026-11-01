"""Two complete B3 stars, literal endpoint types and selected typed exits."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import r3_source, enlarged_candidate, r3_image
from psc.class_a_boundary_e_children import eh_source
from psc.class_a_boundary_b3_children import certify_b3_children, b3_source, b3_star_interface, b3_registered_exit, b3_child_allowed, b3_child_star, b3_image, in_b3_image, verify_b3_packet, verify_b3_star, b3_path, verify_b3_path, _transition
from psc.class_a_boundary_occurrences import RUN, LAST
from psc.param_poly import qx_const
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_b3_children()
    var candidate=enlarged_candidate(True)
    var before=0
    var after=0
    var exits_before=0
    var exits_after=0
    for z in range(len(candidate)):
        var w=candidate[z]
        before+=1 if b3_star_interface(w)!=0 else 0
        after+=1 if b3_star_interface(w,True)!=0 else 0
        exits_before+=1 if b3_registered_exit(w) else 0
        exits_after+=1 if b3_registered_exit(w,True) else 0
        for j in range(z):
            assert_true(w!=candidate[j])
        assert_true(w!=eh_source(2) and w!=eh_source(3))
    assert_true(len(candidate)==41 and before==21 and after==23)
    assert_true(exits_before==19 and exits_after==21)
    var old_image=r3_image()
    var old_stars=0
    var old_exits=0
    for w in old_image:
        old_stars+=1 if b3_star_interface(w,True)!=0 else 0
        old_exits+=1 if b3_registered_exit(w,True) else 0
    assert_true(old_stars==18 and old_exits==16)
    var image=b3_image()
    assert_true(len(image)==20)
    var attained=List[Bool]()
    var child_stars=0
    var child_exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_b3_image(image[z]))
        child_stars+=1 if b3_star_interface(image[z],True)!=0 else 0
        child_exits+=1 if b3_registered_exit(image[z],True) else 0
        for j in range(z):
            assert_true(image[z]!=image[j])
    assert_true(child_stars==10 and child_exits==10)
    # Scalar image predicate and explicit list agree on a surrounding label box.
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in range(-2,3):
                    for y in range(-6,7):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:
                            listed=listed or w==v
                        assert_true(listed==in_b3_image(w))
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
            for kind in range(2):
                var w=b3_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                verify_member_edge(tables,-1,k,n,d,r3_source(kind),0 if kind==1 else d+1,d+1 if kind==1 else 0,w)
                var R=N if kind==0 else A
                var B=A if kind==0 else N
                var star=b3_child_star(kind,k,t)
                verify_b3_star(tables,kind,k,t,star)
                assert_true(len(star)==2*n+(2 if t==0 else 3))
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    assert_true(edge.target.c!=0)
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
                        assert_true(overlaps==b3_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var packet=b3_path(kind,k,t)
                verify_b3_path(tables,kind,k,t,packet)
                verify_b3_packet(tables,kind,k,t,packet[0])
                assert_true(len(packet)==2)
                path_edges+=len(packet)
            assert_true(b3_child_allowed(0,k,t,N,A+1)==(t==0))
            assert_true(b3_child_allowed(0,k,t,n,A+1)==(t<=1))
            if t==0:
                assert_true(2*n+3==A+1)
                assert_true(member_transport(-1,k,n,d,b3_source(0),n,2*n+3)==BoundaryLabel(1,0,-1,-1,3))
            # RR->P0 is an alternative, not the shorter selected H1 path.
            verify_b3_packet(tables,0,k,t,BoundaryEdge(1,n+4,BoundaryLabel(2,2,-1,-1,3)))
    for found in attained:
        assert_true(found)
    var failed=False
    try:
        certify_b3_children(True)
    except:
        failed=True
    assert_true(failed)
    for mode in range(6):
        failed=False
        try:
            _=b3_child_allowed(2 if mode==0 else 0,-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (5 if mode==4 else 0),10 if mode==5 else 0)
        except:
            failed=True
        assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var cache=Dict[CubicElt,Int]()
    assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,eh_source(4))))
    failed=False
    try:
        verify_b3_packet(tables,0,0,0,BoundaryEdge(0,5,eh_source(4)))
    except:
        failed=True
    assert_true(failed) # H2 is interior, same types and in image, but wrong here.
    failed=False
    try:
        var disjoint=member_transport(-1,0,3,5,b3_source(0),0,4)
        verify_b3_packet(tables,0,0,0,BoundaryEdge(0,4,disjoint))
    except:
        failed=True
    assert_true(failed) # legal FR(n+1) has shift -1-h, outside (-1,a).
    failed=False
    try:
        _transition(qx_const(3),qx_const(5),0,LAST,qx_const(3),RUN,qx_const(9),BoundaryLabel(1,2,-1,-1,3))
    except:
        failed=True
    assert_true(failed) # t=0 ordinal 2n+3 is LAST x, not RUN y.
    for mode in range(4):
        var packet=b3_path(0,0,0)
        if mode==0:
            packet[0]=BoundaryEdge(0,5,eh_source(4))
        elif mode==1:
            packet[1]=BoundaryEdge(2,1,BoundaryLabel(2,2,0,0,0))
        elif mode==2:
            packet[1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
        else:
            _=packet.pop()
        failed=False
        try:
            verify_b3_path(tables,0,0,0,packet)
        except:
            failed=True
        assert_true(failed)
    for mode in range(3):
        var star=b3_child_star(0,0,0)
        if mode==0:
            _=star.pop()
        elif mode==1:
            star[1]=star[0]
        else:
            star.append(star[0])
        failed=False
        try:
            verify_b3_star(tables,0,0,0,star)
        except:
            failed=True
        assert_true(failed)
    print("CLASS_A_BOUNDARY_B3_FINITE members=56 source_cells=112", "pairs",pairs,"accepted",accepted,"path_edges",path_edges,"union_labels=20", "candidate41_registered_before=21_after=23_unregistered=18", "R3_D3_image_registered_exits=16_of_36", "BH=false")
    require_contract("class-A minus B3 and real reversal: complete nine-kind stars with t=0/1 endpoint clipping, exact 20-label image, literal all-pair Parikh/Perron checks, actual R3 ancestry, uniform two-edge typed exit via H1 and uniform escape from S41, explicit 41-row registry; invalid ordinals/types/parameters, corrupt identity, disjoint pairs, wrong interior targets, duplicate/incomplete stars, malformed paths and false typed coincidence refused; no all-child/global BH claim")
