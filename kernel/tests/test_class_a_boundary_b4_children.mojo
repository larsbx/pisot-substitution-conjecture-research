"""Complete B4 stars and three-case exits, keeping companion stars unproved."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import r3_source, enlarged_candidate, r3_image
from psc.class_a_boundary_e2_children import e2_source
from psc.class_a_boundary_h3_children import alpha_high
from psc.class_a_boundary_b4_children import certify_b4_children, b4_source, b4_star_interface, b4_exit_interface, b4_child_allowed, b4_child_star, b4_image, in_b4_image, verify_b4_packet, verify_b4_star, b4_path, verify_b4_path, _transition
from psc.class_a_boundary_occurrences import FIRST, RUN
from psc.param_poly import qx_const
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_b4_children()
    var candidate=enlarged_candidate(True)
    var before=0
    var after=0
    var exits_before=0
    var exits_after=0
    for z in range(len(candidate)):
        var w=candidate[z]
        before+=1 if b4_star_interface(w)!=0 else 0
        after+=1 if b4_star_interface(w,True)!=0 else 0
        exits_before+=1 if b4_exit_interface(w)!=0 else 0
        exits_after+=1 if b4_exit_interface(w,True)!=0 else 0
        assert_true(w.c>=-1 and w.c<=1)
        for j in range(z):
            assert_true(w!=candidate[j])
    assert_true(len(candidate)==41 and before==23 and after==25)
    assert_true(exits_before==21 and exits_after==23)
    var old_image=r3_image()
    var old_stars=0
    var old_exits=0
    for w in old_image:
        old_stars+=1 if b4_star_interface(w,True)!=0 else 0
        old_exits+=1 if b4_exit_interface(w,True)!=0 else 0
    assert_true(old_stars==20 and old_exits==18)
    for kind in range(2,6):
        assert_true(b4_star_interface(b4_source(kind),True)==0)
        assert_true(b4_exit_interface(b4_source(kind),True)!=0)
    var image=b4_image()
    assert_true(len(image)==32)
    var attained=List[Bool]()
    var child_stars=0
    var child_exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_b4_image(image[z]))
        assert_true(image[z].c==-2 or image[z].c==2)
        child_stars+=1 if b4_star_interface(image[z],True)!=0 else 0
        child_exits+=1 if b4_exit_interface(image[z],True)!=0 else 0
        for j in range(z):
            assert_true(image[z]!=image[j])
    assert_true(child_stars==2 and child_exits==6)
    for top in range(3):
        for bottom in range(3):
            for x in range(-3,4):
                for c in range(-3,4):
                    for y in range(-9,10):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:
                            listed=listed or w==v
                        assert_true(listed==in_b4_image(w))
    assert_true(not alpha_high(0,0) and not alpha_high(1,1) and alpha_high(2,2))
    var pairs=0
    var accepted=0
    var path_edges=0
    var b4_edges=0
    var companion_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            for kind in range(6):
                var w=b4_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var packet=b4_path(kind,k,t)
                verify_b4_path(tables,kind,k,t,packet)
                assert_true(len(packet)==((3 if t==0 else 5) if kind//2==0 else (2 if kind//2==1 else 4)))
                path_edges+=len(packet)
                if kind>=2:
                    companion_edges+=len(packet)
                    continue
                b4_edges+=len(packet)
                verify_member_edge(tables,-1,k,n,d,r3_source(kind),0 if kind==1 else d+2,d+2 if kind==1 else 0,w)
                var R=N if kind==0 else A
                var B=A if kind==0 else N
                var star=b4_child_star(kind,k,t)
                verify_b4_star(tables,kind,k,t,star)
                assert_true(len(star)==max(1,2*t-1))
                if t<=1:
                    assert_true(len(star)==1 and packet[0].target==star[0].target and packet[0].i==star[0].i and packet[0].j==star[0].j)
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
                        assert_true(overlaps==b4_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                verify_b4_packet(tables,kind,k,t,packet[0])
            if t==0:
                assert_true(2*n+4==A+2)
            elif t==1:
                assert_true(2*n+4==A+1)
                assert_true(member_transport(-1,k,n,d,b4_source(0),0,2*n+4)==e2_source(3))
            else:
                verify_b4_packet(tables,0,k,t,BoundaryEdge(0,2*n+4,b4_source(4)))
    for found in attained:
        assert_true(found)
    # Equal total counts do not permit dropping the exact high/low index split.
    assert_true(not b4_child_allowed(0,5,4,0,2*5+3*4+9))
    assert_true(b4_child_allowed(0,0,4,0,3*4+9))
    var failed=False
    try:
        certify_b4_children(True)
    except:
        failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:
            _=b4_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (5 if mode==4 else 0),10 if mode==5 else 0)
        except:
            failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:
        var disjoint=member_transport(-1,0,3,5,b4_source(0),0,0)
        verify_b4_packet(floor,0,0,0,BoundaryEdge(0,0,disjoint))
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _transition(qx_const(4),qx_const(7),qx_const(1),0,FIRST,qx_const(0),RUN,qx_const(12),b4_source(4))
    except:
        failed=True
    assert_true(failed) # t=1: ordinal 2n+4 is LAST x, not RUN y.
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,14,5,4))
    var cache=Dict[CubicElt,Int]()
    var wrong=BoundaryLabel(0,2,-1,-2,5)
    assert_true(in_b4_image(wrong) and interior_overlap_cached(tables,cache,geometric_state(tables,wrong)))
    failed=False
    try:
        verify_b4_packet(tables,0,0,2,BoundaryEdge(0,14,wrong))
    except:
        failed=True
    assert_true(failed) # right types and interior image label, wrong full offset
    for mode in range(4):
        var packet=b4_path(0,0,2)
        if mode==0:
            packet[0]=BoundaryEdge(0,14,wrong)
        elif mode==1:
            packet[1]=BoundaryEdge(0,4,b4_source(4))
        elif mode==2:
            packet[len(packet)-1]=BoundaryEdge(2,1,BoundaryLabel(2,0,0,0,0))
        else:
            _=packet.pop()
        failed=False
        try:
            verify_b4_path(tables,0,0,2,packet)
        except:
            failed=True
        assert_true(failed)
    for mode in range(3):
        var star=b4_child_star(0,0,2)
        if mode==0:
            _=star.pop()
        elif mode==1:
            star[1]=star[0]
        else:
            star.append(star[0])
        failed=False
        try:
            verify_b4_star(tables,0,0,2,star)
        except:
            failed=True
        assert_true(failed)
    failed=False
    try:
        _=b4_child_star(2,0,0)
    except:
        failed=True
    assert_true(failed) # a companion exit must not become a complete-star claim
    print("CLASS_A_BOUNDARY_B4_FINITE members=56 source_cells=112 path_source_cells=336", "pairs",pairs,"accepted",accepted,"B4_path_edges",b4_edges,"companion_path_edges",companion_edges,"path_edges",path_edges,"union_labels=32", "candidate41_registered_before=23_after=25_unregistered=16", "image_registered_stars=2_exits=6", "BH=false")
    require_contract("class-A minus B4/reversal complete nine-kind stars with exact inherited half separator, max(1,2t-1) occurrences, 32-label image and all literal-pair Parikh/Perron checks; actual R3 ancestry and <=5-edge exits split t=0/1/>=2; D0/F4 uniform selected exits only, separate 41-source and 32-image star/exit registries, singleton-child productivity proved on t<=1, all B4 children outside S41; corrupt identities, invalid indices/types/parameters, disjoint pairs, wrong interior labels, broken paths, false coincidence and incomplete/duplicate stars refused; no companion complete stars, all-t all-child productivity or global BH/PSC promotion")
