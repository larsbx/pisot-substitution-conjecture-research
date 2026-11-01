"""E7 complete indexed stars, exact half-chambers, source exits and B5 tails."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_h3_children import chain_source, alpha_high
from psc.class_a_boundary_b5_children import b5_image, b5_path
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_e7_children import certify_e7_children, e7_source, e7_star_interface, e7_exit_interface, e7_child_allowed, e7_child_star, e7_image, in_e7_image, verify_e7_packet, verify_e7_star, e7_path, verify_e7_path, e7_registered_tail, e7_uniform_b5_tail, verify_e7_steps
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_e7_children()
    assert_true(not alpha_high(0,0) and not alpha_high(1,1) and alpha_high(2,2))
    var candidate=enlarged_candidate(True)
    var before=0
    var after=0
    var exits_before=0
    var exits_after=0
    for w in candidate:
        before+=1 if e7_star_interface(w)!=0 else 0
        after+=1 if e7_star_interface(w,True)!=0 else 0
        exits_before+=1 if e7_exit_interface(w)!=0 else 0
        exits_after+=1 if e7_exit_interface(w,True)!=0 else 0
    assert_true(before==31 and after==33 and exits_before==33 and exits_after==35)
    var old_stars=0
    var old_exits=0
    for w in b5_image():
        old_stars+=1 if e7_star_interface(w,True)!=0 else 0
        old_exits+=1 if e7_exit_interface(w,True)!=0 else 0
    assert_true(old_stars==22 and old_exits==24)
    var image=e7_image()
    var attained=List[Bool]()
    var image_stars=0
    var image_exits=0
    assert_true(len(image)==32)
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_e7_image(image[z]))
        image_stars+=1 if e7_star_interface(image[z],True)!=0 else 0
        image_exits+=1 if e7_exit_interface(image[z],True)!=0 else 0
        for w in candidate:assert_true(w!=image[z])
        for j in range(z):assert_true(image[z]!=image[j])
    assert_true(image_stars==6 and image_exits==8)
    for kind in range(2,6):
        assert_true(e7_star_interface(e7_source(kind),True)==(0 if kind<4 else 18))
        assert_true(e7_exit_interface(e7_source(kind),True)==(20 if kind<4 else 18))
    for top in range(3):
        for bottom in range(3):
            for x in range(-3,4):
                for c in range(-3,4):
                    for y in range(-9,10):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:listed=listed or w==v
                        assert_true(listed==in_e7_image(w))
    var pairs=0
    var accepted=0
    var path_edges=0
    var registered_edges=0
    var b5_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            for kind in range(6):
                var packet=e7_path(kind,k,t)
                verify_e7_path(tables,kind,k,t,packet)
                var length=3 if t<=1 else 5
                if kind//2==1:length=2
                elif kind//2==2:length=4 if n==3 else 2
                assert_true(len(packet)==length)
                path_edges+=len(packet)
                if kind>=2:continue
                var w=e7_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var star=e7_child_star(kind,k,t)
                verify_e7_star(tables,kind,k,t,star)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(A+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    var found=False
                    for z in range(len(image)):
                        if image[z]==edge.target:
                            attained[z]=True;found=True
                    assert_true(found)
                for i in range(A+2):
                    for j in range(A+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==e7_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(A+2)+j in seen))
                        if overlap:accepted+=1
                verify_e7_packet(tables,kind,k,t,packet[0])
                if t<=1:
                    assert_true(len(star)==1 and star[0].i==packet[0].i and star[0].j==packet[0].j and star[0].target==packet[0].target)
                if n==4:
                    var old=b5_path(4+kind,k,t)
                    verify_e7_steps(tables,w,k,t,packet,old)
            for w in image:
                if e7_exit_interface(w,True)!=0:
                    var tail=e7_registered_tail(w,k,t)
                    verify_e7_steps(tables,w,k,t,tail,e7_registered_tail(w,k,t))
                    registered_edges+=len(tail)
            for w in b5_image():
                var tail=e7_uniform_b5_tail(w,k,t)
                verify_e7_steps(tables,w,k,t,tail,e7_uniform_b5_tail(w,k,t))
                assert_true(len(tail)<=7)
                b5_edges+=len(tail)
            assert_true(not in_e7_image(chain_source(4)))
            if t==4 and (k==4 or k==5):
                var low=BoundaryLabel(2,2,2,2,-6)
                var high=BoundaryLabel(0,0,1,2,-7)
                assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,low))==(k==5))
                assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,high))==(k==4))
            if t==1:verify_e7_packet(tables,0,k,t,BoundaryEdge(2*n+4,0,e7_source(4)))
    for found in attained:assert_true(found)
    var failed=False
    try:certify_e7_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:
            _=e7_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),10 if mode==5 else 0)
        except:failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:verify_e7_packet(floor,0,0,0,BoundaryEdge(9,0,e7_source(4)))
    except:failed=True
    assert_true(failed) # wrong offset, despite an interior image target of same types
    var star=e7_child_star(0,0,0)
    star.append(star[0])
    failed=False
    try:verify_e7_star(floor,0,0,0,star)
    except:failed=True
    assert_true(failed)
    var packet=e7_path(0,0,0)
    packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:verify_e7_path(floor,0,0,0,packet)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=e7_registered_tail(BoundaryLabel(2,0,1,2,-5),0,0)
    except:failed=True
    assert_true(failed) # unknown productive status is not an empty tail
    failed=False
    try:_=e7_uniform_b5_tail(BoundaryLabel(2,2,0,0,0),0,0)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_E7_FINITE members=56", "pairs",pairs,"accepted",accepted,"path_edges",path_edges,"registered_image_tail_edges",registered_edges,"uniform_B5_image_tail_edges",b5_edges,"union_labels=32", "BH=false")
    require_contract("class-A minus E7/reversal: exact half-chamber nine-kind stars and max(1,2t-1) indexed count, 32-label chamber union, all word pairs checked in strict full Parikh/Perron geometry, uniform 3/3/5-edge source exits, existing D0/U7 exit and Dxx/V7 with a n>=4 shortcut, singleton-child productivity only t<=1; B5 image has 24 uniform tails; half-chamber disjoint source controls, true t1 LAST x, n3 B2 terminal exception, wrong targets/terminals, malformed stars and corrupt identities refused; no all-t all-child result, closed carrier or global BH")
