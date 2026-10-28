"""B5 complete stars, every actual first choice and guarded finite endpoints."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_y4_children import y4_source
from psc.class_a_boundary_r4_children import _transition
from psc.class_a_boundary_occurrences import FIRST, RUN, LAST
from psc.param_poly import qx_const
from psc.class_a_boundary_b5_children import certify_b5_children, b5_source, b5_star_interface, b5_exit_interface, b5_child_allowed, b5_child_star, b5_image, in_b5_image, verify_b5_packet, verify_b5_star, b5_path, verify_b5_path, b5_child_tail, b5_walk, verify_b5_walk
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_b5_children()
    var candidate=enlarged_candidate(True)
    var stars_before=0
    var stars_after=0
    var exits_before=0
    var exits_after=0
    for w in candidate:
        stars_before+=1 if b5_star_interface(w)!=0 else 0
        stars_after+=1 if b5_star_interface(w,True)!=0 else 0
        exits_before+=1 if b5_exit_interface(w)!=0 else 0
        exits_after+=1 if b5_exit_interface(w,True)!=0 else 0
    assert_true(stars_before==29 and stars_after==29 and exits_before==31 and exits_after==33)
    var image=b5_image()
    var attained=List[Bool]()
    var image_stars=0
    var image_exits=0
    assert_true(len(image)==24)
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_b5_image(image[z]))
        image_stars+=1 if b5_star_interface(image[z],True)!=0 else 0
        image_exits+=1 if b5_exit_interface(image[z],True)!=0 else 0
        for j in range(z):assert_true(image[z]!=image[j])
    assert_true(image_stars==18 and image_exits==22)
    for kind in range(2,6):
        assert_true(b5_star_interface(b5_source(kind),True)==0)
        assert_true(b5_exit_interface(b5_source(kind),True)==(38 if kind<4 else 0))
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in range(-2,3):
                    for y in range(-4,5):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:listed=listed or w==v
                        assert_true(listed==in_b5_image(w))
    var pairs=0
    var accepted=0
    var path_edges=0
    var walk_edges=0
    var max_walk=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            for kind in range(6):
                if kind>=4 and n!=4:continue
                var path=b5_path(kind,k,t)
                verify_b5_path(tables,kind,k,t,path)
                assert_true(len(path)==(3 if kind>=4 else 2))
                path_edges+=len(path)
                if kind>=2:continue
                var w=b5_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                verify_member_edge(tables,-1,k,n,d,y4_source(2+kind),0 if kind==1 else t+1,t+1 if kind==1 else 0,w)
                var R=N if kind==0 else A
                var B=A if kind==0 else N
                var star=b5_child_star(kind,k,t)
                verify_b5_star(tables,kind,k,t,star)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    var walk=b5_walk(kind,k,t,edge)
                    verify_b5_walk(tables,kind,k,t,edge,walk)
                    assert_true(len(walk)>=2 and len(walk)<=8)
                    max_walk=max(max_walk,len(walk))
                    walk_edges+=len(walk)
                    var found=False
                    for z in range(len(image)):
                        if image[z]==edge.target:
                            attained[z]=True
                            found=True
                    assert_true(found)
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==b5_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(B+2)+j in seen))
                        if overlap:accepted+=1
                verify_b5_packet(tables,kind,k,t,path[0])
    for found in attained:assert_true(found)
    assert_true(max_walk==8)
    var failed=False
    try:
        certify_b5_children(True)
    except:
        failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:
            _=b5_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (4 if mode==4 else 0),11 if mode==5 else 0)
        except:
            failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var packet=b5_path(0,0,0)
    packet[0]=BoundaryEdge(0,8,BoundaryLabel(0,2,0,1,-2))
    failed=False
    try:
        verify_b5_path(floor,0,0,0,packet)
    except:
        failed=True
    assert_true(failed)
    var edge=BoundaryEdge(0,9,b5_source(2))
    var walk=b5_walk(0,0,0,edge)
    walk[len(walk)-1]=BoundaryEdge(2,1,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:
        verify_b5_walk(floor,0,0,0,edge,walk)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=b5_path(4,0,0)
    except:
        failed=True
    assert_true(failed) # E7 is n=4-only, never a uniform companion exit
    failed=False
    try:
        _transition(qx_const(3),qx_const(5),b5_source(0),FIRST,qx_const(0),RUN,qx_const(9),BoundaryLabel(0,2,0,1,0))
    except:
        failed=True
    assert_true(failed) # actual LAST x endpoint has the same offset, different type
    var star=b5_child_star(0,0,0)
    star[len(star)-1]=star[0]
    failed=False
    try:
        verify_b5_star(floor,0,0,0,star)
    except:
        failed=True
    assert_true(failed)
    assert_true(b5_star_interface(b5_source(0))==0 and b5_star_interface(b5_source(0),True)==37)
    print("CLASS_A_BOUNDARY_B5_FINITE members=56", "pairs",pairs,"accepted",accepted,"path_edges",path_edges,"all_child_walk_edges",walk_edges,"max_walk",max_walk,"union_labels=24", "BH=false")
    require_contract("class-A minus B5 and reversal: complete 2n-1 indexed stars, 24-label image, exact all-pair Parikh/Perron checks, uniform two-edge source/E6 exits and every actual first-choice walk <=8; E7 endpoints n=4-only, actual LAST types, wrong intermediates/terminals, corrupted identities and malformed stars refused; no uniform E7 exit, closed carrier or global BH")
