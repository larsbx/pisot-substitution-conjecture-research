"""Complete E6 stars, every indexed first-choice walk and n=3 cycle."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_b5_children import b5_source, b5_image
from psc.class_a_boundary_e6_children import certify_e6_children, e6_source, e6_star_interface, e6_exit_interface, e6_child_allowed, e6_child_star, e6_image, in_e6_image, verify_e6_packet, verify_e6_star, e6_path, verify_e6_path, e6_child_tail, e6_walk, verify_e6_walk
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_e6_children()
    var candidate=enlarged_candidate(True)
    var before=0
    var after=0
    var exits_before=0
    var exits_after=0
    for w in candidate:
        before+=1 if e6_star_interface(w)!=0 else 0
        after+=1 if e6_star_interface(w,True)!=0 else 0
        exits_before+=1 if e6_exit_interface(w)!=0 else 0
        exits_after+=1 if e6_exit_interface(w,True)!=0 else 0
    assert_true(before==29 and after==31 and exits_before==33 and exits_after==33)
    var old_stars=0
    for w in b5_image():old_stars+=1 if e6_star_interface(w,True)!=0 else 0
    assert_true(old_stars==20)
    var image=e6_image()
    var attained=List[Bool]()
    var image_stars=0
    var image_exits=0
    assert_true(len(image)==16)
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_e6_image(image[z]))
        image_stars+=1 if e6_star_interface(image[z],True)!=0 else 0
        image_exits+=1 if e6_exit_interface(image[z],True)!=0 else 0
        for j in range(z):assert_true(image[z]!=image[j])
    assert_true(image_stars==10 and image_exits==16)
    for kind in range(2,8):
        assert_true(e6_star_interface(e6_source(kind),True)==0)
        assert_true(e6_exit_interface(e6_source(kind),True)==38+kind//2)
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in range(-2,3):
                    for y in range(-5,6):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:listed=listed or w==v
                        assert_true(listed==in_e6_image(w))
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
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            var local_attained=List[Bool]()
            for _ in image:local_attained.append(False)
            for kind in range(8):
                var path=e6_path(kind,k,t)
                verify_e6_path(tables,kind,k,t,path)
                var length=2
                if kind//2==1:length=8 if n==3 else 4
                elif kind//2==2:length=3
                assert_true(len(path)==length)
                path_edges+=len(path)
                if kind>=2:continue
                var w=e6_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var star=e6_child_star(kind,k,t)
                verify_e6_star(tables,kind,k,t,star)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(A+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    var suffix=e6_child_tail(edge.target,k,t)
                    var walk=e6_walk(kind,k,t,edge)
                    verify_e6_walk(tables,kind,k,t,edge,walk)
                    assert_true(len(suffix)<=8 and len(walk)==len(suffix)+1 and len(walk)<=9)
                    max_walk=max(max_walk,len(walk));walk_edges+=len(walk)
                    var found=False
                    for z in range(len(image)):
                        if image[z]==edge.target:
                            attained[z]=True
                            local_attained[z]=True
                            found=True
                    assert_true(found)
                for i in range(A+2):
                    for j in range(A+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==e6_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(A+2)+j in seen))
                        if overlap:accepted+=1
                verify_e6_packet(tables,kind,k,t,path[0])
            for found in local_attained:assert_true(found)
            verify_e6_packet(tables,0,k,t,BoundaryEdge(A+1,d-2,e6_source(4)))
            assert_true(not in_e6_image(b5_source(0)))
            for w in candidate:assert_true(w!=e6_source(4))
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,member_transport(-1,k,n,d,e6_source(0),n+1,0))))
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,member_transport(-1,k,n,d,e6_source(0),A+1,d))))
            if n==3:
                for flip in range(2):
                    verify_member_edge(tables,-1,k,n,d,b5_source(flip),0 if flip==0 else A+1,A+1 if flip==0 else 0,e6_source(flip))
    for found in attained:assert_true(found)
    assert_true(max_walk==9)
    var failed=False
    try:certify_e6_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:
            _=e6_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),10 if mode==5 else 0)
        except:failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:verify_e6_packet(floor,0,0,0,BoundaryEdge(5,0,BoundaryLabel(2,0,0,1,-2)))
    except:failed=True
    assert_true(failed)
    var star=e6_child_star(0,0,0)
    star[len(star)-1]=star[0]
    failed=False
    try:verify_e6_star(floor,0,0,0,star)
    except:failed=True
    assert_true(failed)
    var edge=BoundaryEdge(9,2,e6_source(2))
    var walk=e6_walk(0,0,0,edge)
    assert_true(len(walk)==9)
    walk[len(walk)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:verify_e6_walk(floor,0,0,0,edge,walk)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=e6_child_tail(BoundaryLabel(2,2,0,0,0),0,0)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_E6_FINITE members=56", "pairs",pairs,"accepted",accepted,"path_edges",path_edges,"all_child_walk_edges",walk_edges,"max_walk",max_walk,"union_labels=16", "BH=false")
    require_contract("class-A minus E6/reversal: complete 2d-1 indexed stars and exact 16-label union, all literal pairs checked by full Parikh/Perron geometry, inherited two-edge source exits, uniform tails for all image labels and every first-choice walk <=9 including D4 n3 exception; genuine n3 cycle and uniform escapes retained; wrong interior offsets, malformed stars/walks, corrupted identities and invalid inputs refused; no companion stars, closed carrier or global BH")
