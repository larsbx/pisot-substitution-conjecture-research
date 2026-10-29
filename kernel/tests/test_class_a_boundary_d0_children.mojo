"""Every D0 word pair, true small endpoints, all-child walks and B5 equality."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_d0_children import certify_d0_children, d0_source, d0_image, in_d0_image, d0_star_interface, d0_exit_interface, d0_child_allowed, d0_child_star, d0_child_tail, d0_path, d0_walk, verify_d0_packet, verify_d0_star, verify_d0_path, verify_d0_walk
from psc.class_a_boundary_e7_children import e7_source, e7_path, e7_image, verify_e7_steps
from psc.class_a_boundary_b5_children import b5_source, b5_image, b5_child_star
from psc.class_a_boundary_p3_children import p3_source
from psc.class_a_boundary_y4_children import y4_source
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_u_children import reverse_label
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_d0_children()
    for kind in range(2):
        assert_true(d0_star_interface(d0_source(kind))==0 and d0_star_interface(d0_source(kind),True)==20)
        assert_true(d0_exit_interface(d0_source(kind))==20 and d0_exit_interface(d0_source(kind),True)==20)
        assert_true(d0_source(kind)!=b5_source(1-kind))
    var candidate=enlarged_candidate(True)
    var stars=0
    var exits=0
    for w in candidate:
        assert_true(d0_star_interface(w)==d0_star_interface(w,True))
        stars+=1 if d0_star_interface(w,True)!=0 else 0
        exits+=1 if d0_exit_interface(w,True)!=0 else 0
        assert_true(w!=d0_source(0) and w!=d0_source(1))
    assert_true(stars==33 and exits==35)
    var image=d0_image()
    var attained=List[Bool]()
    var image_stars=0
    var image_exits=0
    assert_true(len(image)==24)
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_d0_image(image[z]))
        var found=False
        for v in b5_image():found=found or v==image[z]
        assert_true(found)
        for j in range(z):assert_true(image[z]!=image[j])
        image_stars+=1 if d0_star_interface(image[z],True)!=0 else 0
        image_exits+=1 if d0_exit_interface(image[z],True)!=0 else 0
    assert_true(image_stars==22 and image_exits==24)
    var old_e7_stars=0
    var new_e7_stars=0
    var e7_exits=0
    for w in e7_image():
        old_e7_stars+=1 if d0_star_interface(w)!=0 else 0
        new_e7_stars+=1 if d0_star_interface(w,True)!=0 else 0
        e7_exits+=1 if d0_exit_interface(w,True)!=0 else 0
    assert_true(old_e7_stars==6 and new_e7_stars==8 and e7_exits==8)
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in range(-3,4):
                    for y in range(-4,5):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:listed=listed or w==v
                        assert_true(listed==in_d0_image(w))
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
            for kind in range(2):
                var w=d0_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var packet=d0_path(kind,k,t)
                verify_d0_path(tables,kind,k,t,packet)
                assert_true(len(packet)==2)
                path_edges+=len(packet)
                var star=d0_child_star(kind,k,t)
                verify_d0_star(tables,kind,k,t,star)
                var other=b5_child_star(1-kind,k,t)
                assert_true(len(star)==len(other))
                var other_edges=Dict[Int,BoundaryLabel]()
                for edge in other:other_edges[edge.i*(A+2)+edge.j]=edge.target
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(A+2)+edge.j
                    assert_true(key not in seen and key in other_edges and edge.target==other_edges[key])
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    for z in range(len(image)):
                        if image[z]==edge.target:attained[z]=True
                    var walk=d0_walk(kind,k,t,edge)
                    verify_d0_walk(tables,kind,k,t,edge,walk)
                    walk_edges+=len(walk)
                    max_walk=max(max_walk,len(walk))
                for i in range(A+2):
                    for j in range(A+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==d0_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(A+2)+j in seen))
                        if overlap:accepted+=1
                if n<=4:
                    var endpoint=member_transport(-1,k,n,d,w,A+1 if kind==0 else 0,0 if kind==0 else A+1)
                    assert_true(endpoint==reverse_label(b5_source(2+kind) if n==3 else e7_source(kind)))
                # The extra bottom runs in x/x are actual, but strictly disjoint.
                var a=A+1 if kind==0 else n
                var b=n if kind==0 else A+1
                var extra=member_transport(-1,k,n,d,w,a,b)
                var last=member_transport(-1,k,n,d,b5_source(1-kind),a,b)
                assert_true(extra!=last and not interior_overlap_cached(tables,cache,geometric_state(tables,extra)))
                assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,last)))
            # The uniform selected RF reaches T; T's other edge escapes the image.
            verify_member_edge(tables,-1,k,n,d,p3_source(2),0,1,y4_source(0))
            assert_true(not in_d0_image(y4_source(0)))
            # At k=1,t=0, a four-cycle coexists with the inherited C exits.
            if k==1 and t==0:
                for flip in range(2):
                    verify_d0_packet(tables,flip,k,t,BoundaryEdge(A+1 if flip==0 else 0,0 if flip==0 else A+1,e7_source(1-flip)))
                    verify_e7_steps(tables,e7_source(1-flip),k,t,e7_path(1-flip,k,t),e7_path(1-flip,k,t))
                    assert_true(e7_path(1-flip,k,t)[0].target==d0_source(1-flip))
    for found in attained:assert_true(found)
    assert_true(max_walk==8)
    var failed=False
    try:certify_d0_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:_=d0_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),10 if mode==5 else 0)
        except:failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    # A+1 is LAST x, while the fabricated RUN y target has the same offset.
    failed=False
    try:verify_d0_packet(floor,0,0,0,BoundaryEdge(9,0,BoundaryLabel(2,0,0,-1,0)))
    except:failed=True
    assert_true(failed)
    failed=False
    try:verify_d0_packet(floor,0,0,0,BoundaryEdge(7,0,p3_source(2)))
    except:failed=True
    assert_true(failed) # legal strict pair but wrong interior target, same types
    var star=d0_child_star(0,0,0)
    star[len(star)-1]=star[0]
    failed=False
    try:verify_d0_star(floor,0,0,0,star)
    except:failed=True
    assert_true(failed) # duplicate plus omission, same cardinality
    var edge=d0_child_star(0,0,0)[0]
    var walk=d0_walk(0,0,0,edge)
    walk[len(walk)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:verify_d0_walk(floor,0,0,0,edge,walk)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=d0_child_tail(BoundaryLabel(2,2,0,0,0),0,0)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_D0_FINITE members=56", "pairs",pairs,"accepted",accepted,"source_path_edges",path_edges,"all_child_walk_edges",walk_edges,"max_walk",max_walk,"union_labels=24", "BH=false")
    require_contract("class-A minus existing D0/U7 and reversal: nine-kind complete stars, 2n-1 indexed count, 24-label chamber union equal to B5 image, every literal pair checked in strict full typed Parikh/Perron geometry, all actual first choices have selected walks <=8, inherited two-edge source exit and existing <=7 image tails reused; n3/n4 LAST x replaces fictitious RUN y, disjoint extra bottom x runs versus actual LAST c in R(B5), same indexed surviving stars without source identity, four-cycle at k1t0 with exits, wrong types/intermediates, malformed stars/walks and corrupt identities refused; no new companion stars/exits, every-continuation termination, closed carrier or global BH")
