"""W9 actual word-pair, endpoint multiplicity and every-first-choice contract."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_w9_children import certify_w9_children, w9_source, w9_companion, w9_image, in_w9_image, w9_count, w9_child_allowed, w9_child_star, w9_path, w9_companion_path, w9_child_tail, w9_child_walk, verify_w9_packet, verify_w9_star, verify_w9_path, verify_w9_walk, w9_star_interface, w9_exit_interface
from psc.class_a_boundary_h9_children import h9_source, h9_image
from psc.class_a_boundary_p9_children import p9_companion
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_e7_children import verify_e7_steps
from psc.class_a_boundary_u_children import reverse_label
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_w9_children()
    var stars=0
    var exits=0
    for w in enlarged_candidate(True):
        assert_true(w9_star_interface(w)==w9_star_interface(w,True))
        assert_true(w9_exit_interface(w)==w9_exit_interface(w,True))
        stars+=1 if w9_star_interface(w,True)!=0 else 0
        exits+=1 if w9_exit_interface(w,True)!=0 else 0
    assert_true(stars==33 and exits==35)
    var old_h9=0
    var new_h9=0
    for w in h9_image():
        old_h9+=1 if w9_star_interface(w)!=0 else 0
        new_h9+=1 if w9_star_interface(w,True)!=0 else 0
    assert_true(old_h9==2 and new_h9==4)
    var image=w9_image()
    var attained=List[Bool]()
    stars=0;exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_w9_image(image[z]))
        for j in range(z):assert_true(image[z]!=image[j])
        stars+=1 if w9_star_interface(image[z],True)!=0 else 0
        exits+=1 if w9_exit_interface(image[z],True)!=0 else 0
    assert_true(len(image)==16 and stars==2 and exits==16)
    for kind in range(2):
        assert_true(w9_star_interface(w9_source(kind))==0 and w9_star_interface(w9_source(kind),True)==64)
        assert_true(w9_exit_interface(w9_source(kind))==64)
    for kind in range(12):
        assert_true(w9_star_interface(w9_companion(kind),True)==0)
        assert_true(w9_exit_interface(w9_companion(kind))==0 and w9_exit_interface(w9_companion(kind),True)==69+kind//2)
    var pairs=0
    var accepted=0
    var path_edges=0
    var companion_edges=0
    var walk_edges=0
    var image_tail_edges=0
    var max_walk=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            var member_found=List[Bool]()
            for z in range(len(image)):member_found.append(False)
            for kind in range(2):
                var w=w9_source(kind)
                assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,w)))
                var star=w9_child_star(kind,k,t)
                verify_w9_star(tables,kind,k,t,star)
                assert_true(len(star)==4*n+1)
                var path=w9_path(kind,k,t)
                verify_w9_path(tables,kind,k,t,path)
                assert_true(len(path)==4)
                path_edges+=len(path)
                if k==0:
                    verify_member_edge(tables,-1,k,n,d,h9_source(1-kind),0,0,w)
                    verify_member_edge(tables,-1,k,n,d,h9_source(1-kind),A+1,A+1,w)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(A+2)+edge.j
                    assert_true(key not in seen);seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    for z in range(len(image)):
                        if image[z]==edge.target:
                            attained[z]=True
                            member_found[z]=True
                    var walk=w9_child_walk(kind,k,t,edge)
                    verify_w9_walk(tables,kind,k,t,edge,walk)
                    walk_edges+=len(walk);max_walk=max(max_walk,len(walk))
                var source=geometric_state(tables,w)
                for i in range(A+2):
                    for j in range(A+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==w9_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(A+2)+j in seen))
                        if overlap:accepted+=1
            for found in member_found:assert_true(found)
            for kind in range(12):
                var packet=w9_companion_path(kind,k,t)
                verify_e7_steps(tables,w9_companion(kind),k,t,packet,w9_companion_path(kind,k,t))
                assert_true(len(packet)==(5 if kind//2==3 else (2 if kind//2==2 or kind//2==5 else 3)))
                companion_edges+=len(packet)
            for w in image:
                var packet=w9_child_tail(w,k,t)
                verify_e7_steps(tables,w,k,t,packet,w9_child_tail(w,k,t))
                image_tail_edges+=len(packet)
    assert_true(max_walk==6)
    for found in attained:assert_true(found)
    var failed=False
    try:certify_w9_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:_=w9_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),10 if mode==5 else 0)
        except:failed=True
        assert_true(failed)
    failed=False
    try:_=w9_count(0,2_400_000_000_000_000_000)
    except:failed=True
    assert_true(failed) # A fits, but the indexed count 4n+1 overflows.
    failed=False
    try:_=w9_child_star(0,0,2_400_000_000_000_000_000)
    except:failed=True
    assert_true(failed) # Refuse before trying to allocate the huge star.
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    for kind in [2,8]:
        var endpoint=member_transport(-1,0,3,5,w9_companion(kind),1,3)
        assert_true(endpoint==BoundaryLabel(2,1,0,0,0))
        verify_member_edge(floor,-1,0,3,5,w9_companion(kind),1,3,endpoint)
        failed=False
        try:verify_member_edge(floor,-1,0,3,5,w9_companion(kind),1,3,BoundaryLabel(2,2,0,0,0))
        except:failed=True
        assert_true(failed) # nominal bottom RUN3 is actual LAST c at n=3.
    var star=w9_child_star(0,0,0)
    star[len(star)-1]=star[0]
    failed=False
    try:verify_w9_star(floor,0,0,0,star)
    except:failed=True
    assert_true(failed) # Same-cardinality duplicate/omission changes the indexed star.
    failed=False
    try:verify_w9_packet(floor,0,0,0,BoundaryEdge(3,0,p9_companion(2)))
    except:failed=True
    assert_true(failed) # matching types and strict interior, wrong offset
    var packet=w9_path(0,0,0)
    packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:verify_w9_path(floor,0,0,0,packet)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=w9_child_tail(BoundaryLabel(2,2,0,0,0),0,0)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_W9_FINITE members=56", "pairs",pairs,"accepted",accepted,"source_path_edges",path_edges,"companion_edges",companion_edges,"all_child_walk_edges",walk_edges,"all_image_tail_edges",image_tail_edges,"max_walk",max_walk,"memberwise_image_labels",len(image),"BH=false")
    require_contract("class-A minus W9/reversal complete nine-kind indexed stars, count4n+1 and constant16-label memberwise image; every actual first choice has a selected typed completion<=6 attained, inherited source exit4 and six new full-cone exits with lengths3/3/2/5/3/2; every literal word pair, reversal, all image tails, actual LAST c versus fictitious RUN and unequal-type zero offset, same-type wrong strict targets, duplicate/omission stars, corrupt identities, count overflow before allocation and unknown tails checked; no companion stars, every-continuation termination, forward closure or global BH")
