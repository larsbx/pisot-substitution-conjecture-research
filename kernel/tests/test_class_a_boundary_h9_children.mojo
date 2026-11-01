"""H9 actual word-pair, endpoint multiplicity and every-first-choice contract."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_h9_children import certify_h9_children, h9_source, h9_companion, h9_image, in_h9_image, h9_count, h9_child_allowed, h9_child_star, h9_path, h9_companion_path, h9_child_tail, h9_child_walk, verify_h9_packet, verify_h9_star, verify_h9_path, verify_h9_walk, h9_star_interface, h9_exit_interface
from psc.class_a_boundary_p9_children import p9_source, p9_image, p9_companion
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_e7_children import verify_e7_steps
from psc.class_a_boundary_u_children import reverse_label
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_h9_children()
    var stars=0
    var exits=0
    for w in enlarged_candidate(True):
        assert_true(h9_star_interface(w)==h9_star_interface(w,True))
        assert_true(h9_exit_interface(w)==h9_exit_interface(w,True))
        stars+=1 if h9_star_interface(w,True)!=0 else 0
        exits+=1 if h9_exit_interface(w,True)!=0 else 0
    assert_true(stars==33 and exits==35)
    var old_p9=0
    var new_p9=0
    for w in p9_image():
        old_p9+=1 if h9_star_interface(w)!=0 else 0
        new_p9+=1 if h9_star_interface(w,True)!=0 else 0
    assert_true(old_p9==2 and new_p9==4)
    var image=h9_image()
    var attained=List[Bool]()
    stars=0;exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_h9_image(image[z]))
        for j in range(z):assert_true(image[z]!=image[j])
        stars+=1 if h9_star_interface(image[z],True)!=0 else 0
        exits+=1 if h9_exit_interface(image[z],True)!=0 else 0
    assert_true(len(image)==20 and stars==2 and exits==20)
    for kind in range(2):
        assert_true(h9_star_interface(h9_source(kind))==0 and h9_star_interface(h9_source(kind),True)==63)
        assert_true(h9_exit_interface(h9_source(kind))==63)
    for kind in range(6):
        assert_true(h9_star_interface(h9_companion(kind),True)==0)
        assert_true(h9_exit_interface(h9_companion(kind))==0 and h9_exit_interface(h9_companion(kind),True)==66+kind//2)
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
            for kind in range(2):
                var w=h9_source(kind)
                assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,w)))
                var star=h9_child_star(kind,k,t)
                verify_h9_star(tables,kind,k,t,star)
                assert_true(len(star)==(2*A+3 if k<=1 else 2*A-2*k+5))
                var path=h9_path(kind,k,t)
                verify_h9_path(tables,kind,k,t,path)
                assert_true(len(path)==6)
                path_edges+=len(path)
                if k==0:verify_member_edge(tables,-1,k,n,d,p9_source(kind),0,0,w)
                if k<=1:
                    var first=member_transport(-1,k,n,d,w,0,0)
                    var last=member_transport(-1,k,n,d,w,A+1,A+1)
                    assert_true(first==last)
                    verify_h9_packet(tables,kind,k,t,BoundaryEdge(0,0,first))
                    verify_h9_packet(tables,kind,k,t,BoundaryEdge(A+1,A+1,last))
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(A+2)+edge.j
                    assert_true(key not in seen);seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    for z in range(len(image)):
                        if image[z]==edge.target:attained[z]=True
                    var walk=h9_child_walk(kind,k,t,edge)
                    verify_h9_walk(tables,kind,k,t,edge,walk)
                    walk_edges+=len(walk);max_walk=max(max_walk,len(walk))
                var source=geometric_state(tables,w)
                for i in range(A+2):
                    for j in range(A+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==h9_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(A+2)+j in seen))
                        if overlap:accepted+=1
            for kind in range(6):
                var packet=h9_companion_path(kind,k,t)
                verify_e7_steps(tables,h9_companion(kind),k,t,packet,h9_companion_path(kind,k,t))
                assert_true(len(packet)==(4 if kind<2 else (3 if kind<4 else 6)))
                companion_edges+=len(packet)
            for w in image:
                var packet=h9_child_tail(w,k,t)
                verify_e7_steps(tables,w,k,t,packet,h9_child_tail(w,k,t))
                image_tail_edges+=len(packet)
    assert_true(max_walk==7)
    for found in attained:assert_true(found)
    var failed=False
    try:certify_h9_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:_=h9_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),10 if mode==5 else 0)
        except:failed=True
        assert_true(failed)
    failed=False
    try:_=h9_count(0,2_000_000_000_000_000_000)
    except:failed=True
    assert_true(failed) # A fits, but the indexed count 2A+3 overflows.
    failed=False
    try:_=h9_child_star(0,0,2_000_000_000_000_000_000)
    except:failed=True
    assert_true(failed) # Refuse before trying to allocate the huge star.
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var endpoint=member_transport(-1,0,3,5,h9_companion(0),0,9)
    assert_true(endpoint==BoundaryLabel(0,0,0,1,-1))
    verify_member_edge(floor,-1,0,3,5,h9_companion(0),0,9,endpoint)
    failed=False
    try:verify_member_edge(floor,-1,0,3,5,h9_companion(0),0,9,BoundaryLabel(0,2,0,1,-1))
    except:failed=True
    assert_true(failed) # nominal d+4 is actual LAST x, not RUN y, at n=3.
    var star=h9_child_star(0,0,0)
    star[len(star)-1]=star[0]
    failed=False
    try:verify_h9_star(floor,0,0,0,star)
    except:failed=True
    assert_true(failed) # FF and LL share a target but cannot share an index.
    failed=False
    try:verify_h9_packet(floor,0,0,0,BoundaryEdge(0,0,BoundaryLabel(0,0,-1,-3,4)))
    except:failed=True
    assert_true(failed) # matching types and strict interior, wrong offset
    var packet=h9_path(0,0,0)
    packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:verify_h9_path(floor,0,0,0,packet)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=h9_child_tail(BoundaryLabel(2,2,0,0,0),0,0)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_H9_FINITE members=56", "pairs",pairs,"accepted",accepted,"source_path_edges",path_edges,"companion_edges",companion_edges,"all_child_walk_edges",walk_edges,"all_image_tail_edges",image_tail_edges,"max_walk",max_walk,"union_labels=20 BH=false")
    require_contract("class-A minus H9/reversal complete nine-kind indexed stars: 2A+3 at k<=1, 2A-2k+5 otherwise, 20-label chamber union; equal full FF/LL targets retain distinct indices; every actual first choice has a selected typed completion <=7, attained, while inherited source exit remains six; new uniform K9/L9/M9 exits 4/3/6 and all20 image tails, actual small-member RUN/LAST guards, full Parikh transport and reversals; malformed stars/walks/typed terminals, wrong strict targets, corrupt identities, count overflow and unknown tails refused; no companion stars, every-continuation termination, forward closure or global BH")
