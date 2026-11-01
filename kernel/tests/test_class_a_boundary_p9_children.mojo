"""P9 literal-pair contract; native replay status recorded in the packet."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_p9_children import certify_p9_children, p9_source, p9_companion, p9_image, in_p9_image, p9_count, p9_child_allowed, p9_child_star, p9_path, p9_companion_path, p9_child_tail, p9_child_walk, verify_p9_packet, verify_p9_star, verify_p9_path, verify_p9_walk, p9_star_interface, p9_exit_interface
from psc.class_a_boundary_j9_children import j9_source, j9_image
from psc.class_a_boundary_j8_children import j8_source
from psc.class_a_boundary_e7_children import verify_e7_steps
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_u_children import reverse_label
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_p9_children()
    var stars=0
    var exits=0
    for w in enlarged_candidate(True):
        assert_true(p9_star_interface(w)==p9_star_interface(w,True))
        assert_true(p9_exit_interface(w)==p9_exit_interface(w,True))
        stars+=1 if p9_star_interface(w,True)!=0 else 0
        exits+=1 if p9_exit_interface(w,True)!=0 else 0
    assert_true(stars==33 and exits==35)
    var image=p9_image()
    var attained=List[Bool]()
    stars=0;exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_p9_image(image[z]))
        for j in range(z):assert_true(image[z]!=image[j])
        stars+=1 if p9_star_interface(image[z],True)!=0 else 0
        exits+=1 if p9_exit_interface(image[z],True)!=0 else 0
    assert_true(len(image)==24 and stars==2 and exits==20)
    for kind in range(2):
        assert_true(p9_star_interface(p9_source(kind))==0 and p9_star_interface(p9_source(kind),True)==62)
        assert_true(p9_exit_interface(p9_source(kind))==62)
    for kind in range(6):
        assert_true(p9_star_interface(p9_companion(kind),True)==0)
        assert_true(p9_exit_interface(p9_companion(kind),True)==(64+kind//2 if kind<4 else 0))
    var pairs=0
    var accepted=0
    var path_edges=0
    var companion_edges=0
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
                var w=p9_source(kind)
                assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,w)))
                var star=p9_child_star(kind,k,t)
                verify_p9_star(tables,kind,k,t,star)
                assert_true(len(star)==2*n+2+(1 if k>=2 else 0))
                var path=p9_path(kind,k,t)
                verify_p9_path(tables,kind,k,t,path)
                assert_true(len(path)==(7 if k==0 else 6))
                path_edges+=len(path)
                verify_member_edge(tables,-1,k,n,d,j9_source(kind),0 if kind==0 else n+k+3,n+k+3 if kind==0 else 0,w)
                var B=n if kind==0 else A+1
                var R=A+1 if kind==0 else n
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+1)+edge.j
                    assert_true(key not in seen);seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    for z in range(len(image)):
                        if image[z]==edge.target:attained[z]=True
                    var walk=p9_child_walk(kind,k,t,edge)
                    verify_p9_walk(tables,kind,k,t,edge,walk)
                    walk_edges+=len(walk);max_walk=max(max_walk,len(walk))
                var source=geometric_state(tables,w)
                for i in range(R+1):
                    for j in range(B+1):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==p9_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(B+1)+j in seen))
                        if overlap:accepted+=1
            for kind in range(6):
                if kind>=4 and k!=0:continue
                var packet=p9_companion_path(kind,k,t)
                verify_e7_steps(tables,p9_companion(kind),k,t,packet,p9_companion_path(kind,k,t))
                assert_true(len(packet)==(4 if kind<2 else (3 if kind<4 else 6)))
                companion_edges+=len(packet)
    assert_true(max_walk==9)
    for found in attained:assert_true(found)
    var failed=False
    try:certify_p9_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:_=p9_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),4 if mode==5 else 0)
        except:failed=True
        assert_true(failed)
    failed=False
    try:_=p9_count(3_100_000_000_000_000_000,0)
    except:failed=True
    assert_true(failed)
    for kind in [4,5]:
        failed=False
        try:_=p9_companion_path(kind,1,0)
        except:failed=True
        assert_true(failed)
        failed=False
        try:_=p9_child_tail(j8_source(26+kind%2),1,0)
        except:failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var star=p9_child_star(0,0,0)
    star[len(star)-1]=star[0]
    failed=False
    try:verify_p9_star(floor,0,0,0,star)
    except:failed=True
    assert_true(failed)
    failed=False
    try:verify_p9_packet(floor,0,0,0,BoundaryEdge(0,0,p9_companion(0)))
    except:failed=True
    assert_true(failed) # same types, strict interior, wrong full offset
    var packet=p9_path(0,0,0)
    packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:verify_p9_path(floor,0,0,0,packet)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=p9_child_tail(BoundaryLabel(2,2,0,0,0),0,0)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_P9_FINITE members=56", "pairs",pairs,"accepted",accepted,"source_path_edges",path_edges,"companion_edges",companion_edges,"all_child_walk_edges",walk_edges,"max_walk",max_walk,"union_labels=24 BH=false")
    require_contract("class-A minus P9/reversal complete nine-kind indexed stars, count 2n+2+[k>=2], 24-label chamber union; every actual direct child has selected typed coincidence completion <=9; inherited 7/6-edge source exits and uniform W9/B9 4/3-edge exits; X9/L8 tails remain k0-only and X9 keeps actual LAST x; full Parikh transport, every literal pair, reversal, duplicate/omission, wrong strict target, malformed typed terminal, corrupt identity and checked overflow controls; no companion stars, forward closure, every-continuation termination or global BH")
