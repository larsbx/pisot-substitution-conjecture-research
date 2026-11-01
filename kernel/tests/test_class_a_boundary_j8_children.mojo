"""Every J8 literal pair, exact k=0 split, guarded helpers and all-child walks."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_j8_children import certify_j8_children, certify_j8_separator, j8_source, j8_image, in_j8_image, j8_star_interface, j8_exit_interface, j8_child_allowed, j8_child_star, j8_child_tail, j8_path, j8_walk, verify_j8_packet, verify_j8_star, verify_j8_path, verify_j8_walk
from psc.class_a_boundary_e7_children import e7_source, e7_image, verify_e7_steps
from psc.class_a_boundary_h3_children import chain_source, chain_path
from psc.class_a_boundary_r4_children import r4_source, r4_path
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_u_children import reverse_label
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_j8_children()
    for flip in range(2):
        assert_true(j8_source(4+flip)==chain_source(7-flip))
        assert_true(j8_source(16+flip)==r4_source(11-flip))
        assert_true(j8_star_interface(j8_source(4+flip),True)==22)
        assert_true(j8_exit_interface(j8_source(16+flip),True)==28)
    var stars=0
    var exits=0
    for w in enlarged_candidate(True):
        assert_true(j8_star_interface(w)==j8_star_interface(w,True))
        assert_true(j8_exit_interface(w)==j8_exit_interface(w,True))
        stars+=1 if j8_star_interface(w,True)!=0 else 0
        exits+=1 if j8_exit_interface(w,True)!=0 else 0
    assert_true(stars==33 and exits==35)
    var old_stars=0
    var new_stars=0
    var old_exits=0
    var new_exits=0
    for w in e7_image():
        old_stars+=1 if j8_star_interface(w)!=0 else 0
        new_stars+=1 if j8_star_interface(w,True)!=0 else 0
        old_exits+=1 if j8_exit_interface(w)!=0 else 0
        new_exits+=1 if j8_exit_interface(w,True)!=0 else 0
    assert_true(old_stars==8 and new_stars==10 and old_exits==8 and new_exits==10)
    var image=j8_image()
    var attained=List[Bool]()
    stars=0;exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_j8_image(image[z]))
        for j in range(z):assert_true(image[z]!=image[j])
        stars+=1 if j8_star_interface(image[z],True)!=0 else 0
        exits+=1 if j8_exit_interface(image[z],True)!=0 else 0
    assert_true(len(image)==18 and stars==2 and exits==16)
    for kind in range(22,28):assert_true(j8_exit_interface(j8_source(kind),True)==0)
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in [-3,3]:
                    for y in range(-8,9):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:listed=listed or v==w
                        assert_true(listed==in_j8_image(w))
    var pairs=0
    var accepted=0
    var path_cells=0
    var path_edges=0
    var walk_edges=0
    var tail_edges=0
    var max_walk=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            for kind in range(28):
                var group=kind//2
                var source=geometric_state(tables,j8_source(kind))
                assert_true(interior_overlap_cached(tables,cache,source)==(group!=13 or k==0))
                if ((group==11 or group==13) and k!=0) or (group==12 and k!=1):
                    var refused=False
                    try:_=j8_path(kind,k,t)
                    except:refused=True
                    assert_true(refused)
                    continue
                var packet=j8_path(kind,k,t)
                verify_j8_path(tables,kind,k,t,packet)
                path_cells+=1;path_edges+=len(packet)
                if kind>=2:continue
                assert_true(len(packet)==(6 if k==0 else 4))
                var w=j8_source(kind)
                var R=n-1 if kind==0 else A
                var B=A if kind==0 else n-1
                var star=j8_child_star(kind,k,t)
                verify_j8_star(tables,kind,k,t,star)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    for z in range(len(image)):
                        if image[z]==edge.target:attained[z]=True
                    var walk=j8_walk(kind,k,t,edge)
                    verify_j8_walk(tables,kind,k,t,edge,walk)
                    walk_edges+=len(walk);max_walk=max(max_walk,len(walk))
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==j8_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(B+2)+j in seen))
                        if overlap:accepted+=1
                var cycle=BoundaryEdge(n if kind==0 else n+k+2,n+k+2 if kind==0 else n,j8_source(12+kind))
                verify_j8_packet(tables,kind,k,t,cycle)
                verify_member_edge(tables,-1,k,n,d,cycle.target,k+1 if kind==0 else 0,0 if kind==0 else k+1,w)
                if t>=3:verify_member_edge(tables,-1,k,n,d,e7_source(kind),2*n+5 if kind==0 else 0,0 if kind==0 else 2*n+5,w)
                elif t==2:
                    var actual=member_transport(-1,k,n,d,e7_source(kind),A+1 if kind==0 else 0,0 if kind==0 else A+1)
                    assert_true(actual!=w and actual.x==w.x and actual.c==w.c and actual.y==w.y)
            for w in image:
                if (w==j8_source(26) or w==j8_source(27)) and k!=0:continue
                var tail=j8_child_tail(w,k,t)
                assert_true(len(tail)<=8)
                verify_e7_steps(tables,w,k,t,tail,j8_child_tail(w,k,t))
                tail_edges+=len(tail)
    for found in attained:assert_true(found)
    assert_true(max_walk==9)
    var failed=False
    try:certify_j8_separator(True)
    except:failed=True
    assert_true(failed)
    failed=False
    try:certify_j8_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:_=j8_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (4 if mode==4 else 0),10 if mode==5 else 0)
        except:failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var bad: List[BoundaryEdge]=[BoundaryEdge(0,3,j8_source(18))]
    var suffix=j8_path(18,0,0)
    for edge in suffix:bad.append(edge)
    failed=False
    try:verify_e7_steps(floor,j8_source(6),0,0,bad,bad)
    except:failed=True
    assert_true(failed) # R8's true x/c LAST target is not same-offset c/c Q8
    var star=j8_child_star(0,0,0)
    star[len(star)-1]=star[0]
    failed=False
    try:verify_j8_star(floor,0,0,0,star)
    except:failed=True
    assert_true(failed)
    var edge=j8_child_star(0,0,0)[0]
    var walk=j8_walk(0,0,0,edge)
    walk[len(walk)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:verify_j8_walk(floor,0,0,0,edge,walk)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=j8_child_tail(j8_source(26),1,0)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=j8_child_tail(BoundaryLabel(2,2,0,0,0),0,0)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_J8_FINITE members=56", "pairs",pairs,"accepted",accepted,"path_cells",path_cells,"source_companion_path_edges",path_edges,"all_child_walk_edges",walk_edges,"guarded_image_tail_edges",tail_edges,"max_walk",max_walk,"union_labels=18", "BH=false")
    require_contract("class-A minus J8/reversal: exact nine-kind stars with 2n+3+[k=0] indexed children, 18-label chamber union, coefficientwise beta*(beta+1)*(alpha+3h-1)=1-k*beta separator, every literal pair in full typed Parikh/Perron geometry, every actual first choice has selected completion <=9, 6/4-edge source exits; existing reversed L/G5 identities reused, no new companion stars, L8 source/path only k0, Z8/D8 tails only k0/k1 despite interior sources, x/c versus same-offset c/c endpoints retained, E7 ancestry only t>=3, uniform J8/B8 two-cycle with exits, malformed stars/walks/terminals and corrupt identities refused; no all-edge descent, every-continuation termination, closed carrier or global BH")
