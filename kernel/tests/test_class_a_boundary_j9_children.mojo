"""Every J9 word pair, exact half threshold, indexed counts and selected exits."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_j9_children import certify_j9_children, certify_j9_separator, j9_source, j9_image, in_j9_image, j9_v_high, j9_count, j9_star_interface, j9_exit_interface, j9_child_allowed, j9_child_star, j9_path, j9_registered_tail, verify_j9_packet, verify_j9_star, verify_j9_path
from psc.class_a_boundary_j8_children import j8_source
from psc.class_a_boundary_e7_children import e7_source, e7_image, verify_e7_steps
from psc.class_a_boundary_r4_children import r4_source
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_u_children import reverse_label
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_j9_children()
    var stars=0
    var exits=0
    for w in enlarged_candidate(True):
        assert_true(j9_star_interface(w)==j9_star_interface(w,True))
        assert_true(j9_exit_interface(w)==j9_exit_interface(w,True))
        stars+=1 if j9_star_interface(w,True)!=0 else 0
        exits+=1 if j9_exit_interface(w,True)!=0 else 0
    assert_true(stars==33 and exits==35)
    var old_stars=0
    var new_stars=0
    var old_exits=0
    var new_exits=0
    for w in e7_image():
        old_stars+=1 if j9_star_interface(w)!=0 else 0
        new_stars+=1 if j9_star_interface(w,True)!=0 else 0
        old_exits+=1 if j9_exit_interface(w)!=0 else 0
        new_exits+=1 if j9_exit_interface(w,True)!=0 else 0
    assert_true(old_stars==10 and new_stars==12 and old_exits==10 and new_exits==12)
    var image=j9_image()
    var attained=List[Bool]()
    stars=0;exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_j9_image(image[z]))
        for j in range(z):assert_true(image[z]!=image[j])
        stars+=1 if j9_star_interface(image[z],True)!=0 else 0
        exits+=1 if j9_exit_interface(image[z],True)!=0 else 0
    assert_true(len(image)==34 and stars==0 and exits==2)
    for kind in range(6):
        assert_true(j9_star_interface(j9_source(kind),True)==(61 if kind<2 else 0))
        assert_true(j9_exit_interface(j9_source(kind))==0 and j9_exit_interface(j9_source(kind),True)==61+kind//2)
    for top in range(3):
        for bottom in range(3):
            for x in range(-3,4):
                for c in [-4,4]:
                    for y in range(-11,12):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:listed=listed or v==w
                        assert_true(listed==in_j9_image(w))
    var pairs=0
    var accepted=0
    var path_edges=0
    var registered_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,BoundaryLabel(0,2,-1,-4,9)))==j9_v_high(k,t))
            assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,BoundaryLabel(2,2,-2,-4,8)))!=j9_v_high(k,t))
            for kind in range(6):
                var w=j9_source(kind)
                assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,w)))
                var packet=j9_path(kind,k,t)
                verify_j9_path(tables,kind,k,t,packet)
                var length=8 if k==0 else 7
                if kind//2==1:length-=1
                elif kind//2==2:length=6
                assert_true(len(packet)==length)
                path_edges+=len(packet)
                if kind>=2:continue
                var source=geometric_state(tables,w)
                var R=n-1 if kind==0 else A
                var B=A if kind==0 else n-1
                var star=j9_child_star(kind,k,t)
                verify_j9_star(tables,kind,k,t,star)
                assert_true(len(star)==j9_count(k,t))
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen);seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    for z in range(len(image)):
                        if image[z]==edge.target:attained[z]=True
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlap=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlap==j9_child_allowed(kind,k,t,i,j))
                        assert_true(overlap==(i*(B+2)+j in seen))
                        if overlap:accepted+=1
                verify_j9_packet(tables,kind,k,t,packet[0])
                if t>=4:verify_member_edge(tables,-1,k,n,d,e7_source(kind),2*n+6 if kind==0 else 0,0 if kind==0 else 2*n+6,w)
                elif t==3:
                    var actual=member_transport(-1,k,n,d,e7_source(kind),A+1 if kind==0 else 0,0 if kind==0 else A+1)
                    assert_true(actual!=w and actual.x==w.x and actual.c==w.c and actual.y==w.y)
            for flip in range(2):
                var w=j9_source(2+flip)
                var tail=j9_registered_tail(w,k,t)
                verify_e7_steps(tables,w,k,t,tail,j9_path(2+flip,k,t))
                registered_edges+=len(tail)
                assert_true(not in_j9_image(j9_path(2+flip,k,t)[0].target))
                # Preserve the inherited genuine J8/B8 two-cycle with exits.
                verify_member_edge(tables,-1,k,n,d,j8_source(flip),n if flip==0 else n+k+2,n+k+2 if flip==0 else n,j8_source(12+flip))
            if t==0 and (k==2 or k==3):assert_true(j9_count(k,t)==9)
    for found in attained:assert_true(found)
    var failed=False
    try:certify_j9_separator(True)
    except:failed=True
    assert_true(failed)
    failed=False
    try:certify_j9_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:_=j9_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (4 if mode==4 else 0),10 if mode==5 else 0)
        except:failed=True
        assert_true(failed)
    failed=False
    try:_=j9_child_allowed(0,3_100_000_000_000_000_000,0,0,0)
    except:failed=True
    assert_true(failed) # A fits, but the upper LR bound would overflow without its guard.
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var bad: List[BoundaryEdge]=[BoundaryEdge(0,0,r4_source(11))]
    var rest=j9_path(2,0,0)
    for edge in rest:bad.append(edge)
    failed=False
    try:verify_e7_steps(floor,j9_source(2),0,0,bad,bad)
    except:failed=True
    assert_true(failed) # ordinal zero has the actual FIRST x type and zero prefix.
    var star=j9_child_star(0,0,0)
    star[len(star)-1]=star[0]
    failed=False
    try:verify_j9_star(floor,0,0,0,star)
    except:failed=True
    assert_true(failed)
    failed=False
    try:verify_j9_packet(floor,0,0,0,BoundaryEdge(0,6,BoundaryLabel(0,2,-1,-4,8)))
    except:failed=True
    assert_true(failed) # wrong strict interior target of same types
    var packet=j9_path(0,0,0)
    packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:verify_j9_path(floor,0,0,0,packet)
    except:failed=True
    assert_true(failed)
    failed=False
    try:_=j9_registered_tail(BoundaryLabel(0,2,-1,-4,8),0,0)
    except:failed=True
    assert_true(failed) # unknown tail is not an empty path
    print("CLASS_A_BOUNDARY_J9_FINITE members=56", "pairs",pairs,"accepted",accepted,"source_companion_path_edges",path_edges,"registered_image_tail_edges",registered_edges,"union_labels=34", "BH=false")
    require_contract("class-A minus J9/reversal: nine-kind complete stars, exact v>1/2 iff t>=k-2 separator with no equality, clipped piecewise indexed counts, 34-label chamber union, every literal word pair checked in full typed Parikh/Perron geometry, uniform 8/7-edge source exits through P9 and 7/6-edge P9 exits with uniform H9 six-edge suffix; true k0 FIRST x versus fictitious RUN y, E7 ancestry only t>=4, equal counts but opposite half-chamber sources, same-type wrong interior targets, duplicate-omission stars, unequal-type terminals, corrupt identities and upper-bound overflow refused; only two image labels have registered uniform tails, no companion complete stars, all-direct-child productivity, closed carrier or global BH")
