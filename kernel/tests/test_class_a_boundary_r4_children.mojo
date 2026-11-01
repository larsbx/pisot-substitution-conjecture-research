"""R4 complete stars, five companion exits and the actual n=3 exception."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import r3_source, enlarged_candidate, r3_image
from psc.class_a_boundary_r4_children import certify_r4_children, r4_source, r4_star_interface, r4_exit_interface, r4_child_allowed, r4_child_star, r4_image, in_r4_image, verify_r4_packet, verify_r4_star, r4_path, verify_r4_path, _transition
from psc.class_a_boundary_occurrences import FIRST, RUN
from psc.param_poly import qx_const
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_r4_children()
    var candidate=enlarged_candidate(True)
    var before=0
    var after=0
    var exits_before=0
    var exits_after=0
    for z in range(len(candidate)):
        var w=candidate[z]
        before+=1 if r4_star_interface(w)!=0 else 0
        after+=1 if r4_star_interface(w,True)!=0 else 0
        exits_before+=1 if r4_exit_interface(w)!=0 else 0
        exits_after+=1 if r4_exit_interface(w,True)!=0 else 0
        assert_true(w.c>=-1 and w.c<=1)
        for j in range(z):
            assert_true(w!=candidate[j])
    assert_true(len(candidate)==41 and before==25 and after==27)
    assert_true(exits_before==23 and exits_after==27)
    var old_image=r3_image()
    var old_stars=0
    var old_exits=0
    for w in old_image:
        old_stars+=1 if r4_star_interface(w,True)!=0 else 0
        old_exits+=1 if r4_exit_interface(w,True)!=0 else 0
    assert_true(old_stars==22 and old_exits==20)
    for kind in range(2,12):
        assert_true(r4_star_interface(r4_source(kind),True)==0)
        assert_true(r4_exit_interface(r4_source(kind),True)!=0)
    var image=r4_image()
    assert_true(len(image)==20)
    var attained=List[Bool]()
    var child_stars=0
    var child_exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_r4_image(image[z]))
        assert_true(image[z].c==-3 or image[z].c==3)
        child_stars+=1 if r4_star_interface(image[z],True)!=0 else 0
        child_exits+=1 if r4_exit_interface(image[z],True)!=0 else 0
        for j in range(z):
            assert_true(image[z]!=image[j])
    assert_true(child_stars==2 and child_exits==10)
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in range(-4,5):
                    for y in range(-7,8):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:
                            listed=listed or w==v
                        assert_true(listed==in_r4_image(w))
    var pairs=0
    var accepted=0
    var path_edges=0
    var primary_edges=0
    var companion_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            for kind in range(12):
                var w=r4_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var packet=r4_path(kind,k,t)
                verify_r4_path(tables,kind,k,t,packet)
                var expected=3 if kind//2==0 else 2
                if kind//2==0 and t==1:
                    expected=4
                elif kind//2==2:
                    expected=7 if n==3 else 3
                elif kind//2==4:
                    expected=3
                elif kind//2==5:
                    expected=5
                assert_true(len(packet)==expected)
                path_edges+=len(packet)
                if kind>=2:
                    companion_edges+=len(packet)
                    continue
                primary_edges+=len(packet)
                verify_member_edge(tables,-1,k,n,d,r3_source(kind),N if kind==1 else A+1,A+1 if kind==1 else N,w)
                var R=A if kind==0 else N
                var B=N if kind==0 else A
                var star=r4_child_star(kind,k,t)
                verify_r4_star(tables,kind,k,t,star)
                assert_true(len(star)==max(1,2*t))
                if t==0:
                    assert_true(len(star)==1 and star[0].target==r4_source(2+kind))
                elif t==1:
                    assert_true(len(star)==2)
                    for edge in star:
                        assert_true(edge.target==r4_source(4+kind) or edge.target==r4_source(8+kind))
                        assert_true(r4_exit_interface(edge.target,True)!=0)
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
                        assert_true(overlaps==r4_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                verify_r4_packet(tables,kind,k,t,packet[0])
            assert_true(r4_child_allowed(0,k,t,0,n)==(t<=2))
            if t==0:
                assert_true(k+4==n+1)
            elif t==1:
                assert_true(k+4==n)
                assert_true(member_transport(-1,k,n,d,r4_source(0),0,k+4)==r4_source(8))
            if n==3:
                var actual=member_transport(-1,k,n,d,r4_source(4),0,3)
                assert_true(actual==BoundaryLabel(0,1,1,0,-1) and actual!=r4_source(6))
                assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,actual)))
            else:
                verify_member_edge(tables,-1,k,n,d,r4_source(4),0,3,r4_source(6))
    for found in attained:
        assert_true(found)
    var failed=False
    try:
        certify_r4_children(True)
    except:
        failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:
            _=r4_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),5 if mode==5 else 0)
        except:
            failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:
        var disjoint=member_transport(-1,0,3,5,r4_source(0),0,0)
        verify_r4_packet(floor,0,0,0,BoundaryEdge(0,0,disjoint))
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _transition(qx_const(3),qx_const(5),r4_source(4),FIRST,qx_const(0),RUN,qx_const(3),r4_source(6))
    except:
        failed=True
    assert_true(failed) # n=3: ordinal 3 is LAST c, not RUN y.
    failed=False
    try:
        verify_member_edge(floor,-1,0,3,5,r4_source(4),0,3,r4_source(6))
    except:
        failed=True
    assert_true(failed) # the actual x/c edge is interior but has different types
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,14,5,4))
    var cache=Dict[CubicElt,Int]()
    var wrong=r4_source(4)
    assert_true(in_r4_image(wrong) and interior_overlap_cached(tables,cache,geometric_state(tables,wrong)))
    failed=False
    try:
        verify_r4_packet(tables,0,0,2,BoundaryEdge(0,4,wrong))
    except:
        failed=True
    assert_true(failed)
    for mode in range(4):
        var packet=r4_path(0,0,1)
        if mode==0:
            packet[0]=BoundaryEdge(0,3,r4_source(10))
        elif mode==1:
            packet[1]=BoundaryEdge(0,3,r4_source(4))
        elif mode==2:
            packet[len(packet)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
        else:
            _=packet.pop()
        failed=False
        try:
            var one=build_seed_overlap_tables_screened(class_member(CLASS_A,11,4,3))
            verify_r4_path(one,0,0,1,packet)
        except:
            failed=True
        assert_true(failed)
    for mode in range(3):
        var star=r4_child_star(0,0,2)
        if mode==0:
            _=star.pop()
        elif mode==1:
            star[1]=star[0]
        else:
            star.append(star[0])
        failed=False
        try:
            verify_r4_star(tables,0,0,2,star)
        except:
            failed=True
        assert_true(failed)
    failed=False
    try:
        _=r4_child_star(2,0,0)
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_R4_FINITE members=56 source_cells=112 path_source_cells=672", "pairs",pairs,"accepted",accepted,"R4_path_edges",primary_edges,"companion_path_edges",companion_edges,"path_edges",path_edges,"union_labels=20", "candidate41_stars_before=25_after=27_unregistered=14_exits=27", "image_registered_stars=2_exits=10", "BH=false")
    require_contract("class-A minus R4/reversal complete nine-kind stars with inherited alpha+2h<1, max(1,2t) occurrences, 20-label image, all literal-pair Parikh/Perron checks and R3 ancestry; <=4-edge R4 exits split t=0/1/>=2, five uniform companion exits without complete-star flags, exact n=3 D4 alternate path, all direct children productive on t<=1, separate 41-source and 20-image registries with Y4 exit but no star; corrupt identities, invalid inputs, false endpoint types, disjoint pairs, wrong interior labels, malformed paths/stars and false typed coincidence refused; no companion complete stars, all-t all-child productivity or BH/PSC promotion")
