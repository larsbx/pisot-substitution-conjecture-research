"""Complete Y4 stars and a typed <=8-edge walk through every indexed child."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_b3_children import b3_source
from psc.class_a_boundary_r3_children import enlarged_candidate, r3_image
from psc.class_a_boundary_r4_children import r4_source, _transition
from psc.class_a_boundary_p3_children import p3_source
from psc.class_a_boundary_p_children import p_source
from psc.class_a_boundary_y4_children import certify_y4_children, y4_source, y4_star_interface, y4_exit_interface, y4_child_allowed, y4_child_star, y4_image, in_y4_image, verify_y4_packet, verify_y4_star, y4_path, verify_y4_path, y4_child_tail, y4_walk, verify_y4_walk, _seed_suffix
from psc.class_a_boundary_occurrences import FIRST, RUN
from psc.param_poly import qx_const
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_y4_children()
    var candidate=enlarged_candidate(True)
    var before=0
    var after=0
    var exits_before=0
    var exits_after=0
    for z in range(len(candidate)):
        var w=candidate[z]
        before+=1 if y4_star_interface(w)!=0 else 0
        after+=1 if y4_star_interface(w,True)!=0 else 0
        exits_before+=1 if y4_exit_interface(w)!=0 else 0
        exits_after+=1 if y4_exit_interface(w,True)!=0 else 0
        assert_true(w!=y4_source(4) and w!=y4_source(5))
        for j in range(z):
            assert_true(w!=candidate[j])
    assert_true(len(candidate)==41 and before==27 and after==29)
    assert_true(exits_before==27 and exits_after==31)
    var old_image=r3_image()
    var old_stars=0
    var old_exits=0
    for w in old_image:
        old_stars+=1 if y4_star_interface(w,True)!=0 else 0
        old_exits+=1 if y4_exit_interface(w,True)!=0 else 0
    assert_true(old_stars==22 and old_exits==22)
    for kind in range(2,14):
        assert_true(y4_star_interface(y4_source(kind),True)==(7 if kind//2==3 else 0))
        assert_true(y4_exit_interface(y4_source(kind),True)!=0)
    var image=y4_image()
    assert_true(len(image)==18)
    var attained=List[Bool]()
    var child_stars=0
    var child_exits=0
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_y4_image(image[z]))
        child_stars+=1 if y4_star_interface(image[z],True)!=0 else 0
        child_exits+=1 if y4_exit_interface(image[z],True)!=0 else 0
        for j in range(z):
            assert_true(image[z]!=image[j])
    assert_true(child_stars==14 and child_exits==18)
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in range(-2,3):
                    for y in range(-4,5):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:
                            listed=listed or w==v
                        assert_true(listed==in_y4_image(w))
    var pairs=0
    var accepted=0
    var source_edges=0
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
            for kind in range(14):
                var w=y4_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var packet=y4_path(kind,k,t)
                verify_y4_path(tables,kind,k,t,packet)
                var expected=2
                if kind//2==1:
                    expected=3
                elif kind//2==2:
                    expected=1
                elif kind//2==3:
                    expected=5 if t==0 else 7
                elif kind//2==4:
                    expected=6
                elif kind//2==5:
                    expected=4
                elif kind//2==6:
                    expected=5
                assert_true(len(packet)==expected)
                source_edges+=len(packet)
                if kind>=2:
                    continue
                # Both directions of the actual uniform Y4/T two-cycle.
                verify_member_edge(tables,-1,k,n,d,p3_source(2+kind),1 if kind==1 else 0,0 if kind==1 else 1,w)
                verify_member_edge(tables,-1,k,n,d,w,0 if kind==1 else d+1,d+1 if kind==1 else 0,p3_source(2+kind))
                var R=A if kind==0 else N
                var B=N if kind==0 else A
                var star=y4_child_star(kind,k,t)
                verify_y4_star(tables,kind,k,t,star)
                assert_true(len(star)==2*n+2)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    var suffix=y4_child_tail(edge.target,k,t)
                    assert_true(len(suffix)>=1 and len(suffix)<=7)
                    var walk=y4_walk(kind,k,t,edge)
                    verify_y4_walk(tables,kind,k,t,edge,walk)
                    assert_true(len(walk)==1+len(suffix) and len(walk)<=8)
                    walk_edges+=len(walk)
                    max_walk=max(max_walk,len(walk))
                    var found=False
                    for z in range(len(image)):
                        if edge.target==image[z]:
                            attained[z]=True
                            found=True
                    assert_true(found)
                    if n==3:
                        assert_true(edge.target!=y4_source(6) and edge.target!=y4_source(7))
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==y4_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                verify_y4_packet(tables,kind,k,t,BoundaryEdge(n if kind==1 else A+1,A+1 if kind==1 else n,y4_source(4+kind)))
            # New T2 proof preserves the t=0 LAST c endpoint and its true prefix.
            verify_member_edge(tables,-1,k,n,d,y4_source(6),k+3,0,y4_source(10 if t==0 else 8))
            if n==3:
                verify_y4_packet(tables,0,k,t,BoundaryEdge(d+4,1,r4_source(0)))
    for found in attained:
        assert_true(found)
    assert_true(max_walk==8)
    var failed=False
    try:
        certify_y4_children(True)
    except:
        failed=True
    assert_true(failed)
    for mode in range(7):
        failed=False
        try:
            _=y4_child_allowed(2 if mode==0 else (-1 if mode==6 else 0),-1 if mode==1 else 0,-1 if mode==2 else 0,-1 if mode==3 else (10 if mode==4 else 0),5 if mode==5 else 0)
        except:
            failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var cache=Dict[CubicElt,Int]()
    for mode in range(3):
        failed=False
        try:
            if mode==0:
                _transition(qx_const(3),qx_const(5),y4_source(6),RUN,qx_const(3),FIRST,qx_const(0),y4_source(8))
            elif mode==1:
                _transition(qx_const(3),qx_const(5),y4_source(0),RUN,qx_const(9),RUN,qx_const(1),y4_source(7))
            else:
                verify_member_edge(floor,-1,0,3,5,y4_source(10),2,0,y4_source(12))
        except:
            failed=True
        assert_true(failed)
    # A wrong interior image label of the same types cannot replace the true offset.
    var wrong=b3_source(0)
    assert_true(in_y4_image(wrong) and interior_overlap_cached(floor,cache,geometric_state(floor,wrong)))
    failed=False
    try:
        verify_y4_packet(floor,0,0,0,BoundaryEdge(6,0,wrong))
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        var disjoint=member_transport(-1,0,3,5,y4_source(0),0,0)
        verify_y4_packet(floor,0,0,0,BoundaryEdge(0,0,disjoint))
    except:
        failed=True
    assert_true(failed)
    var edge=BoundaryEdge(9,3,y4_source(4))
    for mode in range(4):
        var walk=y4_walk(0,0,0,edge)
        if mode==0:
            walk[0]=BoundaryEdge(9,3,y4_source(2))
        elif mode==1:
            walk[1]=BoundaryEdge(6,1,BoundaryLabel(2,0,0,0,0))
        elif mode==2:
            _=walk.pop()
        else:
            walk.append(walk[len(walk)-1])
        failed=False
        try:
            verify_y4_walk(floor,0,0,0,edge,walk)
        except:
            failed=True
        assert_true(failed)
    for mode in range(3):
        var star=y4_child_star(0,0,0)
        if mode==0:
            _=star.pop()
        elif mode==1:
            star[1]=star[0]
        else:
            star.append(star[0])
        failed=False
        try:
            verify_y4_star(floor,0,0,0,star)
        except:
            failed=True
        assert_true(failed)
    for mode in range(3):
        failed=False
        try:
            if mode==0:
                _=y4_child_star(6,0,0)
            elif mode==1:
                _=y4_child_tail(BoundaryLabel(2,2,0,0,0),0,0)
            else:
                _=_seed_suffix(0,2,0,0)
        except:
            failed=True
        assert_true(failed)
    print("CLASS_A_BOUNDARY_Y4_FINITE members=56 source_cells=112 path_source_cells=784", "pairs",pairs,"accepted",accepted,"source_path_edges",source_edges,"all_child_walk_edges",walk_edges,"max_walk",max_walk,"union_labels=18", "candidate41_stars=29_unregistered=12_exits=31", "image_registered_stars=14_exits=18", "all_direct_children_productive=true", "Y4_T_cycle=true", "BH=false")
    require_contract("class-A minus Y4/reversal complete nine-kind stars with 2n+2 occurrences and exact 18-label union; every indexed direct child has a typed <=7-edge tail and every first-choice walk <=8, all literal-pair Parikh/Perron checks and all generated walks replayed; existing two-edge source exit, new T2 <=7 exit with t=0 LAST c control, R5/D5 and M5/CM/F0 selected exits without new companion stars; uniform T/Y4 cycle and S41 escape via D5, separate 41-source/18-image flags; invalid inputs, corrupt identity, false endpoint/prefix types, disjoint pairs, wrong interior targets, malformed stars/walks and false coincidence refused; no forward closure, all-edge descent, all-T2-child productivity or global BH/PSC promotion")
