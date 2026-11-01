"""D5 complete stars and all first-choice walks, with exact boundary controls."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_d5_children import certify_d5_children, d5_source, d5_candidate, d5_star_interface, d5_exit_interface, d5_image, in_d5_image, d5_child_allowed, d5_child_star, verify_d5_packet, verify_d5_star, d5_path, verify_d5_path, d5_child_tail, d5_walk, verify_d5_walk
from psc.class_a_boundary_y4_children import y4_source, y4_image
from psc.class_a_boundary_r5_children import r5_image
from psc.class_a_boundary_b5_children import b5_image
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_d5_children()
    for scope in range(6):
        var labels=d5_candidate(scope==1)
        if scope==2:labels=d5_image()
        elif scope==3:labels=y4_image()
        elif scope==4:labels=r5_image()
        elif scope==5:labels=b5_image()
        var before=0
        var after=0
        var exits_before=0
        var exits_after=0
        for w in labels:
            before+=1 if d5_star_interface(w)!=0 else 0
            after+=1 if d5_star_interface(w,True)!=0 else 0
            exits_before+=1 if d5_exit_interface(w)!=0 else 0
            exits_after+=1 if d5_exit_interface(w,True)!=0 else 0
        if scope==0:assert_true(len(labels)==41 and before==31 and after==31 and exits_before==33 and exits_after==33)
        elif scope==1:assert_true(len(labels)==43 and before==31 and after==33 and exits_before==35 and exits_after==35)
        elif scope==2:assert_true(len(labels)==6 and before==1 and after==2 and exits_before==1 and exits_after==6)
        elif scope==3:assert_true(before==16 and after==18 and exits_before==18 and exits_after==18)
        elif scope==4:assert_true(before==8 and after==8 and exits_before==8 and exits_after==8)
        else:assert_true(before==20 and after==20 and exits_before==22 and exits_after==22)
    # Companions have selected exits only; X0 is a terminal, not an expanded star.
    for kind in range(2,8):
        assert_true(d5_star_interface(d5_source(kind),True)==0)
        assert_true(d5_exit_interface(d5_source(kind),True)!=0)
    assert_true(d5_star_interface(d5_source(8),True)==39)
    var image=d5_image()
    var attained=List[Bool]()
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_d5_image(image[z]))
        for j in range(z):assert_true(image[z]!=image[j])
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in range(-2,3):
                    for y in range(-3,4):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:listed=listed or w==v
                        assert_true(listed==in_d5_image(w))
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
            for kind in range(9):
                var w=d5_source(kind)
                assert_true(interior_overlap_cached(tables,cache,geometric_state(tables,w)))
                var path=d5_path(kind,k,t)
                verify_d5_path(tables,kind,k,t,path)
                var expected=1
                if kind//2==1:expected=6
                elif kind//2==2:expected=2
                assert_true(len(path)==expected)
                path_edges+=len(path)
                if kind>=2:continue
                var source=geometric_state(tables,w)
                verify_member_edge(tables,-1,k,n,d,y4_source(kind),n if kind==1 else A+1,A+1 if kind==1 else n,w)
                var star=d5_child_star(kind,k,t)
                verify_d5_star(tables,kind,k,t,star)
                var B=n if kind==0 else A
                var R=A if kind==0 else n
                var seen=Dict[Int,Bool]()
                var yy=0
                var xx=0
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    yy+=1 if edge.target==BoundaryLabel(2,2,0,0,0) else 0
                    xx+=1 if edge.target==d5_source(8) else 0
                    var walk=d5_walk(kind,k,t,edge)
                    verify_d5_walk(tables,kind,k,t,edge,walk)
                    assert_true(len(walk)>=1 and len(walk)<=7)
                    walk_edges+=len(walk)
                    max_walk=max(max_walk,len(walk))
                    for z in range(len(image)):
                        if edge.target==image[z]:attained[z]=True
                assert_true(yy==n and xx==1 and len(star)==n+3)
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var v=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,v))
                        var strict=interior_overlap_cached(tables,cache,actual)
                        assert_true(strict==d5_child_allowed(kind,k,t,i,j))
                        assert_true(strict==(i*(B+2)+j in seen))
                        if strict:accepted+=1
                for which in range(5):
                    var i=d+1
                    var j=0
                    if which==1:
                        i=d
                        j=1
                    elif which==2:
                        i=d+2
                        j=1
                    elif which==3:
                        i=A
                        j=n+1
                    elif which==4:
                        i=A+1
                        j=n
                    var a=i if kind==0 else j
                    var b=j if kind==0 else i
                    var target=member_transport(-1,k,n,d,w,a,b)
                    assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,target)))
                    assert_true(not d5_child_allowed(kind,k,t,a,b))
            verify_member_edge(tables,-1,k,n,d,d5_source(2),1,3,BoundaryLabel(2,2,-1,1,1))
    for found in attained:assert_true(found)
    assert_true(max_walk==7)
    var failed=False
    try:certify_d5_children(True)
    except:failed=True
    assert_true(failed)
    for mode in range(8):
        failed=False
        try:
            _=d5_child_allowed(-1 if mode==0 else (2 if mode==1 else 0),-1 if mode==2 else (9223372036854775807 if mode==7 else 0),-1 if mode==3 else 0,-1 if mode==4 else (10 if mode==5 else 0),5 if mode==6 else 0)
        except:failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    for mode in range(4):
        failed=False
        try:
            if mode==0:verify_d5_packet(floor,0,0,0,BoundaryEdge(9,4,BoundaryLabel(2,2,0,0,0)))
            elif mode==1:verify_d5_packet(floor,0,0,0,BoundaryEdge(5,0,d5_source(4)))
            elif mode==2:verify_d5_packet(floor,0,0,0,BoundaryEdge(6,0,member_transport(-1,0,3,5,d5_source(0),6,0)))
            else:_=d5_child_star(8,0,0)
        except:failed=True
        assert_true(failed)
    for mode in range(3):
        var star=d5_child_star(0,0,0)
        if mode==0:_=star.pop()
        elif mode==1:star[1]=star[0]
        else:star.append(star[0])
        failed=False
        try:verify_d5_star(floor,0,0,0,star)
        except:failed=True
        assert_true(failed)
    var edge=BoundaryEdge(5,0,d5_source(2))
    for mode in range(4):
        var walk=d5_walk(0,0,0,edge)
        if mode==0:_=walk.pop()
        elif mode==1:walk[0]=BoundaryEdge(5,0,d5_source(4))
        elif mode==2:walk[len(walk)-1]=BoundaryEdge(1,2,BoundaryLabel(2,0,0,0,0))
        else:walk.append(walk[len(walk)-1])
        failed=False
        try:verify_d5_walk(floor,0,0,0,edge,walk)
        except:failed=True
        assert_true(failed)
    failed=False
    try:_=d5_child_tail(BoundaryLabel(2,0,0,0,0),0,0)
    except:failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_D5_FINITE members=56 source_cells=112 path_source_cells=504", "pairs",pairs,"accepted",accepted,"source_path_edges",path_edges,"all_child_walk_edges",walk_edges,"max_walk",max_walk,"union_labels=6", "S41_stars=31_exits=33", "S43_stars=33_exits=35", "Y4_image_stars=18_exits=18", "global_BH=false")
    require_contract("class-A minus D5/reversal complete nine-kind stars with n+3 indexed children and exact six-label union; all literal-pair Parikh/Perron and actual reversal checks, n y/y coincidences and one genuine x/x terminal retained, every first-choice walk to typed C at most seven edges; inherited one-edge source exit, D6/D7/C6 selected exits without companion stars, actual X0 normalization without a new full star, combined R5/B5 inventories and S43/image escapes; exact touching, false endpoint types, wrong interior targets, corrupt field identities, invalid/overflow inputs, malformed stars/walks and unequal-type zero terminal refused; no forward closure, all-edge descent or global BH/PSC")
