"""R5 complete stars, exact image, old exits and actual endpoint controls."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r3_children import enlarged_candidate, r3_image
from psc.class_a_boundary_y4_children import y4_source, y4_image
from psc.class_a_boundary_h3_children import chain_source, chain_path, verify_chain_path
from psc.class_a_boundary_p_children import p_source, p_path, verify_p_path
from psc.class_a_boundary_r4_children import _transition
from psc.class_a_boundary_r5_children import certify_r5_children, r5_source, r5_star_interface, r5_exit_interface, r5_child_allowed, r5_child_star, r5_image, in_r5_image, verify_r5_packet, verify_r5_star, r5_path, verify_r5_path
from psc.class_a_boundary_occurrences import FIRST, RUN
from psc.param_poly import qx_const
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_r5_children()
    var candidate=enlarged_candidate(True)
    var before=0
    var after=0
    var exits=0
    for w in candidate:
        before+=1 if r5_star_interface(w)!=0 else 0
        after+=1 if r5_star_interface(w,True)!=0 else 0
        exits+=1 if r5_exit_interface(w)!=0 else 0
    assert_true(len(candidate)==41 and before==29 and after==31 and exits==31)
    var old_stars=0
    var old_exits=0
    var old_image=r3_image()
    for w in old_image:
        old_stars+=1 if r5_star_interface(w,True)!=0 else 0
        old_exits+=1 if r5_exit_interface(w)!=0 else 0
    assert_true(old_stars==22 and old_exits==22)
    var yi=y4_image()
    var ys=0
    var ye=0
    for w in yi:
        ys+=1 if r5_star_interface(w,True)!=0 else 0
        ye+=1 if r5_exit_interface(w)!=0 else 0
    assert_true(ys==16 and ye==18)
    var image=r5_image()
    var stars=0
    var image_exits=0
    var attained=List[Bool]()
    assert_true(len(image)==18)
    for z in range(len(image)):
        attained.append(False)
        assert_true(in_r5_image(image[z]))
        stars+=1 if r5_star_interface(image[z],True)!=0 else 0
        image_exits+=1 if r5_exit_interface(image[z])!=0 else 0
        for w in candidate:
            assert_true(w!=image[z])
        for j in range(z):
            assert_true(image[z]!=image[j])
    assert_true(stars==6 and image_exits==6)
    for top in range(3):
        for bottom in range(3):
            for x in range(-2,3):
                for c in range(-3,4):
                    for y in range(-6,7):
                        var w=BoundaryLabel(top,bottom,x,c,y)
                        var listed=False
                        for v in image:
                            listed=listed or w==v
                        assert_true(listed==in_r5_image(w))
    var pairs=0
    var accepted=0
    var path_edges=0
    var reused_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            for kind in range(2):
                var w=r5_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var packet=r5_path(kind,k,t)
                verify_r5_path(tables,kind,k,t,packet)
                assert_true(len(packet)==3)
                path_edges+=len(packet)
                verify_member_edge(tables,-1,k,n,d,y4_source(kind),N if kind==1 else A+1,A+1 if kind==1 else N,w)
                var star=r5_child_star(kind,k,t)
                verify_r5_star(tables,kind,k,t,star)
                assert_true(len(star)==2*n+(2 if t==0 else 3))
                var R=A if kind==0 else N
                var B=N if kind==0 else A
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
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
                        assert_true(overlaps==r5_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                # Bind and replay the complete-star families already in P/H3.
                for group in [2,3]:
                    var suffix=p_path(2*group+kind,k,t)
                    verify_p_path(tables,2*group+kind,k,t,suffix)
                    reused_edges+=len(suffix)
                var suffix=chain_path(4+kind,k,t)
                verify_chain_path(tables,4+kind,k,t,suffix)
                reused_edges+=len(suffix)
                assert_true(in_r5_image(chain_source(4+kind)))
                assert_true(not in_r5_image(suffix[0].target))
    for found in attained:
        assert_true(found)
    var failed=False
    try:
        certify_r5_children(True)
    except:
        failed=True
    assert_true(failed)
    for mode in range(8):
        failed=False
        try:
            _=r5_child_allowed(-1 if mode==0 else (2 if mode==1 else 0),-1 if mode==2 else (9223372036854775807 if mode==7 else 0),-1 if mode==3 else 0,-1 if mode==4 else (10 if mode==5 else 0),4 if mode==6 else 0)
        except:
            failed=True
        assert_true(failed)
    var floor=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var one=build_seed_overlap_tables_screened(class_member(CLASS_A,11,4,3))
    verify_r5_packet(one,0,0,1,BoundaryEdge(0,0,BoundaryLabel(0,0,0,-2,4)))
    for mode in range(4):
        failed=False
        try:
            if mode==0:
                # At t=1 nominal RF(t-1,0) is actual FIRST/FIRST, not K.
                _transition(qx_const(4),qx_const(7),r5_source(0),RUN,qx_const(0),FIRST,qx_const(0),chain_source(4))
            elif mode==1:
                verify_member_edge(floor,-1,0,3,5,r5_source(0),1,1,p_source(0))
            elif mode==2:
                # Both same-type B2 labels are strict and in the image.
                verify_r5_packet(floor,0,0,0,BoundaryEdge(1,1,p_source(5)))
            else:
                var disjoint=member_transport(-1,0,3,5,r5_source(0),0,1)
                verify_r5_packet(floor,0,0,0,BoundaryEdge(0,1,disjoint))
        except:
            failed=True
        assert_true(failed)
    for mode in range(3):
        var star=r5_child_star(0,0,0)
        if mode==0:
            _=star.pop()
        elif mode==1:
            star[1]=star[0]
        else:
            star.append(star[0])
        failed=False
        try:
            verify_r5_star(floor,0,0,0,star)
        except:
            failed=True
        assert_true(failed)
    for mode in range(4):
        var path=r5_path(0,0,0)
        if mode==0:
            _=path.pop()
        elif mode==1:
            path[0]=BoundaryEdge(1,1,p_source(0))
        elif mode==2:
            path[2]=BoundaryEdge(path[2].i,path[2].j,BoundaryLabel(2,0,0,0,0))
        else:
            path[0]=BoundaryEdge(0,1,path[0].target)
        failed=False
        try:
            verify_r5_path(floor,0,0,0,path)
        except:
            failed=True
        assert_true(failed)
    print("CLASS_A_BOUNDARY_R5_FINITE members=56 source_cells=112", "pairs",pairs,"accepted",accepted,"source_path_edges",path_edges,"reused_exit_edges",reused_edges,"union_labels=18", "candidate41_stars=31_unregistered=10_exits=31", "image_registered_stars=6_exits=6", "Y4_image_registered_stars=16_exits=18", "BH=false")
    require_contract("class-A minus R5/reversal complete nine-kind stars with 2n+2 occurrences at t=0 else 2n+3 and exact 18-label chamber union; all literal-pair full Parikh/Perron and actual reversal checks, inherited three-edge typed exits and uniform Y4 ancestry, reused K/B2/B2h interfaces and exit replay, S41 and image escapes, independent source/image inventories; invalid input, corrupt field identity, false FIRST/RUN type, copied D3 prefix, disjoint pair, wrong interior target, duplicate/incomplete stars and altered/truncated/unequal-type-terminal paths refused; no all-child productivity, closed carrier or global BH/PSC promotion")
