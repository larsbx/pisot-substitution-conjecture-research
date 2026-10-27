"""Entire H4 actual-child Cartesian oracle against canonical Perron geometry."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, geometric_state,
)
from psc.class_a_boundary_e2_children import verify_e2_packet
from psc.class_a_boundary_h4_children import (
    certify_h4_children, h4_source, h4_child_allowed, h4_child_star,
    h4_image, verify_h4_packet,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child,
    interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def main() raises:
    certify_h4_children()
    var image=h4_image()
    assert_true(len(image)==13)
    var reached=List[Bool]()
    for _ in image:
        reached.append(False)
    var members=0
    var pairs=0
    var accepted=0
    for k in range(6):
        for t in range(6):
            members+=1
            var n=k+3+t
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(
                class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            var H=h4_source()
            var source=geometric_state(tables,H)
            assert_true(interior_overlap_cached(tables,cache,source))
            # Literal Dxx last-x vs x-run index 2n+1 is the
            # real source of H4 throughout the chamber.
            verify_e2_packet(tables,2,k,t,
                BoundaryEdge(A+1,2*n+1,H))
            var star=h4_child_star(k,t)
            assert_true(len(star)==2*t+5)
            var seen=Dict[Int,Bool]()
            for edge in star:
                var key=edge.i*(N+2)+edge.j
                assert_true(key not in seen)
                seen[key]=True
                verify_h4_packet(tables,k,t,edge)
                var found=False
                for z in range(len(image)):
                    if edge.target==image[z]:
                        reached[z]=True
                        found=True
                assert_true(found)
            var hits=0
            for i in range(A+2):
                for j in range(N+2):
                    pairs+=1
                    var target=member_transport(-1,k,n,d,H,i,j)
                    var actual=selected_overlap_child(tables,source,i,j)
                    assert_true(actual==geometric_state(tables,target))
                    var hit=interior_overlap_cached(tables,cache,actual)
                    assert_true(hit==h4_child_allowed(k,t,i,j))
                    assert_true(hit==(i*(N+2)+j in seen))
                    if hit:
                        hits+=1
                        accepted+=1
            assert_true(hits==len(star))
    for flag in reached:
        assert_true(flag)
    var refused=False
    try:
        certify_h4_children(True)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=h4_child_allowed(-1,0,1,0)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=h4_child_allowed(0,0,1000,0)
    except:
        refused=True
    assert_true(refused)
    # H4 first/first is literal but physically disjoint and cannot be
    # passed off as a genuine occurrence with an invented packet target.
    var tbl=build_seed_overlap_tables_screened(
        class_member(CLASS_A,8,3,2))
    refused=False
    try:
        verify_h4_packet(tbl,0,0,
            BoundaryEdge(0,0,BoundaryLabel(0,0,2,2,2)))
    except:
        refused=True
    assert_true(refused)
    print("CLASS_A_BOUNDARY_H4_FINITE members",members,
          "pairs",pairs,"accepted",accepted,
          "labels=13","all_attained=true",
          "e2_envelope_subset=true","BH=false")
    require_contract("minus boundary H4=x/y (0,-2,4): exact all k,t nine-kind child star, 2t+5 ordered edges, 13 labels inside E2 image; actual Dxx ancestry, all Cartesian Parikh/Perron comparisons, corrupt/invalid edge refusals; no closure or BH")
