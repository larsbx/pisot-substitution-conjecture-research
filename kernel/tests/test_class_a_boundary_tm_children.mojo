"""All ordered occurrence pairs against the complete T_m guard table."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, geometric_state, boundary_r,
)
from psc.class_a_boundary_tm_children import (
    certify_tm_children, tm_child_allowed, tm_child_star, verify_tm_packet,
    tm_target_envelope,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def main() raises:
    certify_tm_children()
    var pairs=0
    var accepted=0
    var members=0
    var envelope=tm_target_envelope()
    var attained=List[Bool]()
    for _ in envelope:
        attained.append(False)
    for eps in [-1,1]:
        for k in range(10):
            for t in range(5):
                members+=1
                var n=k+3+t if eps==-1 else 2*(k+2)+t
                var d=2*n+6*eps+5-k
                var N=n+eps
                var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n+eps))
                var cache=Dict[CubicElt,Int]()
                var r=boundary_r(eps,k)
                for m in range(r,r+2):
                    var parent=BoundaryLabel(2,2,-1,1,m)
                    var source=geometric_state(tables,parent)
                    assert_true(interior_overlap_cached(tables,cache,source))
                    var seen=Dict[Int,Bool]()
                    var edges=tm_child_star(eps,k,t,m)
                    for edge in edges:
                        var key=edge.i*(N+2)+edge.j
                        assert_true(key not in seen)
                        seen[key]=True
                        verify_tm_packet(tables,eps,k,t,m,edge)
                        var found_label=False
                        for z in range(len(envelope)):
                            if edge.target==envelope[z]:
                                attained[z]=True
                                found_label=True
                        assert_true(found_label)
                    var found=0
                    for i in range(N+2):
                        for j in range(N+2):
                            pairs+=1
                            var target=member_transport(eps,k,n,d,parent,i,j)
                            var actual=selected_overlap_child(tables,source,i,j)
                            assert_true(actual==geometric_state(tables,target))
                            var overlaps=interior_overlap_cached(tables,cache,actual)
                            assert_true(overlaps==tm_child_allowed(eps,k,t,m,i,j))
                            assert_true(overlaps==(i*(N+2)+j in seen))
                            if overlaps:
                                found+=1
                                accepted+=1
                    assert_true(found==len(edges))
    for reached in attained:
        assert_true(reached)
    var failed=False
    try:
        _=tm_child_allowed(-1,0,0,1,-1,0)
    except:
        failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var parent=BoundaryLabel(2,2,-1,1,1)
    var original=member_transport(-1,0,3,5,parent,0,0)
    failed=False
    try:
        verify_tm_packet(tables,-1,0,0,1,BoundaryEdge(0,0,
            BoundaryLabel(original.top,original.bottom,original.x,original.c,original.y+1)))
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_TM_FINITE members",members,"pairs",pairs,
          "accepted",accepted,"all_nine_kinds=true", "universal_image_labels=50",
          "every_envelope_label_attained=true", "global_closure=false", "BH=false")
    require_contract("class-A boundary both T_m sources all nine first/run/last child kinds; exact chamber guards, complete linear-time occurrence carrier, no duplicates, full Parikh and Perron-field differential replay of every finite pair; invalid ordinals and altered packets refused; no global closure or BH")
