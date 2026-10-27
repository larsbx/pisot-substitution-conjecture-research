"""Every U child pair, exact target image, four-cycle and invalid controls."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge,
)
from psc.class_a_boundary_u_children import (
    certify_u_children, u_child_allowed, u_child_star, verify_u_packet,
    u_target_envelope, reverse_label,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def main() raises:
    certify_u_children()
    var pairs=0
    var accepted=0
    var cycles=0
    var envelope=u_target_envelope()
    var attained=List[Bool]()
    for _ in envelope:
        attained.append(False)
    var parent=BoundaryLabel(0,2,1,2,-3)
    var T1=BoundaryLabel(2,2,-1,1,1)
    for k in range(8):
        for t in range(7):
            var n=k+3+t
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            var source=geometric_state(tables,parent)
            assert_true(interior_overlap_cached(tables,cache,source))
            # Uniform two-level incoming witness, preserving concrete indices.
            verify_member_edge(tables,-1,k,n,d,BoundaryLabel(0,1,0,0,0),1,2,T1)
            verify_member_edge(tables,-1,k,n,d,T1,0,t+1,parent)
            var seen=Dict[Int,Bool]()
            var edges=u_child_star(k,t)
            assert_true(len(edges)==2*n-1)
            for edge in edges:
                var key=edge.i*(n+1)+edge.j
                assert_true(key not in seen)
                seen[key]=True
                verify_u_packet(tables,k,t,edge)
                verify_member_edge(tables,-1,k,n,d,reverse_label(parent),edge.j,edge.i,
                                   reverse_label(edge.target))
                var found=False
                for z in range(len(envelope)):
                    if edge.target==envelope[z]:
                        attained[z]=True
                        found=True
                assert_true(found)
            for i in range(A+2):
                for j in range(n+1):
                    pairs+=1
                    var target=member_transport(-1,k,n,d,parent,i,j)
                    var actual=selected_overlap_child(tables,source,i,j)
                    assert_true(actual==geometric_state(tables,target))
                    var overlaps=interior_overlap_cached(tables,cache,actual)
                    assert_true(overlaps==u_child_allowed(k,t,i,j))
                    assert_true(overlaps==(i*(n+1)+j in seen))
                    if overlaps:
                        accepted+=1
            if n>=5:
                verify_member_edge(tables,-1,k,n,d,parent,d+5,1,reverse_label(T1))
                verify_member_edge(tables,-1,k,n,d,reverse_label(T1),t+1,0,reverse_label(parent))
                verify_member_edge(tables,-1,k,n,d,reverse_label(parent),1,d+5,T1)
                cycles+=1
            assert_true(not u_child_allowed(k,t,0,0))
            assert_true(not u_child_allowed(k,t,1,1))
            assert_true(not u_child_allowed(k,t,A+1,n))
    for reached in attained:
        assert_true(reached)
    var failed=False
    try:
        certify_u_children(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=u_child_allowed(0,0,10,0)
    except:
        failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:
        verify_u_packet(tables,0,0,BoundaryEdge(7,0,BoundaryLabel(2,0,0,-1,3)))
    except:
        failed=True
    assert_true(failed)
    # Word-legal but geometrically disjoint, even with the correct transport.
    failed=False
    try:
        verify_u_packet(tables,0,0,BoundaryEdge(0,0,member_transport(-1,0,3,5,parent,0,0)))
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_U_FINITE members=56", "pairs",pairs,
          "accepted",accepted,"four_cycle_members",cycles,
          "image_labels=12", "all_labels_attained=true", "BH=false")
    require_contract("class-A minus boundary U all nine child kinds; complete linear-time occurrence carrier and exact 12-label image; every finite child checked against full Parikh/Perron geometry, orientation reversal and actual four-cycle; illegal and disjoint occurrences and changed targets refused; no global closure, all-edge descent or BH")
