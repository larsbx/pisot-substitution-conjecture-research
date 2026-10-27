"""Canonical exact Perron replay of U ancestry and all ordered children."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, geometric_state,
)
from psc.class_a_boundary_next_run import first_run_allowed
from psc.class_a_boundary_U_star import (
    certify_U_star, U_label, U_child_allowed, U_child_star,
    verify_U_packet, U_target_envelope, in_U_target_envelope,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, seed_overlap_states,
    selected_overlap_child, interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def main() raises:
    certify_U_star()
    var envelope=U_target_envelope()
    assert_true(len(envelope)==12)
    var reached=List[Bool]()
    for _ in envelope:
        reached.append(False)
    var members=0
    var pair_count=0
    var child_count=0
    for k in [0,1,2,4,8,12]:
        for t in [0,1,2,5]:
            members+=1
            var n=k+3+t
            var d=2*n-1-k
            var top_last=n+d+1
            var bot_last=n
            var tables=build_seed_overlap_tables_screened(
                class_member(CLASS_A,n+d,n,n-1))
            var cache=Dict[CubicElt,Int]()
            var seed=BoundaryLabel(0,1,0,0,0)
            var source=geometric_state(tables,seed)
            var found=False
            for initial in seed_overlap_states(tables):
                if initial==source:
                    found=True
            assert_true(found)
            var T1=BoundaryLabel(2,2,-1,1,1)
            var first=selected_overlap_child(tables,source,1,2)
            assert_true(first==geometric_state(tables,T1))
            assert_true(interior_overlap_cached(tables,cache,first))
            assert_true(first_run_allowed(-1,k,t,1,t+1))
            var U=selected_overlap_child(tables,first,0,t+1)
            assert_true(U==geometric_state(tables,U_label()))
            assert_true(interior_overlap_cached(tables,cache,U))

            var star=U_child_star(k,t)
            assert_true(len(star)==2*n-1)
            var seen=Dict[Int,Bool]()
            for edge in star:
                var identity=edge.i*(bot_last+1)+edge.j
                assert_true(identity not in seen)
                seen[identity]=True
                verify_U_packet(tables,k,t,edge)
                for z in range(len(envelope)):
                    if edge.target==envelope[z]:
                        reached[z]=True
            for i in range(top_last+1):
                for j in range(bot_last+1):
                    pair_count+=1
                    var target=member_transport(-1,k,n,d,U_label(),i,j)
                    var actual=selected_overlap_child(tables,U,i,j)
                    assert_true(actual==geometric_state(tables,target))
                    var hit=interior_overlap_cached(tables,cache,actual)
                    assert_true(hit==U_child_allowed(k,t,i,j))
                    assert_true(hit==(i*(bot_last+1)+j in seen))
                    if hit:
                        child_count+=1
    for attained in reached:
        assert_true(attained)
    var failed=False
    try:
        _=U_child_allowed(0,0,-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=U_child_allowed(0,0,1000,0)
    except:
        failed=True
    assert_true(failed)
    var t0=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var good=member_transport(-1,0,3,5,U_label(),7,0)
    failed=False
    try:
        verify_U_packet(t0,0,0,BoundaryEdge(7,0,
            BoundaryLabel(good.top,good.bottom,good.x,good.c,good.y+1)))
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_U_FINITE members",members,
          "pairs",pair_count,"true_edges",child_count,
          "envelope=12","complete_star=true","BH=false")
    require_contract("minus class-A U=(x,y,1,2,-3): all k,t true ordered children in O(n), exact 2n-1 cardinality and 12-target envelope, two-stage literal ancestry, each Parikh/Perron packet verified, all Cartesian counterchecks and invalid/tampered refusals; not BH")
