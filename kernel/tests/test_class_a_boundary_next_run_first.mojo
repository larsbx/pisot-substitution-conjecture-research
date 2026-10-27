"""All indexed run/first children of both actual T_m labels, exact geometry."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, geometric_state, boundary_r,
)
from psc.class_a_boundary_next_run_first import (
    certify_run_first, run_first_allowed, run_first_star, verify_run_first_packet,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child,
    interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def main() raises:
    certify_run_first()
    var members=0
    var ordinals=0
    var accepted=0
    for eps in [-1,1]:
        for k in [0,1,2,3,4,5,6,7,8,12]:
            for t in [0,1,2,6]:
                members+=1
                var n=k+3+t if eps==-1 else 2*(k+2)+t
                var d=2*n+6*eps+5-k
                var tables=build_seed_overlap_tables_screened(
                    class_member(CLASS_A,n+d,n,n+eps))
                var cache=Dict[CubicElt,Int]()
                var r=boundary_r(eps,k)
                for m in range(r,r+2):
                    var parent=BoundaryLabel(2,2,-1,1,m)
                    var source=geometric_state(tables,parent)
                    assert_true(interior_overlap_cached(tables,cache,source))
                    var edges=run_first_star(eps,k,t,m)
                    var found=0
                    for i in range(1,n+eps+1):
                        ordinals+=1
                        var target=member_transport(eps,k,n,d,parent,i,0)
                        assert_true(target==BoundaryLabel(
                            2,0,m-1,m+1,m*(n+eps)-d-i+1))
                        var actual=selected_overlap_child(tables,source,i,0)
                        assert_true(actual==geometric_state(tables,target))
                        var hit=interior_overlap_cached(tables,cache,actual)
                        assert_true(hit==run_first_allowed(eps,k,t,m,i))
                        if hit:
                            found+=1
                            accepted+=1
                    assert_true(found==len(edges))
                    for edge in edges:
                        verify_run_first_packet(tables,eps,k,t,m,edge)
    var failed=False
    try:
        certify_run_first(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=run_first_allowed(1,0,0,3,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=run_first_allowed(1,4,0,3,1)
    except:
        failed=True
    assert_true(failed)
    # A nominal source/target of the right letter type cannot bypass
    # the genuine occurrence index and Parikh guard.
    var t0=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:
        verify_run_first_packet(t0,-1,0,0,2,
            BoundaryEdge(1,0,BoundaryLabel(2,0,1,3,0)))
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_RUN_FIRST_FINITE members",members,
          "ordinals",ordinals,"accepted",accepted,"BH=false")
    require_contract("boundary T_m run/first actual 1..N children: exact Q[t,k] signs, entire three-chamber integer ranges, Parikh/Perron targets, word clips and rejected invalid/damaged evidence; no BH")
