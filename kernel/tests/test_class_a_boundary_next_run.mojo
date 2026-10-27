"""All actual first/run ordinals; independent Perron geometry and target guards."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, geometric_state, boundary_r,
)
from psc.class_a_boundary_next_run import (
    certify_next_run, first_run_allowed, first_run_star, verify_first_run_packet,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def main() raises:
    certify_next_run()
    var total=0
    var accepted=0
    var members=0
    for eps in [-1,1]:
        for k in [0,3,4,5,6,7,8,12]:
            for t in [0,1,2,5,30]:
                members+=1
                var n=k+3+t if eps==-1 else 2*(k+2)+t
                var d=2*n+6*eps+5-k
                var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n+eps))
                var cache=Dict[CubicElt,Int]()
                var r=boundary_r(eps,k)
                for m in range(r,r+2):
                    var parent=BoundaryLabel(2,2,-1,1,m)
                    var source=geometric_state(tables,parent)
                    assert_true(interior_overlap_cached(tables,cache,source))
                    var edges=first_run_star(eps,k,t,m)
                    var found=0
                    for j in range(1,n+eps+1):
                        total+=1
                        var target=member_transport(eps,k,n,d,parent,0,j)
                        assert_true(target==BoundaryLabel(0,2,m,m+1,m*(n+eps)-d+j-1))
                        var actual=selected_overlap_child(tables,source,0,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==first_run_allowed(eps,k,t,m,j))
                        if overlaps:
                            found+=1
                            accepted+=1
                    assert_true(found==len(edges))
                    for edge in edges:
                        verify_first_run_packet(tables,eps,k,t,m,edge)
                        if m==1:
                            var q=edge.j-t if eps==-1 else edge.j-k-t-11
                            assert_true(edge.target==BoundaryLabel(0,2,1,2,q-4))
                        else:
                            assert_true(edge.target==BoundaryLabel(0,2,2,3,k-10+edge.j))
    var failed=False
    try:
        certify_next_run(True)
    except:
        failed=True
    assert_true(failed)
    for bad_j in [0,5]:
        failed=False
        try:
            _=first_run_allowed(-1,0,2,1,bad_j)
        except:
            failed=True
        assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,14,5,4))
    # j=4 exists as a y, but its child is physically disjoint.
    var parent=BoundaryLabel(2,2,-1,1,1)
    var disjoint=member_transport(-1,0,5,9,parent,0,4)
    failed=False
    try:
        verify_first_run_packet(tables,-1,0,2,1,BoundaryEdge(0,4,disjoint))
    except:
        failed=True
    assert_true(failed)
    # A geometrically valid ordinal with an altered target coordinate.
    var edge=BoundaryEdge(0,1,BoundaryLabel(0,2,1,2,-4))
    failed=False
    try:
        verify_first_run_packet(tables,-1,0,2,1,edge)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=first_run_star(1,4,0,3)
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_NEXT_RUN_FINITE members",members,"ordinals",total,
          "accepted",accepted,"infinite_proof=coefficient_identities_and_written_rounding",
          "BH=false")
    require_contract("class-A boundary T_m complete first/run indexed children on all chambers; canonical polynomial identities, word clips and exact Parikh/Perron target packets; all finite ordinals, polynomial corruption, unavailable runs, disjoint children and altered targets; no closure or BH")
