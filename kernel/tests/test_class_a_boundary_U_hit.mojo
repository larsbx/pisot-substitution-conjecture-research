"""All four literal seed→T1→U→V→internal coincident occurrence edges."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge, geometric_state,
)
from psc.class_a_boundary_U_hit import (
    certify_U_uniform_hit, U_hit_path, verify_U_hit_path,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child, cached_sign,
)
from psc.perron_field3 import (
    CubicElt, cubic_mul_beta, cubic_add_checked, cubic_sub_checked,
)
from std.collections import Dict


def main() raises:
    certify_U_uniform_hit()
    var members=0
    for k in [0,1,2,4,8,16]:
        for t in [0,1,2,7]:
            members+=1
            var n=k+3+t
            var d=2*n-1-k
            var tables=build_seed_overlap_tables_screened(
                class_member(CLASS_A,n+d,n,n-1))
            verify_U_hit_path(tables,k,t)
            var path=U_hit_path(k,t)
            assert_true(len(path)==4)
            var parent=BoundaryLabel(0,1,0,0,0)
            for edge in path:
                verify_member_edge(tables,-1,k,n,d,
                                   parent,edge.i,edge.j,edge.target)
                parent=edge.target
            assert_true(parent==BoundaryLabel(2,2,0,0,0))

            # Unlike an outer-boundary diagonal, the final y/y pair
            # has a start > left edge and an end < right edge of
            # the inflated V parent overlap (top interval [0,beta*Ly]).
            var cache=Dict[CubicElt,Int]()
            var zero=CubicElt()
            var Ly=tables.lengths.at(2)
            var first_y=tables.prefix(2,1)
            var end_y=cubic_add_checked(first_y,Ly)
            var inflated_top=cubic_mul_beta(tables.field,Ly)
            assert_true(cached_sign(tables,cache,
                             cubic_sub_checked(first_y,zero))>0)
            assert_true(cached_sign(tables,cache,
                             cubic_sub_checked(inflated_top,end_y))>0)
            # Literal top index 1 and bottom index 2 share the
            # same start, not merely the same terminal letter.
            var V=BoundaryLabel(2,0,0,-1,1)
            var parent_state=geometric_state(tables,V)
            var shifted_bottom_start=cubic_add_checked(
                cubic_mul_beta(tables.field,parent_state.shift),
                tables.prefix(0,2))
            assert_true(first_y==shifted_bottom_start)

    var failed=False
    try:
        _=U_hit_path(-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=U_hit_path(0,-1)
    except:
        failed=True
    assert_true(failed)
    # A nearby valid same-letter pair at bottom ordinal 1 is NOT
    # an aligned offset-zero target (actual parent V used).
    var tbl=build_seed_overlap_tables_screened(
        class_member(CLASS_A,8,3,2))
    var wrong=member_transport(-1,0,3,5,
                   BoundaryLabel(2,0,0,-1,1),1,1)
    assert_true(not (wrong==BoundaryLabel(2,2,0,0,0)))
    failed=False
    try:
        verify_member_edge(tbl,-1,0,3,5,
            BoundaryLabel(2,0,0,-1,1),1,1,
            BoundaryLabel(2,2,0,0,0))
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_U_HIT_FINITE members",members,
          "four_edges_per_member=4",
          "last_event_internal=true",
          "universal_BH=false")
    require_contract("minus class-A entire k,t boundary chamber, uniform actual four-step seed/T1/U/V/offset-zero y/y occurrence with true word indices; last common start strictly internal on both inflated tilings; exact Parikh/Perron replay and mutated/index refusals, not universal BH or BPA packet factorization")
