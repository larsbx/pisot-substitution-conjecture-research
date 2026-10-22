"""A formal rectangular cover fails; reachable-state coverage remains open."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_cover_obstruction import verify_cover_identities, replay_cover_escape, in_rectangle
from psc.class_a_run_index import member, labelled, checked_step, complete_graph, check_symbolic_edge
from psc.param_poly import qx_const, qx_affine, qx_neg, qx_add
from psc.overlap_seed_patch import build_seed_overlap_tables_screened


def main() raises:
    verify_cover_identities()
    for n in [4,8,18,64,256]:
        replay_cover_escape(n)
    # These two complete finite seed graphs distinguish formal real overlaps
    # from reachable states. No arbitrary-n nonmembership is inferred.
    for n in [4,18]:
        var tables=build_seed_overlap_tables_screened(member(n))
        var v=labelled(tables,0,1,-n-1,n+4,-2)
        var w=labelled(tables,0,2,-n,n+3,-1)
        var g=complete_graph(n)
        for state in g.states:
            assert_true(state!=v and state!=w)
        print("CLASS_A_COVER_FINITE_NONMEMBERSHIP",n,g.size(),"source=false child=false universal=not_asserted")
    var tables=build_seed_overlap_tables_screened(member(4))
    var source=labelled(tables,0,1,-5,8,-2)
    var target=labelled(tables,0,2,-4,7,-1)
    for mutation in range(3):
        var refused=False
        try:
            if mutation==0:
                _=checked_step(tables,source,0,2,target)
            elif mutation==1:
                _=checked_step(tables,labelled(tables,0,1,5,-8,2),0,3,target)
            else:
                _=checked_step(tables,source,0,3,labelled(tables,0,1,-4,7,-1))
        except:
            refused=True
        assert_true(refused)
    var refused=False
    try:
        var n=qx_affine(0,1)
        check_symbolic_edge(0,1,[qx_neg(qx_add(n,qx_const(1))),qx_add(n,qx_const(4)),qx_const(-2)],qx_const(0),qx_const(3),0,1,0,2,[qx_neg(n),qx_add(n,qx_const(3)),qx_const(0)])
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        replay_cover_escape(3)
    except:
        refused=True
    assert_true(refused)
    assert_true(in_rectangle(4,-5,8,-2))
    assert_true(not in_rectangle(4,-4,7,-1))
    require_contract("class-A rectangular formal cover is not forward closed: uniform polynomial length/edge/margin identities and strict ordered replay; finite seed nonmembership only; index, orientation, type and polynomial refusals; no reachable escape or BH failure asserted")
