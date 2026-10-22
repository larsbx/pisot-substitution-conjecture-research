"""Guard the explicit run-index family and its scope; no all-class-A BH claim."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_a_run_index import (
    member, labelled, checked_step, replay_family, complete_graph, probe,
    verify_symbolic_identities, check_symbolic_edge,
)
from psc.param_poly import qx_const
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, interior_overlap
from a1_normal_form_census import class_member, CLASS_A


def main() raises:
    verify_symbolic_identities()
    for n in [4,8,18,24,64]:
        assert_equal(replay_family(n),n+2)
    var row=probe(18)
    assert_equal(row,List[Int]([835,15,832,15,14]))
    # A genuine recurrent seed vertex needs 15 steps: K=14 is already false.
    var refused=False
    try:
        _=complete_graph(4,1)
    except:
        refused=True
    assert_true(refused)
    var tables=build_seed_overlap_tables_screened(member(4))
    var a=labelled(tables,1,2,4,-4,0)
    var b=labelled(tables,2,0,4,-5,1)
    _=checked_step(tables,a,4,0,b)
    # Altered occurrence, reversed offset and wrong child letter must refuse.
    for mode in range(3):
        refused=False
        try:
            var parent=a
            var expected=b
            var ti=4
            if mode==0:
                ti=3
            elif mode==1:
                parent=labelled(tables,1,2,-4,4,0)
            else:
                expected=labelled(tables,1,0,4,-5,1)
            _=checked_step(tables,parent,ti,0,expected)
        except:
            refused=True
        assert_true(refused)
    # A touching endpoint is not an interior overlap; zero offset alone is
    # not equal-letter coincidence.
    assert_true(not interior_overlap(tables,labelled(tables,1,2,0,1,0)))
    var aligned=labelled(tables,1,2,0,0,0)
    assert_true(interior_overlap(tables,aligned))
    assert_true(not aligned.is_coincidence())
    # Tamper with the closing polynomial edge, not just a numerical sample.
    refused=False
    try:
        check_symbolic_edge(2,0,[qx_const(0),qx_const(-1),qx_const(1)],qx_const(2),qx_const(1),1,1,2,2,[qx_const(1),qx_const(0),qx_const(0)])
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=build_seed_overlap_tables_screened(class_member(CLASS_A,2,1,1))
    except:
        refused=True
    assert_true(refused)  # det=0 is outside the PIP family
    for n in [0,257]:
        refused=False
        try:
            _=member(n)
        except:
            refused=True
        assert_true(refused)
    require_contract("class-A explicit run-index family: polynomial bootstrap/cycle/descent/eigenvector identities; exact ordered geometric replay; finite recurrent K14 countermodel; cap, non-PIP, orientation, index, endpoint and target-semantic refusals; no all-class-A/C or universal BH claim")
