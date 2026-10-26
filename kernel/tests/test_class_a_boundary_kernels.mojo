"""Exact symbolic chambers, typed occurrence indices, and real geometry refusals."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_boundary_signs import certify_all_chambers, certify_chamber_signs
from psc.class_a_boundary_occurrences import (
    certify_all_typed_occurrences, certify_typed_occurrences,
)
from psc.class_a_run_index import labelled
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child,
    interior_overlap, seed_overlap_states,
)


def _geometry(eps: Int, n: Int, d: Int) raises:
    var tables=build_seed_overlap_tables_screened(
        class_member(CLASS_A,n+d,n,n+eps))
    var root=labelled(tables,0,1,0,0,0)
    assert_true(interior_overlap(tables,root))
    var found=False
    for x in seed_overlap_states(tables):
        if x==root:
            found=True
    assert_true(found)
    var first=selected_overlap_child(tables,root,0,0)
    assert_true(first==root)
    var same_letter=selected_overlap_child(tables,root,1,1)
    assert_true(same_letter==labelled(tables,2,2,-1,1,0))
    assert_true(not interior_overlap(tables,same_letter))


def main() raises:
    certify_all_chambers()
    certify_all_typed_occurrences()
    # Exact Perron-field agreement with literal selected occurrence pairs,
    # for both determinant signs; these are samples, not the uniform theorem.
    _geometry(-1,3,5)
    _geometry(1,4,19)

    var failed=False
    try:
        certify_chamber_signs(0)
    except:
        failed=True
    assert_true(failed)
    for eps in [-1,1]:
        failed=False
        try:
            certify_chamber_signs(eps,True)
        except:
            failed=True
        assert_true(failed)
        failed=False
        try:
            certify_typed_occurrences(eps,True)
        except:
            failed=True
        assert_true(failed)
    require_contract("class-A l=0 all-k,t exact nonnegative-cone signs and u>1; indexed first/run/last Parikh transport; rejected malformed polynomial, invalid sign, run indices and false same-letter geometry; no BH")
