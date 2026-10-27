"""Exact symbolic chambers, typed occurrence indices, and real geometry refusals."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_boundary_signs import certify_all_chambers, certify_chamber_signs
from psc.class_a_boundary_occurrences import (
    certify_all_typed_occurrences, certify_typed_occurrences,
)
from psc.class_a_boundary_run_pairs import (
    certify_run_pair_chambers, run_pair_allowed,
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


def _run_pair_geometry(eps: Int, n: Int, d: Int, k: Int) raises:
    # Replay every possible delta=1,2,3 from a real seed with
    # genuine run ordinal (top i=1, bottom j=1+delta).
    var tables=build_seed_overlap_tables_screened(
        class_member(CLASS_A,n+d,n,n+eps))
    var root=labelled(tables,0,1,0,0,0)
    for delta in range(1,4):
        var child=selected_overlap_child(tables,root,1,1+delta)
        assert_true(child.top==2 and child.bottom==2)
        assert_true(interior_overlap(tables,child)==run_pair_allowed(eps,k,delta))


def main() raises:
    certify_all_chambers()
    certify_all_typed_occurrences()
    certify_run_pair_chambers()
    # Exact Perron-field agreement with literal selected occurrence pairs,
    # for both determinant signs; these are samples, not the uniform theorem.
    _geometry(-1,3,5)
    _geometry(1,4,19)
    _run_pair_geometry(-1,4,7,0)
    _run_pair_geometry(1,4,19,0)
    _run_pair_geometry(1,12,31,4)

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
    failed=False
    try:
        certify_run_pair_chambers(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=run_pair_allowed(1,-1,2)
    except:
        failed=True
    assert_true(failed)
    require_contract("class-A l=0 all-k,t exact nonnegative-cone signs and u>1; indexed first/run/last Parikh transport; rejected malformed polynomial, invalid sign, run indices and false same-letter geometry; exact all-delta run/run child classification across k=3/4, corruption and invalid-k refusals; no BH")
