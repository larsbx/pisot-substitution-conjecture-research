"""Both class-A determinant signs: two-parameter identities and exact non-transfer."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_run_index import labelled
from psc.class_a_typed_carrier import template_rows
from psc.class_a_residual_geometry import (
    certify_general_class_a_geometry, _check_columns, _check_child_columns,
    _check_d2_nontransfer_rows,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, interior_overlap,
)


def main() raises:
    certify_general_class_a_geometry()
    # The analytic all-n countermodel has a faithful finite native replay at
    # q=n=4,d=2,r=n+1: the formal row label is not an actual real overlap.
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,6,4,5))
    var witness=labelled(tables,2,2,-4,6,-2)
    assert_true(not interior_overlap(tables,witness))
    # Invalid determinant signs cannot silently borrow a two-sign contract.
    var refused=False
    try:
        _check_columns(0)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _check_child_columns(0)
    except:
        refused=True
    assert_true(refused)
    # Alter the witness row itself: the historical-carrier locator is an
    # auditable dependence, not a handwritten assertion immune to changes.
    var damaged=List[List[Int]]()
    for row in template_rows():
        if row[0]==2 and row[1]==2 and row[2]==0 and row[3]==-2:
            continue
        damaged.append(row.copy())
    refused=False
    try:
        _check_d2_nontransfer_rows(damaged)
    except:
        refused=True
    assert_true(refused)
    require_contract("class-A determinant-two both-sign Q[n,d,h] eigenlength and incidence identities, exact child-coordinate columns; uniform n>=4 d=2 plus obstruction to transplanting the d=1 carrier (formal strict-geometry failure, not nonproductivity), native n=4 and malformed/sign refusals")
