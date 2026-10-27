"""Class-A l=0 boundary-layer exact polynomial identities and refusals."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_boundary_layer import (
    certify_class_a_boundary_layer, _check_boundary_polynomials,
)


def main() raises:
    certify_class_a_boundary_layer()
    var failed=False
    try:
        _check_boundary_polynomials(0)
    except:
        failed=True
    assert_true(failed)
    # If one coefficient of the claimed exact rational endpoint formula is
    # corrupted, symbolic verification refuses, rather than certifying samples.
    failed=False
    try:
        _check_boundary_polynomials(-1,True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _check_boundary_polynomials(1,True)
    except:
        failed=True
    assert_true(failed)
    require_contract("class-A l=0 boundary-distance rays: exact integral coefficient checks for non-Perron root endpoint brackets (both signs), invalid-sign and mutated-identity refusals; not BH")
