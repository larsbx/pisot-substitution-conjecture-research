"""Uniform domain premises, exact boundary controls and middle-strip BH contract.

The expensive graph certificates are separately replayed in the workflow.
"""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_lower_strip import boundary_identities, domain_identities, middle_cone
from psc.param_poly import qx_at
from finite_linear_algebra.scalar import q_int


def main() raises:
    for eps in [1, -1]:
        assert_true(domain_identities(eps).startswith("DOMAIN"))
        boundary_identities(eps)
        var cone = middle_cone(eps, 16, 16)
        # Independent hand substitution u=1,v=2: d=35,n=122.
        assert_true(qx_at(cone.run[0], 2, 1).eq(q_int(157)))
        assert_true(qx_at(cone.run[1], 2, 1).eq(q_int(122)))
        assert_true(qx_at(cone.run[2], 2, 1).eq(q_int(87 + eps)))
    for eps in [0, 2]:
        var raised = False
        try:
            _ = middle_cone(eps, 16, 16)
        except:
            raised = True
        assert_true(raised)
    for a in [0, 25]:
        var raised = False
        try:
            _ = middle_cone(1, a, 16)
        except:
            raised = True
        assert_true(raised)
    require_contract("class C lower-strip polynomial domain premises for all d>=6, n>=2d-5 plus / 2d+1 minus; chi(-1)=0 one below and 2 two below; integral middle-cone parametrization and invalid-input refusals; all-vertex graph certificates replay separately")
