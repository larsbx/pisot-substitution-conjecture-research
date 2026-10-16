"""Exact uniform-tail closure, finite prefix, full-support checks and refusals."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_d_boundary_template import offset_sign, affine_nonnegative, boundary_template, certify_minus_boundary, check_exact_support, template_depths


def main() raises:
    assert_equal(offset_sign(0,0,0,4),0)
    assert_equal(offset_sign(1,2,-4,4),1)
    assert_equal(offset_sign(-1,-2,4,4),-1)
    assert_true(affine_nonnegative(1,-3,3))
    assert_true(not affine_nonnegative(-1,2,3))
    var refused = False
    try:
        _ = offset_sign(1,2,-4,0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = affine_nonnegative(1,-3,2)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = boundary_template(4,1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = boundary_template(3)
    except:
        refused = True
    assert_true(refused)
    var g = certify_minus_boundary()
    assert_equal(len(g.vertices),145)
    assert_equal(g.edge_count(),781)
    var counts = List[Int](length=5,fill=0)
    for d in template_depths(g):
        assert_true(d >= 0 and d <= 4)
        counts[d] += 1
    assert_equal(counts,List[Int]([6,15,50,72,2]))
    # Same vertices, altered outgoing support: cross-check must reject it.
    var altered = False
    for i in range(len(g.adj)):
        if len(g.adj[i]) > 0:
            g.adj[i] = List[Int]()
            altered = True
            break
    assert_true(altered)
    refused = False
    try:
        check_exact_support(g,4)
    except:
        refused = True
    assert_true(refused)
    require_contract("class-D minus b=0 complete-line candidate: exhaustive symbolic seed/child closure for a>=4, exact finite prefix a=0..3, 145 vertices and 781 directed edges, all half-depths <=4, full-support checks at a=4,8; mixed signs, range changes, lowered floor, cap and same-vertex edge deletion refuse; no plus-branch or two-parameter closure")
