"""Plus-tail full child closure, exact prefix including empty run, and refusals."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_d_boundary import boundary_member
from psc.class_d_boundary_template import offset_sign, boundary_template, certify_plus_boundary, check_exact_support, template_depths


def main() raises:
    # The branch-dependent Perron difference is ell_x-ell_c=s/beta.
    assert_equal(offset_sign(1,-1,0,7,1),1)
    assert_equal(offset_sign(1,-1,0,7,-1),-1)
    var initial = boundary_member(1,0)
    assert_equal(initial[2],List[Int]([1,1]))
    var refused = False
    try:
        _ = boundary_template(0,20000,1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = boundary_template(6,20000,1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = boundary_template(7,1,1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = boundary_template(7,20000,0)
    except:
        refused = True
    assert_true(refused)
    var g = certify_plus_boundary()
    assert_equal(g.branch,1)
    assert_equal(g.floor,7)
    assert_equal(len(g.vertices),718)
    assert_equal(g.edge_count(),4326)
    var counts = List[Int](length=7,fill=0)
    for d in template_depths(g):
        assert_true(d >= 0 and d <= 6)
        counts[d] += 1
    assert_equal(counts,List[Int]([6,27,102,243,196,136,8]))
    for i in range(len(g.adj)):
        if len(g.adj[i]) > 0:
            g.adj[i] = List[Int]()
            break
    refused = False
    try:
        check_exact_support(g,7)
    except:
        refused = True
    assert_true(refused)
    require_contract("class-D plus b=0 complete-line candidate: exhaustive symbolic seed/child closure for a>=7, exact finite prefix a=0..6 including the empty y-run, 718 vertices and 4326 directed edges, half-depth <=6; full-support checks at a=7,8; wrong branch, empty-run tail, unsupported floor, cap and same-vertex edge deletion refuse; no b>0 closure")
