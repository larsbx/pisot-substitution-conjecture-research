"""Bounded complete incoming histories, compact-set countermodels and refusals."""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from finite_linear_algebra.integer_vector import add, sub, matvec
from psc.affine_ancestry_trace import build_affine_trace_tables, _prefix_parikh
from psc.c4_bounded_cover import (
    BoundedCover, build_bounded_cover, verify_bounded_cover, cover_summary,
    fixture_cover, node_packet, cover_countercontrols, z3_affine_image,
    z3_tile_equation,
)


def _reject(cover: BoundedCover) raises:
    var refused = False
    try:
        verify_bounded_cover(cover)
    except:
        refused = True
    assert_true(refused)


def test_complete_histories_and_occurrence_multiplicity() raises:
    var first = fixture_cover(0)
    assert_equal(cover_summary(first),[8,24,18,0,2,2,0,2])
    var repeated = fixture_cover(1)
    assert_equal(cover_summary(repeated),[15,28,14,0,8,8,7,1])
    var top_positions = List[Int]()
    for node in repeated.nodes:
        if node[2] == 3:
            assert_equal(node_packet(node),[0,0,0,0,0])
            assert_equal(node[10],node[13])
            assert_equal(node[11]+node[12]+node[14]+node[15],0)
            assert_false(node[10] in top_positions)
            top_positions.append(node[10])
    assert_equal(len(top_positions),8)
    for position in range(8):
        assert_true(position in top_positions)
    for index in range(4):
        var cover = fixture_cover(index)
        verify_bounded_cover(cover)
        var summary = cover_summary(cover)
        if index >= 2:
            assert_true(summary[3] > 0)
            assert_true(summary[4] > summary[5])
        if index == 3:
            assert_equal(cover.determinant,4)
            assert_equal(len(cover.digits),18)
        print("C4_BOUNDED_COVER",index,summary[0],summary[1],summary[2],summary[3],summary[4],summary[5],summary[6],summary[7])
    var zero = build_bounded_cover(first.images,first.roots,first.domain,0)
    assert_equal(len(zero.candidates),0)
    assert_equal(cover_summary(zero),[2,0,0,0,2,2,0,2])


def test_exact_history_mutations() raises:
    var original = fixture_cover(1)
    var changed = original.copy()
    changed.nodes[2][3] = changed.nodes[1][3]
    changed.nodes[2][4] = changed.nodes[1][4]
    # Both endpoint packets are still identical. Literal addresses are not.
    assert_equal(node_packet(changed.nodes[1]),node_packet(changed.nodes[2]))
    _reject(changed)
    changed = original.copy()
    changed.nodes[2] = changed.nodes[1].copy()
    _reject(changed)
    changed = original.copy()
    changed.nodes[2][1] = 2  # circular path reference
    _reject(changed)
    changed = original.copy()
    changed.nodes[2][10] += 1
    _reject(changed)
    changed = original.copy()
    changed.nodes[2][16] = 0
    _reject(changed)
    changed = original.copy()
    changed.nodes[2][17] = 0
    _reject(changed)
    changed = original.copy()
    changed.digits[1][3] = 0
    _reject(changed)
    changed = original.copy()
    changed.candidates[0][3] = 0
    _reject(changed)
    changed = original.copy()
    var fewer = List[List[Int]]()
    for i in range(len(changed.nodes)-1):
        fewer.append(changed.nodes[i].copy())
    changed.nodes = fewer^
    _reject(changed)
    changed = original.copy()
    changed.unique_states += 1
    _reject(changed)
    print("C4_BOUNDED_COVER_MUTATIONS",10)


def test_budget_and_singular_refusals() raises:
    var images: List[List[Int]] = [[0,0],[1,1],[2,2]]
    var roots: List[List[Int]] = [[0,0,0,0,0]]
    var refused = False
    try:
        _ = build_bounded_cover(images,roots,roots,3,history_cap=7)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_bounded_cover(images,roots,roots,3,candidate_cap=3)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_bounded_cover(images,roots,roots,3,word_cap=4)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_bounded_cover([[0,1],[1],[2]],[[0,1,0,0,0]],[[0,1,0,0,0]],1,state_cap=1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_bounded_cover([[0,0],[0,0],[0,0]],roots,roots,1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_bounded_cover(images,[[0,0,65,0,0]],roots,1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_bounded_cover(images,[roots[0].copy(),roots[0].copy()],roots,1)
    except:
        refused = True
    assert_true(refused)
    for depth in [-1,7]:
        refused = False
        try:
            _ = build_bounded_cover(images,roots,roots,depth)
        except:
            refused = True
        assert_true(refused)
    print("C4_BOUNDED_COVER_REFUSALS",9)


def test_inverse_closed_forward_leak() raises:
    var cover = fixture_cover(0)
    assert_equal(cover_summary(cover)[3],0)  # full inverse rows are internal
    var tables = build_affine_trace_tables(cover.images)
    var matrix: List[List[Int]] = [[2,0,0],[0,2,0],[0,0,2]]
    var total_mass = 0
    var retained_mass = 0
    var positive_exits = 0
    for root in cover.roots:
        for i in range(2):
            for j in range(2):
                var top = _prefix_parikh(tables,root[0],i)
                var bottom = _prefix_parikh(tables,root[1],j)
                var delta = sub(add(matvec(matrix,[root[2],root[3],root[4]]),[top.x,top.y,top.z]),[bottom.x,bottom.y,bottom.z])
                var target: List[Int] = [root[0],root[1],delta[0],delta[1],delta[2]]
                var displacement = delta[0]+delta[1]+delta[2]
                # Diagnostic physical interval length only; no compact measure.
                var mass = max(0,min(1,1-displacement)-max(0,-displacement))
                total_mass += mass
                if target in cover.domain:
                    retained_mass += mass
                elif mass > 0:
                    positive_exits += 1
                    assert_equal(i,1)
                    assert_equal(j,1)
    assert_equal(total_mass,4)
    assert_equal(retained_mass,2)
    assert_equal(positive_exits,2)
    print("C4_BOUNDED_COVER_FORWARD_LEAK",total_mass,retained_mass,positive_exits)


def test_compact_finite_group_and_exclusion_countermodels() raises:
    # All three images of multiplication by two are distinct in Z3.
    assert_equal(z3_affine_image(7,2,0),7)
    assert_true(z3_tile_equation([[0,0],[1,1],[2,2]],2,[7,7,7]))
    var controls = cover_countercontrols()
    assert_equal(controls[0],[3,0,4])  # no reflection: full overlap, no integral edge
    assert_equal(controls[1],[0,3])    # physical zero does not imply compact empty
    assert_equal(controls[2],[0,3])    # false enclosure would delete a nonempty set
    assert_equal(controls[3],[1])      # closed boundary contact is a singleton
    assert_equal(controls[4],[2,1])    # two actual nonempty pieces, one retained covers all
    assert_equal(controls[5],[2,1])    # omitting one actual set piece loses a point
    assert_equal(controls[6],[3,1,0])  # internally empty domain misses a real piece
    assert_equal(controls[7],[4,2,2])  # inverse closure does not force forward closure
    print("C4_BOUNDED_COVER_FINITE_SET_CONTROLS",8)


def main() raises:
    test_complete_histories_and_occurrence_multiplicity()
    test_exact_history_mutations()
    test_budget_and_singular_refusals()
    test_inverse_closed_forward_leak()
    test_compact_finite_group_and_exclusion_countermodels()
    require_contract("C4 complete bounded inverse histories preserve literal addresses and multiplicities; domain exits remain visible and exhausted budgets refuse")
    require_contract("C4 compact cover assumptions: inverse-closed forward leak, residue reflection, nonempty omission, redundancy, enclosure and boundary countercontrols")
