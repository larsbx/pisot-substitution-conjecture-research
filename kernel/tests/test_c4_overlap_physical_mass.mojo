"""Guard the orientation, completeness, and conservative-block refusal."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_overlap_physical_mass import certify_physical_mass, source_loss_witnesses
from psc.c4_pair_overlap_new_incidence import build_new_incidence_graph


def main() raises:
    var rows: List[List[Int]] = [[1], []]
    var witnesses = source_loss_witnesses(rows, [True, False], 1)
    assert_equal(len(witnesses), 1)
    assert_equal(witnesses[0][2], 0)

    # theta=2, H=(1,1), e=(0,1), v=(1,0). Checking just the inverse
    # sink would falsely certify nullity despite the conservative source.
    var conservative: List[List[Int]] = [[0, 0, 1], []]
    var refused = False
    try:
        _ = source_loss_witnesses(conservative, [False, True], 1)
    except:
        refused = True
    assert_true(refused)

    var disconnected: List[List[Int]] = [[], []]
    refused = False
    try:
        _ = source_loss_witnesses(disconnected, [True, True], 1)
    except:
        refused = True
    assert_true(refused)

    var graph = build_new_incidence_graph(0)
    var report = certify_physical_mass(graph)
    assert_equal(len(report[0]), 3664)
    assert_equal(len(report[2]), 1)
    assert_equal(report[2][0][2], 2)

    # Removing one occurrence can create artificial loss, including when
    # another occurrence to the same target remains in the row.
    var changed = False
    for i in range(len(graph.rows)):
        for j in range(1, len(graph.rows[i])):
            if graph.rows[i][j] == graph.rows[i][0]:
                var row = List[Int]()
                for k in range(1, len(graph.rows[i])):
                    row.append(graph.rows[i][k])
                graph.rows[i] = row^
                changed = True
                break
        if changed:
            break
    assert_true(changed)
    refused = False
    try:
        _ = certify_physical_mass(graph)
    except:
        refused = True
    assert_true(refused)
    require_contract("C4 physical mass authenticates every occurrence and refuses conservative inverse source SCCs")
