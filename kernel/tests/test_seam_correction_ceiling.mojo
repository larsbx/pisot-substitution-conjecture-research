"""Source ceiling of the one-track seam correction against literal full boxes."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.one_track_seam_spectrum import one_track_seam_cycles, overlap_boundary_masks
from psc.periodic_overlap_returns import PeriodicOverlapGraph
from psc.seam_correction_ceiling import MAX_ORDER, SeamCeiling, copy_trace, seam_ceiling

comptime TRACE_HORIZON = 60


def _mobius(n: Int) -> Int:
    var m = n
    var sign = 1
    var p = 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            sign = -sign
        p += 1
    return -sign if m > 1 else sign


def corrections_from_traces(sigma: List[List[Int]], ceiling: SeamCeiling) raises -> List[Int]:
    """Net orbit counts u_k from fixed counts by Mobius inversion, then
    b_d = sum of u_k over d | k. Independent of the orbit weights."""
    var traces = List[Int](length=TRACE_HORIZON + 1, fill=0)
    for n in range(1, TRACE_HORIZON + 1):
        traces[n] = copy_trace(sigma, ceiling, n)
    var net = List[Int](length=TRACE_HORIZON + 1, fill=0)
    for k in range(1, TRACE_HORIZON + 1):
        var total = 0
        for j in range(1, k + 1):
            if k % j == 0:
                total += _mobius(k // j) * traces[j]
        assert_equal(total % k, 0)
        net[k] = total // k
    # every orbit of the whole copy has length at most 5 * 6 here
    for k in range(31, TRACE_HORIZON + 1):
        assert_equal(net[k], 0)
    var out = List[Int]()
    for d in range(1, MAX_ORDER + 1):
        var b = 0
        for k in range(d, TRACE_HORIZON + 1, d):
            b += net[k]
        out.append(b)
    return out^


def check(
    sigma: List[List[Int]], periods: List[Int], ceiling: List[Int], floor: List[Int], whole: List[Int]
) raises:
    var c = seam_ceiling(sigma)
    print(sigma, "periods", c.periods, "ceiling", c.ceiling, "floor", c.floor, "whole", c.whole)
    assert_equal(c.periods, periods)
    assert_equal(c.ceiling, ceiling)
    assert_equal(c.floor, floor)
    assert_equal(c.whole, whole)
    assert_equal(corrections_from_traces(sigma, c), whole)
    # The complete overlap box realizes the whole copy literally.
    var graph = PeriodicOverlapGraph(sigma)
    assert_equal(graph.aligned_sinks, 0)
    var profile = one_track_seam_cycles(graph.graph.adj, overlap_boundary_masks(graph.tables, graph.graph.states))
    for d in range(1, MAX_ORDER + 1):
        assert_equal(profile.cyclotomic_correction(d), whole[d - 1])
        assert_true(floor[d - 1] <= whole[d - 1] and whole[d - 1] <= ceiling[d - 1])


def main() raises:
    # det +1: epsilon = +1 at every weight. Positive literal correction at +1
    # from K_{2,3} copied over one interior 4-cycle.
    check([[0, 1], [1, 2, 2], [2, 0, 1]], [4], [1, 1, 0, 1], [-2, -2, 0, -2], [1, 1, 0, 1])
    # #601 controls: the 01/12/021 square, 1/02/202, and two (F) specimens.
    check([[0, 1], [1, 2], [0, 2, 1]], [1], [0, 1, 0, 0], [-1, 0, 0, 0], [-1, 1, 0, 0])
    check([[1], [0, 2], [2, 0, 2]], [2], [0, 0, 0, 0], [-1, -1, 0, 0], [-1, -1, 0, 0])
    check([[1], [2], [0, 2, 1]], [], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0])
    check([[0, 1], [0, 2], [0]], [], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0])
    # det -1: literal +2 at -1; and a ceiling at +1 above the whole copy.
    check([[1, 2], [0, 2, 1], [1, 2, 2]], [3, 1], [0, 2, 0, 0], [-2, 0, -1, 0], [-2, 2, -1, 0])
    check([[1, 2], [1, 2, 0], [2, 2, 1]], [3, 1], [1, 0, 2, 0], [-3, 0, -2, 0], [0, 0, 2, 0])

    var refused = False
    try:
        _ = seam_ceiling([[0, 0, 1], [2], [0, 0]])
    except e:
        refused = String(e).find("unimodular") >= 0
    assert_true(refused)

    require_contract("The source seam ceiling bounds the one-track correction by invariant subgraphs of copied cyclic bigram graphs. Whole-copy values agree with Mobius-inverted fixed counts and with literal full boxes. A det +1 PIP fixture has positive correction at +1; nonunit input refuses.")
