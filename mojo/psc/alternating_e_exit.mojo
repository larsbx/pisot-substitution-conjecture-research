"""Exit profile of the alternating type-E hub star.

In the alternating-E aligned template the prefix endpoint map fixes the hub c
and swaps the Barge-Diamond-good edge G={a,b}. The open transport target of
`docs/p1a-aligned-cycle-normal-form-2026-10-01.md` §5 asks for G to appear as
an offset-zero pair below a bad hub edge. This module measures, exactly, how
the hub star {a,c},{b,c} is actually left: the overlap closure of the two
orientations of the aligned edge (a,c,0) is built in the exact Perron field,
and the profile records whether an offset-zero G vertex is reachable and
whether a coincidence is reachable along paths that never visit one.

A capped closure is inconclusive and fails closed.
"""

from psc.bd_endpoint import complementary_hub_letter
from psc.hub_selector import alternating_e_template
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapTables,
    build_overlap_graph_from_seeds,
)
from psc.perron_field3 import CubicElt


def endpoint_map(sigma: List[List[Int]]) -> List[Int]:
    """`h(x)`: the first letter of `sigma(x)`."""
    return [sigma[0][0], sigma[1][0], sigma[2][0]]


def alternating_e_hub(sigma: List[List[Int]]) raises -> Int:
    """The hub `c` when `h` fixes `c` and swaps the other two letters, else `-1`.

    That edge is then the only good edge for which the aligned template is
    alternating (`alternating_e_template`), so the hub is determined by `h`."""
    var h = endpoint_map(sigma)
    for a in range(3):
        for b in range(a + 1, 3):
            if alternating_e_template(h, a, b):
                return complementary_hub_letter(a, b)
    return -1


struct HubStarExit(Copyable, Movable):
    var reaches_good_edge: Bool
    """Some offset-zero vertex below the hub star carries the pair G."""
    var coincides_avoiding_good_edge: Bool
    """A coincidence is reachable on a path that visits no offset-zero G vertex."""

    def __init__(out self, reaches_good_edge: Bool, coincides_avoiding_good_edge: Bool):
        self.reaches_good_edge = reaches_good_edge
        self.coincides_avoiding_good_edge = coincides_avoiding_good_edge


def _is_good_edge_aligned(s: OverlapState, hub: Int) -> Bool:
    return s.shift.is_zero() and s.top != s.bottom and s.top != hub and s.bottom != hub


def hub_star_exit(
    tables: SeedOverlapTables,
    hub: Int,
    mut sign_cache: Dict[CubicElt, Int],
    max_states: Int = 200000,
) raises -> HubStarExit:
    """Exit profile of the aligned hub edge `{a,c}`, `a` the smaller good letter.

    Both orientations seed the closure; `{b,c}` is the first child of `{a,c}`,
    so its descendants are included."""
    var a = 1 if hub == 0 else 0
    var seeds: List[OverlapState] = [
        OverlapState(a, hub, CubicElt()),
        OverlapState(hub, a, CubicElt()),
    ]
    var g = build_overlap_graph_from_seeds(tables, seeds, sign_cache, max_states)
    if g.capped:
        raise Error("hub-star closure capped: exit profile is inconclusive")
    var reaches = False
    for i in range(g.size()):
        if _is_good_edge_aligned(g.states[i], hub):
            reaches = True
    # Forward search from the seeds that refuses to expand an offset-zero G vertex.
    var seen = List[Bool](length=g.size(), fill=False)
    var queue: List[Int] = [0, 1]
    seen[0] = True
    seen[1] = True
    var head = 0
    var avoiding = False
    while head < len(queue):
        var k = queue[head]
        head += 1
        if g.states[k].is_coincidence():
            avoiding = True
            break
        if _is_good_edge_aligned(g.states[k], hub):
            continue
        for j in range(len(g.adj[k])):
            var c = g.adj[k][j]
            if not seen[c]:
                seen[c] = True
                queue.append(c)
    return HubStarExit(reaches, avoiding)
