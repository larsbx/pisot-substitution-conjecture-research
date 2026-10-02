"""Which letter pairs a single swap seed exposes at offset zero.

Theorem 5.38 needs only the overlaps reachable from one swap seed `(ab, ba)`.
The seed contains `(a,b,0)` itself, so its productivity already forces `{a,b}`
to be eventually coincident (Barge-Diamond). Every other distinct-letter
offset-zero vertex reachable from the seed adds the eventual coincidence of
its pair to the aligned obligation. This module reports that set of pairs as
a bit mask: bit `x + y - 1` for the unordered pair `{x,y}` (`{0,1}`, `{0,2}`,
`{1,2}` give bits 0, 1, 2). The closure stops at coincidences, as in
`build_overlap_graph_from_seeds`, and a capped closure fails closed.
"""

from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapTables,
    build_overlap_graph_from_seeds,
    seed_overlap_states_cached,
)
from psc.perron_field3 import CubicElt

comptime ALL_PAIRS = 7


def pair_bit(x: Int, y: Int) -> Int:
    return 1 << (x + y - 1)


def pair_seed_states(
    tables: SeedOverlapTables, a: Int, b: Int, mut sign_cache: Dict[CubicElt, Int]
) raises -> List[OverlapState]:
    """The overlaps of the swap seed `(ab, ba)` alone."""
    var all_seeds = seed_overlap_states_cached(tables, sign_cache)
    var out = List[OverlapState]()
    for k in range(len(all_seeds)):
        var t = all_seeds[k]
        if (t.top == a or t.top == b) and (t.bottom == a or t.bottom == b):
            out.append(t)
    return out^


def seed_aligned_pair_mask(
    tables: SeedOverlapTables,
    a: Int,
    b: Int,
    mut sign_cache: Dict[CubicElt, Int],
    max_states: Int = 200000,
) raises -> Int:
    """Mask of the pairs met at offset zero below the swap seed of `{a,b}`."""
    var seeds = pair_seed_states(tables, a, b, sign_cache)
    var g = build_overlap_graph_from_seeds(tables, seeds, sign_cache, max_states)
    if g.capped:
        raise Error("seed closure capped: aligned pair mask is inconclusive")
    var mask = 0
    for i in range(g.size()):
        ref t = g.states[i]
        if t.shift.is_zero() and t.top != t.bottom:
            mask |= pair_bit(t.top, t.bottom)
    if (mask & pair_bit(a, b)) == 0:
        raise Error("a swap seed must expose its own pair at offset zero")
    return mask
