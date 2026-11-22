"""Census of the origin-tile recurrence of `0 -> 1, 1 -> 0 1^k 2, 2 -> 001`.

For each `k` in the stated range, every interior lattice tile `(a; v)` with
`|v_i| <= BOX` is followed to its cycle by exact sign queries
(`psc.origin_cycle`). The line for `k` gives the maximum distance to a first
cycle tile and lists every cycle reached. The Lean theorem
`periodicLatticeOriginsClassified` gives the interior classification for
all `k >= 2`. For the sampled parameters `k >= 2` the only cycle other than the vertex cycle
`(0;0,0,0) -> (1;0,0,0)` is the three-phase interior cycle
`(1;1,0,0) -> (1;-1,1,0) -> (1;0,0,1)`; `k = 1` is the negative control,
where that cycle does not exist.

Finite evidence for the named box and range of `k` only.  A periodic tile
outside the box is not excluded, and no value of `k` beyond the range is
examined. An orbit that exceeds the step cap raises before the row for its
parameter is printed.
"""

from psc.origin_cycle import OriginSystem, cycle_census, cycle_text

comptime BOX = 8
comptime CAP = 4096
comptime K_MAX = 12


def main() raises:
    print("origin-cycle census: box", BOX, "step cap", CAP)
    for k in range(1, K_MAX + 1):
        var system = OriginSystem(k)
        var census = cycle_census(system, BOX, CAP)
        print("k", k, "interior tiles", census.tiles, "longest transient", census.longest,
              "cycles", len(census.cycles))
        for i in range(len(census.cycles)):
            print("  cycle length", len(census.cycles[i]), ":", cycle_text(census.cycles[i]))
