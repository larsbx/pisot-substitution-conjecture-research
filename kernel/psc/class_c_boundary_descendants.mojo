"""Two complete plus-boundary descendant stars, uniformly d>=7 in the proof.

Executable replay inherits SeedInterface's d=7..64 budget. No graph is built.
Proof: docs/class-c-boundary-descendants-2026-10-30.md.
"""
from std.collections import Dict
from psc.class_c_seed_interfaces import SeedInterface
from psc.overlap_seed_patch import OverlapState, interior_overlap_cached
from psc.perron_field3 import CubicElt


def boundary_parent(m: SeedInterface, stage: Int) raises -> OverlapState:
    if m.eps != 1 or m.c != 0 or stage < 0 or stage > 1:
        raise Error("boundary descendants require plus c=0 and stage 0 or 1")
    if stage == 0:
        return OverlapState(0,2,m.v(1,1,-6))
    return OverlapState(0,1,m.v(3,-10,10))


def boundary_children(m: SeedInterface, stage: Int) raises -> List[OverlapState]:
    _ = boundary_parent(m,stage)
    var out = List[OverlapState]()
    if stage == 0:
        out.append(boundary_parent(m,1))
    else:
        for t in range(7,11):
            out.append(OverlapState(0,2,m.v(-4,11,-t)))
        for t in range(6,8):
            out.append(OverlapState(2,2,m.v(-5,11,-t)))
        for t in range(6,10):
            out.append(OverlapState(2,0,m.v(-5,11,-t)))
    var seen = Dict[OverlapState,Bool]()
    var cache = Dict[CubicElt,Int]()
    for i in range(len(out)):
        if out[i] in seen or not interior_overlap_cached(m.tables,cache,out[i]):
            raise Error("boundary descendant formula duplicate or non-overlap")
        seen[out[i]] = True
    return out^
