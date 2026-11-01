"""Uniform complete R/T/U stars; conditional integer transfer is shared."""
from psc.class_c_seed_interfaces import SeedInterface
from psc.class_c_boundary_frontier import BoundaryOffset
from psc.overlap_seed_patch import OverlapState


def r_parent(m: SeedInterface, index: Int) raises -> OverlapState:
    if m.eps != 1 or m.c != 0 or index < 0 or index > 2:
        raise Error("R/T/U interfaces require plus c=0 and index 0..2")
    if index == 0:
        return BoundaryOffset(-2,2,1).state(m,0,1)
    if index == 1:
        return BoundaryOffset(-1,1,-4).state(m,0,0)
    return BoundaryOffset(3,-3,4).state(m,0,2)


def r_children(m: SeedInterface, index: Int) raises -> List[OverlapState]:
    _ = r_parent(m,index)
    var out = List[OverlapState]()
    if index == 0:
        out.append(r_parent(m,1))
    elif index == 1:
        for s in range(4):
            out.append(BoundaryOffset(s,-3,4).state(m,0,2))
        for s in range(2):
            out.append(BoundaryOffset(s,-4,2).state(m,2,2))
        for s in range(-2,2):
            out.append(BoundaryOffset(s,-4,2).state(m,2,0))
    else:
        out.append(BoundaryOffset(-1,3,0).state(m,0,1))
        for s in range(1,3):
            out.append(BoundaryOffset(s,3,1).state(m,0,2))
        out.append(BoundaryOffset(0,3,0).state(m,2,1))
    return out^
