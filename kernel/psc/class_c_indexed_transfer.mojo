"""Exact A_K boundary stars, 0<=K<=d, including the sharp K=d wall.

This direct symbolic family is not restricted to the shared (5,10) query
envelope. Its all-parameter proof is docs/class-c-indexed-transfer-2026-10-30.md.
"""
from psc.class_c_seed_interfaces import SeedInterface
from psc.class_c_boundary_frontier import BoundaryOffset
from psc.overlap_seed_patch import OverlapState


def indexed_parent(m: SeedInterface, K: Int) raises -> OverlapState:
    if m.eps != 1 or m.c != 0 or K < 0 or K > m.d:
        raise Error("indexed boundary family requires plus c=0 and 0<=K<=d")
    return BoundaryOffset(-1,3,-K).state(m,0,1)


def indexed_children(m: SeedInterface, K: Int) raises -> List[OverlapState]:
    _ = indexed_parent(m,K)
    var out = List[OverlapState]()
    var wall = K == m.d
    for j in range(m.d-5,m.d-2+(1 if wall else 0)+1):
        out.append(BoundaryOffset(-m.d+5+j,-K,K-1).state(m,0,2))
    for ell in range(m.d-2+(1 if wall else 0),m.d+(1 if wall else 0)):
        out.append(BoundaryOffset(-m.d+2+ell,-K-1,K-3).state(m,2,2))
    for i in range(m.d-4-(1 if wall else 0),m.d):
        out.append(BoundaryOffset(m.d-3-i,-K-1,K-3).state(m,2,0))
    return out^


def indexed_representatives(d: Int) raises -> List[Int]:
    if d < 7 or d > 64:
        raise Error("indexed replay requires d=7..64")
    var out = List[Int]()
    if d <= 9:
        for K in range(d+1):
            out.append(K)
    else:
        out = [0,1,4,d-2,d-1,d]
    return out^
