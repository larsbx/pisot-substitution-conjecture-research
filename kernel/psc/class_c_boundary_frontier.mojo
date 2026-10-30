"""Complete ten-source boundary frontier, using proved integer endpoint rules.

Coordinates N+U/beta+R/(beta*(beta+1)) are Class-C model coordinates,
not a new arithmetic kernel. Field evaluation reuses SeedInterface.v.
"""
from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_c_seed_interfaces import SeedInterface
from psc.overlap_seed_patch import OverlapState


struct BoundaryOffset(Copyable, Movable):
    var n: Int
    var u: Int
    var r: Int

    def __init__(out self, n: Int = 0, u: Int = 0, r: Int = 0):
        self.n = n
        self.u = u
        self.r = r

    def plus(self, other: Self) raises -> Self:
        return Self(checked_add(self.n,other.n),checked_add(self.u,other.u),checked_add(self.r,other.r))

    def minus(self, other: Self) raises -> Self:
        return Self(checked_sub(self.n,other.n),checked_sub(self.u,other.u),checked_sub(self.r,other.r))

    def shift(self, k: Int) raises -> Self:
        return Self(checked_add(self.n,k),self.u,self.r)

    def negative(self) raises -> Self:
        return BoundaryOffset().minus(self)

    def state(self, m: SeedInterface, top: Int, bottom: Int) raises -> OverlapState:
        # a=3+u+2rho, b=2+rho, ell_y=1; invert this integer basis.
        var A = self.u
        var B = checked_sub(self.r,checked_mul(2,self.u))
        var Y = checked_sub(checked_add(self.n,self.u),checked_mul(2,self.r))
        return OverlapState(top,bottom,m.v(A,B,Y))


def boundary_fraction_sign(d: Int, U: Int, R: Int) raises -> Int:
    if d < 7 or d > 64 or U < -5 or U > 5 or R < -10 or R > 10:
        raise Error("boundary endpoint sign outside proved coefficient/replay envelope")
    var L = U*(d+1)+R
    if L != 0:
        return 1 if L > 0 else -1
    return 1 if U > 0 else (-1 if U < 0 else 0)


def boundary_sign(d: Int, value: BoundaryOffset) raises -> Int:
    var fraction = boundary_fraction_sign(d,value.u,value.r)
    if value.n != 0:
        return 1 if value.n > 0 else -1
    return fraction


def boundary_window(d: Int, lower: BoundaryOffset, upper: BoundaryOffset, lo: Int, hi: Int, cap: Int) raises -> List[Int]:
    var ls = boundary_fraction_sign(d,lower.u,lower.r)
    var us = boundary_fraction_sign(d,upper.u,upper.r)
    var first = max(lo,checked_add(lower.n,1 if ls >= 0 else 0))
    var last = min(hi,checked_sub(upper.n,1 if us <= 0 else 0))
    var out = List[Int]()
    if last < first:
        return out^
    if checked_add(checked_sub(last,first),1) > cap:
        raise Error("boundary symbolic window exceeded local width bound")
    for i in range(first,checked_add(last,1)):
        out.append(i)
    return out^


def boundary_length(letter: Int) raises -> BoundaryOffset:
    if letter == 0:
        return BoundaryOffset(3,1,2)
    if letter == 1:
        return BoundaryOffset(2,0,1)
    if letter == 2:
        return BoundaryOffset(1,0,0)
    raise Error("boundary length requires a letter in 0..2")


def frontier_parent(m: SeedInterface, index: Int) raises -> OverlapState:
    if m.eps != 1 or m.c != 0 or index < 0 or index >= 10:
        raise Error("ten-source frontier requires plus c=0 and index 0..9")
    if index < 4:
        return OverlapState(0,2,m.v(-4,11,-(7+index)))
    var t = index+2 if index < 6 else index
    return OverlapState(2,2 if index < 6 else 0,m.v(-5,11,-t))


def frontier_children(m: SeedInterface, index: Int) raises -> List[OverlapState]:
    var parent = frontier_parent(m,index)
    var t = 7+index if index < 4 else (index+2 if index < 6 else index)
    var N = (10-t) if index < 4 else (7-t)
    var U = -4 if index < 4 else -5
    var R = 3 if index < 4 else 1
    # beta*(N+U*u+R*rho)=(d*N+U)+R*u+(2*N-R)*rho.
    var S = BoundaryOffset(m.d*N+U,R,2*N-R)
    var ra = m.p if parent.top == 0 else m.r
    var rb = m.p if parent.bottom == 0 else m.r
    var hA = boundary_length(0 if parent.top == 0 else 1)
    var hB = boundary_length(0 if parent.bottom == 0 else 1)
    var posA: List[BoundaryOffset] = [BoundaryOffset(),hA.shift(ra)]
    var posB: List[BoundaryOffset] = [BoundaryOffset(),hB.shift(rb)]
    var endsA: List[Int] = [0,0] if parent.top == 0 else [1,1]
    var endsB: List[Int] = [0,0] if parent.bottom == 0 else [1,1]
    var candidates = List[OverlapState]()
    for a in range(2):
        for b in range(2):
            var w = S.plus(posB[b]).minus(posA[a])
            if boundary_sign(m.d,w.plus(boundary_length(endsB[b]))) > 0 and boundary_sign(m.d,boundary_length(endsA[a]).minus(w)) > 0:
                candidates.append(w.state(m,endsA[a],endsB[b]))
        var C = S.plus(hB).minus(posA[a])
        var js = boundary_window(m.d,C.negative().shift(-1),boundary_length(endsA[a]).minus(C),0,rb-1,5)
        for j in range(len(js)):
            candidates.append(C.shift(js[j]).state(m,endsA[a],2))
    for b in range(2):
        var C = S.plus(posB[b]).minus(hA)
        var ii = boundary_window(m.d,C.shift(-1),C.plus(boundary_length(endsB[b])),0,ra-1,5)
        for i in range(len(ii)):
            candidates.append(C.shift(-ii[i]).state(m,2,endsB[b]))
    var C = S.plus(hB).minus(hA)
    var kk = boundary_window(m.d,C.negative().shift(-1),C.negative().shift(1),1-ra,rb-1,2)
    for k in range(len(kk)):
        candidates.append(C.shift(kk[k]).state(m,2,2))
    if len(candidates) > 26:
        raise Error("boundary frontier violated 26-child bound")
    var out = List[OverlapState]()
    var seen = Dict[OverlapState,Bool]()
    for i in range(len(candidates)):
        if candidates[i] not in seen:
            seen[candidates[i]] = True
            out.append(candidates[i])
    return out^
