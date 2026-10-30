"""Exact first-generation Class-C seed formulas and reusable segment transfers.

Quantified hand proof: docs/class-c-nine-seed-interfaces-2026-10-30.md.
Executable parameter budget: 7 <= d <= 64, remaining lower cone only.
No frozen graph, symbolic cone engine, or boundary-hitting predicate is used.
"""
from std.collections import Dict
from psc.class_c_gap_profile import c_member
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.perron_field3 import (
    CubicElt, TileLengths3, cubic_add_checked as add,
    cubic_sub_checked as sub, cubic_scale_checked as scale,
    cubic_mul_beta, screened_perron_field3, sign_at_perron,
)
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, _tables_from, interior_overlap_cached,
    cached_sign,
)


struct SeedInterface(Copyable, Movable):
    var d: Int
    var eps: Int
    var n: Int
    var c: Int
    var p: Int
    var r: Int
    var B: Int  # floor(b)
    var T: Int  # floor(2b)
    var M: Int  # floor(a+b)
    var D: Int  # floor(Delta)
    var tables: SeedOverlapTables

    def __init__(out self, d: Int, eps: Int, c: Int) raises:
        if d < 7 or d > 64 or (eps != 1 and eps != -1):
            raise Error("seed interface finite replay budget: d=7..64, eps=+-1")
        var max_c = d + 4 if eps == 1 else d - 2
        if c < 0 or c > max_c:
            raise Error("seed interface requires the remaining lower cone")
        self.d = d
        self.eps = eps
        self.c = c
        self.n = 2*d + (-5 if eps == 1 else 1) + c
        self.p = self.n + d
        self.r = self.n - d + eps
        self.B = 2 if eps == 1 and c == 0 else 1
        self.T = 4 if eps == 1 and c == 0 else (2 if eps == 1 and c >= d+1 else 3)
        self.D = 1 if eps == 1 and c <= 1 else 0
        self.M = (5 if c == 0 else (4 if c <= (d+1)//2 else 3)) if eps == 1 else (4 if c <= (d-3)//2 else 3)
        var sigma = c_member(d, eps, self.n)
        var field = screened_perron_field3(Mat3(substitution_incidence(sigma)))
        # One positive polynomial scale: (beta-2)(beta-1). This is a
        # Class-C model binding, not an alternative arithmetic implementation.
        var lengths = TileLengths3(CubicElt(-self.p,self.p,0), CubicElt(self.p-2*self.n,self.n,0), CubicElt(2,-3,1))
        for k in range(3):
            if sign_at_perron(field, lengths.at(k)) <= 0:
                raise Error("Class-C length binding is not positive")
        self.tables = _tables_from(sigma, field, lengths)
        var unit = lengths.l2
        # Executably validate the exact chamber data used by the formulas.
        var vals = List[CubicElt]()
        vals.append(lengths.l1)
        vals.append(scale(lengths.l1,2))
        vals.append(add(lengths.l0,lengths.l1))
        vals.append(sub(lengths.l0,lengths.l1))
        var floors: List[Int] = [self.B,self.T,self.M,self.D]
        for k in range(4):
            if sign_at_perron(field,sub(vals[k],scale(unit,floors[k]))) <= 0 or sign_at_perron(field,sub(scale(unit,floors[k]+1),vals[k])) <= 0:
                raise Error("strict Class-C chamber formula failed")
        if sign_at_perron(field,sub(scale(unit,4),lengths.l0)) <= 0:
            raise Error("26-child guard failed")

    def v(self, a: Int = 0, b: Int = 0, y: Int = 0) raises -> CubicElt:
        return add(add(scale(self.tables.lengths.l0,a),scale(self.tables.lengths.l1,b)),scale(self.tables.lengths.l2,y))

    def seed(self, index: Int) raises -> OverlapState:
        if index < 0 or index >= 9:
            raise Error("canonical seed index must be 0..8")
        var pair = index // 3
        var A = 0 if pair < 2 else 1
        var B = 1 if pair == 0 else 2
        var kind = index % 3
        if kind == 0:
            return OverlapState(A,B,CubicElt())
        if kind == 1:
            return OverlapState(A,A,self.tables.lengths.at(B))
        return OverlapState(B,A,sub(self.tables.lengths.at(B),self.tables.lengths.at(A)))

    def children(self, index: Int) raises -> List[OverlapState]:
        """Closed first-layer tables: no search and no filtered candidates."""
        _ = self.seed(index)
        var out = List[OverlapState]()
        var n = self.n
        var r = self.r
        var d = self.d
        var plus = self.eps == 1
        if index == 0 or index == 3:  # aligned x/c or x/y
            out.append(OverlapState(0,1,CubicElt()))
            for j in range(self.D+1):
                out.append(OverlapState(0,2,self.v(0,1,j)))
            for k in range(self.D,self.D+2):
                out.append(OverlapState(2,2,self.v(-1,1,k)))
            if index == 0:
                for i in range(n-self.D-1,n+self.B+1):
                    out.append(OverlapState(2,0,self.v(-1,1,n-i)))
            else:
                for i in range(r-self.D-1,r+(1 if plus else 2)):
                    out.append(OverlapState(2,1,self.v(-1,1,r-i)))
        elif index == 6:  # aligned c/y
            out.append(OverlapState(1,1,CubicElt()))
            out.append(OverlapState(2,2,CubicElt()))
            for k in range(self.B+1):
                out.append(OverlapState(2,1,self.v(0,0,-k)))
        elif index == 1:  # (x,x,b)
            for i in range(n+self.B,n+self.M+1):
                out.append(OverlapState(2,0,self.v(0,1,n-i)))
            for k in range(n+self.M,n+self.M+2):
                out.append(OverlapState(2,2,self.v(1,1,n-k)))
            for j in range(d-self.M-1,d-self.B):
                out.append(OverlapState(0,2,self.v(1,1,j-d)))
        elif index == 2:  # (c,x,-Delta)
            for j in range(d-self.B-1,d):
                out.append(OverlapState(1,2,self.v(0,1,j-d)))
            out.append(OverlapState(2,2,CubicElt()))
            out.append(OverlapState(0,0,CubicElt()))
        elif index == 4 or index == 7:  # (x,x,1) or (c,c,1)
            var gap = 2*d-self.eps if index == 4 else d-self.eps
            var low_i = (0 if plus else 1) if index == 4 else self.B
            for i in range(r+low_i,r+self.T+1):
                out.append(OverlapState(2,0 if index == 4 else 1,self.v(-1 if index == 4 else 0,2 if index == 4 else 1,r-i)))
            for k in range(r+self.T,r+self.T+2):
                out.append(OverlapState(2,2,self.v(0,2,r-k)))
            for j in range(gap-self.T-1,gap-(1 if plus else 2)+1):
                out.append(OverlapState(0,2,self.v(0,2,j-gap)))
        else:  # (y,x,1-a) or (y,c,1-b)
            var gap = 2*d-self.eps if index == 5 else d-self.eps
            for j in range(gap-(1 if plus else 2),gap+self.D+1):
                out.append(OverlapState(1,2,self.v(-1,2,j-gap)))
            for k in range(gap+self.D,gap+self.D+2):
                out.append(OverlapState(2,2,self.v(-1,1,k-gap)))
            for i in range(r-self.D-1,r):
                out.append(OverlapState(2,0,self.v(-1,1,r-i)))
            out.append(OverlapState(1,0,self.v(-1,1)))
        # Identity uses the actual cubic field; duplicates are a defect in
        # this table, never silently removed to make its count agree.
        var seen = Dict[OverlapState,Bool]()
        var cache = Dict[CubicElt,Int]()
        for k in range(len(out)):
            if out[k] in seen:
                raise Error("duplicate in distinct seed child table")
            if not interior_overlap_cached(self.tables,cache,out[k]):
                raise Error("seed formula produced a non-overlap")
            seen[out[k]] = True
        return out^


def sum_wall_polynomial(m: SeedInterface, k: Int) raises -> Int:
    if k < 3 or k > 6:
        raise Error("sum wall test only defines m=3..6")
    var c = m.c
    var d = m.d
    if m.eps == 1:
        if k == 3:
            return 3*c*c-6*c-12*d*d+8*d-9
        if k == 4:
            return 6*c*c+9*c*d-8*c-6*d*d-6*d-14
        if k == 5:
            return 9*c*c+18*c*d-6*d-25
        return 12*c*c+27*c*d+18*c+6*d*d+8*d-30
    if k == 3:
        return 3*c*c+10*c-12*d*d-24*d+7
    if k == 4:
        return 6*c*c+9*c*d+36*c-6*d*d+2*d+54
    if k == 5:
        return 9*c*c+18*c*d+72*c+42*d+143
    return 12*c*c+27*c*d+118*c+6*d*d+96*d+286


def sum_wall_resultant(m: SeedInterface, k: Int) raises -> Int:
    _ = sum_wall_polynomial(m,k)  # validate the test domain first
    var q0 = CubicElt(2*m.eps,-(3*m.r+2*k+2),3)
    var q1 = cubic_mul_beta(m.tables.field,q0)
    var q2 = cubic_mul_beta(m.tables.field,q1)
    # Multiplication by Q in Z[t]/chi. Existing Mat3 determinant is safe:
    # in the validated d<=64 scope |chi_i|<=200, |Q_i|<=410, hence every
    # matrix entry <250000 and its six determinant terms sum to <2^57.
    return Mat3([q0.a0,q1.a0,q2.a0,q0.a1,q1.a1,q2.a1,q0.a2,q1.a2,q2.a2]).det()


def integer_window(t: SeedOverlapTables, mut cache: Dict[CubicElt,Int], lower: CubicElt, upper: CubicElt, lo: Int, hi: Int, cap: Int) raises -> List[Int]:
    """All integers lo..hi with lower < k*ell_y < upper; exact binary search.

    Bounds are actual occurrence bounds (RR uses the difference bounds).
    No floating floor and no fixed graph label set. Oversized windows raise.
    """
    var out = List[Int]()
    if lo > hi:
        return out^
    var left = lo
    var right = hi+1
    while left < right:
        var mid = left+(right-left)//2
        if cached_sign(t,cache,sub(scale(t.lengths.l2,mid),lower)) > 0:
            right = mid
        else:
            left = mid+1
    var first = left
    left = first
    right = hi+1
    while left < right:
        var mid = left+(right-left)//2
        if cached_sign(t,cache,sub(upper,scale(t.lengths.l2,mid))) > 0:
            left = mid+1
        else:
            right = mid
    if left-first > cap:
        raise Error("segment window exceeded proved local branching bound")
    for k in range(first,left):
        out.append(k)
    return out^


def segment_children(m: SeedInterface, mut cache: Dict[CubicElt,Int], parent: OverlapState) raises -> List[OverlapState]:
    """Reusable exact nine-segment-pair transfer for ANY overlapping parent."""
    ref t = m.tables
    if not interior_overlap_cached(t,cache,parent):
        raise Error("segment transfer requires strict interior parent overlap")
    var A = parent.top
    var B = parent.bottom
    var ra = len(t.sigma[A])-2
    var rb = len(t.sigma[B])-2
    var hA = t.lengths.at(t.sigma[A][0])
    var hB = t.lengths.at(t.sigma[B][0])
    var endsA: List[Int] = [t.sigma[A][0],t.sigma[A][ra+1]]
    var endsB: List[Int] = [t.sigma[B][0],t.sigma[B][rb+1]]
    var posA: List[CubicElt] = [CubicElt(),add(hA,scale(t.lengths.l2,ra))]
    var posB: List[CubicElt] = [CubicElt(),add(hB,scale(t.lengths.l2,rb))]
    var S = cubic_mul_beta(t.field,parent.shift)
    var candidates = List[OverlapState]()
    for a in range(2):
        for b in range(2):
            var child = OverlapState(endsA[a],endsB[b],sub(add(S,posB[b]),posA[a]))
            if interior_overlap_cached(t,cache,child):
                candidates.append(child)
        var C = sub(add(S,hB),posA[a])
        var js = integer_window(t,cache,sub(scale(C,-1),t.lengths.l2),sub(t.lengths.at(endsA[a]),C),0,rb-1,5)
        for j in range(len(js)):
            candidates.append(OverlapState(endsA[a],2,add(C,scale(t.lengths.l2,js[j]))))
    for b in range(2):
        var C = sub(add(S,posB[b]),hA)
        var ii = integer_window(t,cache,sub(C,t.lengths.l2),add(C,t.lengths.at(endsB[b])),0,ra-1,5)
        for i in range(len(ii)):
            candidates.append(OverlapState(2,endsB[b],sub(C,scale(t.lengths.l2,ii[i]))))
    var C = sub(add(S,hB),hA)
    var kk = integer_window(t,cache,sub(scale(C,-1),t.lengths.l2),sub(t.lengths.l2,C),1-ra,rb-1,2)
    for i in range(len(kk)):
        candidates.append(OverlapState(2,2,add(C,scale(t.lengths.l2,kk[i]))))
    if len(candidates) > 26:
        raise Error("26-child bound violated before deduplication")
    var seen = Dict[OverlapState,Bool]()
    var out = List[OverlapState]()
    for i in range(len(candidates)):
        if not interior_overlap_cached(t,cache,candidates[i]):
            raise Error("segment transfer produced non-overlap")
        if candidates[i] not in seen:
            seen[candidates[i]] = True
            out.append(candidates[i])
    return out^
