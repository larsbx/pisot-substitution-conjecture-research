"""Complete outgoing occurrence star of (x,c,0), not a closed BH carrier.

Symbolic rounding proof: docs/class-a-boundary-child-carrier-2026-10-26.md.
The member interface refuses overflow; the cone certificate is unbounded Q[t,k].
Every accepted member edge also checks the literal words, all Parikh coordinates,
the canonical Perron-field geometry, and its supplied target packet.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_signs import (
    chamber_parameters, _cone_nonnegative, _cone_positive, _same,
)
from psc.class_a_boundary_run_pairs import certify_run_pair_chambers
from psc.class_a_boundary_occurrences import symbolic_child, _equal3, FIRST, RUN, LAST
from psc.param_poly import QX, qx_add, qx_sub, qx_const
from psc.overlap_seed_patch import (
    SeedOverlapTables, OverlapState, selected_overlap_child, interior_overlap,
)
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_scale_checked,
)


struct BoundaryLabel(ImplicitlyCopyable, Copyable, Movable, Equatable):
    var top: Int
    var bottom: Int
    var x: Int
    var c: Int
    var y: Int

    def __init__(out self, top: Int, bottom: Int, x: Int, c: Int, y: Int):
        self.top=top
        self.bottom=bottom
        self.x=x
        self.c=c
        self.y=y

    def __eq__(self, other: Self) -> Bool:
        return (self.top==other.top and self.bottom==other.bottom
                and self.x==other.x and self.c==other.c and self.y==other.y)


struct BoundaryEdge(ImplicitlyCopyable, Copyable, Movable):
    var i: Int
    var j: Int
    var target: BoundaryLabel

    def __init__(out self, i: Int, j: Int, target: BoundaryLabel):
        self.i=i
        self.j=j
        self.target=target


def check_boundary_member(eps: Int, k: Int, n: Int, d: Int) raises:
    if (eps!=-1 and eps!=1) or k<0:
        raise Error("invalid boundary chamber sign or k")
    var floor=checked_add(k,3) if eps==-1 else checked_mul(2,checked_add(k,2))
    if n<floor:
        raise Error("outside boundary chamber n floor")
    if d!=checked_sub(checked_add(checked_mul(2,n),6*eps+5),k):
        raise Error("d does not match boundary chamber")
    _=checked_add(checked_add(n,d),2)


def boundary_r(eps: Int, k: Int) raises -> Int:
    if (eps!=-1 and eps!=1) or k<0:
        raise Error("invalid boundary chamber")
    return 2 if eps==1 and k<=3 else 1


def certify_seed_star() raises:
    # All chamber/root/u statements are dependencies, not assumed samples.
    certify_run_pair_chambers()
    for eps in [-1,1]:
        var params=chamber_parameters(eps)
        _cone_nonnegative(qx_sub(params[0],qx_const(3 if eps==-1 else 4)))
        _cone_nonnegative(qx_sub(params[1],qx_const(5)))
        _cone_positive(qx_sub(params[1],qx_const(2)))
        var n=params[0].copy()
        var zero=qx_const(0)
        var old=List[QX]()
        for _ in range(3):
            old.append(zero.copy())
        for r in range(1,2 if eps==-1 else 3):
            for j in range(1,r+2):
                var got=symbolic_child(eps,0,1,old,FIRST,zero,RUN,qx_const(j),0,2)
                var want=List[QX]()
                want.append(zero.copy())
                want.append(qx_const(1))
                want.append(qx_const(j-1))
                _equal3(got,want)
            for delta in range(r,r+2):
                var want=List[QX]()
                want.append(qx_const(-1))
                want.append(qx_const(1))
                want.append(qx_const(delta))
                var got=symbolic_child(eps,0,1,old,RUN,qx_const(1),
                                       RUN,qx_const(1+delta),2,2)
                _equal3(got,want)
                # Both extremes of each complete free-index interval.
                got=symbolic_child(eps,0,1,old,RUN,qx_sub(n,qx_const(delta)),
                                   RUN,n,2,2)
                _equal3(got,want)
            for v in range(-1 if eps==-1 else 0,r+2):
                var got=symbolic_child(eps,0,1,old,
                    RUN,qx_add(n,qx_const(1-v)),
                    LAST,qx_add(n,qx_const(1)),2,0)
                var want=List[QX]()
                want.append(qx_const(-1))
                want.append(qx_const(1))
                want.append(qx_const(v))
                _equal3(got,want)
        # Full next-family c-coordinate escape: all nine first/run/last
        # combinations; a free run ordinal never contributes c in sigma(y).
        var positions=List[QX]()
        positions.append(zero.copy())
        positions.append(qx_const(1))
        positions.append(qx_add(n,qx_const(eps+1)))
        for m in range(1,3 if eps==-1 else 4):
            var source=List[QX]()
            source.append(qx_const(-1))
            source.append(qx_const(1))
            source.append(qx_const(m))
            for tk in range(3):
                for bk in range(3):
                    var ct=0 if tk==FIRST else (2 if tk==RUN else 1)
                    var cb=0 if bk==FIRST else (2 if bk==RUN else 1)
                    var got=symbolic_child(eps,2,2,source,
                        tk,positions[tk],bk,positions[bk],ct,cb)
                    _same(got[1],qx_const(m+1))
    print("CLASS_A_BOUNDARY_CHILD_STAR all_first_run_last_types=true",
          "b=1-eps/beta", "infinite_rounding=written_proof",
          "closed_carrier=false", "BH=false")


def _run(eps: Int, n: Int, d: Int, parent: Int) raises -> Int:
    if parent==0:
        return checked_add(n,d)
    if parent==1:
        return n
    if parent==2:
        return checked_add(n,eps)
    raise Error("parent outside alphabet")


def _prefix(eps: Int, n: Int, d: Int, parent: Int, index: Int) raises -> List[Int]:
    var run=_run(eps,n,d,parent)
    if index<0 or index>checked_add(run,1):
        raise Error("nonexistent child ordinal")
    if index==0:
        return [0,0,0]
    return [0 if parent==1 else 1, 1 if parent==1 else 0,index-1]


def _letter(eps: Int, n: Int, d: Int, parent: Int, index: Int) raises -> Int:
    var run=_run(eps,n,d,parent)
    if index<0 or index>checked_add(run,1):
        raise Error("nonexistent child ordinal")
    if index==0:
        return 1 if parent==1 else 0
    if index<=run:
        return 2
    return 1 if parent==2 else 0


def member_transport(eps: Int, k: Int, n: Int, d: Int,
                     parent: BoundaryLabel, i: Int, j: Int) raises -> BoundaryLabel:
    """All parent types: actual word ordinals and full checked Parikh update.

    Algebraic transport alone deliberately does not accept an overlap edge.
    """
    check_boundary_member(eps,k,n,d)
    var a=_prefix(eps,n,d,parent.top,i)
    var b=_prefix(eps,n,d,parent.bottom,j)
    var x=checked_add(checked_add(checked_mul(2,parent.x),parent.c),parent.y)
    var c=checked_add(parent.c,parent.y)
    var y=checked_add(checked_add(checked_mul(checked_add(n,d),parent.x),
                                checked_mul(n,parent.c)),
                     checked_mul(checked_add(n,eps),parent.y))
    return BoundaryLabel(_letter(eps,n,d,parent.top,i),
        _letter(eps,n,d,parent.bottom,j),
        checked_add(x,checked_sub(b[0],a[0])),
        checked_add(c,checked_sub(b[1],a[1])),
        checked_add(y,checked_sub(b[2],a[2])))


def seed_child_allowed(eps: Int, k: Int, n: Int, d: Int,
                       i: Int, j: Int) raises -> Bool:
    """IFF strict overlap for this parent, including actual occurrence bounds."""
    check_boundary_member(eps,k,n,d)
    var top_run=checked_add(n,d)
    if i<0 or i>checked_add(top_run,1) or j<0 or j>checked_add(n,1):
        raise Error("nonexistent seed child occurrence")
    var r=boundary_r(eps,k)
    if i==0:
        return j<=r+1
    if i<=top_run:
        if j>=1 and j<=n:
            var delta=checked_sub(j,i)
            return delta==r or delta==r+1
        if j==n+1:
            return i>=n-r and i<=checked_add(n,2 if eps==-1 else 1)
    return False


def seed_star(eps: Int, k: Int, n: Int, d: Int) raises -> List[BoundaryEdge]:
    """O(n) occurrence carrier, with duplicates retained and no geometry guesses."""
    check_boundary_member(eps,k,n,d)
    var r=boundary_r(eps,k)
    var root=BoundaryLabel(0,1,0,0,0)
    var out=List[BoundaryEdge]()
    out.append(BoundaryEdge(0,0,root))
    for j in range(1,r+2):
        out.append(BoundaryEdge(0,j,BoundaryLabel(0,2,0,1,j-1)))
    for delta in range(r,r+2):
        for i in range(1,n-delta+1):
            out.append(BoundaryEdge(i,i+delta,BoundaryLabel(2,2,-1,1,delta)))
    for i in range(n-r,checked_add(n,3 if eps==-1 else 2)):
        out.append(BoundaryEdge(i,n+1,BoundaryLabel(2,0,-1,1,n-i+1)))
    var expected=checked_add(checked_mul(2,n),4 if eps==-1 else 3)
    if len(out)!=expected:
        raise Error("complete seed-star occurrence cardinality mismatch")
    return out^


def geometric_state(tables: SeedOverlapTables, label: BoundaryLabel) raises -> OverlapState:
    if label.top<0 or label.top>2 or label.bottom<0 or label.bottom>2:
        raise Error("target packet type outside alphabet")
    var shift=cubic_add_checked(
        cubic_add_checked(cubic_scale_checked(tables.lengths.l0,label.x),
                          cubic_scale_checked(tables.lengths.l1,label.c)),
        cubic_scale_checked(tables.lengths.l2,label.y))
    return OverlapState(label.top,label.bottom,shift)


def verify_member_edge(tables: SeedOverlapTables, eps: Int, k: Int, n: Int, d: Int,
                       parent: BoundaryLabel, i: Int, j: Int,
                       target: BoundaryLabel) raises:
    """Verify the caller's concrete packet; it is not a BH success certificate.

    Tables are bound to these full ordered words, not merely the same incidence.
    """
    check_boundary_member(eps,k,n,d)
    if len(tables.sigma)!=3:
        raise Error("wrong number of image words")
    for p in range(3):
        var run=_run(eps,n,d,p)
        if len(tables.sigma[p])!=checked_add(run,2):
            raise Error("tables have different image lengths")
        for index in range(run+2):
            if tables.sigma[p][index]!=_letter(eps,n,d,p,index):
                raise Error("tables have different ordered image words")
    var child=member_transport(eps,k,n,d,parent,i,j)
    if not (child==target):
        raise Error("child does not match target packet type/Parikh offset")
    var source=geometric_state(tables,parent)
    if not interior_overlap(tables,source):
        raise Error("parent is not a strict interior overlap")
    var actual=selected_overlap_child(tables,source,i,j)
    if actual!=geometric_state(tables,target):
        raise Error("Parikh transport disagrees with Perron-field transport")
    if not interior_overlap(tables,actual):
        raise Error("word-valid child is geometrically disjoint or endpoint-only")
