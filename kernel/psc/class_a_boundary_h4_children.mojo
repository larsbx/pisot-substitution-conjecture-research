"""Complete true ordered child star of H4=(x,y,0,-2,4), minus boundary.

This extends PR #360's E2/Dxx work without claiming full carrier closure.
H4 has exactly 2*t+5 physical interior children for ALL k,t>=0.
The exact 13-label image is contained in E2's prior 46-label image.

The proof uses beta in (n+2,n+3), 0<h=1/beta<alpha,
0<z=alpha+h<1, and alpha_high(k,t) iff alpha>1/2,
all inherited from previously certified exact polynomial lemmas.
The nine interval inequalities are in docs/class-a-boundary-h4-2026-10-27.md.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge,
)
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_e2_children import certify_e2_children, in_e2_image
from psc.class_a_boundary_h3_children import (
    alpha_high, chain_source, chain_path, chain_rank, verify_chain_path,
)
from psc.class_a_boundary_occurrences import (
    symbolic_child, _equal3, FIRST, RUN, LAST,
)
from psc.class_a_boundary_signs import (
    chamber_parameters, _same, _cone_nonnegative, _cone_positive,
)
from psc.param_poly import QX, qx_const, qx_add, qx_sub, qx_mul
from psc.overlap_seed_patch import SeedOverlapTables


def h4_source() -> BoundaryLabel:
    return BoundaryLabel(0,2,0,-2,4)


def _source_params(k: Int, t: Int) raises -> Tuple[Int,Int,Int,Int]:
    var p=_parameters(-1,k,t)
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var N=checked_sub(n,1)
    return (n,d,A,N)


def _want(x: QX, c: QX, y: QX) -> List[QX]:
    var out=List[QX]()
    out.append(x.copy())
    out.append(c.copy())
    out.append(y.copy())
    return out^


def certify_h4_children(corrupt: Bool=False) raises:
    # These exact earlier certificates are load-bearing: h<alpha,
    # alpha+h<1, the root bounds and the half-chamber separator.
    certify_e2_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var t=p[3].copy()
    var zero=qx_const(0)
    var one=qx_const(1)
    var two=qx_const(2)
    var A=qx_add(n,d)
    var N=qx_sub(n,one)
    _same(A,qx_add(qx_mul(two,n),qx_add(t,two)))
    _cone_positive(qx_sub(n,two))
    _cone_nonnegative(qx_sub(A,qx_add(qx_mul(two,n),one)))
    _cone_nonnegative(qx_sub(N,qx_add(t,two)))

    var source=List[QX]()
    source.append(zero.copy())
    source.append(qx_const(-2))
    source.append(qx_const(4))
    # Algebraic transport of the actual i=2n+1 run/first pair,
    # uniformly available in both literal image words.
    var target=symbolic_child(-1,0,2,source,RUN,
                 qx_add(qx_mul(two,n),one),
                 FIRST,zero,2,0)
    var intended=_want(one,two,qx_const(-4))
    if corrupt:
        intended[2]=qx_const(-3)
    _equal3(target,intended)
    # Literal final-run j=t+2 is uniformly in [1,N].
    var last_run=symbolic_child(-1,0,2,source,LAST,
                    qx_add(A,one),RUN,qx_add(t,two),0,2)
    _equal3(last_run,_want(two,two,qx_const(-5)))
    # Last/first exists physically only at t=0, or t=1 in the
    # high-alpha chamber. Its Parikh formula holds for all t,
    # but this identity alone must NOT admit an unrealizable edge.
    var last_first=symbolic_child(-1,0,2,source,LAST,
                          qx_add(A,one),FIRST,zero,0,0)
    _equal3(last_first,_want(one,two,
                             qx_sub(qx_const(-6),t)))
    # Actual run/run target formulas follow the genuine word ordinals.
    # No all-edge descent or unproved identification of balanced factors.
    print("CLASS_A_BOUNDARY_H4 all_k_t=true",
          "child_cardinality=2*t+5", "target_envelope=13",
          "contained_in_E2_image=true",
          "alpha_half_separator=inherited_exact",
          "global_closed_carrier=false", "BH=false")


def h4_child_allowed(k: Int, t: Int, i: Int, j: Int) raises -> Bool:
    """IFF strict geometric child for genuine top/bottom word ordinals."""
    var p=_source_params(k,t)
    var n=p[0]
    var A=p[2]
    var N=p[3]
    var high=alpha_high(k,t)
    var twice=checked_mul(n,2)
    if i<0 or i>checked_add(A,1) or j<0 or j>checked_add(N,1):
        raise Error("H4 nonexistent top/bottom occurrence")
    if i==0:
        return False
    if i<=A:
        if j==0:
            return (i>=checked_add(twice,1)
                    and i<=min(A,checked_add(twice,4 if high else 3)))
        if j==N+1:
            return False
        var delta=checked_sub(i,j)
        return (delta==checked_add(twice,3 if high else 2)
                or delta==checked_add(twice,4 if high else 3))
    # Last top x.
    if j==0:
        return t==0 or (t==1 and high)
    if j==N+1:
        return False
    return j>=max(1,t-(1 if high else 0)) and j<=checked_add(t,2)


def in_h4_image(w: BoundaryLabel) -> Bool:
    if w.c!=2:
        return False
    if w.top==2 and w.bottom==0 and w.x==1:
        return w.y>=-7 and w.y<=-4
    if w.top==2 and w.bottom==2 and w.x==2:
        return w.y>=-8 and w.y<=-6
    if w.top==0 and w.bottom==0 and w.x==1:
        return w.y>=-7 and w.y<=-6
    if w.top==0 and w.bottom==2 and w.x==2:
        return w.y>=-8 and w.y<=-5
    return False


def h4_image() raises -> List[BoundaryLabel]:
    var out=List[BoundaryLabel]()
    for y in range(-7,-3):
        out.append(BoundaryLabel(2,0,1,2,y))
    for y in range(-8,-5):
        out.append(BoundaryLabel(2,2,2,2,y))
    for y in range(-7,-5):
        out.append(BoundaryLabel(0,0,1,2,y))
    for y in range(-8,-4):
        out.append(BoundaryLabel(0,2,2,2,y))
    if len(out)!=13:
        raise Error("H4 target image cardinality not 13")
    for w in out:
        if not in_e2_image(w):
            raise Error("H4 image outside the previously certified E2 envelope")
    return out^


def _append(mut out: List[BoundaryEdge], k:Int,t:Int,n:Int,d:Int,
            i:Int,j:Int) raises:
    if not h4_child_allowed(k,t,i,j):
        raise Error("symbolic H4 edge is not an actual interior overlap")
    var target=member_transport(-1,k,n,d,h4_source(),i,j)
    if not in_h4_image(target) or not in_e2_image(target):
        raise Error("H4 child escapes exact E2 or H4 typed image")
    out.append(BoundaryEdge(i,j,target))


def h4_child_star(k:Int,t:Int) raises -> List[BoundaryEdge]:
    """Linear output-sensitive enumeration; keep every occurrence ordinal."""
    var p=_source_params(k,t)
    var n=p[0]
    var d=p[1]
    var A=p[2]
    var high=alpha_high(k,t)
    var twice=checked_mul(n,2)
    var out=List[BoundaryEdge]()
    for i in range(checked_add(twice,1),
                   checked_add(min(A,checked_add(twice,4 if high else 3)),1)):
        _append(out,k,t,n,d,i,0)
    for delta in [checked_add(twice,3 if high else 2),
                  checked_add(twice,4 if high else 3)]:
        for j in range(1,checked_add(checked_sub(A,delta),1)):
            _append(out,k,t,n,d,checked_add(j,delta),j)
    if t==0 or (t==1 and high):
        _append(out,k,t,n,d,checked_add(A,1),0)
    for j in range(max(1,t-(1 if high else 0)),
                   checked_add(checked_add(t,2),1)):
        _append(out,k,t,n,d,checked_add(A,1),j)
    if len(out)!=checked_add(checked_mul(t,2),5):
        raise Error("H4 actual occurrence count is not 2*t+5")
    return out^


def verify_h4_packet(tables:SeedOverlapTables,k:Int,t:Int,
                     edge:BoundaryEdge) raises:
    var p=_source_params(k,t)
    if not h4_child_allowed(k,t,edge.i,edge.j):
        raise Error("H4 packet is disjoint or an unavailable child")
    if not in_h4_image(edge.target):
        raise Error("H4 packet escaped the exact 13-label envelope")
    verify_member_edge(tables,-1,k,p[0],p[1],h4_source(),
                       edge.i,edge.j,edge.target)


def h4_path(k: Int, t: Int) raises -> List[BoundaryEdge]:
    """Uniform 5-edge typed-coincidence exit: H4 -> J -> K -> L -> H1 -> C.

    Source H4 is a real Dxx child, but this is NOT a proof of its
    global seed reachability or of closure of any image envelope.
    """
    var p=_source_params(k,t)
    var n=p[0]
    var d=p[1]
    var out=List[BoundaryEdge]()
    var i=checked_add(checked_mul(2,n),1)
    if not h4_child_allowed(k,t,i,0):
        raise Error("H4 universal first child missing")
    var J=chain_source(2)
    var got=member_transport(-1,k,n,d,h4_source(),i,0)
    if not (got==J):
        raise Error("H4 first occurrence does not reach J")
    out.append(BoundaryEdge(i,0,J))
    var suffix=chain_path(2,k,t)
    for edge in suffix:
        out.append(edge)
    if len(out)!=5:
        raise Error("H4 selected coincidence path does not have five edges")
    return out^


def h4_rank(w: BoundaryLabel) raises -> Int:
    """Rank on the SIX selected path labels only; NOT all outgoing edges."""
    if w==h4_source():
        return 5
    return chain_rank(w)


def verify_h4_path(tables: SeedOverlapTables,k: Int,t: Int,
                   packet: List[BoundaryEdge]) raises:
    """Replay every true word/geometry edge, refusing even if terminal is C."""
    var want=h4_path(k,t)
    if len(packet)!=len(want):
        raise Error("incomplete H4 selected path")
    for i in range(len(packet)):
        if (packet[i].i!=want[i].i or packet[i].j!=want[i].j
            or packet[i].target!=want[i].target):
            raise Error("H4 selected path differs in occurrence or typed target")
    verify_h4_packet(tables,k,t,packet[0])
    if h4_rank(packet[0].target)>=h4_rank(h4_source()):
        raise Error("H4 entry rank did not descend")
    var suffix=List[BoundaryEdge]()
    for i in range(1,len(packet)):
        suffix.append(packet[i])
    verify_chain_path(tables,2,k,t,suffix)
    if packet[len(packet)-1].target!=BoundaryLabel(2,2,0,0,0):
        raise Error("H4 path ends without typed diagonal coincidence")
