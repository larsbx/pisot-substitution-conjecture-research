"""Uniform actual H5-to-typed-coincidence exits, minus class-A boundary.

H5=(x,y,2,2,-5) is a TRUE H4 last/run child for every k,t>=0.
The entire minus boundary chamber admits the following concrete paths:
  k=0: H5 -> (x,x,0,-3,4) -> (y,x,0,1,-1) -> C
  k=1: H5 -> (x,x,0,-3,3) -> C
  k>=2: H5 -> (y,x,0,-3,3) -> C.
Each path consists of exact word-ordinal pairs and strict physical
overlaps. No all-outgoing-star, seed-wide BH, or internal-space claim.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_signs import (
    chamber_parameters, _same, _cone_nonnegative, _cone_positive,
)
from psc.class_a_boundary_h4_children import (
    certify_h4_children, h4_source, h4_child_allowed, verify_h4_packet,
)
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge,
)
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_occurrences import (
    symbolic_child, _equal3, FIRST, RUN, LAST,
)
from psc.param_poly import (
    QX, qx_const, qx_add, qx_sub, qx_mul, qx_shift,
)
from psc.overlap_seed_patch import SeedOverlapTables


def h5_source() -> BoundaryLabel:
    return BoundaryLabel(0,2,2,2,-5)


def _v(a: QX,b: QX,c: QX) -> List[QX]:
    var out=List[QX]()
    out.append(a.copy())
    out.append(b.copy())
    out.append(c.copy())
    return out^


def certify_h5_exits(corrupt: Bool=False) raises:
    # Includes the exact all-chamber Perron inequalities:
    # beta in (n+2,n+3), h=1/beta, u=1+alpha-2h,
    # 0<h<alpha, and 0<alpha+h<1 (inherited).
    certify_h4_children()
    var p=chamber_parameters(-1)
    var n=p[0].copy()
    var d=p[1].copy()
    var k=p[2].copy()
    var t=p[3].copy()
    var zero=qx_const(0)
    var one=qx_const(1)
    var A=qx_add(n,d)
    var source=_v(qx_const(2),qx_const(2),qx_const(-5))
    var h4=_v(zero,qx_const(-2),qx_const(4))

    # Every H4 has a real last/run child at (A+1,t+2),
    # which is exactly the symbolically fixed label H5.
    var H=symbolic_child(-1,0,2,h4,LAST,qx_add(A,one),
                           RUN,qx_add(t,qx_const(2)),0,2)
    _equal3(H,source)

    # H5 top last/bottom first has target (x,x,0,-3,4-k):
    # for k=0,1 this is a strict overlap; the label changes with k.
    var E=symbolic_child(-1,0,2,source,LAST,qx_add(A,one),
                           FIRST,zero,0,0)
    _equal3(E,_v(zero,qx_const(-3),qx_sub(qx_const(4),k)))

    # H5 top run index i=2d-n+3, bottom first, gives one fixed
    # (y,x,0,-3,3) label; it is an actual run iff k>=2.
    var i=qx_add(qx_sub(qx_mul(qx_const(2),d),n),
                 qx_const(3))
    # Do not invoke RUN(i) with an unshifted k variable: the
    # actual-word bound A-i=k-2 holds only in the k>=2 subchamber.
    # Check the exact full Parikh transport identity globally, then
    # certify the word legality after the honest k->k+2 shift.
    var G=_v(zero,qx_const(-3),
             qx_sub(qx_add(qx_sub(qx_mul(qx_const(2),d),n),
                           qx_const(6)),i))
    _equal3(G,_v(zero,qx_const(-3),qx_const(3)))
    _same(qx_sub(A,i),qx_sub(k,qx_const(2)))
    _cone_nonnegative(qx_shift(qx_sub(A,i),0,2))
    _cone_positive(i)

    # k=0: (x,x,0,-3,4) --(t+1,0)--> V=(y,x,0,1,-1).
    var E0=_v(zero,qx_const(-3),qx_const(4))
    var V=symbolic_child(-1,0,0,E0,RUN,qx_add(t,one),
                           FIRST,zero,2,0)
    _equal3(V,_v(zero,one,qx_sub(k,one)))

    # The fixed E1 and G targets have the same exact Parikh vector
    # but different top letter type. Their real RUN1/RUN4 children
    # are both the true typed coincidence C=(y,y,0,0,0).
    var E1=_v(zero,qx_const(-3),qx_const(3))
    var C0=symbolic_child(-1,0,0,E1,RUN,one,RUN,qx_const(4),2,2)
    var C1=symbolic_child(-1,2,0,E1,RUN,one,RUN,qx_const(4),2,2)
    _equal3(C0,_v(zero,zero,zero))
    _equal3(C1,_v(zero,zero,zero))
    # k=0: V=(y,x,0,1,-1) --(2,1)--> C.
    var V0=_v(zero,one,qx_const(-1))
    var C2=symbolic_child(-1,2,0,V0,RUN,qx_const(2),
                            RUN,one,2,2)
    var expected=_v(zero,zero,zero)
    if corrupt:
        expected[2]=one.copy()
    _equal3(C2,expected)
    _cone_positive(qx_sub(n,qx_const(2)))
    _cone_positive(qx_sub(A,qx_const(4)))
    _cone_positive(qx_sub(A,qx_add(t,one)))
    print("CLASS_A_BOUNDARY_H5_EXIT minus_all_k_t=true",
          "H4_to_H5_actual=true","k0_depth=3","k1_depth=2",
          "k_ge_2_depth=2","true_typed_C=true","global_BH=false")


def h5_path(k:Int,t:Int) raises -> List[BoundaryEdge]:
    var p=_parameters(-1,k,t)
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var source=h5_source()
    if not h4_child_allowed(k,t,checked_add(A,1),checked_add(t,2)):
        raise Error("H4 to H5 source occurrence missing")
    var out=List[BoundaryEdge]()
    if k<=1:
        var E=member_transport(-1,k,n,d,source,checked_add(A,1),0)
        var y=4-k
        if not (E==BoundaryLabel(0,0,0,-3,y)):
            raise Error("H5 endpoint child mismatch")
        out.append(BoundaryEdge(checked_add(A,1),0,E))
        source=E
        if k==0:
            var V=member_transport(-1,k,n,d,source,checked_add(t,1),0)
            if not (V==BoundaryLabel(2,0,0,1,-1)):
                raise Error("H5 k0 middle child mismatch")
            out.append(BoundaryEdge(checked_add(t,1),0,V))
            source=V
    else:
        var i=checked_add(checked_sub(checked_mul(2,d),n),3)
        if i<1 or i>A:
            raise Error("H5 selected run does not exist")
        var G=member_transport(-1,k,n,d,source,i,0)
        if not (G==BoundaryLabel(2,0,0,-3,3)):
            raise Error("H5 high-k child mismatch")
        out.append(BoundaryEdge(i,0,G))
        source=G

    var top_i=2 if k==0 else 1
    var bottom_j=1 if k==0 else 4
    var C=member_transport(-1,k,n,d,source,top_i,bottom_j)
    if not (C==BoundaryLabel(2,2,0,0,0)):
        raise Error("selected H5 path does not end in typed coincidence")
    out.append(BoundaryEdge(top_i,bottom_j,C))
    if len(out)!=(3 if k==0 else 2):
        raise Error("H5 path length mismatch")
    return out^


def verify_h5_path(tables:SeedOverlapTables,k:Int,t:Int,
                    steps:List[BoundaryEdge]) raises:
    var p=_parameters(-1,k,t)
    var n=p[0]
    var d=p[1]
    var A=checked_add(n,d)
    var source=h5_source()
    var ancestor=BoundaryEdge(checked_add(A,1),checked_add(t,2),source)
    verify_h4_packet(tables,k,t,ancestor)
    var expected=h5_path(k,t)
    if len(steps)!=len(expected):
        raise Error("H5 typed path incomplete")
    for ix in range(len(steps)):
        var step=steps[ix]
        if (step.i!=expected[ix].i or step.j!=expected[ix].j
            or step.target!=expected[ix].target):
            raise Error("H5 occurrence/target differs from selected certificate")
        verify_member_edge(tables,-1,k,n,d,source,
                           step.i,step.j,step.target)
        source=step.target
    if source!=BoundaryLabel(2,2,0,0,0):
        raise Error("H5 path not a typed coincidence")
