"""Uniform four-step *existential* offset-zero occurrence for one class-A seed.

For every minus boundary member (n=k+3+t, d=2*n-1-k, k,t>=0),
the **real, literal** occurrence addresses are

  (x,c,0) --(run 1, run 2)--> T1=(y,y,-1,1,1)
          --(first 0, run t+1)--> U=(x,y,1,2,-3)
          --(run d+3, first 0)--> V=(y,x,0,-1,1)
          --(run 1, run 2)--> (y,y,0,0,0).

The last y/y child begins at a *strictly internal common child start*
of the substituted V overlap. This is NOT universal BH: it proves
one selected seed branch, not all cyclic strict-zipper overlap states.
It is also not a target-aware BPA packet/factorization certificate.
"""
from psc.class_a_boundary_u_children import certify_u_children
from psc.class_a_boundary_next_run import _parameters, first_run_allowed
from psc.class_a_boundary_run_pairs import run_pair_allowed
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge,
)
from psc.class_a_boundary_occurrences import (
    symbolic_child, _equal3, FIRST, RUN,
)
from psc.class_a_boundary_signs import (
    chamber_parameters, _cone_nonnegative, _cone_positive,
)
from psc.param_poly import QX, qx_const, qx_add, qx_sub
from psc.overlap_seed_patch import SeedOverlapTables


def U_label() -> BoundaryLabel:
    return BoundaryLabel(0,2,1,2,-3)


def _z3() -> List[QX]:
    var out=List[QX]()
    for _ in range(3):
        out.append(qx_const(0))
    return out^


def _want(a: Int,b: Int,c: Int) -> List[QX]:
    var out=List[QX]()
    out.append(qx_const(a))
    out.append(qx_const(b))
    out.append(qx_const(c))
    return out^


def certify_U_uniform_hit() raises:
    """All-k,t word-symbolic identity plus previously proved Perron guards."""
    certify_u_children()
    var params=chamber_parameters(-1)
    var n=params[0].copy()
    var d=params[1].copy()
    var t=params[3].copy()
    var one=qx_const(1)
    var zero=qx_const(0)

    # Word bounds for the four selected addresses.
    _cone_nonnegative(qx_sub(n,qx_const(3)))
    _cone_nonnegative(qx_sub(qx_add(n,d),qx_add(d,qx_const(3))))
    _cone_nonnegative(qx_sub(qx_sub(n,one),qx_const(2)))
    _cone_positive(qx_sub(qx_sub(n,one),t))
    _cone_positive(d)

    # Check every actual proper-prefix Parikh update, not merely a
    # matrix quotient or a pair of terminal letter labels.
    var T1=symbolic_child(-1,0,1,_z3(),RUN,one,RUN,qx_const(2),2,2)
    _equal3(T1,_want(-1,1,1))
    var U=symbolic_child(-1,2,2,T1,FIRST,zero,RUN,
                         qx_add(t,one),0,2)
    _equal3(U,_want(1,2,-3))
    var V=symbolic_child(-1,0,2,U,RUN,qx_add(d,qx_const(3)),
                         FIRST,zero,2,0)
    _equal3(V,_want(0,-1,1))
    var terminal=symbolic_child(-1,2,0,V,RUN,one,RUN,
                                qx_const(2),2,2)
    _equal3(terminal,_z3())

    # Literal real-overlap conditions:
    #  T1 shift/Ly=1-u in (-1,0); U shift/Ly=u+3/beta;
    #  V shift/Ly=1-b=-1/beta; terminal shift=0.
    # These signs use the prior exact root bracket and 1<u<2,
    # plus beta>n+2>2. The coincidence lies at top run 1 start
    # Lx>0, with end Lx+Ly<beta*Ly because
    # beta*Ly=Lx+(n-1)*Ly+Lc and n>=3, Lc>0.
    _cone_positive(qx_sub(n,qx_const(2)))
    print("CLASS_A_BOUNDARY_U_HIT minus_all_k_t=true",
          "seed_occurrence_depth=4", "U_occurrence_depth=2",
          "real_strict_y_y_internal_target=true",
          "parent_child_word_addresses=true", "BH_universal=false")


def U_hit_path(k:Int,t:Int) raises -> List[BoundaryEdge]:
    """Four actual word-level edges; refuses parameters outside the chamber."""
    var member=_parameters(-1,k,t)
    var n=member[0]
    var d=member[1]
    if not run_pair_allowed(-1,k,1):
        raise Error("seed first run pair lost geometry")
    if not first_run_allowed(-1,k,t,1,t+1):
        raise Error("T1 first/run address not geometrically admissible")

    var parent=BoundaryLabel(0,1,0,0,0)
    var out=List[BoundaryEdge]()
    var v=member_transport(-1,k,n,d,parent,1,2)
    if not (v==BoundaryLabel(2,2,-1,1,1)):
        raise Error("first actual child did not give T1")
    out.append(BoundaryEdge(1,2,v))
    parent=v
    v=member_transport(-1,k,n,d,parent,0,t+1)
    if not (v==U_label()):
        raise Error("second actual child did not give U")
    out.append(BoundaryEdge(0,t+1,v))
    parent=v
    v=member_transport(-1,k,n,d,parent,d+3,0)
    if not (v==BoundaryLabel(2,0,0,-1,1)):
        raise Error("third actual child did not give V")
    out.append(BoundaryEdge(d+3,0,v))
    parent=v
    v=member_transport(-1,k,n,d,parent,1,2)
    if not (v==BoundaryLabel(2,2,0,0,0)):
        raise Error("final word-level occurrence not an offset-zero y/y child")
    out.append(BoundaryEdge(1,2,v))
    return out^


def verify_U_hit_path(tables:SeedOverlapTables,k:Int,t:Int) raises:
    var member=_parameters(-1,k,t)
    var path=U_hit_path(k,t)
    var parent=BoundaryLabel(0,1,0,0,0)
    for edge in path:
        verify_member_edge(tables,-1,k,member[0],member[1],
                           parent,edge.i,edge.j,edge.target)
        parent=edge.target
    if not (parent==BoundaryLabel(2,2,0,0,0)):
        raise Error("four-step occurrence path not coincident")
    if len(path)!=4:
        raise Error("four-step occurrence certificate incomplete")
