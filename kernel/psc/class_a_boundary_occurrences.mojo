"""Typed *word-level* occurrence/address transport for class-A l=0 rays.

Unlike a quotient six-state map, each selected proper-prefix child retains
the actual parent, first/run/last kind and occurrence index in Z[t,k].
Algebraic child compatibility is deliberately not real geometric overlap:
the (x,c,0) seed's first y/y runs at indices (1,1) are disjoint when u>1.
We certify the exact affine incidence update and cone-legal prefix positions.
"""
from psc.class_a_boundary_signs import (
    chamber_parameters, certify_chamber_signs, _same, _cone_nonnegative,
)
from psc.param_poly import (
    QX, qx_add, qx_sub, qx_mul, qx_const, qx_is_zero,
)

comptime FIRST=0
comptime RUN=1
comptime LAST=2


def _run_count(eps: Int, parent: Int, n: QX, d: QX) raises -> QX:
    if parent==0:
        return qx_add(n,d)
    if parent==1:
        return n.copy()
    if parent==2:
        return qx_add(n,qx_const(eps))
    raise Error("parent letter out of alphabet")


def _child(parent: Int, kind: Int) raises -> Int:
    if parent<0 or parent>2 or kind<FIRST or kind>LAST:
        raise Error("bad letter or occurrence kind")
    if kind==RUN:
        return 2
    if kind==FIRST:
        return 1 if parent==1 else 0
    return 1 if parent==2 else 0


def _prefix(parent: Int, kind: Int, index: QX,
            eps: Int, n: QX, d: QX) raises -> List[QX]:
    var run=_run_count(eps,parent,n,d)
    if kind==FIRST:
        if not qx_is_zero(index):
            raise Error("first child has nonzero index")
        return [qx_const(0),qx_const(0),qx_const(0)]
    if kind==RUN:
        # Both bounds are proved throughout the infinite parameter cone,
        # not checked for one sample word.
        _cone_nonnegative(qx_sub(index,qx_const(1)))
        _cone_nonnegative(qx_sub(run,index))
        var y=qx_sub(index,qx_const(1))
        if parent==1:
            return [qx_const(0),qx_const(1),y.copy()]
        return [qx_const(1),qx_const(0),y.copy()]
    if kind==LAST:
        _same(index,qx_add(run,qx_const(1)))
        if parent==1:
            return [qx_const(0),qx_const(1),run.copy()]
        return [qx_const(1),qx_const(0),run.copy()]
    raise Error("unknown occurrence kind")


def symbolic_child(eps: Int, top: Int, bottom: Int, old: List[QX],
                   tkind: Int, tidx: QX, bkind: Int, bidx: QX,
                   want_top: Int, want_bottom: Int) raises -> List[QX]:
    """Return full occurrence-indexed bottom-minus-top Parikh offset.

    Actual interior overlap / boundary classification is a further check
    in the existing Perron exact-geometry kernel.
    """
    if len(old)!=3:
        raise Error("expected full three-coordinate Parikh offset")
    var params=chamber_parameters(eps)
    var n=params[0].copy()
    var d=params[1].copy()
    if _child(top,tkind)!=want_top or _child(bottom,bkind)!=want_bottom:
        raise Error("target child types do not match actual word")
    var pt=_prefix(top,tkind,tidx,eps,n,d)
    var pb=_prefix(bottom,bkind,bidx,eps,n,d)
    var first=qx_add(qx_add(qx_mul(qx_const(2),old[0]),old[1]),old[2])
    var second=qx_add(old[1],old[2])
    var third=qx_add(qx_add(qx_mul(qx_add(n,d),old[0]),
                            qx_mul(n,old[1])),
                     qx_mul(qx_add(n,qx_const(eps)),old[2]))
    return [qx_add(first,qx_sub(pb[0],pt[0])),
            qx_add(second,qx_sub(pb[1],pt[1])),
            qx_add(third,qx_sub(pb[2],pt[2]))]


def _equal3(a: List[QX],b:List[QX]) raises:
    if len(a)!=3 or len(b)!=3:
        raise Error("malformed Parikh triple")
    for i in range(3):
        _same(a[i],b[i])


def certify_typed_occurrences(eps: Int, corrupt: Bool=False) raises:
    # The geometric disjointness conclusion is valid only after the full
    # all-parameter Perron bracket and u>1 cone certificate has passed.
    certify_chamber_signs(eps)
    var par=chamber_parameters(eps)
    var n=par[0].copy()
    var d=par[1].copy()
    var zero=qx_const(0)
    var one=qx_const(1)
    var old=List[QX]()
    old.append(zero.copy())
    old.append(zero.copy())
    old.append(zero.copy())

    # (x,c,0) is the first tile-pair of the real (xc,cx) swap patch.
    # Its selected first children form a genuine noncoincident first-child
    # loop, without deciding whether there is a productive *other* child.
    var first=symbolic_child(eps,0,1,old,FIRST,zero,FIRST,zero,0,1)
    _equal3(first,old)

    # Both index-1 children are y letters, but their starts differ by
    # L_c-L_x=-d*h*(1+h), whose magnitude exceeds L_y=(1+h) since u>1.
    # This syntactically valid y/y event is NOT an actual overlap edge.
    var run=symbolic_child(eps,0,1,old,RUN,one,RUN,one,2,2)
    var wanted=List[QX]()
    wanted.append(qx_const(-1))
    wanted.append(one.copy())
    wanted.append(zero.copy())
    if corrupt:
        wanted[2]=one.copy()
    _equal3(run,wanted)
    # Positions 2/2 are also word-legal throughout the cone, but still
    # need the independent geometric overlap check.
    var two=qx_const(2)
    var run2=symbolic_child(eps,0,1,old,RUN,two,RUN,two,2,2)
    _equal3(run2,wanted)

    # LAST occurrence of sigma(y) and sigma(c):
    # prefixes x*y^(n+eps) and c*y^n; retain epsilon in the residual.
    var a=qx_add(qx_add(n,qx_const(eps)),one)
    var b=qx_add(n,one)
    var last=symbolic_child(eps,2,1,old,LAST,a,LAST,b,1,0)
    var expected_last=List[QX]()
    expected_last.append(qx_const(-1))
    expected_last.append(one.copy())
    expected_last.append(qx_const(-eps))
    _equal3(last,expected_last)

    # Some important algebraic prefix choices are unrealizable words.
    var failed=False
    try:
        _=symbolic_child(eps,0,1,old,RUN,zero,RUN,one,2,2)
    except:
        failed=True
    if not failed:
        raise Error("accepted nonexistent run ordinal zero")
    failed=False
    try:
        _=symbolic_child(eps,0,1,old,RUN,qx_add(qx_add(n,d),one),RUN,one,2,2)
    except:
        failed=True
    if not failed:
        raise Error("accepted run ordinal past last y")
    print("CLASS_A_BOUNDARY_OCCURRENCE eps",eps,
          "first_loop=true",
          "same_letter_algebraic_not_geometric=true",
          "actual_prefix_indices=cone_checked",
          "BH=false")


def certify_all_typed_occurrences() raises:
    for eps in [-1,1]:
        certify_typed_occurrences(eps)
