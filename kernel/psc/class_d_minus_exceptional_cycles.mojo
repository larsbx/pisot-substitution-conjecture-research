"""Productivity certificates for the four recurrent cycle-superset exceptions.

The four genuine noncarrier recurrent candidates of
class_d_minus_cycle_superset are

  U  = (y,c,-2,4,-3),   Ubar = (c,y,2,-4,3),
  V  = (y,c,3,-6,4),    Vbar = (c,y,-3,6,-4).

Each has an explicit occurrence path into the sealed ranked carrier for every
a>=2,b>=1.  The child-state arithmetic is exact affine arithmetic in (a,b);
geometry is checked from the normalized minus root box X=d-2 in (0,1),
Y=10/beta in (0,1).
"""
from psc.class_d_minus_spine_data import minus_spine_rows
from psc.class_d_positive_b_spine import _occurrence, _occurrence_fixed_b
from psc.class_d_positive_b_geometry import _margins20, _verify_minus_root_box



def _label(row: List[Int]) -> List[Int]:
    return [row[0],row[1],row[2],row[3],row[4]]

def _same(a: List[Int], b: List[Int]) -> Bool:
    return len(a) == len(b) and a == b


def _child(
    source: List[Int], top_index: List[Int], bottom_index: List[Int],
    amin: Int = 2, bmin: Int = 1,
) raises -> List[Int]:
    var top = _occurrence(source[0],top_index,amin,bmin)
    var bottom = _occurrence(source[1],bottom_index,amin,bmin)
    var x = source[2]
    var c = source[3]
    var y = source[4]
    var mw = List[List[Int]]()
    mw.append([0,x+c,0])
    mw.append([0,x+c+2*y,0])
    mw.append([3*x+3*c+2*y,5*x+6*c+4*y,x+c+y])
    var out = List[Int]([top[0][0],bottom[0][0]])
    for k in range(3):
        var pt = top[1+k].copy()
        var pb = bottom[1+k].copy()
        var ca = mw[k][0]+pb[0]-pt[0]
        var c0 = mw[k][1]+pb[1]-pt[1]
        var cb = mw[k][2]+pb[2]-pt[2]
        if ca != 0 or cb != 0:
            raise Error("exceptional positive-b child state is not constant")
        out.append(c0)
    return out^


def _child_b1(
    source: List[Int], top_index: List[Int], bottom_index: List[Int],
) raises -> List[Int]:
    var top = _occurrence_fixed_b(source[0],top_index,1)
    var bottom = _occurrence_fixed_b(source[1],bottom_index,1)
    var x = source[2]
    var c = source[3]
    var y = source[4]
    var mw = List[List[Int]]()
    mw.append([0,x+c])
    mw.append([0,x+c+2*y])
    mw.append([3*x+3*c+2*y,5*x+6*c+4*y+(x+c+y)])
    var out = List[Int]([top[0][0],bottom[0][0]])
    for k in range(3):
        var pt = top[1+k].copy()
        var pb = bottom[1+k].copy()
        var ca = mw[k][0]+pb[0]-pt[0]
        var c0 = mw[k][1]+pb[1]-pt[1]
        if ca != 0:
            raise Error("exceptional b=1 child state is not constant")
        out.append(c0)
    return out^


def _corner_min(f: List[Int]) -> Int:
    # f=c+aX+bY on the closed unit square.
    var out = f[0]
    for X in range(2):
        for Y in range(2):
            out = min(out,f[0]+f[1]*X+f[2]*Y)
    return out


def _uniform_real(label: List[Int]) raises:
    var m = _margins20(label)
    if _corner_min(m[0]) <= 0 or _corner_min(m[1]) <= 0:
        raise Error("exceptional target is not uniformly interior on the root box")


def _source_implies_target(source: List[Int], target: List[Int]) raises:
    """One target margin may be source-identical; the other must be positive.

    This handles V->A and its mirror, where the new y/y state has one margin
    exactly equal to the source's delicate margin and the other equal to a
    positive combination of X,Y.
    """
    var sm = _margins20(source)
    var tm = _margins20(target)
    var matched = False
    for k in range(2):
        if _same(tm[k],sm[0]) or _same(tm[k],sm[1]):
            matched = True
            continue
        # Strictly positive on the open box: nonnegative coefficients and at
        # least one positive coefficient of X or Y, or positive constant.
        if tm[k][0] < 0 or tm[k][1] < 0 or tm[k][2] < 0:
            raise Error("exceptional target margin has a negative box coefficient")
        if tm[k][0] == 0 and tm[k][1] == 0 and tm[k][2] == 0:
            raise Error("exceptional target margin is identically zero")
    if not matched:
        raise Error("exceptional target does not inherit a source margin")


def verify_minus_exceptional_productivity() raises -> List[Int]:
    _verify_minus_root_box()
    var rows = minus_spine_rows()

    var U: List[Int] = [2,1,-2,4,-3]
    var Ub: List[Int] = [1,2,2,-4,3]
    var V: List[Int] = [2,1,3,-6,4]
    var Vb: List[Int] = [1,2,-3,6,-4]
    var A: List[Int] = [2,2,-3,5,-3]
    var Ab: List[Int] = [2,2,3,-5,3]

    # U -> sealed row 69: top FIRST, bottom run occurrence b.
    if _child(U,[0,0,0],[0,0,1]) != _label(rows[69]):
        raise Error("U exceptional exit changed")
    _uniform_real(_label(rows[69]))

    # Ubar -> sealed row 97: top run occurrence b, bottom FIRST.
    if _child(Ub,[0,0,1],[0,0,0]) != _label(rows[97]):
        raise Error("Ubar exceptional exit changed")
    _uniform_real(_label(rows[97]))

    # V -> A: top run b, bottom run a+2.
    if _child(V,[0,0,1],[1,2,0]) != A:
        raise Error("V first exceptional step changed")
    _source_implies_target(V,A)

    # For b=1, A -> row 44 by FIRST/FIRST.
    if _child_b1(A,[0,0,0],[0,0,0]) != _label(rows[44]):
        raise Error("V b=1 exceptional exit changed")
    _uniform_real(_label(rows[44]))

    # For b>=2, A -> row 69 by top FIRST, bottom run b-1.
    if _child(A,[0,0,0],[0,-1,1],2,2) != _label(rows[69]):
        raise Error("V b>=2 exceptional exit changed")

    # Mirror path.
    if _child(Vb,[1,2,0],[0,0,1]) != Ab:
        raise Error("Vbar first exceptional step changed")
    _source_implies_target(Vb,Ab)

    if _child_b1(Ab,[0,0,0],[0,0,0]) != _label(rows[35]):
        raise Error("Vbar b=1 exceptional exit changed")
    _uniform_real(_label(rows[35]))

    if _child(Ab,[0,-1,1],[0,0,0],2,2) != _label(rows[97]):
        raise Error("Vbar b>=2 exceptional exit changed")

    # All carrier targets above have rank <=2.
    for i in [35,44,69,97]:
        if rows[i][5] > 2:
            raise Error("exceptional exit no longer lands at rank <=2")

    return [4,8,4,2]
