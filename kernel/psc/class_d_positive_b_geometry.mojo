"""Exact conditional geometry for the minus positive-b selected spine.

Normalize ell_y=1 and put X=d-2, Y=10/beta.  On the minus residual with
a>=2,b>=1, the PIP root satisfies 0<X<1 and 0<Y<1.  For any fixed overlap
label, 20 times each realness margin is an integer-affine form in X,Y.

For every #287 selected descent this module proves by checked Farkas
certificates that source realness on the closed box 0<=X,Y<=1 implies both
target margins are >2/20=1/10.  Thus conditional geometric interiority does
not require parameter chambers on the minus branch.
"""
from psc.class_d_minus_spine_data import minus_spine_rows
from psc.class_d_positive_b_spine import positive_b_target_row
from finite_linear_algebra.scalar import q_int
from psc.farkas_lp import lp_infeasible
from psc.param_poly import TPoly, qx_add, qx_const, tp_const, tp_sub, tp_t
from psc.symbolic_line import Eventual, Line, NORM_UNDECIDED, certify_wedge_pisot, norm_sign
from symbolic_line_certificate import ClassWedge
from a1_normal_form_census import CLASS_D


def _length20(letter: Int) -> List[Int]:
    # [constant, X coefficient, Y coefficient], where
    # d=2+X and beta^{-1}=Y/10.
    if letter == 0:
        return [20,10,-2]  # 20*(d/2 - 1/beta)
    if letter == 1:
        return [20,10,0]   # 20*(d/2)
    return [20,0,0]        # 20*ell_y


def _add(u: List[Int], v: List[Int]) -> List[Int]:
    return [u[0]+v[0],u[1]+v[1],u[2]+v[2]]


def _neg(u: List[Int]) -> List[Int]:
    return [-u[0],-u[1],-u[2]]


def _margins20(row: List[Int]) -> List[List[Int]]:
    # shift = (x+c)d/2 + y - x/beta.
    var x = row[2]
    var c = row[3]
    var y = row[4]
    var shift: List[Int] = [20*(x+c+y), 10*(x+c), -2*x]
    var lower = _add(shift,_length20(row[1]))
    var upper = _add(_length20(row[0]),_neg(shift))
    return [lower^,upper^]


def _prove_target_margin(source: List[Int], target_margin: List[Int]) raises:
    # LP variables X,Y are already constrained >=0 by psc.farkas_lp.
    # Add X<=1, Y<=1 and the closed source-realness margins.
    var forms = List[List[Int]]()
    forms.append([1,-1,0])
    forms.append([1,0,-1])
    var sm = _margins20(source)
    forms.append(sm[0].copy())
    forms.append(sm[1].copy())
    # Refute target_margin <= 2.  Since all quantities are exact rationals,
    # infeasibility proves target_margin > 2, i.e. physical margin > 1/10.
    forms.append([2-target_margin[0],-target_margin[1],-target_margin[2]])
    if not lp_infeasible(forms,2):
        raise Error("source realness does not prove the selected target margin")


def _prove_case(rows: List[List[Int]], source: Int, branch: Int) raises:
    var target = positive_b_target_row(rows,source,branch)
    if target < 0 or target >= len(rows):
        raise Error("conditional geometry has no selected target")
    if rows[target][5] >= rows[source][5]:
        raise Error("conditional geometry target is not lower rank")
    var tm = _margins20(rows[target])
    _prove_target_margin(rows[source],tm[0])
    _prove_target_margin(rows[source],tm[1])


def _perron_sign(line: Line, h: TPoly, mut ev: Eventual) raises -> Int:
    var s = norm_sign(line,h,ev)
    if s == NORM_UNDECIDED:
        s = line.field.sign_at_beta(h,ev)
    return s


def _verify_minus_root_box() raises:
    # Shifted second parameter c=b-1>=0. Restrict first parameter to a>=2
    # by setting Eventual.threshold=1 (the region is integer a>threshold).
    var line = ClassWedge(CLASS_D, [6,3,1, 7,3,1, 5,2,1]).line()
    var ev = Eventual()
    ev.threshold = q_int(1)
    ev.b_floor = 0
    var cert = certify_wedge_pisot(line,ev)
    if not cert.holds:
        raise Error("minus positive-b root box failed the PIP certificate")
    if ev.first_integer_above() != 2 or ev.b_floor != 0:
        raise Error("minus positive-b root-box proof shrank its declared domain")

    var r = line.run[2].copy()
    var beta_gt_r2 = tp_sub(tp_t(),tp_const(qx_add(r,qx_const(2))))
    var r3_gt_beta = tp_sub(tp_const(qx_add(r,qx_const(3))),tp_t())
    var beta_gt_10 = tp_sub(tp_t(),tp_const(qx_const(10)))
    if _perron_sign(line,beta_gt_r2,ev) <= 0:
        raise Error("failed to prove beta > r+2")
    if _perron_sign(line,r3_gt_beta,ev) <= 0:
        raise Error("failed to prove beta < r+3")
    if _perron_sign(line,beta_gt_10,ev) <= 0:
        raise Error("failed to prove beta > 10")
    if ev.first_integer_above() != 2 or ev.b_floor != 0:
        raise Error("Perron box signs required an undeclared parameter cut")

def verify_minus_positive_b_conditional_geometry() raises -> List[Int]:
    _verify_minus_root_box()
    var rows = minus_spine_rows()
    if len(rows) != 145:
        raise Error("sealed minus spine row count changed")
    var targets = 0
    var cases = 0
    var margins = 0
    for i in range(len(rows)):
        if rows[i][6] < 0:
            targets += 1
            continue
        if i == 123 or i == 141:
            _prove_case(rows,i,1)
            cases += 1
            margins += 2
        _prove_case(rows,i,2)
        cases += 1
        margins += 2
    if targets != 6 or cases != 141 or margins != 282:
        raise Error("conditional geometry case count changed")
    return [len(rows),targets,cases,margins,1,10]
