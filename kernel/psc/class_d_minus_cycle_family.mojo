"""Symbolic exclusion of one unbounded higher-sum six-edge family.

QX's first formal variable is k here (the second is unused). Guard rows are
[c(k), u(k), v(k)]; a single u=a-2,v=b-1 applies to the whole itinerary.
No sampling in k establishes the certificate: polynomial identities do.
"""
from finite_linear_algebra.scalar import q_int
from psc.exact import q_sign
from psc.param_poly import (
    QX, qx_const, qx_affine, qx_add, qx_sub, qx_scale, qx_is_zero, qx_key, qx_mul, qx_shift,
)
from psc.class_d_minus_cycle_superset import _segment
from psc.class_d_minus_shared_cycles import negative_cycle, negative_segments


def six_edge_family() -> List[List[QX]]:
    var rows = List[List[QX]]()
    rows.append([qx_affine(0,-2), qx_affine(-1,4), qx_affine(1,-3)])
    rows.append([qx_affine(-1,2), qx_affine(2,-4), qx_affine(-2,3)])
    rows.append([qx_affine(1,-2), qx_affine(-3,4), qx_affine(2,-3)])
    rows.append([qx_affine(-1,2), qx_affine(2,-4), qx_affine(-2,3)])
    rows.append([qx_affine(1,-2), qx_affine(-3,4), qx_affine(2,-3)])
    rows.append([qx_affine(-2,2), qx_affine(2,-4), qx_affine(0,3)])
    return rows^


def _linear3(row: List[QX], a: Int, b: Int, c: Int) -> QX:
    return qx_add(qx_add(qx_scale(row[0],q_int(a)),qx_scale(row[1],q_int(b))),qx_scale(row[2],q_int(c)))


def six_edge_family_forms(rows: List[List[QX]]) raises -> List[List[QX]]:
    if len(rows) != 6:
        raise Error("six-edge symbolic itinerary needs six rows")
    for row in rows:
        if len(row) != 3:
            raise Error("symbolic offset needs three coordinates")
    var types = negative_cycle()
    var segments = negative_segments()
    var forms = List[List[QX]]()
    for i in range(6):
        var j = (i+1)%6
        var st = _segment(types[i].top,segments[i][0])
        var sb = _segment(types[i].bottom,segments[i][1])
        if types[j].top != st[0][0] or types[j].bottom != sb[0][0]:
            raise Error("symbolic family typed edge mismatch")
        var x = qx_add(_linear3(rows[i],1,1,0),qx_const(sb[1][0]-st[1][0]))
        var c = qx_add(_linear3(rows[i],1,1,2),qx_const(sb[1][1]-st[1][1]))
        if not qx_is_zero(qx_sub(rows[j][0],x)) or not qx_is_zero(qx_sub(rows[j][1],c)):
            raise Error("symbolic family x/c replay failed, including closing edge")
        # j_index-i_index = sp - A*a - C - s*b, with legal interval
        # [bottom_low-top_high, bottom_high-top_low]. No valuation is chosen.
        var req = List[QX]()
        req.append(_linear3(rows[i],-3,-3,-2))
        req.append(qx_sub(_linear3(rows[j],1,1,1),_linear3(rows[i],7,8,6)))
        req.append(_linear3(rows[i],-1,-1,-1))
        for side in range(2):
            var raw = List[QX]()
            for d in range(3):
                if side == 0:
                    raw.append(qx_sub(req[d],qx_const(sb[2][d]-st[3][d])))
                else:
                    raw.append(qx_sub(qx_const(sb[3][d]-st[2][d]),req[d]))
            # Raw order A,C,B -> shifted c,u,v after a=2+u,b=1+v.
            var shifted = List[QX]()
            shifted.append(qx_add(qx_add(raw[1],qx_scale(raw[0],q_int(2))),raw[2]))
            shifted.append(raw[0].copy())
            shifted.append(raw[2].copy())
            forms.append(shifted^)
    return forms^



def verify_even_family_edge_witnesses(forms: List[List[QX]]) raises:
    # For k=2t, t>=1, each edge has its OWN integral valuation. These are
    # not a whole-walk witness. Check their guards as polynomial identities.
    var us = List[QX]()
    us.append(qx_scale(qx_affine(-2,1),q_int(9).div(q_int(2))))
    us.append(qx_affine(-8,4))
    us.append(qx_affine(-4,2))
    us.append(qx_affine(-8,4))
    us.append(qx_affine(-3,2))
    us.append(qx_affine(-6,3))
    var vs: List[Int] = [7,2,0,2,0,4]
    for i in range(6):
        # u(k)>=0 for k>=2, v>=0. For even k the sole half-coefficient
        # 9(k-2)/2 is integral; the other witnesses are integral polynomials.
        var checks = List[QX]()
        checks.append(us[i].copy())
        for side in range(2):
            var f = forms[2*i+side].copy()
            checks.append(qx_add(qx_add(f[0],qx_mul(f[1],us[i])),qx_scale(f[2],q_int(vs[i]))))
        for check in checks:
            var shifted = qx_shift(check,2,0)  # k=2+h, h>=0
            for row in shifted:
                for coefficient in row:
                    if q_sign(coefficient) < 0:
                        raise Error("even-family edge witness lacks nonnegative coefficients")
    print("EVEN_FAMILY_EDGE_WITNESSES all_integer_t_ge_1=true k=2t per_edge_only=true whole_cycle_refuted=true")


def verify_six_edge_family() raises:
    var rows = six_edge_family()
    var forms = six_edge_family_forms(rows)
    var expected_sums = List[QX]()
    expected_sums.append(qx_affine(0,-1))
    expected_sums.append(qx_affine(-1,1))
    expected_sums.append(qx_affine(0,-1))
    expected_sums.append(qx_affine(-1,1))
    expected_sums.append(qx_affine(0,-1))
    expected_sums.append(qx_affine(0,1))
    for i in range(6):
        if not qx_is_zero(qx_sub(_linear3(rows[i],1,1,1),expected_sums[i])):
            raise Error("symbolic higher-sum pattern changed")
        print("FAMILY_OFFSET",i,qx_key(rows[i][0]),qx_key(rows[i][1]),qx_key(rows[i][2]))
    for i in range(len(forms)):
        print("FAMILY_GUARD",i,qx_key(forms[i][0]),qx_key(forms[i][1]),qx_key(forms[i][2]))
    verify_even_family_edge_witnesses(forms)
    var expected: List[Int] = [-7,-1,0]
    for d in range(3):
        if not qx_is_zero(qx_sub(qx_add(forms[0][d],forms[5][d]),qx_const(expected[d]))):
            raise Error("symbolic family unit-multiplier certificate failed")
    # Unit multipliers are nonnegative for every k. The resulting -7-u is
    # strictly negative for u>=0. This excludes all integer k>=2, without cap.
    print("SIX_EDGE_FAMILY_REFUTED all_integer_k_ge_2=true k_cap=none rows=0,5 sum=-7-u CycleSum=separate_seed_cover")
