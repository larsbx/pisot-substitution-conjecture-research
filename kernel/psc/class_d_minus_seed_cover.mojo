"""Conditional forward closure of the sealed carrier, without CycleSum.

Every real swap seed and every real occurrence child of a real nonterminal
carrier state lies in the carrier. Strict geometry uses a correlated outer
region, not independent parameter choices. No bound on child sums is assumed:
the finite enumeration bound is derived from child interiority.
"""
from psc.class_d_minus_cycle_superset import CycleState, _segment, edge_forms
from psc.class_d_minus_spine_data import minus_spine_rows
from psc.class_d_positive_b_geometry import _margins20, _verify_minus_root_box
from psc.class_d_minus_recurrent_support import carrier_index
from psc.farkas_lp import lp_infeasible
from finite_linear_algebra.scalar import q_int
from psc.param_poly import TPoly, qx_const, qx_add, qx_affine2, qx_is_zero, tp_t, tp_const, tp_add, tp_sub, tp_mul, tp_scale
from symbolic_line_certificate import ClassWedge
from a1_normal_form_census import CLASS_D


def verify_correlated_root_region() raises:
    _verify_minus_root_box()
    var line = ClassWedge(CLASS_D,[6,3,1,7,3,1,5,2,1]).line()
    var beta = tp_t()
    var x = tp_sub(beta,tp_const(qx_add(line.run[2],qx_const(2))))
    # Bind the normalized lengths used by _margins20 to this exact matrix.
    # A positive left eigenvector is L=(beta*d-2,beta*d,2beta), d=beta-r;
    # dividing by L_y gives (d/2-1/beta,d/2,1).
    var d = tp_sub(beta,tp_const(line.run[2]))
    var lengths = List[TPoly]([tp_sub(tp_mul(beta,d),tp_const(qx_const(2))),tp_mul(beta,d),tp_scale(beta,qx_const(2))])
    for j in range(3):
        var identity = tp_sub(tp_const(qx_const(0)),tp_mul(beta,lengths[j]))
        for i in range(3):
            identity = tp_add(identity,tp_scale(lengths[i],line.m[i][j]))
        var remainder = line.field.reduce(identity)
        for coefficient in remainder:
            if not qx_is_zero(coefficient):
                raise Error("normalized tile-length binding failed")
    # Check the Perron identities modulo the exact characteristic polynomial.
    # beta*X = 2a+4-2/beta > 8-1/5 > 7, since beta>10.
    # beta*(1-X) = b+2+X+2/beta > 3, since b>=1 and X>0.
    # Thus 10X>7Y and 10-10X>3Y for Y=10/beta. Direct norm-sign
    # search on these expressions has a sign-changing auxiliary polynomial;
    # these identities use the already certified root box instead.
    var first = tp_add(tp_sub(tp_mul(tp_mul(beta,beta),x),tp_mul(tp_const(qx_affine2(4,2,0)),beta)),tp_const(qx_const(2)))
    var second = tp_sub(tp_sub(tp_mul(tp_mul(beta,beta),tp_sub(tp_const(qx_const(1)),x)),tp_mul(beta,tp_add(tp_const(qx_affine2(3,0,1)),x))),tp_const(qx_const(2)))
    for identity in [first.copy(),second.copy()]:
        var remainder = line.field.reduce(identity)
        for coefficient in remainder:
            if not qx_is_zero(coefficient):
                raise Error("correlated Perron identity failed exact reduction")
    if not q_int(7).lt(q_int(8).sub(q_int(2).div(q_int(10)))):
        raise Error("lower correlated-region rational estimate failed")
    print("MINUS_CORRELATED_ROOT_REGION 0<X,Y<1 10X>7Y 10-10X>3Y a>=2 b>=1")


def root_region(refined: Bool = True) -> List[List[Int]]:
    var forms: List[List[Int]] = [[0,1,0],[0,0,1],[1,-1,0],[1,0,-1]]
    if refined:
        forms.append([0,10,-7])
        forms.append([10,-10,-3])
    return forms^


def strict_geometry_refuted(forms: List[List[Int]]) raises -> Bool:
    # A single affine margin nonpositive everywhere on [0,1]^2 suffices.
    for f in forms:
        if len(f) != 3:
            raise Error("geometry form must have width three")
        if f[0]+max(f[1],0)+max(f[2],0) <= 0:
            return True
    # If all f_i(X,Y)>0, choose epsilon>0 no greater than every f_i.
    # Variables (X/epsilon,Y/epsilon,1/epsilon)>=0 satisfy
    # -1 + a_i*x + b_i*y + c_i*z >=0. Refute that closed system.
    # Missing Farkas certificate retains the obligation, never removes an edge.
    var lifted = List[List[Int]]()
    for f in forms:
        lifted.append([-1,f[1],f[2],f[0]])
    return lp_infeasible(lifted,3)


def _add_margins(mut forms: List[List[Int]], v: CycleState):
    var ms = _margins20([v.top,v.bottom,v.x,v.c,v.y])
    forms.append(ms[0].copy())
    forms.append(ms[1].copy())


def seed_cover_check(rows: List[List[Int]], refined: Bool = True) raises -> List[Int]:
    # This interface is intentionally restricted to the finite certificate's
    # coordinate budget; it does not accept unchecked arbitrary machine ints.
    if len(rows) == 0 or len(rows) > 200:
        raise Error("seed-cover table budget exceeded")
    for row in rows:
        if len(row) < 5 or row[0] < 0 or row[0] > 2 or row[1] < 0 or row[1] > 2:
            raise Error("invalid seed-cover row")
        for j in range(2,5):
            if row[j] < -10 or row[j] > 10:
                raise Error("seed-cover coordinate budget exceeded")
        if abs(row[2]+row[3]+row[4]) > 1:
            raise Error("carrier does not imply the sum conclusion")
    var seeds_in = 0
    var seeds_excluded = 0
    for a in range(3):
        for b in range(a+1,3):
            for i in range(2):
                for j in range(2):
                    var w: List[Int] = [0,0,0]
                    if j == 1:
                        w[b] += 1
                    if i == 1:
                        w[a] -= 1
                    var v = CycleState(a if i==0 else b,b if j==0 else a,w[0],w[1],w[2])
                    if carrier_index(v,rows) >= 0:
                        seeds_in += 1
                    else:
                        var forms = root_region(refined)
                        _add_margins(forms,v)
                        if not strict_geometry_refuted(forms):
                            print("SEED_COVER_UNRESOLVED_SEED",v.key())
                            raise Error("seed cover failed initial inclusion")
                        seeds_excluded += 1
    var children_in = 0
    var geometry_excluded = 0
    var guards_excluded = 0
    var segments = 0
    var candidates = 0
    var terminals = 0
    for row in rows:
        var v = CycleState(row[0],row[1],row[2],row[3],row[4])
        if v.top == v.bottom and v.is_zero_offset():
            terminals += 1
            continue
        for kt in range(3):
            var st = _segment(v.top,kt)
            for kb in range(3):
                var sb = _segment(v.bottom,kb)
                segments += 1
                # Affine recurrence: M w plus bottom minus top proper prefixes.
                var xp = v.x+v.c+sb[1][0]-st[1][0]
                var cp = v.x+v.c+2*v.y+sb[1][1]-st[1][1]
                var mp = xp+cp
                # Child t'=sp+mp*X/2-xp*Y/10; tile lengths <3/2.
                # Interiority implies |sp|<3/2+|mp|/2+|xp|/10,
                # hence the conservative integer bound below covers ALL sums.
                var bound = 2+abs(mp)+abs(xp)
                for sp in range(-bound,bound+1):
                    candidates += 1
                    var child = CycleState(st[0][0],sb[0][0],xp,cp,sp-mp)
                    if carrier_index(child,rows) >= 0:
                        children_in += 1
                        continue
                    var forms = root_region(refined)
                    _add_margins(forms,v)
                    _add_margins(forms,child)
                    if strict_geometry_refuted(forms):
                        geometry_excluded += 1
                        continue
                    if lp_infeasible(edge_forms(v,st,sb,sp),2):
                        guards_excluded += 1
                        continue
                    print("SEED_COVER_UNRESOLVED_CHILD",v.key(),kt,kb,child.key())
                    raise Error("seed cover has an unexplained child obligation")
    print("MINUS_SEED_COVER_COUNTS",len(rows),seeds_in,seeds_excluded,terminals,segments,candidates,children_in,geometry_excluded,guards_excluded)
    return [len(rows),seeds_in,seeds_excluded,terminals,segments,candidates,children_in,geometry_excluded,guards_excluded]


def verify_minus_seed_cover() raises -> List[Int]:
    verify_correlated_root_region()
    var result = seed_cover_check(minus_spine_rows())
    print("MINUS_SEED_COVER_CERTIFIED a>=2 b>=1 all_real_seed_descendants_in_carrier=true abs_sum<=1 parameter_cap=none")
    return result^
