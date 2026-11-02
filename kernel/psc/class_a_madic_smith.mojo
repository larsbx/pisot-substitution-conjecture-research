"""Exact Smith-invariant trichotomy of minus Class-A nonunit M-adic balls.

Not an overlap-hitting result. The binary address transversal of #453
exists in all chambers, but its finite quotient GROUP changes type:
 t even: cyclic order 2^m,
 t odd, k even: three balanced ramified exponents,
 t odd, k odd: one trivial invariant and two balanced exponents.

Expected factors are the parameter-uniform mathematical assertion.
The independent oracle is the EXISTING arbitrary precision generic Smith
kernel over exact Q, not an implementation of the same closed formula.
For verification, m<=6; the theorem's mathematical scope has no level cap.
"""
from finite_linear_algebra.madic_ball import quotient_invariants
from finite_exact.bigint_z import bigz_eq, bigz_from_i64
from psc.class_a_madic_digits import parameters, apply_incidence
from finite_exact.checked_int import checked_add, checked_sub, checked_mul


def predicted_smith(k: Int, t: Int, level: Int) raises -> List[Int]:
    _ = parameters(k,t)
    if level < 0 or level > 30:
        raise Error("out-of-range finite output level; not a theorem limitation")
    if t % 2 == 0:
        return [1,1,1 << level]
    if k % 2 == 0:
        var q=level//3
        var r=level%3
        var base=1 << q
        if r==0:
            return [base,base,base]
        if r==1:
            return [base,base,2*base]
        return [base,2*base,2*base]
    var q=level//2
    var base=1 << q
    if level%2 == 0:
        return [1,base,base]
    return [1,base,2*base]


def class_a_integer_matrix(k: Int,t: Int) raises -> List[Int]:
    var params=parameters(k,t)
    var n=params[0]
    var d=params[1]
    return [2,1,1,0,1,1,checked_add(n,d),n,checked_sub(n,1)]


def certify_smith_against_generic(k: Int,t: Int,level: Int) raises -> List[Int]:
    if level<0 or level>6:
        raise Error("independent exact generic Smith replay budget")
    var predicted=predicted_smith(k,t,level)
    var actual=quotient_invariants(class_a_integer_matrix(k,t),3,level)
    if len(actual)!=3:
        raise Error("generic Smith arithmetic produced wrong dimension")
    for i in range(3):
        if not bigz_eq(actual[i],bigz_from_i64(predicted[i])):
            raise Error("Class-A closed Smith invariant disagrees with exact determinantal divisors")
    return predicted


def cyclic_krylov_mod2(k: Int,t: Int) raises -> Bool:
    """Mod-2 cyclic-vector witness for Z_2[x]/(chi_M) model.

    For t odd use e_x; t even,k even use e_c; t even,k odd use e_c+e_y.
    Each choice is an actual integral vector. Odd determinant of
    [v,Mv,M²v] gives an integral 2-adic basis.
    """
    _ = parameters(k,t)
    var v: List[Int]
    if t%2!=0:
        v=[1,0,0]
    elif k%2==0:
        v=[0,1,0]
    else:
        v=[0,1,1]
    var u=apply_incidence(k,t,v)
    var w=apply_incidence(k,t,u)
    var d0=checked_sub(checked_mul(u[1],w[2]),checked_mul(u[2],w[1]))
    var d1=checked_sub(checked_mul(v[1],w[2]),checked_mul(v[2],w[1]))
    var d2=checked_sub(checked_mul(v[1],u[2]),checked_mul(v[2],u[1]))
    var determinant=checked_add(
        checked_sub(checked_mul(v[0],d0),checked_mul(u[0],d1)),
        checked_mul(w[0],d2),
    )
    if determinant%2==0:
        raise Error("selected Class-A local cyclic vector has even determinant")
    return True
