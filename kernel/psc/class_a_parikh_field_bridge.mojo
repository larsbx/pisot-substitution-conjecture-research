"""Exact minus-class-A full-Parikh <-> cubic field bridge.

With normalized lengths x=(-1,d,1), c=(-1,0,1), y=(0,-1,1)
in the power basis (1,beta,beta^2), the length map has determinant d.
Thus full Parikh coordinates are uniquely recoverable whenever d>0.
All integer arithmetic is checked; no global tile-length independence assumed.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul, checked_neg
from psc.perron_field3 import (
    CubicElt, PerronField3, TileLengths3,
    cubic_mul_beta, cubic_add_checked,
)

def class_a_parameters(k: Int, t: Int) raises -> List[Int]:
    if k < 0 or t < 0:
        raise Error("minus class-A chamber requires k,t >= 0")
    var n = checked_add(checked_add(k,t),3)
    var d = checked_add(checked_add(k,checked_mul(2,t)),5)
    return [n,d,checked_add(n,d)]

def check_minus_class_a_field(field: PerronField3, n: Int, d: Int) raises:
    if n < 3 or d < 5:
        raise Error("invalid minus class-A n/d chamber")
    if (field.chi0 != 2 or
        field.chi1 != checked_sub(checked_sub(n,d),1) or
        field.chi2 != checked_neg(checked_add(n,2))):
        raise Error("cubic field does not match minus class-A incidence")

def class_a_lengths(d: Int) raises -> TileLengths3:
    if d < 5:
        raise Error("minus class-A length lattice requires d >= 5")
    return TileLengths3(
        CubicElt(-1,d,1), CubicElt(-1,0,1), CubicElt(0,-1,1))

def parikh_shift(d: Int, p: Int, q: Int, r: Int) raises -> CubicElt:
    if d < 5:
        raise Error("invalid minus class-A d")
    return CubicElt(
        checked_neg(checked_add(p,q)),
        checked_sub(checked_mul(d,p),r),
        checked_add(checked_add(p,q),r))

def decode_parikh_shift(d: Int, shift: CubicElt) raises -> List[Int]:
    """Invert the exact index-d sublattice; refuse off-lattice shifts."""
    if d < 5:
        raise Error("invalid class-A Parikh-lattice index")
    var numerator = checked_add(checked_add(shift.a0,shift.a1),shift.a2)
    if numerator % d != 0:
        raise Error("cubic shift is outside the full-Parikh length lattice")
    var p = numerator // d
    var q = checked_sub(checked_neg(shift.a0),p)
    var r = checked_add(shift.a0,shift.a2)
    if parikh_shift(d,p,q,r) != shift:
        raise Error("Parikh-to-cubic inverse failed")
    return [p,q,r]

def verify_class_a_intertwining(
    field: PerronField3, n: Int, d: Int, p: Int, q: Int, r: Int,
) raises:
    """S(M*w)=beta*S(w) for exact cubic, with checked intermediates."""
    check_minus_class_a_field(field,n,d)
    var A = checked_add(n,d)
    var m_p = checked_add(checked_add(checked_mul(2,p),q),r)
    var m_q = checked_add(q,r)
    var m_r = checked_add(
        checked_add(checked_mul(A,p),checked_mul(n,q)),
        checked_mul(checked_sub(n,1),r))
    if parikh_shift(d,m_p,m_q,m_r) != cubic_mul_beta(
        field,parikh_shift(d,p,q,r)):
        raise Error("full Parikh/cubic-field beta intertwining failed")

def verify_indexed_parikh_child(
    field: PerronField3, n: Int, d: Int,
    p: Int, q: Int, r: Int,
    top_x: Int, top_c: Int, top_y: Int,
    bottom_x: Int, bottom_c: Int, bottom_y: Int,
    result_x: Int, result_c: Int, result_y: Int,
) raises:
    """Check transported actual prefix counts, not their word addresses.

    Caller must separately prove that these are real indexed prefixes.
    """
    for val in [top_x,top_c,top_y,bottom_x,bottom_c,bottom_y]:
        if val < 0:
            raise Error("proper-prefix Parikh counts cannot be negative")
    verify_class_a_intertwining(field,n,d,p,q,r)
    var A=checked_add(n,d)
    var target_x=checked_sub(
        checked_add(checked_add(checked_mul(2,p),q),r),
        checked_sub(top_x,bottom_x))
    var target_c=checked_sub(checked_add(q,r),checked_sub(top_c,bottom_c))
    var target_y=checked_sub(
        checked_add(
            checked_add(checked_mul(A,p),checked_mul(n,q)),
            checked_mul(checked_sub(n,1),r)),
        checked_sub(top_y,bottom_y))
    if result_x != target_x or result_c != target_c or result_y != target_y:
        raise Error("actual child full Parikh identity mismatch")
    var shift=parikh_shift(d,p,q,r)
    var prefix_delta=parikh_shift(d,
        checked_sub(bottom_x,top_x),
        checked_sub(bottom_c,top_c),
        checked_sub(bottom_y,top_y))
    var expected=cubic_add_checked(cubic_mul_beta(field,shift),prefix_delta)
    if parikh_shift(d,result_x,result_c,result_y) != expected:
        raise Error("actual child cubic shift does not commute with Parikh")
