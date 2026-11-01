"""Exact integer-lattice squeeze for plus class-D sealed row 12.

For D=a+2>=2, the row-12 Perron comparison has two rational b-thresholds

  b0=(245D^3-511D^2+345D-77)/(7D-5)^2
  b1=(245D^3-392D^2+200D-34)/(7D-4)^2.

This verifier proves

  5D-4 < b0 < 5D-3 < b1 < 5D-2

for every integer D>=2 by rewriting each cross-multiplied numerator in
n=D-2>=0 and checking coefficient positivity. Therefore the only integer b
between the two thresholds is b=5D-3, equivalently c=b-1=5a+6.
"""


from psc.param_poly import QX, qx_const, qx_affine, qx_add, qx_sub, qx_mul, qx_key, qx_row
from finite_linear_algebra.scalar import q_int
from psc.exact import q_sign


def _polynomial(coeff: List[Int], variable: QX) -> QX:
    var out = qx_const(0)
    for i in range(len(coeff)-1,-1,-1):
        out = qx_add(qx_mul(out,variable),qx_const(coeff[i]))
    return out^


def _positive(p: QX) raises:
    if len(p)!=1 or len(p[0])==0 or q_sign(p[0][0])<=0:
        raise Error("row-12 strict coefficient positivity failed")
    for c in p[0]:
        if q_sign(c)<0:
            raise Error("row-12 coefficient positivity failed")


def verify_plus_row12_threshold_formulas(numerator0: List[Int], numerator1: List[Int]) raises:
    # Build every difference from the actual threshold formulas, rather than
    # accepting independent positive tuples as evidence for an unrelated claim.
    var D = qx_affine(2,1)
    var n = qx_affine(0,1)
    var den0 = _polynomial([-5,7],D)
    var den1 = _polynomial([-4,7],D)
    _positive(den0); _positive(den1)
    var square0=qx_mul(den0,den0)
    var square1=qx_mul(den1,den1)
    var low=_polynomial([-4,5],D)
    var middle=_polynomial([-3,5],D)
    var high=_polynomial([-2,5],D)
    var num0=_polynomial(numerator0,D)
    var num1=_polynomial(numerator1,D)
    var actual=List[QX]()
    actual.append(qx_sub(num0,qx_mul(low,square0)))
    actual.append(qx_sub(qx_mul(middle,square0),num0))
    actual.append(qx_sub(num1,qx_mul(middle,square1)))
    actual.append(qx_sub(qx_mul(high,square1),num1))
    var expected=List[List[Int]]()
    expected.append([43,80,35]);expected.append([38,46,14])
    expected.append([58,92,35]);expected.append([42,48,14])
    for i in range(4):
        if qx_key(actual[i])!=qx_key(_polynomial(expected[i],n)):
            raise Error("row-12 threshold identity mismatch")
        _positive(actual[i])


def verify_plus_row12_integer_chamber() raises -> List[Int]:
    verify_plus_row12_threshold_formulas([-77,345,-511,245],[-34,200,-392,245])
    return [4,5,7,5,6]
