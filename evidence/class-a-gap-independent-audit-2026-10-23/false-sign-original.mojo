from old_poly import PolyHU, sign_on_box
from finite_exact.rat_q import Q
from psc.exact import q_sign

def main() raises:
    var f = PolyHU.const(1).add(PolyHU.monomial(1, 0, -106)).add(PolyHU.monomial(2, 0, 2809)).add(PolyHU.monomial(11, 0, -1))
    print("ORIGINAL_CERTIFIED_SIGN", sign_on_box(f, 1, 53))
    # u=1-10^-12, t=1/53: a point in the declared box.
    var h = Q(999999999999, 53000000000000)
    var hp = Q.one()
    for _ in range(11):
        hp = hp.mul(h)
    var v = Q.one().sub(Q(53,1).mul(h))
    print("EXACT_POINT_SIGN", q_sign(v.mul(v).sub(hp)))
