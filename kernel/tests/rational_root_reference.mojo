"""Frozen main@f6e181d rational-root algorithm, for tests/benchmarks only."""
from psc.exact import q_poly, q_int, q_is_zero
from psc.pisot import poly_eval

def has_rational_root(coeffs: List[Int]) -> Bool:
    """Any degree, exact. A rational root of a monic integer polynomial is an
    integer dividing the constant term."""
    if coeffs[0] == 0:
        return True                      # zero is a root
    var p = q_poly(coeffs)
    var c = abs(coeffs[0])
    var d = 1
    while d * d <= c:
        if c % d == 0:
            var other = c // d
            if q_is_zero(poly_eval(p, q_int(d))):
                return True
            if q_is_zero(poly_eval(p, q_int(-d))):
                return True
            if q_is_zero(poly_eval(p, q_int(other))):
                return True
            if q_is_zero(poly_eval(p, q_int(-other))):
                return True
        d += 1
    return False

