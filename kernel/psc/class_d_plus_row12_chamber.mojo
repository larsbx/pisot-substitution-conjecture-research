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


def _strict_positive_poly(coeff: List[Int]) -> Bool:
    """sum coeff[k] n^k is >0 for every integer n>=0 by coefficients."""
    if len(coeff) == 0 or coeff[0] <= 0:
        return False
    for c in coeff:
        if c < 0:
            return False
    return True


def verify_plus_row12_integer_chamber() raises -> List[Int]:
    # D=n+2.  The four exact cross-multiplied differences are:
    #
    # b0-(5D-4):
    #   (35D^2-60D+23)/(7D-5)^2
    # = (35n^2+80n+43)/(7n+9)^2.
    #
    # (5D-3)-b0:
    #   2(7D^2-5D+1)/(7D-5)^2
    # = (14n^2+46n+38)/(7n+9)^2.
    #
    # b1-(5D-3):
    #   (35D^2-48D+14)/(7D-4)^2
    # = (35n^2+92n+58)/(7n+10)^2.
    #
    # (5D-2)-b1:
    #   2(7D^2-4D+1)/(7D-4)^2
    # = (14n^2+48n+42)/(7n+10)^2.
    var numerators = List[List[Int]]()
    numerators.append([43,80,35])
    numerators.append([38,46,14])
    numerators.append([58,92,35])
    numerators.append([42,48,14])

    for p in numerators:
        if not _strict_positive_poly(p):
            raise Error("row-12 integer chamber numerator is not uniformly positive")

    # Denominator bases are 7n+9 and 7n+10, positive for every n>=0.
    if not _strict_positive_poly([9,7]) or not _strict_positive_poly([10,7]):
        raise Error("row-12 threshold denominator is not uniformly positive")

    # Translate the unique integer middle value:
    # b=5D-3=5(a+2)-3=5a+7; c=b-1=5a+6.
    var interface_b_slope = 5
    var interface_b_const = 7
    var interface_c_slope = 5
    var interface_c_const = 6

    return [
        len(numerators),
        interface_b_slope,
        interface_b_const,
        interface_c_slope,
        interface_c_const,
    ]
