"""Independent exact symbolic cross multiplication of the row-12 thresholds."""
from sympy import symbols, expand, Poly


def test_thresholds_derive_the_four_positive_quadratics():
    n=symbols('n');D=n+2
    f0=245*D**3-511*D**2+345*D-77
    f1=245*D**3-392*D**2+200*D-34
    q0=(7*D-5)**2;q1=(7*D-4)**2
    differences=[f0-(5*D-4)*q0,(5*D-3)*q0-f0,
                 f1-(5*D-3)*q1,(5*D-2)*q1-f1]
    expected=[35*n*n+80*n+43,14*n*n+46*n+38,
              35*n*n+92*n+58,14*n*n+48*n+42]
    for got,want in zip(differences,expected):
        assert expand(got-want)==0
        assert all(c>0 for c in Poly(expand(got),n).all_coeffs())
