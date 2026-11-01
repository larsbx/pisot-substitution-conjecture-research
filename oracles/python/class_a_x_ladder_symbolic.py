"""Exact polynomial certificate, not finite parameter interpolation.

SymPy is only used for Z[k,t,m] and polynomial remainder arithmetic;
no numerical roots, analytical estimates or floating decisions are used.
Domain inequalities and strict geometry are derived in the accompanying note.
"""
from pathlib import Path
import runpy
from sympy import Poly, expand, symbols

local = runpy.run_path(str(Path(__file__).with_name("class_a_x_productivity.py")))
k, t, m, beta = symbols("k t m beta")
n, d = k+t+3, k+2*t+5
A = n+d


def zero(expr):
    if not Poly(expand(expr), k, t, m, beta).is_zero:
        raise ValueError("nonzero symbolic coefficient")


def run(parent):
    return (A, n, n-1)[parent]


def occurrence(parent, kind, index):
    if kind == "FIRST":
        zero(index)
        return (1 if parent == 1 else 0), (0, 0, 0)
    if kind == "LAST":
        zero(index-run(parent)-1)
        return (1 if parent == 2 else 0), (int(parent != 1), int(parent == 1), run(parent))
    if kind != "RUN":
        raise ValueError("unknown occurrence kind")
    # RUN inequalities are separately certified, not inferred from the name.
    return 2, (int(parent != 1), int(parent == 1), index-1)


def check_edge(a, tk, i, bk, j, b):
    lt, pt = occurrence(a[0], tk, i)
    lb, pb = occurrence(a[1], bk, j)
    if (lt, lb) != b[:2]:
        raise ValueError("wrong symbolic target type")
    p, q, r = a[2:]
    image = (2*p+q+r, q+r, (n+d)*p+n*q+(n-1)*r)
    for z in range(3):
        zero(image[z]+pb[z]-pt[z]-b[z+2])


def certify():
    a, b = local["ladder_a"](m), local["ladder_b"](m)
    D, H, J, X, Q, C = ((2, 0, -1, -4, 6), (0, 2, 1, 2, -3),
        (0, 2, 1, -1, 1), local["X"], (2, 0, 0, -1, 1), local["C"])
    i, j = d+k+8-2*(k+1)*m, d+2*k+9-2*(k+1)*m
    rows = [(a, "RUN", i, "FIRST", 0, b),
        (b, "FIRST", 0, "RUN", j, local["ladder_a"](m-1)),
        (local["ladder_a"](1), "RUN", d+5-k, "FIRST", 0, D),
        (D, "FIRST", 0, "RUN", t+6, H),
        (H, "LAST", A+1, "RUN", n-1, J),
        (J, "LAST", A+1, "FIRST", 0, X),
        (X, "RUN", d+1, "FIRST", 0, Q),
        (Q, "RUN", 1, "RUN", 2, C)]
    for a, tk, i, bk, j, b in rows:
        check_edge(a, tk, i, bk, j, b)
        check_edge(local["reverse"](a), bk, j, tk, i, local["reverse"](b))
    # Root identities: polynomial divisibility, with explicit nonzero beta
    # and beta+1 denominators inherited from beta>n+2>=5.
    chi = beta**3-(n+2)*beta**2-(t+3)*beta+2
    alpha = beta-(n+2)
    h = 1/beta
    rho = alpha-h
    v = (k+1)/(beta+1)
    for expr in (alpha-(t+3)*h+2*h**2,
                 (alpha+2*h)*(beta+1)-(beta-k), 1-rho-3*h-v):
        from sympy import cancel, fraction
        numerator, _ = fraction(cancel(expr))
        remainder = Poly(numerator, beta).rem(Poly(chi, beta)).as_expr()
        zero(remainder)
    # Direct physical shift expressions and algebraic index slack identities.
    aa, bb = 2+rho, 1+h
    from sympy import cancel, fraction
    for label, want in ((local["ladder_a"](m), 2+h-2*m*v),
                         (local["ladder_b"](m), -2-h+(2*m-1)*v)):
        p, q, r = label[2:]
        numerator, _ = fraction(cancel(p*aa+q*bb+r-want))
        zero(Poly(numerator, beta).rem(Poly(chi, beta)).as_expr())
    i, j = d+k+8-2*(k+1)*m, d+2*k+9-2*(k+1)*m
    zero(i-(2*(k+t+6-(k+1)*m)+1))
    zero(j-i-k-1)
    zero((A-j)-((2*k+t-2)+k+2*(k+1)*(m-2)))
    zero((A-i)-((2*k+t-2)+2*k+1+2*(k+1)*(m-2)))
    zero((A-(d+5-k))-(2*k+t-2))
    zero((A-(t+6))-(2*k+2*t+2))
    return dict(symbolic_directed_edges=16, coefficient_ring="Z[k,t,m]",
        root_identities=3, strict_geometry="written exact inequalities; inherited root bounds",
        universal_x_productivity=False)


if __name__ == "__main__":
    import json
    print(json.dumps(certify(), indent=2, sort_keys=True))
