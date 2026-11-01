"""Exact odd-plane transport and integer guard certificates.

No interpolation: compare full polynomial coefficients over Z[k,t,z,s,p].
Generic identities do NOT assert the occurrence guards. The four unbounded
integer guard chambers certify only the z=1,s=0 productive slice.
"""
from sympy import Poly, cancel, expand, fraction, symbols

k, t, z, s, p = symbols("k t z s p")
beta = symbols("beta")
n, d, K = k+t+3, k+2*t+5, k+1
A = n+d
GENS = (k, t, z, s, p, beta)


def zero(expr):
    if not Poly(expand(expr), *GENS).is_zero:
        raise ValueError("nonzero polynomial coefficient")


def src(z, s, p):
    return (0, 2, p, 3*p+2*s+1, z-6*p-3*s-1)


def mid(z, s, p):
    return (2, 0, z-p-s-1, z-3*p-s, 6*p+3*s+1-4*z)


def reverse(w):
    return (w[1], w[0], *(-v for v in w[2:]))


def occurrence(parent, kind, index, fixed):
    run = (A, n, n-1)[parent].subs(fixed)
    index = expand(index).subs(fixed)
    if kind == "FIRST":
        zero(index)
        return (1 if parent == 1 else 0), (0, 0, 0)
    if kind == "LAST":
        zero(index-run-1)
        return (1 if parent == 2 else 0), (int(parent != 1), int(parent == 1), run)
    if kind != "RUN":
        raise ValueError("unknown occurrence type")
    return 2, (int(parent != 1), int(parent == 1), index-1)


def check_edge(a, tk, i, bk, j, b, fixed=None):
    fixed = fixed or {}
    lt, pt = occurrence(a[0], tk, i, fixed)
    lb, pb = occurrence(a[1], bk, j, fixed)
    if (lt, lb) != b[:2]:
        raise ValueError("wrong target child letter")
    x, c, y = a[2:]
    image = (2*x+c+y, c+y, (n+d)*x+n*c+(n-1)*y)
    for q in range(3):
        zero(expand(image[q]+pb[q]-pt[q]-b[q+2]).subs(fixed))


def nonnegative(expr, gens):
    if any(v < 0 for v in Poly(expand(expr), *gens).coeffs()):
        raise ValueError("negative coefficient in unbounded guard chamber")


def certify():
    i = (z-s)*n-K*p+3*z+1
    j = (K+3)*z-K*p+(n-K)*s+d+1
    rows = [(src(z, s, p), "RUN", i, "FIRST", 0, mid(z, s, p)),
            (mid(z, s, p), "FIRST", 0, "RUN", j, src(z, s, p-z))]
    P0, E, D, C = src(1, 0, 0), (0, 0, 0, 1, 0), (2, 0, 0, 1, -1), (2, 2, 0, 0, 0)
    base = [(P0, "RUN", n+2, "FIRST", 0, D),
            (E, "RUN", n+2, "FIRST", 0, D),
            (D, "RUN", 2, "RUN", 1, C)]
    for a, tk, ii, bk, jj, b in rows+base:
        check_edge(a, tk, ii, bk, jj, b)
        check_edge(reverse(a), bk, jj, tk, ii, reverse(b))
    exceptional = (mid(1, 0, 1), "FIRST", 0, "LAST", 9, E)
    a, tk, ii, bk, jj, b = exceptional
    check_edge(a, tk, ii, bk, jj, b, {k: 0, t: 0})
    check_edge(reverse(a), bk, jj, tk, ii, reverse(b), {k: 0, t: 0})
    w = src(z, s, p)
    zero(3*w[2]+3*w[3]+2*w[4]-(2*z+1))
    zero(w[3]-3*w[2]-(2*s+1))
    for got, want in zip(reverse(mid(1, 0, p))[2:], src(1, -1, p)[2:]):
        zero(got-want)
    zero((j-i)-((K-n)*z+(2*n-K)*(s+1)))
    # z=2,s=0,p=2m is exactly the preceding A_m transfer, not a rival map.
    for q, want in zip(src(2, 0, 2*p)[2:], (2*p, 6*p+1, 1-12*p)):
        zero(q-want)
    zero(i.subs({z: 2, s: 0, p: 2*p}, simultaneous=True)-(d+k+8-2*K*p))
    zero(j.subs({z: 2, s: 0, p: 2*p}, simultaneous=True)-(d+2*k+9-2*K*p))
    # Unit slice ordinal slacks and the only possible LAST overshoot.
    iu, ju = n+4-K*p, 2*n+4-K*p
    zero(iu-i.subs({z: 1, s: 0}))
    zero(ju-j.subs({z: 1, s: 0}))
    zero(iu-((n+3-K*p)+1))
    zero(A-iu-(d-4+K*p))
    zero(A-ju-(t-2+K*p))
    # Four exact, exhaustive nonexceptional integer cases. p>=1.
    u, v = symbols("u v")
    slack = t-2+K*p
    nonnegative(slack.subs({t: u+2, p: v+1}), (k, u, v))
    nonnegative(slack.subs({t: 1, p: v+1}), (k, v))
    nonnegative(slack.subs({t: 0, k: u+1, p: v+1}), (u, v))
    nonnegative(slack.subs({t: 0, k: 0, p: u+2}), (u,))
    zero(slack.subs({k: 0, t: 0, p: 1})+1)
    # Inherited cubic and exact physical shift formulas for P_p and Q_p.
    chi = beta**3-(n+2)*beta**2-(t+3)*beta+2
    h, rho = 1/beta, beta-(n+2)-1/beta
    vv = K/(beta+1)
    exprs = [1-rho-3*h-vv]
    for label, want in ((src(1, 0, p), 1+h-p*vv),
                        (mid(1, 0, p), -2+h+p*vv)):
        x, c, y = label[2:]
        exprs.append(x*(2+rho)+c*(1+h)+y-want)
    for expr in exprs:
        numerator, _ = fraction(cancel(expr))
        zero(Poly(numerator, beta).rem(Poly(chi, beta)).as_expr())
    return dict(coefficient_ring="Z[k,t,z,s,p]", generic_directed_edges=4,
        base_directed_edges=6, exceptional_directed_edges=2,
        unbounded_integer_guard_chambers=4, inherited_root_and_shift_identities=3,
        generic_guard_free_productivity=False, universal_x_productivity=False)


if __name__ == "__main__":
    import json
    print(json.dumps(certify(), indent=2, sort_keys=True))
