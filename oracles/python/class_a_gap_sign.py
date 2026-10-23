"""Independent Fraction oracle for native tensor Bernstein conversion fixtures.

Mojo is canonical. This audits 25 deterministic bidegrees, their coefficients,
and polynomial identities at a full unisolvent rational tensor grid.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import sys


def power(m, n):
    seed = 5*m+n
    return [[(-1)**(i+j)*(1+(3*i+5*j+seed) % 7)
             for i in range(m+1)] for j in range(n+1)]


def audit(text):
    held = {}
    decisions = {}
    for line in text.splitlines():
        if line.startswith('GAP_SIGN_BILINEAR '):
            _, *fields = line.split()
            a,b,c,d,accepted = map(int, fields)
            if (a,b,c,d) in decisions or accepted not in (0,1):
                raise ValueError('malformed or duplicate bilinear decision')
            decisions[a,b,c,d] = accepted
    keys = {(a,b,c,d) for a in range(-1,2) for b in range(-1,2)
            for c in range(-1,2) for d in range(-1,2)}
    if set(decisions) != keys:
        raise ValueError('incomplete bilinear decision grid')
    for (a,b,c,d),accepted in decisions.items():
        # On (0,1]^2, nonnegative corners and a strictly positive (1,1)
        # corner are necessary and sufficient for bilinear strict positivity:
        # the positive xy weight always contributes that corner.
        positive = min(a,a+b,a+c,a+b+c+d) >= 0 and a+b+c+d > 0
        if accepted and not positive:
            raise ValueError(f'false-positive bilinear decision {(a,b,c,d)}')
    for line in text.splitlines():
        if not line.startswith('GAP_SIGN_COEFF'):
            continue
        _, m, n, j, i, value = line.split()
        key = tuple(map(int, (m,n,j,i)))
        if key in held:
            raise ValueError('duplicate native coefficient')
        held[key] = F(value)
    expected_keys = {(m,n,j,i) for m in range(5) for n in range(5)
                     for j in range(n+1) for i in range(m+1)}
    if set(held) != expected_keys:
        raise ValueError('incomplete native coefficient fixture grid')
    identities = 0
    for m in range(5):
        for n in range(5):
            p = power(m,n)
            for j in range(n+1):
                for i in range(m+1):
                    expected = sum(F(p[b][a])*F(2,7)**a*F(3,5)**b
                                   *F(comb(i,a),comb(m,a))*F(comb(j,b),comb(n,b))
                                   for a in range(i+1) for b in range(j+1))
                    if held[m,n,j,i] != expected:
                        raise ValueError(f'coefficient mismatch {(m,n,j,i)}')
            # Distinct m+1 by n+1 nodes uniquely identify these bidegrees.
            for xk in range(m+1):
                for yk in range(n+1):
                    x,y = F(xk,m+1), F(yk,n+1)
                    direct = sum(F(p[j][i])*(F(2,7)*x)**i*(F(3,5)*y)**j
                                 for j in range(n+1) for i in range(m+1))
                    bern = sum(held[m,n,j,i]*comb(m,i)*x**i*(1-x)**(m-i)
                               *comb(n,j)*y**j*(1-y)**(n-j)
                               for j in range(n+1) for i in range(m+1))
                    if direct != bern:
                        raise ValueError('polynomial identity mismatch')
                    identities += 1
    return len(held), identities


if __name__ == '__main__':
    coeffs, points = audit(Path(sys.argv[1]).read_text())
    print(f'GAP_SIGN_ORACLE polynomials=25 coefficients={coeffs} identity_points={points} exact_fraction=true bilinear_soundness=81')
