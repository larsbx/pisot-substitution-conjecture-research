#!/usr/bin/env python3
"""Independent Python exact-integer regression for Class-C Perron-root walls.

The universally quantified mathematical argument is the algebraic derivation
in docs/class-c-lower-cone-root-walls-2026-10-30.md, not this finite grid.
No floating-point roots or external dependencies.
"""

def chi(d: int, eps: int, n: int, t: int) -> int:
    # Independent from Mojo's factored form.
    A = n - d + eps + 3
    B = n - 3*d + 3*eps + 2
    return t**3 - A*t*t + B*t - 2*eps

def run() -> None:
    count = 0
    for eps in (1, -1):
        for d in range(7, 81):
            for c in range(d + 7):
                n = (2*d - 5 if eps == 1 else 2*d + 1) + c
                r = n-d+eps
                got = [chi(d,eps,n,r+h) for h in (2,3,4,5)]
                if eps == 1:
                    want = [
                        -2*((d-1)*c + d*d - 3*d + 3),
                        c*(c-1)-d*(d-1)-2,
                        2*(c*c+c*d-1),
                        3*c*c+4*c*d+5*c+d*d+3*d,
                    ]
                    if 0 <= c <= d+4:
                        if c == 0:
                            assert got[2] < 0 < got[3]  # r+4 < beta < r+5
                        elif c <= d:
                            assert got[1] < 0 < got[2]  # r+3 < beta < r+4
                        else:
                            assert got[0] < 0 < got[1]  # r+2 < beta < r+3
                    if c == 0: assert got[2] == -2
                    if c == 1: assert got[2] == 2*d
                    if c == d: assert got[1] == -2
                    if c == d+1: assert got[1] == 2*d-2
                else:
                    want = [
                        -2*((d+1)*c + d*d + 3*d + 1),
                        c*(c+3)-d*(d+3)+2,
                        2*(c*c+c*d+6*c+2*d+9),
                        3*c*c+4*c*d+25*c+d*d+15*d+52,
                    ]
                    if 0 <= c <= d-2:
                        assert got[1] < 0 < got[2]  # r+3 < beta < r+4
                    if c == d-1: assert got[1] == -2*d
                    if c == d: assert got[1] == 2
                assert got == want, (eps,d,c,got,want)
                assert got[0] < 0 < got[3]
                count += 1
    print("ROOT_WALL_EXACT_ORACLE_PASS",count)

if __name__ == "__main__":
    run()
