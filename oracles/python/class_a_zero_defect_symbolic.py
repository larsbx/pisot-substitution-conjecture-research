"""Coefficientwise address/guard certificates for the entire local theorem.

Every chamber is parameterized by independent nonnegative integers. A RUN
guard is accepted only when both ordinal slacks have nonnegative polynomial
coefficients. FIRST and LAST require polynomial equality. Hence this does
not interpolate a table from sampled substitutions. The chamber selector
chooses formulas only; all legality and endpoint claims are proved over the
whole symbolic chamber. Geometry then follows by backward containment.
"""
from pathlib import Path
import runpy

from sympy import Poly, expand, symbols, sympify

ORACLE = runpy.run_path(str(Path(__file__).with_name("class_a_zero_defect_escape.py")))
formula = ORACLE["address_formula"]
endpoint_source = ORACLE["endpoint_source"]
u, v, s = symbols("u v s")
VARIABLES = (u, v, s)


def zero(expr):
    if not Poly(expand(expr), *VARIABLES).is_zero:
        raise ValueError(f"nonzero coefficient identity: {expand(expr)}")


def nonnegative(expr):
    if any(coefficient < 0 for coefficient in Poly(expand(expr), *VARIABLES).coeffs()):
        raise ValueError(f"unproved integer guard: {expand(expr)}")


def occurrence(parent, index, n, A):
    index = sympify(index)
    run = (A, n, n-1)[parent]
    if expand(index) == 0:
        return (1 if parent == 1 else 0), (0, 0, 0), "FIRST"
    if expand(index-run-1) == 0:
        return (1 if parent == 2 else 0), (int(parent != 1), int(parent == 1), run), "LAST"
    nonnegative(index-1)
    nonnegative(run-index)
    return 2, (int(parent != 1), int(parent == 1), index-1), "RUN"


def walk(k, t, source, addresses):
    n, d = k+t+3, k+2*t+5
    A, w = n+d, source
    kinds = {"FIRST": 0, "RUN": 0, "LAST": 0}
    for i, j in addresses:
        a, pa, ka = occurrence(w[0], i, n, A)
        b, pb, kb = occurrence(w[1], j, n, A)
        kinds[ka] += 1
        kinds[kb] += 1
        p, q, r = w[2:]
        image = (2*p+q+r, q+r, A*p+n*q+(n-1)*r)
        w = (a, b, *(expand(image[z]+pb[z]-pa[z]) for z in range(3)))
    for coordinate in w[2:]:
        zero(coordinate)
    return kinds


def certify():
    # These16 disjoint rectangular chambers partition all k,t>=0.
    intervals = ((0, 0), (1, 1), (2, 2), (u+3, 3))
    ordinary = [(a, b, j) for a, b, limit in ((0, 0, 4), (0, 1, 3),
                 (1, 0, 3), (1, 1, 2)) for j in range(1, limit+1)]
    cases = []
    for k, sk in intervals:
        for t0, st in intervals:
            t = sympify(t0).subs(u, v)
            for a, b, j in ordinary:
                cases.append((k, t, sk, st, a, b, j))
    # Complete, disjoint strict domain for the thirteenth endpoint.
    fifth = ((2, 4, 2, 4), (3, 5, 3, 5), (u+4, u+6, 4, 6),
             (u, u+3, 0, 3), (u, u+4, 0, 4),
             (u+1, u+v+6, 1, 6), (0, v+5, 0, 5))
    cases.extend((k, t, sk, st, 0, 0, 5) for k, t, sk, st in fifth)
    counts = {"FIRST": 0, "RUN": 0, "LAST": 0}
    edges = max_length = 0
    for k, t, sk, st, a, b, j in cases:
        addresses = formula(k, t, a, b, j, sk, st)
        source = endpoint_source(a, b, j)
        try:
            kinds = walk(k, t, source, addresses)
            flipped = (b, a, *(-z for z in source[2:]))
            reverse_kinds = walk(k, t, flipped, [(y, x) for x, y in addresses])
        except ValueError as error:
            raise ValueError(f"chamber k={k},t={t},endpoint={a,b,j}: {error}") from error
        for name in counts:
            counts[name] += kinds[name] + reverse_kinds[name]
        edges += 2*len(addresses)
        max_length = max(max_length, len(addresses))
    assert max_length == 9

    # Full affine source reduction, for every oriented source pair.
    n, d = u+v+3, u+2*v+5
    A = n+d
    for a in range(3):
        for b in range(3):
            delta = int(a != 1) - int(b != 1)
            run = (A, n, n-1)[a]
            m = run+s
            p, q, r = delta, m-(d+1)*delta, -m+d*delta
            image = (2*p+q+r, q+r, A*p+n*q+(n-1)*r)
            for got, wanted in zip(image, (delta, -delta, m)):
                zero(got-wanted)
            last, prefix, _ = occurrence(a, run+1, n, A)
            first, _, _ = occurrence(b, 0, n, A)
            target = (-int(first == 0), -int(first == 1), s)
            for got, subtrahend, wanted in zip(image, prefix, target):
                zero(got-subtrahend-wanted)
            assert last in (0, 1) and first in (0, 1)

    # Counter-calibration: an incorrect literal ordinal cannot be accepted
    # by the zero-endpoint coefficient check merely because it is legal.
    refused = False
    try:
        walk(u, v, endpoint_source(0, 0, 1), [(0, u+2*v+7), (2, 1)])
    except ValueError:
        refused = True
    assert refused
    return {"coefficient_ring": "Z[u,v,s], u,v nonnegative integers",
            "ordinary_parameter_chambers": 16,
            "strict_fifth_endpoint_chambers": len(fifth),
            "endpoint_chamber_paths": len(cases),
            "directed_paths_including_reversal": 2*len(cases),
            "checked_directed_edges": edges,
            "occurrence_kinds": counts,
            "source_reduction_orientations": 9,
            "endpoint_length_bound": max_length,
            "strict_zero_defect_length_bound": max_length+1,
            "wrong_ordinal_control_rejected": refused,
            "universal_seed_entry": False}


if __name__ == "__main__":
    import json
    print(json.dumps(certify(), indent=2, sort_keys=True))
