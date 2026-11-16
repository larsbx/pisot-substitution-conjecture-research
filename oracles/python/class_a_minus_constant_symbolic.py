"""Unbounded coefficient certificates for minus-Class-A constant descent.

Canonical computation is Mojo. This independent SymPy oracle verifies exact
full-Parikh identities and original occurrence inequalities on exhaustive
integer chambers. The density and recurrence identities support the written
proof; they do not assert that its entire geometry is formalized in Lean.
"""
from __future__ import annotations

from copy import deepcopy
import json
from sympy import Matrix, Poly, cancel, expand, fraction, symbols, sympify

u, v, s, z = symbols("u v s z")
N, D, H, B, h, delta, a, b, c = symbols("n d H beta h delta a b c")
FREE = (u, v, s)
ALL = FREE + (z, N, D, H, B, h, delta, a, b, c)


def zero(expression):
    numerator, _ = fraction(cancel(expression))
    if not Poly(expand(numerator), *ALL).is_zero:
        raise ValueError(f"nonzero coefficient identity: {expand(numerator)}")


def nonnegative(expression, variables=FREE):
    expression = expand(expression)
    if not expression.free_symbols <= set(variables):
        raise ValueError("guard contains an undeclared chamber variable")
    if any(coefficient < 0 for coefficient in Poly(expression, *variables).coeffs()):
        raise ValueError(f"coefficient guard is not proved: {expression}")
    return str(expression)


def positive(expression, variables=FREE):
    nonnegative(expression, variables)
    if Poly(expand(expression), *variables).TC() <= 0:
        raise ValueError("strict positivity fails on an allowed closed face")
    return str(expand(expression))


def matrix(n, d):
    return Matrix(((2, 1, 1), (0, 1, 1), (n+d, n, n-1)))


def reverse(label):
    return (label[1], label[0], *(-value for value in label[2:]))


def occurrence(parent, index, n, d):
    """Decode the original letter index without eliding FIRST or LAST."""
    if parent not in (0, 1, 2):
        raise ValueError("invalid original parent letter")
    index = sympify(index)
    run = (n+d, n, n-1)[parent]
    if expand(index) == 0:
        return (1 if parent == 1 else 0), (0, 0, 0), "FIRST"
    if expand(index-run-1) == 0:
        return (1 if parent == 2 else 0), (int(parent != 1), int(parent == 1), run), "LAST"
    nonnegative(index-1)
    nonnegative(run-index)
    return 2, (int(parent != 1), int(parent == 1), index-1), "RUN"


def cases():
    d = 5+u
    result = []
    # These disjoint chambers exhaust H>=1, d>=5, 2dH<=n.
    for height, name in ((sympify(1), "H1"), (2+v, "Hge2")):
        n = 2*d*height+s
        final = (1, 3) if name == "H1" else (d*(height-1)-1, 1)
        result.append(dict(name=name, n=n, d=d, H=height,
            source=(2, 2, height, -height, 0),
            addresses=[(d*height+2, 1), (1, n+2-d*height), final],
            expected=[(2, 2, height, -height, -1),
                      (2, 2, height-1, -height-1, 2),
                      (2, 2, height-1, -height+1, 0)]))
    return result


def certify_path(case, flip=False):
    n, d, height = case["n"], case["d"], case["H"]
    nonnegative(d-5)
    nonnegative(n-d-1)
    nonnegative(height-1)
    nonnegative(n-2*d*height)
    source = reverse(case["source"]) if flip else case["source"]
    addresses = [(j, i) for i, j in case["addresses"]] if flip else case["addresses"]
    expected = [reverse(w) for w in case["expected"]] if flip else case["expected"]
    if len(addresses) != 3 or len(expected) != 3:
        raise ValueError("height descent requires all three actual edges")
    M = matrix(n, d)
    w, P, Q, scaled = source, Matrix((0, 0, 0)), Matrix((0, 0, 0)), Matrix(source[2:])
    records = []
    for (i, j), wanted in zip(addresses, expected):
        top, pt, tk = occurrence(w[0], i, n, d)
        bottom, pb, bk = occurrence(w[1], j, n, d)
        if (top, bottom) != wanted[:2] or (tk, bk) != ("RUN", "RUN"):
            raise ValueError("descent digit is not the stated actual RUN occurrence")
        image = M*Matrix(w[2:])+Matrix(pb)-Matrix(pt)
        for actual, target in zip(image, wanted[2:]):
            zero(actual-target)
        P, Q, scaled = M*P+Matrix(pt), M*Q+Matrix(pb), M*scaled
        for actual, target in zip(scaled+Q-P, wanted[2:]):
            zero(actual-target)
        w = wanted
        records.append(dict(indices=[str(expand(i)), str(expand(j))],
                            target=[str(expand(value)) for value in w]))
    wanted_endpoint = (2, 2, height-1, -height+1, 0)
    if flip:
        wanted_endpoint = reverse(wanted_endpoint)
    for actual, target in zip(w, wanted_endpoint):
        zero(actual-target)
    return dict(chamber=case["name"], reversed=flip, edges=3, records=records,
                final_top_prefix=[str(expand(value)) for value in P],
                final_bottom_prefix=[str(expand(value)) for value in Q],
                full_original_prefix_identity=True)


def root_zero(expression):
    chi = B**3-(N+2)*B**2+(N-D-1)*B+2
    numerator, _ = fraction(cancel(expression))
    zero(Poly(numerator, B).rem(Poly(chi, B)).as_expr())


def certify_density_and_recurrence():
    chi = B**3-(N+2)*B**2+(N-D-1)*B+2
    zero(chi.subs(B, N+1)+((N+1)*(D+2)-2))
    zero(chi.subs(B, N+2)-((N-D-1)*(N+2)+2))
    for root, value in ((1, -D), (-1, D-2*N),
                        (2, -2*N-2*D), (-2, 2*D-6*N-12)):
        zero(chi.subs(B, root)-value)
    lengths = (B-N-1/B, 1+1/B, sympify(1))
    M = matrix(N, D)
    for parent in range(3):
        root_zero(B*lengths[parent]-sum(M[letter, parent]*lengths[letter]
                                       for letter in range(3)))
    root_zero(lengths[0]-(1+1/B+D/(B-1)))
    root_zero(2/B-(B-N-2)-(1-D/(B-1)))
    # The central full packet determines its next first two coordinates.
    packet = Matrix((b, b-2*a, c-3*b+2*a))
    zero((M*packet)[0]-c)
    zero((M*packet)[1]-(c-2*b))
    root_zero(sum(packet[i]*lengths[i] for i in range(3))
              -(c+(B-N-2)*b-2*a/B))
    # Exact literal density margins; the written argument supplies each sign.
    margins = []
    for parent in range(3):
        nx, nc, ny = M[:, parent]
        margins.append((ny-(N-1)*lengths[parent],
                        2*lengths[parent]-nx*lengths[0], lengths[parent]-nc))
    root_zero(margins[0][0]-(B-N-1)*lengths[0])
    zero(margins[1][0]-(1-(N-1)/B))
    zero(margins[2][0])
    zero(margins[0][1])
    zero(margins[1][1]-(2+2/B-lengths[0]))
    zero(margins[2][1]-(2-lengths[0]))
    zero(margins[0][2]-lengths[0])
    zero(margins[1][2]-1/B)
    zero(margins[2][2])
    # Exhaustive parameter quadrant: d=5+u, n=d+1+v.
    n, d = 6+u+v, 5+u
    root_guards = {
        "negative_at_n_plus_1": positive(((N+1)*(D+2)-2).subs({N: n, D: d})),
        "positive_at_n_plus_2": positive(((N-D-1)*(N+2)+2).subs({N: n, D: d})),
        "n_at_least_six": nonnegative(n-6),
        "word_length_at_most_2n_plus_1": nonnegative(2*n+1-(n+d+2)),
    }
    lower_gap = (N*N-N-22)/((N+6)*(N+2))
    zero((lower_gap-sympify(1)/12)*12*(N+6)*(N+2)-(N-6)*(11*N+46))
    gap_guards = {
        "positive_lower_numerator": positive((N*N-N-22).subs(N, n)),
        "gap_at_least_one_twelfth": nonnegative(((N-6)*(11*N+46)).subs(N, n)),
        "positive_denominator": positive(((N+6)*(N+2)).subs(N, n)),
    }
    zero(4*(N+2)+8*(2*N+1)+4-20*(N+1))
    # Intermediate physical displacements, with normalized lengths.
    formal_lengths = (1+h+delta, 1+h, sympify(1))
    for offset, shift in (((H, -H, 0), delta*H),
                          ((H, -H, -1), delta*H-1),
                          ((H-1, -H-1, 2), delta*(H-1)-2*h)):
        zero(sum(offset[i]*formal_lengths[i] for i in range(3))-shift)
    return dict(parameter_chamber="d=5+u, n=6+u+v; u,v>=0",
                root_guards=root_guards, density_gap_guards=gap_guards,
                literal_density_margins=[[str(cancel(e)) for e in row] for row in margins],
                density_gap="eta>=(1/12), in fact eta>1/12",
                sufficient_actual_entry="beta^m*ell0>=240*(n+1), m>=1",
                strictness_hypotheses=["0<h<1/7", "0<delta", "delta*H<1/2"],
                constant_central_interval="2*d*abs(H)<=n",
                recurrence="c=nearest(2*a/beta-(beta-n-2)*b)")


def reject(action):
    try:
        action()
    except ValueError:
        return True
    raise AssertionError("a deliberately corrupted symbolic assertion was accepted")


def certify():
    rows = [certify_path(case, flip) for case in cases() for flip in (False, True)]
    bad = deepcopy(cases()[0])
    bad["addresses"][0] = (bad["addresses"][0][0]+1, 1)
    wrong_branch = deepcopy(cases()[0])
    wrong_branch["addresses"][2] = (-1, 1)
    forged_zero = deepcopy(cases()[1])
    forged_zero["expected"][-1] = (2, 2, 0, 0, 0)
    missing = deepcopy(cases()[0])
    missing["addresses"].pop()
    controls = {
        "legal_but_wrong_ordinal": reject(lambda: certify_path(bad)),
        "H1_requires_negative_gap_branch": reject(lambda: certify_path(wrong_branch)),
        "nonzero_endpoint_is_not_zero": reject(lambda: certify_path(forged_zero)),
        "missing_required_edge": reject(lambda: certify_path(missing)),
        "wrong_recurrence_sign": reject(lambda: root_zero(2/B+(B-N-2)-(1-D/(B-1)))),
        "closed_face_is_not_strict": reject(lambda: positive(u)),
        "negative_guard": reject(lambda: nonnegative(u-1)),
        "foreign_variable": reject(lambda: nonnegative(H)),
    }
    return dict(scope="unbounded symbolic full-Parikh and original-RUN proof support",
                parameter_chambers=2, directed_paths=4, checked_edges=12,
                literal_RUN_occurrences=24, all_height_decrement=True,
                paths=rows, geometry=certify_density_and_recurrence(),
                negative_controls=controls)


if __name__ == "__main__":
    print(json.dumps(certify(), sort_keys=True, indent=2))
