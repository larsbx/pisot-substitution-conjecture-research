"""Universal polynomial certificates for the Class-A central cycle exits.

The canonical executable is kernel/psc/class_a_central_entry.mojo. This
independent oracle checks every coefficient of full Parikh transport and
every original occurrence bound over exhaustive, unbounded integer chambers.
It does not infer a theorem from sampled parameters. The general KH>=4 path
ends at the exact reversed Q_H packet of the existing unit-descent theorem;
that theorem, rather than a new unrolled loop, supplies the remaining tail.

The density certificate checks literal depth-two counts, exact root-field
identities, and positivity over a larger domain containing the inherited
Perron hypotheses n>=6, 0<h<1/8, rho>h. It is a symbolic proof-support oracle,
not a claim that the entire central-entry theorem is formalized in Lean.
"""
from __future__ import annotations

from copy import deepcopy
import json

from sympy import Matrix, Poly, cancel, expand, fraction, symbols, sympify

u, v, s, z, w = symbols("u v s z w")
B, N, K, H, h, rho = symbols("beta n K H h rho")
FREE = (u, v, s)
ALL = FREE + (z, w, B, N, K, H, h, rho)


def zero(expression):
    if not Poly(expand(expression), *ALL).is_zero:
        raise ValueError(f"nonzero full coefficient identity: {expand(expression)}")


def nonnegative(expression, variables=FREE):
    expression = expand(expression)
    if not expression.free_symbols <= set(variables):
        raise ValueError("guard has a variable outside its declared integer chamber")
    if any(coefficient < 0 for coefficient in Poly(expression, *variables).coeffs()):
        raise ValueError(f"unproved coefficientwise guard: {expression}")


def reverse(label):
    return (label[1], label[0], *(-coordinate for coordinate in label[2:]))


def occurrence(parent, index, n, A):
    """Literal FIRST/RUN/LAST decoding with proved ordinal inequalities."""
    if parent not in (0, 1, 2):
        raise ValueError("parent letter outside the literal three-letter alphabet")
    index = sympify(index)
    run = (A, n, n-1)[parent]
    if expand(index) == 0:
        return (1 if parent == 1 else 0), (0, 0, 0), "FIRST"
    if expand(index-run-1) == 0:
        return (1 if parent == 2 else 0), (int(parent != 1), int(parent == 1), run), "LAST"
    nonnegative(index-1)
    nonnegative(run-index)
    return 2, (int(parent != 1), int(parent == 1), index-1), "RUN"


def matrix(n, K):
    A = 3*n-K
    return Matrix(((2, 1, 1), (0, 1, 1), (A, n, n-1)))


def certify_path(n, K, source, addresses, expected, *, require_zero):
    """Check each actual typed successor and the composed prefix identity."""
    if len(addresses) != len(expected):
        raise ValueError("one expected full packet is required for every actual edge")
    nonnegative(n-6)
    nonnegative(K-1)
    nonnegative(n-K-2)  # t>=0, k=K-1>=0.
    A, M = 3*n-K, matrix(n, K)
    current = tuple(source)
    P, Q, scaled = Matrix((0, 0, 0)), Matrix((0, 0, 0)), Matrix(source[2:])
    kinds = {"FIRST": 0, "RUN": 0, "LAST": 0}
    records = []
    for (i, j), wanted in zip(addresses, expected):
        top, pt, tk = occurrence(current[0], i, n, A)
        bottom, pb, bk = occurrence(current[1], j, n, A)
        if (top, bottom) != tuple(wanted[:2]):
            raise ValueError("actual FIRST/RUN/LAST child letters disagree")
        image = M*Matrix(current[2:]) + Matrix(pb) - Matrix(pt)
        for actual, target in zip(image, wanted[2:]):
            zero(actual-target)
        P, Q, scaled = M*P + Matrix(pt), M*Q + Matrix(pb), M*scaled
        for actual, target in zip(scaled+Q-P, wanted[2:]):
            zero(actual-target)
        current = tuple(wanted)
        kinds[tk] += 1
        kinds[bk] += 1
        records.append(dict(indices=[str(expand(i)), str(expand(j))],
                            kinds=[tk, bk],
                            target=[str(expand(a)) for a in current]))
    if require_zero:
        for coordinate in current[2:]:
            zero(coordinate)
        for coordinate in scaled-P+Q:
            zero(coordinate)
    return dict(edges=len(addresses), occurrence_kinds=kinds, records=records,
                final_top_prefix=[str(expand(a)) for a in P],
                final_bottom_prefix=[str(expand(a)) for a in Q],
                full_original_prefix_identity=True)


def small_cases():
    """Six chambers partition all five positive factorizations KH<=3."""
    cases = []
    for height in (1, 2):
        n = 6+s
        cases.append(dict(name=f"K1_H{height}", K=1, H=height, n=n,
            source=(2, 2, height, 3*height, -6*height),
            addresses=[(0, 0), (1, 1+(n+2)*height), (2*height+1, 1)],
            expected=[(0, 0, -height, -3*height, 5*height),
                      (2, 2, 0, 2*height, -2*height), (2, 2, 0, 0, 0)]))
    n = 6+s
    cases.append(dict(name="K2_H1", K=2, H=1, n=n,
        source=(2, 2, 1, 3, -6), addresses=[(0, 0), (0, 2*n+2), (2, 1)],
        expected=[(0, 0, -1, -3, 4), (0, 2, 0, 1, -1), (2, 2, 0, 0, 0)]))
    cases.append(dict(name="K3_H1", K=3, H=1, n=n,
        source=(2, 2, 1, 3, -6), addresses=[(0, 1), (1, 4)],
        expected=[(0, 2, 0, -3, 3), (2, 2, 0, 0, 0)]))
    for n, bottom, name in ((sympify(6), 0, "K1_H3_n6_LAST"),
                             (7+s, 2, "K1_H3_nge7_RUN")):
        cases.append(dict(name=name, K=1, H=3, n=n,
            source=(2, 2, 3, 9, -18),
            addresses=[(0, 1), (0, 1), (2*n, 0), (1, 2*n+6), (5, 1)],
            expected=[(0, 2, -2, -9, 15), (0, 2, 3, 6, -13),
                      (2, 0, -2, -7, 11), (2, bottom, 0, 4, -4),
                      (2, 2, 0, 0, 0)]))
    return cases


def general_cases():
    """Disjoint integer chambers exhaust KH>=4, KH<=n-2."""
    cases = []
    for factor, height, name in ((1, 4+u, "K1_Hge4"),
                                 (2, 2+u, "K2_Hge2"),
                                 (3, 2+u, "K3_Hge2"),
                                 (4+u, 1+v, "Kge4_Hge1")):
        kh, n = factor*height, factor*height+2+s
        nonnegative(kh-4)
        nonnegative(n-2-kh)
        nonnegative(n+3-kh)  # The reused unit-descent theorem's domain.
        cases.append(dict(name=name, K=factor, H=height, n=n,
            source=(2, 2, height, 3*height, -6*height),
            addresses=[(1, kh), (0, n+3-kh)],
            expected=[(2, 2, -height, -3*height, 6*height-1),
                      (0, 2, height, 3*height-1, 3-6*height)]))
    return cases


def certify_splice(case):
    """The general endpoint is R(Q_H), reached by the old first digit too."""
    n, K, height = case["n"], case["K"], case["H"]
    source = (2, 0, -height, -3*height-1, 6*height)  # R(P_H)
    expected = (0, 2, height, 3*height-1, 3-6*height)  # R(Q_H)
    if case["expected"][-1][:2] != expected[:2]:
        raise ValueError("suffix splice changed an actual source letter")
    for a, b in zip(case["expected"][-1][2:], expected[2:]):
        zero(a-b)
    # The first reversed P_H digit lands at precisely the packet at which
    # the imported Q_H suffix begins. Its original occurrence is retained.
    return certify_path(n, K, source, [(0, n+4-K*height)], [expected],
                        require_zero=False)


def root_zero(expression):
    """Exact identity in Q(n,K)[beta] modulo the inherited literal cubic."""
    chi = B**3-(N+2)*B**2-(N-K+1)*B+2
    numerator, _ = fraction(cancel(expression))
    remainder = Poly(numerator, B).rem(Poly(chi, B)).as_expr()
    zero(remainder)


def positive_rational(expression, nonnegative_variables=FREE,
                      positive_variables=(z, w)):
    """Coefficient certificate on the stated partially open orthant.

    A positive monomial must survive when every merely nonnegative variable
    is zero. This avoids incorrectly treating u>0 when the chamber allows u=0.
    """
    variables = tuple(nonnegative_variables) + tuple(positive_variables)
    numerator, denominator = map(expand, fraction(cancel(expression)))
    nonnegative(numerator, variables)
    nonnegative(denominator, variables)
    denominator_poly = Poly(denominator, *variables)
    if denominator_poly.TC() <= 0:
        raise ValueError("denominator has no strictly positive constant bound")
    numerator_poly = Poly(numerator, *variables)
    open_index = len(nonnegative_variables)
    if not any(coefficient > 0 and all(e == 0 for e in powers[:open_index])
               for powers, coefficient in numerator_poly.terms()):
        raise ValueError("strict positivity disappears on an allowed closed face")
    return dict(numerator=str(numerator), denominator=str(denominator),
                coefficient_terms=len(numerator_poly.terms()))


def certify_density():
    """Literal M² counts and all three strengthened block-density margins."""
    A, M = 3*N-K, matrix(N, K)
    # Columns are obtained by substituting each actual first-level letter.
    counts = Matrix(((A+4, N+3, N+2),
                     (A, N+1, N),
                     (A*(N+1), A+N**2, A+N**2-N+1)))
    for coefficient in M*M-counts:
        zero(coefficient)

    lengths = (B-N-1/B, 1+1/B, sympify(1))
    h_exact, rho_exact = 1/B, B-(N+2)-1/B
    # Full ordered words supply the same incidence and exact scaling.
    for a in range(3):
        root_zero(B*lengths[a]-sum(M[b, a]*lengths[b] for b in range(3)))
    root_zero(1-rho_exact-3*h_exact-K/(B+1))

    for a in range(3):
        nx, nc, ny = M[:, a]
        gap = nx*lengths[0]-lengths[a]
        x_margin = nx*rho_exact+nc*h_exact
        c_margin = gap+nc*h_exact
        y_margin = (B-7)*gap+nc*(N-5*lengths[1])+ny*(N-6)
        root_zero(B*lengths[a]-counts[0, a]-x_margin)
        root_zero((B-1)*lengths[a]-counts[1, a]-c_margin)
        root_zero(counts[2, a]-(6*B-7)*lengths[a]-y_margin)

    # These four chambers exhaust k,t>=0 with n=k+t+3>=6.
    chambers = ((1, 6+s, "K1"), (2, 6+s, "K2"),
                (3, 6+s, "K3"), (4+u, 6+u+v, "Kge4"))
    positive = []
    hh = z/(8*(1+z))  # Exactly 0<h<1/8 for z>0.
    rr = hh+w         # rho>h for w>0; upper bounds are not needed here.
    for factor, n, name in chambers:
        nonnegative(n-6)
        nonnegative(n-factor-2)
        AA = 3*n-factor
        symbolic_lengths = (2+rr, 1+hh, sympify(1))
        beta = n+2+rr+hh
        columns = ((2, 0, AA), (1, 1, n), (1, 1, n-1))
        for a, (nx, nc, ny) in enumerate(columns):
            gap = nx*symbolic_lengths[0]-symbolic_lengths[a]
            expressions = {
                "x": nx*rr+nc*hh,
                "c": gap+nc*hh,
                "y": (beta-7)*gap+nc*(n-5*symbolic_lengths[1])+ny*(n-6),
            }
            positive.append(dict(chamber=name, parent=a,
                parameters=dict(K=str(factor), n=str(n)),
                margins={key: positive_rational(value)
                         for key, value in expressions.items()}))
    Y0, X0, C0 = (6*B-7)/B**2, 1/B, (B-1)/B**2
    zero(cancel(B**2*(Y0-3*X0-2*C0)-(B-5)))
    return dict(literal_two_level_count_entries=9,
                root_field_margin_identities=9,
                exact_scaling_identities=3,
                parameter_chambers=4,
                strict_density_margin_certificates=36,
                inherited_hypotheses=["n>=6", "0<h<1/8", "rho>h",
                    "n+2<beta<n+3", "the literal incidence cubic"],
                density_gap="Y0-3*X0-2*C0=(beta-5)/beta^2>0",
                positive_certificates=positive)


def _reject(action):
    try:
        action()
    except ValueError:
        return True
    raise AssertionError("an intentionally corrupted symbolic assertion was accepted")


def certify():
    cases = small_cases() + general_cases()
    rows, counts, edges = [], {"FIRST": 0, "RUN": 0, "LAST": 0}, 0
    for case in cases:
        for flip in (False, True):
            source = reverse(case["source"]) if flip else case["source"]
            addresses = ([(j, i) for i, j in case["addresses"]]
                         if flip else case["addresses"])
            expected = ([reverse(a) for a in case["expected"]]
                        if flip else case["expected"])
            result = certify_path(case["n"], case["K"], source, addresses, expected,
                                  require_zero=case in cases[:6])
            result.update(name=case["name"], reversed=flip,
                parameters={key: str(case[key]) for key in ("K", "H", "n")})
            for name, count in result["occurrence_kinds"].items():
                counts[name] += count
            edges += result["edges"]
            rows.append(result)
    splices = [certify_splice(case) for case in general_cases()]
    density = certify_density()

    # Mutations remain literal, inspectable failed stronger variants.
    bad_index = deepcopy(small_cases()[0])
    i, j = bad_index["addresses"][1]
    bad_index["addresses"][1] = (i, j+1)  # Still legal, wrong full offset.
    last_as_run = deepcopy(small_cases()[4])
    last_as_run["expected"][3] = (2, 2, 0, 4, -4)
    controls = {
        "legal_but_wrong_ordinal": _reject(lambda: certify_path(
            bad_index["n"], bad_index["K"], bad_index["source"],
            bad_index["addresses"], bad_index["expected"], require_zero=True)),
        "LAST_relabelled_RUN": _reject(lambda: certify_path(
            last_as_run["n"], last_as_run["K"], last_as_run["source"],
            last_as_run["addresses"], last_as_run["expected"], require_zero=True)),
        "nonexistent_original_ordinal": _reject(lambda: occurrence(2, 7+s, 6+s, 17+3*s)),
        "finite_fit_is_not_identity": _reject(lambda: zero(u*(u-1))),
        "negative_guard_coefficient": _reject(lambda: nonnegative(1-u)),
        "closed_face_is_not_positive": _reject(lambda: positive_rational(u)),
        "changed_density_count": _reject(lambda: root_zero(B*lengths_x()-
            ((3*N-K)+4)-2*(B-(N+2)-1/B)+1)),
    }
    return dict(coefficient_ring="Z[u,v,s]; chamber variables are nonnegative integers",
                small_KH_chambers=6, general_KH_chambers=4,
                directed_paths_including_reversal=len(rows),
                checked_directed_edges=edges, occurrence_kinds=counts,
                small_cycle_zero_length_bound=5,
                exact_reversed_QH_splices=len(splices),
                reused_tail="existing unit_descent_path theorem, first reversed edge omitted",
                density=density, controls=controls, paths=rows,
                splices=splices, whole_theorem_formalized_in_Lean=False)


def lengths_x():
    return B-N-1/B


if __name__ == "__main__":
    print(json.dumps(certify(), indent=2, sort_keys=True))
