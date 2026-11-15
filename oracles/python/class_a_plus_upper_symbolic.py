"""Independent all-n occurrence/prefix support for the eight upper cycles.

Canonical path construction lives in kernel/psc/class_a_plus_upper_cycles.mojo.
This checker does not import that implementation or its Python path constructor.
It spells out the eight complete positive transcripts, counts the literal
FIRST/RUN/LAST word schematic, and replays in Z[n].  Each range inequality is
certified by nonnegative coefficients after n=7+t, t>=0.  No finite sample is
used to discharge the unbounded n quantifier.

Scope: actual typed occurrences, full integral transport, composability,
proper original prefixes, and M^m*w=P-Q at typed zero.  Strict overlap follows
backwards from positive tile lengths and exact inflation scaling; that
geometric lemma and its literal-field specialization are separate proof
obligations, and are not declared proved by this polynomial checker.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import json
from pathlib import Path

from sympy import Float, Matrix, Poly, Rational, expand, symbols, sympify
from sympy.polys.polyerrors import CoercionFailed, PolynomialError

N, T = symbols("n t")
CASES = ((1, 1), (1, 2), (1, 3), (1, 4),
         (2, 1), (2, 2), (3, 1), (4, 1))
ZERO = (2, 2, 0, 0, 0)


def polynomial(expression):
    """An exact integer polynomial on the declared n=7+t chamber."""
    expression = sympify(expression)
    if expression.atoms(Float):
        raise ValueError("floating input is not an exact integer polynomial")
    if not expression.free_symbols <= {N, T}:
        raise ValueError("undeclared symbolic parameter")
    try:
        return Poly(expand(expression.subs(N, 7+T)), T, domain="ZZ")
    except (CoercionFailed, PolynomialError) as exc:
        raise ValueError("expression is not an exact integer polynomial") from exc


def zero(expression):
    if not polynomial(expression).is_zero:
        raise ValueError("full integer-polynomial identity is false: " + str(expand(expression)))


def nonnegative(expression):
    """Sufficient, auditable proof on every integer t>=0, not a sign sample."""
    p = polynomial(expression)
    coefficients = list(reversed(p.all_coeffs()))
    if any(c < 0 for c in coefficients):
        raise ValueError("coefficientwise nonnegative guard is not proved: " + str(p.as_expr()))
    return dict(expression=str(expand(expression)), chamber=str(p.as_expr()),
                coefficients_low_to_high=[int(c) for c in coefficients])


def positive_integer(expression):
    return nonnegative(expression-1)


def _label(top, bottom, p, q, r):
    return top, bottom, p, q, r


def _step(i, j, target):
    return dict(indices=(i, j), target=target)


def cases():
    """Complete independent table; no call to the recursive native recipe."""
    w2, w3 = _label(2, 2, 2, 6, -12), _label(2, 2, 3, 9, -18)
    base11 = [_step(0, 0, _label(0, 0, -1, -3, 5)),
              _step(1, N+5, _label(2, 2, 0, 2, -2)), _step(1, 3, ZERO)]
    base12 = [_step(0, 0, _label(0, 0, -2, -6, 10)),
              _step(1, 2*N+9, _label(2, 2, 0, 4, -4)), _step(1, 5, ZERO)]
    base21 = [_step(0, 0, _label(0, 0, -1, -3, 4)),
              _step(0, 2*N+6, _label(0, 2, 0, 1, -1)), _step(1, 2, ZERO)]
    decrement13 = [_step(0, 1, _label(0, 2, -2, -9, 15)), _step(6, 1, w2)]
    rows = [
        (1, 1, base11),
        (1, 2, base12),
        (1, 3, decrement13 + base12),
        (1, 4, [_step(0, 2, _label(0, 2, -3, -12, 21)), _step(7, 1, w3)]
               + decrement13 + base12),
        (2, 1, base21),
        (2, 2, [_step(0, 2, _label(0, 2, -1, -6, 9)),
                _step(6, 1, _label(2, 2, 1, 3, -6))] + base21),
        (3, 1, [_step(0, 1, _label(0, 2, 0, -3, 3)), _step(4, 1, ZERO)]),
        (4, 1, [_step(0, 2, _label(0, 2, 0, -3, 3)), _step(4, 1, ZERO)]),
    ]
    return [dict(J=J, H=H, reversed=False, source=(2, 2, H, 3*H, -6*H),
                 steps=deepcopy(steps)) for J, H, steps in rows]


def reverse_label(label):
    return label[1], label[0], *(-x for x in label[2:])


def reverse_case(case):
    result = deepcopy(case)
    result["reversed"] = not result["reversed"]
    result["source"] = reverse_label(result["source"])
    result["steps"] = [dict(indices=(step["indices"][1], step["indices"][0]),
                            target=reverse_label(step["target"]))
                       for step in result["steps"]]
    return result


def word_schematics(J):
    if type(J) is not int or not 1 <= J <= 4:
        raise ValueError("outside eight-case upper parameter domain")
    d = 2*N+12-J
    # (literal first letter, number of consecutive y letters, literal last).
    return ((0, N+d, 0), (1, N, 0), (0, N+1, 1))


def incidence(J):
    columns = []
    for first, run, last in word_schematics(J):
        positive_integer(run)
        columns.append(Matrix(tuple(int(first == a)+int(last == a)
                                    + (run if a == 2 else 0) for a in range(3))))
    return Matrix.hstack(*columns)


def occurrence(J, parent, index):
    """Decode one literal ordinal and certify its entire all-n range."""
    if type(parent) is not int or parent not in range(3):
        raise ValueError("parent is outside the literal alphabet")
    polynomial(index)
    index = sympify(index)
    first, run, last = word_schematics(J)[parent]
    guards = [nonnegative(index), nonnegative(run+1-index)]
    if polynomial(index).is_zero:
        child, prefix, tag = first, Matrix((0, 0, 0)), "FIRST"
    elif polynomial(index-run-1).is_zero:
        child, tag = last, "LAST"
        prefix = Matrix(tuple(int(first == a)+(run if a == 2 else 0) for a in range(3)))
    else:
        guards += [nonnegative(index-1), nonnegative(run-index)]
        child, tag = 2, "RUN"
        prefix = Matrix(tuple(int(first == a)+(index-1 if a == 2 else 0)
                              for a in range(3)))
    zero(sum(prefix)-index)
    return child, prefix, dict(parent=parent, index=str(expand(index)), kind=tag,
                              child=child, prefix=[str(expand(x)) for x in prefix],
                              range_guards=guards)


def _check_label(label):
    if len(label) != 5 or any(type(x) is not int or x not in range(3) for x in label[:2]):
        raise ValueError("malformed complete typed label")
    for x in label[2:]:
        polynomial(x)


def _encoded_label(label):
    return list(label[:2]) + [str(expand(x)) for x in label[2:]]


def certify_path(case):
    J, H, flip = case["J"], case["H"], case["reversed"]
    if type(J) is not int or type(H) is not int or (J, H) not in CASES or type(flip) is not bool:
        raise ValueError("outside exactly eight directed upper cases")
    source = case["source"]
    wanted_source = (2, 2, H, 3*H, -6*H)
    if flip:
        wanted_source = reverse_label(wanted_source)
    _check_label(source)
    if tuple(source[:2]) != wanted_source[:2]:
        raise ValueError("wrong typed upper-cycle source")
    for actual, wanted in zip(source[2:], wanted_source[2:]):
        zero(actual-wanted)
    d = 2*N+12-J
    parameter_guards = [nonnegative(N-7), nonnegative(d-N-5),
                        nonnegative(2*N+11-d)]
    M = incidence(J)
    P, Q = Matrix.zeros(3, 1), Matrix.zeros(3, 1)
    scaled = Matrix(source[2:])
    top_total = Matrix(tuple(int(a == source[0]) for a in range(3)))
    bottom_total = Matrix(tuple(int(a == source[1]) for a in range(3)))
    w, records = source, []
    for step in case["steps"]:
        if all(polynomial(x).is_zero for x in w[2:]):
            raise ValueError("symbolic transcript continues after integral zero")
        if len(step["indices"]) != 2:
            raise ValueError("an ordered occurrence requires both original indices")
        i, j = step["indices"]
        child_top, pt, top_record = occurrence(J, w[0], i)
        child_bottom, pb, bottom_record = occurrence(J, w[1], j)
        wanted = step["target"]
        _check_label(wanted)
        if (child_top, child_bottom) != tuple(wanted[:2]):
            raise ValueError("claimed target type differs from literal occurrence")
        image = M*Matrix(w[2:])+pb-pt
        for actual, target in zip(image, wanted[2:]):
            zero(actual-target)
        P, Q, scaled = M*P+pt, M*Q+pb, M*scaled
        top_total, bottom_total = M*top_total, M*bottom_total
        # The same original tracks, not merely newly chosen endpoint marks.
        for actual, target in zip(scaled+Q-P, wanted[2:]):
            zero(actual-target)
        proper_guards = [nonnegative(x) for x in list(P)+list(Q)]
        proper_guards += [positive_integer(sum(top_total)-sum(P)),
                          positive_integer(sum(bottom_total)-sum(Q))]
        records.append(dict(source=_encoded_label(w), target=_encoded_label(wanted),
                            top_occurrence=top_record, bottom_occurrence=bottom_record,
                            top_original_prefix=[str(expand(x)) for x in P],
                            bottom_original_prefix=[str(expand(x)) for x in Q],
                            proper_prefix_guards=proper_guards))
        w = wanted
    if not records or tuple(w[:2]) != (2, 2) or not all(polynomial(x).is_zero for x in w[2:]):
        raise ValueError("symbolic transcript lacks complete typed y/y zero")
    for actual, wanted in zip(scaled, P-Q):
        zero(actual-wanted)
    return dict(J=J, H=H, reversed=flip, depth=len(records),
                source=_encoded_label(source), parameter_guards=parameter_guards,
                records=records, terminal=_encoded_label(w),
                final_top_prefix=[str(expand(x)) for x in P],
                final_bottom_prefix=[str(expand(x)) for x in Q],
                scaled_original_source=[str(expand(x)) for x in scaled],
                original_prefix_identity="M^m*w_original=P-Q",
                full_original_prefix_identity=True)


def _reject(action):
    try:
        action()
    except ValueError:
        return True
    raise AssertionError("a corrupted symbolic occurrence certificate was accepted")


def negative_controls():
    baseline = cases()
    legal_wrong = deepcopy(baseline[6])
    legal_wrong["steps"][0]["indices"] = (0, 2)
    wrong_type = deepcopy(baseline[4])
    wrong_type["steps"][1]["target"] = (2, 2, 0, 1, -1)
    wrong_vector = deepcopy(baseline[0])
    wrong_vector["steps"][0]["target"] = (0, 0, -1, -3, 4)
    missing = deepcopy(baseline[0])
    missing["steps"].pop()
    continued = deepcopy(baseline[0])
    continued["steps"].append(_step(1, 1, ZERO))
    negative_index = deepcopy(baseline[6])
    negative_index["steps"][0]["indices"] = (-1, 1)
    overrun = deepcopy(baseline[6])
    overrun["steps"][0]["indices"] = (0, N+3)
    old_formula = deepcopy(baseline[7])
    old_formula["steps"] = [_step(1, 4, (2, 2, -1, -3, 5)),
                             _step(1, N+2, (2, 2, 0, 2, -2)),
                             _step(1, 3, ZERO)]
    reversed_without_tracks = reverse_case(baseline[4])
    for corrupted, original in zip(reversed_without_tracks["steps"], baseline[4]["steps"]):
        corrupted["indices"] = original["indices"]
    mixed_zero = deepcopy(baseline[0])
    mixed_zero["steps"][-1]["target"] = (0, 2, 0, 0, 0)
    erased_source = deepcopy(baseline[0])
    erased_source["source"] = ZERO
    bad_height = deepcopy(baseline[7])
    bad_height["H"] = 2
    mutations = dict(legal_but_wrong_ordinal=legal_wrong,
                     wrong_actual_target_type=wrong_type,
                     changed_full_offset=wrong_vector,
                     incomplete_path=missing, continuation_after_zero=continued,
                     negative_ordinal=negative_index, beyond_literal_last=overrun,
                     old_JH4_last_c_is_not_run_y=old_formula,
                     coordinate_negation_without_track_swap=reversed_without_tracks,
                     mixed_letter_zero=mixed_zero, erased_nonzero_source=erased_source,
                     outside_eight_case_height=bad_height)
    controls = {name: _reject(lambda case=case: certify_path(case))
                for name, case in mutations.items()}
    controls.update(
        noninteger_ordinal=_reject(lambda: occurrence(3, 2, Rational(1, 2))),
        floating_ordinal=_reject(lambda: occurrence(3, 2, 1.0)),
        undeclared_parameter=_reject(lambda: occurrence(3, 2, symbols("foreign"))),
        negative_chamber_coefficient=_reject(lambda: nonnegative(N-8)),
        nonzero_polynomial_is_not_identity=_reject(lambda: zero(N-7)))
    return controls


def certify():
    source_cases = cases()
    if tuple((case["J"], case["H"]) for case in source_cases) != CASES:
        raise ValueError("independent table is not the complete exact eight-case set")
    directed = [case for positive in source_cases for case in (positive, reverse_case(positive))]
    rows = [certify_path(case) for case in directed]
    controls = negative_controls()
    return dict(schema="psc-class-a-plus-upper-symbolic-v1",
                scope="all n>=7; eight W_H cases and genuine track reversals; literal occurrences and original prefixes",
                parameter_chamber="n=7+t, t an arbitrary nonnegative integer",
                finite_sampling_used=False, canonical_language="Mojo",
                directed_paths=len(rows), checked_edges=sum(row["depth"] for row in rows),
                original_occurrences=2*sum(row["depth"] for row in rows),
                maximum_path_length=max(row["depth"] for row in rows),
                paths=rows, negative_controls=controls,
                geometry_scope="conditional backward strictness from positive lengths and exact inflation scaling; not proved by this polynomial checker",
                strict_geometry_formalized_here=False,
                recurrence_executed=False, all_source_entry=False, universal_BH=False)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = certify()
    text = json.dumps(result, sort_keys=True, indent=2)+"\n"
    if args.output:
        args.output.write_text(text)
        print(json.dumps({key: value for key, value in result.items() if key != "paths"}, sort_keys=True))
    else:
        print(text, end="")
