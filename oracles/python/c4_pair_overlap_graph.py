"""Exact finite overlap-graph certificates for the two #495 controls.

The native producer reuses the existing chart/word code. This independent
stdlib verifier uses rational Gaussian inversion and direct literal digits.
No strong-coincidence search, strict-component premise, or PDS import is used.
The finite arithmetic supports the written compact M-adic measure argument;
it is not a machine proof of that argument or a general PSC conclusion.
"""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import lcm
import argparse
import hashlib
import json
from pathlib import Path

CONTROLS = (("1", "021", "001"), ("1", "012", "001"))
M = ((0, 1, 2), (1, 1, 1), (0, 1, 0))
GRID = 1_000_000
COEFFICIENTS = ((828911, 828912), (440619, 440620))
RADII = (16, 8)
RATE_NUMERATORS = (99, 101)
STATE_CAP = 16000
COORDINATE_CAP = 32
WEIGHT_CAP = 1_000_000
SCHEMA = "c4-pair-overlap-graph-v1"


class InvalidCertificate(ValueError):
    """Reject a finite obligation; never convert exhaustion into a verdict."""


def require(condition, reason):
    if not condition:
        raise InvalidCertificate(reason)


def fixture_words(fixture):
    require(type(fixture) is int and fixture in (0, 1), "unsupported fixture")
    return CONTROLS[fixture]


def mm(a, b):
    return tuple(tuple(sum(x*y for x, y in zip(row, col)) for col in zip(*b)) for row in a)


def power(m, n):
    result = tuple(tuple(int(i == j) for j in range(len(m))) for i in range(len(m)))
    for _ in range(n):
        result = mm(result, m)
    return result


def inverse(m):
    rows = [[Q(x) for x in row] + [Q(i == j) for j in range(3)] for i, row in enumerate(m)]
    for col in range(3):
        pivot = next((i for i in range(col, 3) if rows[i][col]), None)
        require(pivot is not None, "singular incidence")
        rows[col], rows[pivot] = rows[pivot], rows[col]
        q = rows[col][col]
        rows[col] = [x/q for x in rows[col]]
        for i in range(3):
            if i != col:
                q = rows[i][col]
                rows[i] = [x-q*y for x, y in zip(rows[i], rows[col])]
    return tuple(tuple(row[3:]) for row in rows)


def polynomial(x):
    return x*x*x-x*x-2*x-2


@lru_cache(maxsize=1)
def root_bracket():
    lo, hi = Q(2), Q(5, 2)
    for _ in range(64):
        mid = (lo+hi)/2
        if polynomial(mid) < 0:
            lo = mid
        else:
            hi = mid
    require(polynomial(lo) < 0 < polynomial(hi), "Perron isolation")
    return lo, hi


def imul(a, b):
    v = [x*y for x in a for y in b]
    return min(v), max(v)


def interval(poly):
    out = (Q(0), Q(0))
    for c in reversed(poly):
        lo, hi = imul(out, root_bracket())
        out = lo+c, hi+c
    return out


def field_add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def field_mul(a, b):
    out = [Q(0)]*5
    for i in range(3):
        for j in range(3):
            out[i+j] += a[i]*b[j]
    # beta^3 = beta^2 + 2 beta + 2.
    for k in (4, 3):
        c = out[k]
        out[k-1] += c
        out[k-2] += 2*c
        out[k-3] += 2*c
    return tuple(out[:3])


def stable_block():
    a = (Q(0), Q(3, 2), Q(-1, 2))
    b = (Q(-1), Q(-1, 2), Q(1, 2))
    neg = lambda t: tuple(-x for x in t)
    zero, one = (Q(0),)*3, (Q(1), Q(0), Q(0))
    stable = ((neg(a), field_add((Q(2), Q(0), Q(0)), neg(a))), (neg(b), neg(b)))
    result = ((one, zero), (zero, one))
    for _ in range(12):
        result = tuple(tuple(field_add(field_mul(result[i][0], stable[0][j]),
                                       field_mul(result[i][1], stable[1][j]))
                             for j in range(2)) for i in range(2))
    return result


def occurrences(fixture, depth):
    sigma = fixture_words(fixture)
    require(type(depth) is int and 0 <= depth <= 12, "literal depth budget")
    words = ("0", "1", "2")
    for _ in range(depth):
        words = tuple("".join(sigma[int(c)] for c in w) for w in words)
        require(all(len(w) <= 100000 for w in words), "literal word budget")
    for source, word in enumerate(words):
        prefix = [0, 0, 0]
        for position, letter in enumerate(word):
            yield source, position, int(letter), tuple(prefix)
            prefix[int(letter)] += 1


@lru_cache(maxsize=2)
def certify_chart(fixture):
    sigma = fixture_words(fixture)
    require(tuple(tuple(w.count(str(i)) for w in sigma) for i in range(3)) == M, "incidence mismatch")
    beta_lo, _ = root_bracket()
    require(beta_lo*beta_lo > Q(103, 20), "insufficient strict contraction denominator")
    a = interval((Q(0), Q(3, 2), Q(-1, 2)))
    b = interval((Q(-1), Q(-1, 2), Q(1, 2)))
    for bounds, value in zip(COEFFICIENTS, (a, b)):
        require(Q(bounds[0], GRID) <= value[0] <= value[1] <= Q(bounds[1], GRID), "coarse chart enclosure")
    block = stable_block()
    bounds = ((Q(473,1000), Q(390,1000)), (Q(147,1000), Q(344,1000)))
    for i in range(2):
        for j in range(2):
            require(max(map(abs, interval(block[i][j]))) <= bounds[i][j], "stable block bound")
    maximum = [Q(0), Q(0)]
    count = 0
    for _, _, _, (x, y, z) in occurrences(fixture, 12):
        count += 1
        maximum[0] = max(maximum[0], abs(x-a[0]*y), abs(x-a[1]*y))
        maximum[1] = max(maximum[1], abs(z-b[0]*y), abs(z-b[1]*y))
    digits = (Q(23, 5), Q(14, 5))
    for i in range(2):
        require(maximum[i] <= digits[i], "incomplete/underestimated block digit enclosure")
        require(sum(bounds[i][j]*RADII[j] for j in range(2)) < RADII[i], "noncontracting weighted box")
        require(digits[i]+sum(bounds[i][j]*RADII[j] for j in range(2)) <= RADII[i], "box invariance")
    require(count == 55583, "complete block inventory mismatch")
    return {"block": 12, "literal_digits": count, "radii": list(RADII),
            "stable_entry_bounds": [[str(x) for x in row] for row in bounds],
            "digit_bounds": [str(x) for x in digits], "beta_squared_lower": "103/20"}


def canonical(c, d, z):
    left = (c, d, *z)
    right = (d, c, *(-x for x in z))
    return min(left, right)


def outside_box(z):
    """Prune only on a strictly separated rational interval, never its center."""
    for coordinate, (lo, hi), radius in zip((0, 2), COEFFICIENTS, RADII):
        ends = (GRID*z[coordinate]-lo*z[1], GRID*z[coordinate]-hi*z[1])
        if min(ends) > 2*radius*GRID or max(ends) < -2*radius*GRID:
            return True
    return False


@dataclass
class Graph:
    fixture: int
    states: list
    rows: list
    residue_rejections: int
    box_rejections: int


def build_graph(fixture, state_cap=STATE_CAP):
    fixture_words(fixture)
    require(type(state_cap) is int and 3 <= state_cap <= STATE_CAP, "state cap domain")
    certify_chart(fixture)
    digits = [[] for _ in range(3)]
    for d, pos, c, p in occurrences(fixture, 2):
        digits[c].append((d, pos, p))
    inv = inverse(power(M, 2))
    denominator = lcm(*(x.denominator for row in inv for x in row))
    numer = tuple(tuple(int(denominator*x) for x in row) for row in inv)
    states = [canonical(c, d, (0,0,0)) for c, d in combinations(range(3), 2)]
    ids, rows = {s: i for i, s in enumerate(states)}, []
    residue_rejections = box_rejections = 0
    for c, d, x, y, z in states:
        targets = []
        for a, pos, p in digits[c]:
            for b, other_pos, q in digits[d]:
                delta = (x+q[0]-p[0], y+q[1]-p[1], z+q[2]-p[2])
                candidate = tuple(sum(a*b for a,b in zip(row,delta)) for row in numer)
                if any(v % denominator for v in candidate):
                    residue_rejections += 1
                    continue
                translated = tuple(v//denominator for v in candidate)
                if outside_box(translated):
                    box_rejections += 1
                    continue
                require(max(map(abs, translated)) <= COORDINATE_CAP, "coordinate cap exhausted; inconclusive")
                child = canonical(a,b,translated)
                if child not in ids:
                    require(len(states) < state_cap, "state cap exhausted; inconclusive")
                    ids[child] = len(states)
                    states.append(child)
                targets.append(ids[child])  # Keep every paired occurrence, including repeats.
        rows.append(targets)
    return Graph(fixture, states, rows, residue_rejections, box_rejections)


def validate_weights(graph, weights, numerator, denominator=20):
    require(type(numerator) is int and type(denominator) is int and 0 < numerator and denominator > 0,
            "invalid rational graph rate")
    require(Q(numerator,denominator) < Q(103,20), "rate not strictly below certified beta squared")
    require(len(weights) == len(graph.states) == len(graph.rows), "weight dimensions")
    require(all(type(w) is int and 0 < w <= WEIGHT_CAP for w in weights), "positive bounded integer weights required")
    gaps = []
    for i,row in enumerate(graph.rows):
        require(all(type(j) is int and 0 <= j < len(weights) for j in row), "bad target index")
        gap = numerator*weights[i]-denominator*sum(weights[j] for j in row)
        require(gap >= 0, "false graph subinvariance")
        gaps.append(gap)
    return min(gaps)


def construct_weights(graph, iteration_cap=4000):
    require(type(iteration_cap) is int and 1 <= iteration_cap <= 4000, "iteration cap domain")
    n = RATE_NUMERATORS[graph.fixture]
    weights = [1]*len(graph.states)
    for iteration in range(1,iteration_cap+1):
        following = [1+(20*sum(weights[j] for j in row)+n-1)//n for row in graph.rows]
        require(max(following) <= WEIGHT_CAP, "weight budget exhausted; inconclusive")
        if following == weights:
            gap = validate_weights(graph, weights, n)
            return weights, iteration, gap
        weights = following
    raise InvalidCertificate("iteration cap exhausted; inconclusive")


def graph_lines(graph, weights, iterations):
    f = graph.fixture
    yield f"graph {f} {len(graph.states)} {sum(map(len,graph.rows))} {graph.residue_rejections} {graph.box_rejections} {iterations} {RATE_NUMERATORS[f]} 20"
    for i,(state,row,w) in enumerate(zip(graph.states,graph.rows,weights)):
        yield "node " + " ".join(map(str,(f,i,*state,w)))
        yield "row " + " ".join(map(str,(f,i,len(row),*row)))


def graph_text(graph, weights, iterations):
    return "\n".join(graph_lines(graph,weights,iterations))+"\n"


def validate_supplied_graph(fixture, states, rows, weights):
    """The theorem-facing path reconstructs every row; arithmetic alone is not admission."""
    actual = build_graph(fixture)
    require(states == actual.states and rows == actual.rows, "incomplete/relabelled occurrence graph")
    validate_weights(actual, weights, RATE_NUMERATORS[fixture])
    return actual


def summary(graph, weights, iterations, gap):
    n = RATE_NUMERATORS[graph.fixture]
    content = graph_text(graph, weights, iterations)
    ratios = [Q(512*w)*Q(n,103)**1024 for w in weights[:3]]
    require(all(u < Q(1,10) for u in ratios), "advertised rational upper bound failed")
    return {"fixture":graph.fixture,"sigma":list(CONTROLS[graph.fixture]),
            "states":len(graph.states),"occurrence_edges":sum(map(len,graph.rows)),
            "residue_rejections":graph.residue_rejections,"box_rejections":graph.box_rejections,
            "weight_iterations":iterations,"minimum_weight":min(weights),"maximum_weight":max(weights),
            "minimum_integer_gap":gap,"root_weights":weights[:3],"rate":str(Q(n,20)),
            "contractive_ratio_upper":str(Q(n,103)),
            "zero_offset_diagonal_states":sum(s[0]==s[1] and s[2:]==(0,0,0) for s in graph.states),
            "roots_all_below_one_tenth_at_1024_blocks":True,
            "canonical_graph_sha256":hashlib.sha256(content.encode()).hexdigest(),
            "chart":certify_chart(graph.fixture)}


@lru_cache(maxsize=2)
def reference(fixture):
    graph = build_graph(fixture)
    weights, iterations, gap = construct_weights(graph)
    return graph, weights, iterations, gap


def receipt():
    return {"schema":SCHEMA,"base_main":"60536272b3d68b4f53ce772e7674efabce840fde",
            "scope":"two named compact M-adic controls; no SC witness input or general PSC claim",
            "fixtures":[summary(*reference(f)) for f in range(2)]}


def verify_native(text):
    require(len(text.encode()) <= 4_000_000, "native packet byte budget")
    lines = text.splitlines()
    require(lines and lines[0] == "schema "+SCHEMA, "wrong graph schema")
    expected = []
    for f in range(2):
        g,w,it,_ = reference(f)
        expected.extend(graph_lines(g,w,it))
    require(lines[1:] == expected, "native/reference complete graph mismatch")
    return receipt()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native",type=Path)
    parser.add_argument("--emit-packet",action="store_true")
    args = parser.parse_args()
    if args.native:
        out = verify_native(args.native.read_text())
    elif args.emit_packet:
        print("schema "+SCHEMA)
        for f in range(2):
            g,w,it,_ = reference(f)
            print(graph_text(g,w,it),end="")
        return
    else:
        out = receipt()
    print(json.dumps(out,indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
