"""Independent exact oracle for the second non-unit incidence and its carrier.

Literature gate: docs/c4-finite-overlap-carrier-literature-gate-2026-11-05.md.
Canonical implementation is Mojo. This oracle uses Fraction Gaussian inverse,
field-power stable matrices and direct literal digits; no SC input is read.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from math import lcm
import argparse
import hashlib
import json
from pathlib import Path

M = ((0, 1, 1), (2, 1, 1), (0, 1, 0))
P = (-2, -3, -1, 1)
A = (Q(1, 4), Q(3, 4), Q(-1, 4))
B = (Q(-3, 2), Q(-1, 2), Q(1, 2))
ELL = ((Q(1), Q(0), Q(0)), (Q(0), Q(1, 2), Q(0)),
       (Q(-1), Q(-1, 2), Q(1, 2)))
F = ((Q(1), Q(1), Q(0)), (Q(0), Q(0), Q(1)), (Q(0), Q(1), Q(0)))
SCHEMA = 'c4-pair-overlap-new-incidence-v1'
GRID = 1000000
RADII = (8, 8)
COEFFICIENTS = ((556693, 556694), (398160, 398161))
BLOCK_BOUNDS = ((Q(313, 1000), Q(103, 1000)), (Q(184, 1000), Q(148, 1000)))
DIGIT_BOUNDS = (Q(41, 10), Q(24, 5))
RATE_NUMERATOR = 125
RATE_DENOMINATOR = 20
STATE_BUDGET = 20000
WEIGHT_BUDGET = 1000000


class InvalidCertificate(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise InvalidCertificate(reason)


def source_images(index):
    require(type(index) is int and 0 <= index < 12, 'source outside twelve-order class')
    middle = ('012', '021', '102', '120', '201', '210')
    return '11', middle[index // 2], ('01', '10')[index % 2]


def mm(a, b):
    return tuple(tuple(sum(x*y for x, y in zip(row, col)) for col in zip(*b)) for row in a)


def power(a, n):
    out = tuple(tuple(int(i == j) for j in range(len(a))) for i in range(len(a)))
    for _ in range(n):
        out = mm(out, a)
    return out


def inverse(a):
    n = len(a)
    rows = [[Q(x) for x in row]+[Q(i == j) for j in range(n)] for i, row in enumerate(a)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if rows[i][k]), None)
        require(pivot is not None, 'singular rational matrix')
        rows[k], rows[pivot] = rows[pivot], rows[k]
        divisor = rows[k][k]
        rows[k] = [x/divisor for x in rows[k]]
        for i in range(n):
            if i != k:
                factor = rows[i][k]
                rows[i] = [x-factor*y for x, y in zip(rows[i], rows[k])]
    return tuple(tuple(row[n:]) for row in rows)


def poly(x):
    return x*x*x-x*x-3*x-2


@lru_cache(maxsize=1)
def root_bracket():
    lo, hi = Q(5, 2), Q(13, 5)
    for _ in range(64):
        mid = (lo+hi)/2
        if poly(mid) < 0:
            lo = mid
        else:
            hi = mid
    require(poly(lo) < 0 < poly(hi), 'strict Perron bracket')
    return lo, hi


def iadd(a, b):
    return a[0]+b[0], a[1]+b[1]


def ineg(a):
    return -a[1], -a[0]


def imul(a, b):
    products = tuple(x*y for x in a for y in b)
    return min(products), max(products)


def idiv(a, b):
    require(b[0] > 0 or b[1] < 0, 'interval denominator contains zero')
    return imul(a, (1/b[1], 1/b[0]))


def interval(p):
    out = Q(0), Q(0)
    for coefficient in reversed(p):
        out = iadd(imul(out, root_bracket()), (coefficient, coefficient))
    return out


def fadd(a, b):
    return tuple(x+y for x, y in zip(a, b))


def fscale(a, c):
    return tuple(c*x for x in a)


def fmul(a, b):
    out = [Q(0)]*5
    for i in range(3):
        for j in range(3):
            out[i+j] += a[i]*b[j]
    for k in (4, 3):
        coefficient = out[k]
        for j in range(3):
            out[k-3+j] -= coefficient*P[j]
    return tuple(out[:3])


def certify_algebra():
    zero = (Q(0),)*3
    beta = (Q(0), Q(1), Q(0))
    one = (Q(1), Q(0), Q(0))
    for c in range(3):
        left = zero
        right = zero
        for d in range(3):
            left = fadd(left, fscale(F[d], M[c][d]))
            right = fadd(right, fscale(ELL[d], M[d][c]))
        require(left == fmul(beta, F[c]), 'right Perron identity')
        require(right == fmul(beta, ELL[c]), 'left Perron identity')
    require(fmul(A, ELL[2]) == (Q(1, 2), Q(0), Q(0)), 'a ell2 simplification')
    chart = ((one, fscale(A, -1), zero), (zero, fscale(B, -1), one))
    stable = ((fscale(A, -2), fadd(one, fscale(A, -1))),
              (fscale(B, -2), fscale(B, -1)))
    for i in range(2):
        annihilator = zero
        for j in range(3):
            annihilator = fadd(annihilator, fmul(chart[i][j], F[j]))
            left, right = zero, zero
            for k in range(3):
                left = fadd(left, fscale(chart[i][k], M[k][j]))
            for k in range(2):
                right = fadd(right, fmul(stable[i][k], chart[k][j]))
            require(left == right, 'stable intertwining identity')
        require(annihilator == zero, 'stable chart annihilates Perron line')
    require(all(poly(x) for x in (-2, -1, 1, 2)), 'irreducibility rational-root control')
    require(all(x > 0 for row in power(M, 2) for x in row), 'primitive square')
    a, b, c = -1, -3, -2
    require(a*a*b*b-4*b*b*b-4*a*a*a*c-27*c*c+18*a*b*c == -107, 'cubic discriminant')
    return True


@lru_cache(maxsize=1)
def stable_block():
    one, zero = (Q(1), Q(0), Q(0)), (Q(0),)*3
    stable = ((fscale(A, -2), fadd(one, fscale(A, -1))),
              (fscale(B, -2), fscale(B, -1)))
    out = ((one, zero), (zero, one))
    for _ in range(12):
        out = tuple(tuple(fadd(fmul(out[i][0], stable[0][j]),
                               fmul(out[i][1], stable[1][j])) for j in range(2)) for i in range(2))
    return out


def literal_words(index, depth):
    require(type(depth) is int and 0 <= depth <= 12, 'bounded literal depth')
    sigma = source_images(index)
    words = ('0', '1', '2')
    for _ in range(depth):
        require(all(sum(len(sigma[int(c)]) for c in w) <= 100000 for w in words), 'literal word budget')
        words = tuple(''.join(sigma[int(c)] for c in word) for word in words)
    return words


def occurrences(index, depth):
    for source, word in enumerate(literal_words(index, depth)):
        prefix = [0, 0, 0]
        for position, character in enumerate(word):
            letter = int(character)
            yield source, position, letter, tuple(prefix)
            prefix[letter] += 1


@lru_cache(maxsize=12)
def exact_digit_extrema(index):
    endpoints = [(coordinate, value.numerator, value.denominator)
                 for coordinate, coefficients in ((0, interval(A)), (2, interval(B)))
                 for value in coefficients]
    maxima = [0]*4
    count = 0
    for _, _, _, p in occurrences(index, 12):
        count += 1
        for i, (coordinate, numerator, denominator) in enumerate(endpoints):
            maxima[i] = max(maxima[i], abs(p[coordinate]*denominator-numerator*p[1]))
    maxima = [Q(x, spec[2]) for x, spec in zip(maxima, endpoints)]
    return count, max(maxima[:2]), max(maxima[2:])


def floor_q(x):
    return x.numerator // x.denominator


def ceil_q(x):
    return -floor_q(-x)


@lru_cache(maxsize=1)
def carrier_boxes():
    a, b, c = interval(A), interval(B), interval(ELL[2])
    d = interval(fadd(fscale(A, 3), (Q(1, 2), Q(0), Q(0))))
    one = Q(1), Q(1)
    half = Q(1, 2), Q(1, 2)
    inv = ((idiv(a, d), idiv(iadd(d, ineg(a)), d), ineg(idiv(half, d))),
           (idiv(one, d), ineg(idiv(one, d)), ineg(idiv(c, d))),
           (idiv(b, d), ineg(idiv(b, d)), idiv(iadd(d, ineg(imul(b, c))), d)))
    require(d[0] > 0, 'invertible physical/stable chart')
    out = {}
    for first in range(3):
        for second in range(first, 3):
            domain = ((-interval(ELL[first])[1], interval(ELL[second])[1]),
                      (Q(-2*RADII[0]), Q(2*RADII[0])),
                      (Q(-2*RADII[1]), Q(2*RADII[1])))
            bounds = []
            for row in inv:
                total = Q(0), Q(0)
                for coefficient, coordinate in zip(row, domain):
                    total = iadd(total, imul(coefficient, coordinate))
                bounds.append((ceil_q(total[0]), floor_q(total[1])))
            require(all(lo <= hi for lo, hi in bounds), 'empty carrier box')
            out[first, second] = tuple(bounds)
    return out


@lru_cache(maxsize=12)
def certify_model(index):
    certify_algebra()
    images = source_images(index)
    require(tuple(tuple(w.count(str(c)) for w in images) for c in range(3)) == M, 'source incidence')
    for start in range(3):
        seen, letter = {}, start
        while letter not in seen:
            seen[letter] = len(seen)
            letter = int(images[letter][0])
        require(12 % (len(seen)-seen[letter]) == 0, 'common attractor block/prefix period')
    for coarse, exact in zip(COEFFICIENTS, (interval(A), interval(B))):
        require(Q(coarse[0], GRID) <= exact[0] <= exact[1] <= Q(coarse[1], GRID), 'coarse chart interval')
    for i, row in enumerate(stable_block()):
        for j, value in enumerate(row):
            require(max(map(abs, interval(value))) <= BLOCK_BOUNDS[i][j], 'stable block bound')
        linear = sum(BLOCK_BOUNDS[i][j]*RADII[j] for j in range(2))
        require(linear < RADII[i] and linear+DIGIT_BOUNDS[i] <= RADII[i], 'contracting invariant box')
    count, x, y = exact_digit_extrema(index)
    require(count == 178973, 'complete block digit inventory')
    require(x <= DIGIT_BOUNDS[0] and y <= DIGIT_BOUNDS[1], 'complete block digit bounds')
    require(root_bracket()[0]**2 > Q(63, 10), 'strict beta-squared lower bound')
    return {'block':12, 'radii':RADII, 'literal_digits':count,
            'carrier':carrier_boxes(), 'carrier_capacity':sum(
                (r[0][1]-r[0][0]+1)*(r[1][1]-r[1][0]+1)*(r[2][1]-r[2][0]+1)
                for r in carrier_boxes().values())}


def canonical(first, second, offset):
    return min((first, second, *offset), (second, first, *(-x for x in offset)))


def outside_box(offset):
    for coordinate, (lo, hi), radius in zip((0, 2), COEFFICIENTS, RADII):
        ends = (GRID*offset[coordinate]-lo*offset[1], GRID*offset[coordinate]-hi*offset[1])
        if min(ends) > 2*radius*GRID or max(ends) < -2*radius*GRID:
            return True
    return False


def outside_carrier(state):
    return any(x < lo or x > hi for x, (lo, hi) in zip(state[2:], carrier_boxes()[state[:2]]))


@dataclass
class Graph:
    index: int
    states: list
    rows: list
    residue_rejections: int
    box_rejections: int
    carrier_rejections: int


def build_graph(index, state_cap=STATE_BUDGET):
    model = certify_model(index)
    require(type(state_cap) is int and 3 <= state_cap <= model['carrier_capacity'], 'operational state budget')
    inv = inverse(power(M, 2))
    denominator = lcm(*(x.denominator for row in inv for x in row))
    numerator = tuple(tuple(int(x*denominator) for x in row) for row in inv)
    digits = list(occurrences(index, 2))
    by_letter = [tuple(d for d in digits if d[2] == c) for c in range(3)]
    states = [(0, 1, 0, 0, 0), (0, 2, 0, 0, 0), (1, 2, 0, 0, 0)]
    lookup = {state:i for i, state in enumerate(states)}
    rows, cursor, residue, box, carrier = [], 0, 0, 0, 0
    while cursor < len(states):
        first, second, *offset = states[cursor]
        row = []
        for d, _, _, p in by_letter[first]:
            for e, _, _, r in by_letter[second]:
                delta = tuple(x+y-z for x, y, z in zip(offset, r, p))
                values = tuple(sum(x*y for x, y in zip(line, delta)) for line in numerator)
                if any(x % denominator for x in values):
                    residue += 1
                    continue
                shift = tuple(x//denominator for x in values)
                if outside_box(shift):
                    box += 1
                    continue
                child = canonical(d, e, shift)
                if outside_carrier(child):
                    carrier += 1
                    continue
                if child not in lookup:
                    require(len(states) < state_cap, 'state budget exhausted; inconclusive')
                    lookup[child] = len(states)
                    states.append(child)
                row.append(lookup[child])
        rows.append(row)
        cursor += 1
    return Graph(index, states, rows, residue, box, carrier)


def verify_weights(graph, weights, numerator=RATE_NUMERATOR, denominator=RATE_DENOMINATOR):
    """Check a finite inequality only; authenticate supplied graphs separately."""
    require(type(numerator) is int and type(denominator) is int and numerator > 0 and denominator > 0,
            'positive rational rate')
    require(Q(numerator, denominator) < Q(63, 10), 'rate must be below certified lower bound')
    require(len(weights) == len(graph.states) == len(graph.rows) and len(weights) > 0, 'weight dimensions')
    require(all(type(w) is int and 1 <= w <= WEIGHT_BUDGET for w in weights), 'positive bounded weights')
    gaps = []
    for i, row in enumerate(graph.rows):
        require(all(type(j) is int and 0 <= j < len(weights) for j in row), 'target before indexing')
        gap = numerator*weights[i]-denominator*sum(weights[j] for j in row)
        require(gap >= 0, 'false positive subinvariance')
        gaps.append(gap)
    return min(gaps)


def construct_weights(graph, numerator=RATE_NUMERATOR, denominator=RATE_DENOMINATOR, iteration_cap=4000):
    require(type(iteration_cap) is int and 1 <= iteration_cap <= 10000, 'weight iteration budget')
    require(type(numerator) is int and type(denominator) is int and numerator > 0 and denominator > 0,
            'positive rational rate before division')
    require(Q(numerator, denominator) < Q(63, 10), 'strict certified rate')
    require(0 < len(graph.states) == len(graph.rows) <= STATE_BUDGET, 'graph dimensions before iteration')
    require(all(len(row) <= 81 and all(type(j) is int and 0 <= j < len(graph.states) for j in row)
                for row in graph.rows), 'bounded targets before weight indexing')
    weights = [1]*len(graph.states)
    for sweep in range(1, iteration_cap+1):
        changed = False
        for i, row in enumerate(graph.rows):
            value = 1+(denominator*sum(weights[j] for j in row)+numerator-1)//numerator
            require(weights[i] <= value, 'ordered iteration must be monotone')
            require(value <= WEIGHT_BUDGET, 'weight budget exhausted; inconclusive')
            if weights[i] != value:
                changed = True
                weights[i] = value
        if not changed:
            return weights, sweep, verify_weights(graph, weights, numerator, denominator)
    raise InvalidCertificate('weight iteration budget exhausted; inconclusive')


def certify_uniform_upper_tenth():
    """An exact finite upper bound, separate from the limiting nullity proof."""
    require(Q(125, 126)**126 < Q(3, 8), 'first rational power inequality')
    require(256*WEIGHT_BUDGET*Q(3, 8)**24 < Q(1, 10), 'second rational power inequality')
    require(3072 >= 24*126, 'finite refinement exponent')
    return True


@lru_cache(maxsize=12)
def reference(index):
    graph = build_graph(index)
    weights, sweeps, gap = construct_weights(graph)
    return graph, weights, sweeps, gap


def validate_supplied_graph(index, states, rows, weights,
                            numerator=RATE_NUMERATOR, denominator=RATE_DENOMINATOR):
    """Reconstruct every actual occurrence row before accepting an inequality."""
    expected, _, _, _ = reference(index)
    require(states == expected.states, 'complete ordered state inventory mismatch')
    require(rows == expected.rows, 'complete occurrence rows/multiplicities mismatch')
    return verify_weights(expected, weights, numerator, denominator)


def graph_lines(graph, weights, sweeps):
    yield ' '.join(map(str, ('graph', graph.index, len(graph.states), sum(map(len, graph.rows)),
                             graph.residue_rejections, graph.box_rejections, graph.carrier_rejections,
                             sweeps, RATE_NUMERATOR, RATE_DENOMINATOR)))
    for i, (state, weight, row) in enumerate(zip(graph.states, weights, graph.rows)):
        yield ' '.join(map(str, ('node', graph.index, i, *state, weight)))
        yield ' '.join(map(str, ('row', graph.index, i, len(row), *row)))


def packet_lines():
    yield 'schema '+SCHEMA
    yield 'model 8 8 12 556693 556694 398160 398161 1000000'
    for pair, box in carrier_boxes().items():
        capacity = (box[0][1]-box[0][0]+1)*(box[1][1]-box[1][0]+1)*(box[2][1]-box[2][0]+1)
        yield ' '.join(map(str, ('carrier', *pair, *(v for bounds in box for v in bounds), capacity)))
    for index in range(12):
        graph, weights, sweeps, _ = reference(index)
        yield from graph_lines(graph, weights, sweeps)


def text_digest(lines):
    digest = hashlib.sha256()
    for line in lines:
        digest.update((line+'\n').encode('ascii'))
    return digest.hexdigest()


def receipt():
    certify_uniform_upper_tenth()
    results = []
    for index in range(12):
        graph, weights, sweeps, gap = reference(index)
        results.append({'index':index, 'images':list(source_images(index)),
                        'states':len(graph.states), 'edges':sum(map(len, graph.rows)),
                        'residue_rejections':graph.residue_rejections,
                        'box_rejections':graph.box_rejections,
                        'carrier_rejections':graph.carrier_rejections,
                        'sweeps':sweeps, 'minimum_gap':gap, 'maximum_weight':max(weights),
                        'root_weights':weights[:3],
                        'certificate_sha256':text_digest(graph_lines(graph, weights, sweeps))})
    return {'schema':SCHEMA, 'canonical_language':'Mojo',
            'source_count':12, 'distinct_letter_root_count':36,
            'incidence':[list(row) for row in M], 'characteristic_polynomial':list(P),
            'radii':list(RADII), 'block':12, 'literal_digits_per_source':178973,
            'carrier':[{'pair':list(pair), 'bounds':[list(r) for r in box]}
                       for pair, box in carrier_boxes().items()],
            'carrier_capacity':178002, 'state_budget_per_source':STATE_BUDGET,
            'weight_budget':WEIGHT_BUDGET, 'rate':[RATE_NUMERATOR, RATE_DENOMINATOR],
            'beta_squared_lower_bound':[63,10], 'finite_exponent':3072,
            'finite_upper_bound_strictly_below':[1,10],
            'total_states':sum(r['states'] for r in results),
            'total_edges':sum(r['edges'] for r in results), 'sources':results,
            'normalized_packet_sha256':text_digest(packet_lines()),
            'scope':'complete finite graphs and rational inequalities; nullity uses the written measure proof',
            'non_claims':['general C4', 'BPA termination', 'SC', 'degree-one tiling', 'PDS', 'PSC']}


def verify_native(packet):
    """Require the complete deterministic twelve-source packet, token for token.

    Comparing all records authenticates models, source identities, state order,
    every repeated edge, weights, rates and rejection counts. This is stronger
    than comparing a summary or accepting a truncated certificate.
    """
    require(isinstance(packet, str), 'native packet must be text')
    actual = [line.split() for line in packet.splitlines() if line.strip()]
    require(len(actual) >= 8 and actual[0] == ['schema', SCHEMA], 'native packet preamble mismatch')
    expected = [line.split() for line in packet_lines()]
    require(len(actual) == len(expected), 'complete native packet record count mismatch')
    for number, (left, right) in enumerate(zip(actual, expected), 1):
        require(left == right, 'native packet mismatch at record '+str(number))
    return receipt()


def exploration():
    certify_algebra()
    block = [[max(map(abs, interval(p))) for p in row] for row in stable_block()]
    print(json.dumps({'beta':list(map(float, root_bracket())),
                     'coefficients': [list(map(float, interval(p))) for p in (A, B)],
                     'block12':[[float(x) for x in row] for row in block]}), flush=True)
    for index in range(12):
        count, x, y = exact_digit_extrema(index)
        print(json.dumps({'index':index,'source':source_images(index),'digits':count,'extrema':[float(x),float(y)]}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--explore', action='store_true')
    parser.add_argument('--index', type=int)
    parser.add_argument('--native', type=Path, help='authenticate a complete native stdout packet')
    parser.add_argument('--packet', action='store_true', help='emit an oracle calibration packet, not native evidence')
    args = parser.parse_args()
    if args.explore:
        exploration()
    elif args.native:
        print(json.dumps(verify_native(args.native.read_text()), indent=2))
    elif args.packet:
        print('\n'.join(packet_lines()))
    elif args.index is None:
        print(json.dumps(receipt(), indent=2))
    else:
        print(json.dumps({'carrier': {str(k):v for k,v in carrier_boxes().items()}}), flush=True)
        for index in (range(12) if args.index is None else (args.index,)):
            graph = build_graph(index)
            try:
                weights, sweeps, gap = construct_weights(graph)
                result = {'sweeps':sweeps,'minimum_gap':gap,'max_weight':max(weights),'root_weights':weights[:3]}
            except InvalidCertificate as error:
                result = {'inconclusive':str(error)}
            print(json.dumps({'index':index,'states':len(graph.states),'edges':sum(map(len, graph.rows)),
                              'rejections':[graph.residue_rejections,graph.box_rejections,graph.carrier_rejections],
                              **result}), flush=True)
