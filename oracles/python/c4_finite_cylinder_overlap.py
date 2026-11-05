"""Independent exact verifier for the bounded native cylinder certificate.

Canonical producer: kernel/psc/c4_finite_cylinder_overlap.mojo.
This verifier reconstructs words, uses Gaussian-inverse residue classes, and
checks every rectangle against algebraic affine corners. It does not execute
the measure-theoretic proof of M3 or manufacture a strict-component premise.
Only the two declared controls and the v1 resource envelope are supported.
"""

from collections import defaultdict, deque
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, product
import argparse
import json
import math
from pathlib import Path
import re


CONTROLS = (("1", "021", "001"), ("1", "012", "001"))
DEPTHS = (2, 4, 6)
M = ((0, 1, 2), (1, 1, 1), (0, 1, 0))
P = (-2, -2, -1, 1)
ZERO = (Q(0), Q(0), Q(0))
ONE = (Q(1), Q(0), Q(0))
BETA = (Q(0), Q(1), Q(0))
CHART = "ell0=1;W=(x0-a*x1,x2-b*x1);haar=probability"
WORD_CAP = 100000


class InvalidCertificate(ValueError):
    """A finite obligation failed; no mathematical conclusion is returned."""


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def poly_reduce(coeffs):
    out = [Q(c) for c in coeffs]
    out += [Q(0)] * max(0, 3 - len(out))
    for k in range(len(out) - 1, 2, -1):
        coefficient = out[k]
        for j in range(3):
            out[k - 3 + j] -= coefficient * P[j]
    return tuple(out[:3])


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def scale(a, c):
    return tuple(x * c for x in a)


def mul(a, b):
    result = [Q(0)] * 5
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return poly_reduce(result)


INV_BETA = (Q(-1), Q(-1, 2), Q(1, 2))
A = mul(add(BETA, scale(ONE, 2)), mul(INV_BETA, INV_BETA))
C = add(add(mul(BETA, BETA), scale(BETA, -1)), scale(ONE, -1))
KAPPA = add(add(A, BETA), mul(INV_BETA, C))
B = ((scale(A, -1), add(scale(ONE, 2), scale(A, -1))),
     (scale(INV_BETA, -1), scale(INV_BETA, -1)))


def polynomial_at(x):
    return x*x*x - x*x - 2*x - 2


@lru_cache(maxsize=None)
def root_bracket(bits=96):
    require(1 <= bits <= 160, "root isolation budget")
    lo, hi = Q(2), Q(5, 2)
    for _ in range(bits):
        mid = (lo + hi) / 2
        if polynomial_at(mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


def interval_mul(x, y):
    values = [a*b for a in x for b in y]
    return min(values), max(values)


def interval_at(poly, bracket=None):
    beta = root_bracket() if bracket is None else bracket
    result = (Q(0), Q(0))
    for coefficient in reversed(poly):
        lo, hi = interval_mul(result, beta)
        result = lo + coefficient, hi + coefficient
    return result


@lru_cache(maxsize=50000)
def sign_at_beta(poly):
    poly = poly_reduce(poly)
    if poly == ZERO:
        return 0
    for bits in (48, 96, 160):
        lo, hi = interval_at(poly, root_bracket(bits))
        if lo > 0:
            return 1
        if hi < 0:
            return -1
    raise InvalidCertificate("algebraic sign budget exhausted")


def contains_algebraic(lo, hi, poly):
    return (sign_at_beta(add(poly, scale(ONE, -lo))) >= 0
            and sign_at_beta(add(scale(ONE, hi), scale(poly, -1))) >= 0)


def field_matmul(a, b):
    return tuple(tuple(add(mul(a[i][0], b[0][j]), mul(a[i][1], b[1][j]))
                       for j in range(2)) for i in range(2))


@lru_cache(maxsize=None)
def stable_power(n):
    require(0 <= n <= 12, "stable matrix power budget")
    result = ((ONE, ZERO), (ZERO, ONE))
    for _ in range(n):
        result = field_matmul(result, B)
    return result


def integer_matmul(a, b):
    return tuple(tuple(sum(x*y for x, y in zip(row, col)) for col in zip(*b))
                 for row in a)


@lru_cache(maxsize=None)
def matrix_power(n):
    require(0 <= n <= 12, "integer matrix power budget")
    result = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    for _ in range(n):
        result = integer_matmul(result, M)
    return result


def inverse(matrix):
    rows = [[Q(x) for x in row] + [Q(i == j) for j in range(3)]
            for i, row in enumerate(matrix)]
    for col in range(3):
        pivot = next((i for i in range(col, 3) if rows[i][col]), None)
        require(pivot is not None, "singular lattice")
        rows[col], rows[pivot] = rows[pivot], rows[col]
        divisor = rows[col][col]
        rows[col] = [x/divisor for x in rows[col]]
        for i in range(3):
            if i != col:
                multiplier = rows[i][col]
                rows[i] = [x-multiplier*y for x, y in zip(rows[i], rows[col])]
    return tuple(tuple(row[3:]) for row in rows)


@lru_cache(maxsize=None)
def inverse_power(q):
    return inverse(matrix_power(q))


def residue_key(q, prefix):
    require(0 <= q <= 6 and len(prefix) == 3, "residue domain")
    values = tuple(sum(x*y for x, y in zip(row, prefix)) % 1
                   for row in inverse_power(q))
    scaled = tuple((2**q)*value for value in values)
    require(all(x.denominator == 1 for x in scaled), "nonintegral residue key")
    return tuple(int(x) for x in scaled)


@lru_cache(maxsize=None)
def quotient_representatives(q):
    require(q in (0, 2, 4, 6), "quotient depth domain")
    representatives = {(0, 0, 0): (0, 0, 0)}
    pending = deque([(0, 0, 0)])
    while pending:
        representative = pending.popleft()
        for coordinate in range(3):
            new = tuple(x + (j == coordinate) for j, x in enumerate(representative))
            key = residue_key(q, new)
            if key not in representatives:
                require(len(representatives) < 2**q, "wrong quotient index")
                representatives[key] = new
                pending.append(new)
    require(len(representatives) == 2**q, "incomplete finite quotient")
    return representatives


def words(sigma, q, cap=WORD_CAP):
    require(sigma in CONTROLS, "unsupported geometric substitution")
    require(type(q) is int and 0 <= q <= 12, "word depth budget")
    require(type(cap) is int and 0 < cap <= WORD_CAP, "word cap domain")
    result = ("0", "1", "2")
    for _ in range(q):
        require(all(sum(len(sigma[int(c)]) for c in w) <= cap for w in result),
                "word budget exhausted")
        result = tuple("".join(sigma[int(c)] for c in w) for w in result)
    return result


def occurrences(sigma, q):
    for source, word in enumerate(words(sigma, q)):
        prefix = [0, 0, 0]
        for position, c in enumerate(word):
            yield source, position, int(c), tuple(prefix)
            prefix[int(c)] += 1


def project(prefix):
    x, y, z = prefix
    return (add(scale(ONE, x), scale(A, -y)),
            add(scale(ONE, z), scale(INV_BETA, -y)))


@lru_cache(maxsize=32)
def validate_chart(sigma, chart):
    beta_lo, beta_hi, radius, block, kappa_lo, kappa_hi = chart
    require(all(isinstance(v,(int,Q)) and not isinstance(v,bool)
                for v in (beta_lo,beta_hi,kappa_lo,kappa_hi)),
            "chart scalars must be exact rational")
    require(Q(2) < beta_lo < beta_hi < Q(5, 2), "invalid Perron bracket")
    require(polynomial_at(beta_lo) < 0 < polynomial_at(beta_hi), "wrong Perron root")
    require(type(radius) is int and 0 < radius <= 4096, "outer radius domain")
    require(type(block) is int and block in (2, 4, 6, 8, 10, 12), "block/period mismatch")
    require(Q(0) < kappa_lo <= kappa_hi, "nonpositive covolume")
    require(contains_algebraic(kappa_lo, kappa_hi, KAPPA), "mismatched chart covolume")
    block_matrix = stable_power(block)
    rho = max(sum(max(abs(v) for v in interval_at(entry)) for entry in row)
              for row in block_matrix)
    require(rho < 1, "outer enclosure lacks a contracting block")
    # Independent literal block digits, without residue occupancy calculation.
    a_lo, a_hi = interval_at(A)
    b_lo, b_hi = interval_at(INV_BETA)
    translation = Q(0)
    for _, _, _, (x, y, z) in occurrences(sigma, block):
        translation = max(translation, abs(x-a_hi*y), abs(x-a_lo*y),
                          abs(z-b_hi*y), abs(z-b_lo*y))
    require(rho*radius + translation <= radius, "invalid invariant outer radius")
    return {"rho_upper": str(rho), "digit_upper": str(translation),
            "radius": radius, "block": block}


def rectangle_valid(rect):
    require(len(rect) == 4, "rectangle shape")
    require(all(isinstance(v,(int,Q)) and not isinstance(v,bool) for v in rect),
            "rectangle coordinates must be exact rational")
    x0, x1, y0, y1 = rect
    require(x0 <= x1 and y0 <= y1, "reversed rectangle")
    require(all(abs(v) <= 4096 for v in rect), "rectangle coordinate cap")


@lru_cache(maxsize=10000)
def validate_occurrence_rectangle(q, prefix, radius, rect):
    rectangle_valid(rect)
    matrix = stable_power(q)
    shift = project(prefix)
    for corner in product((-radius, radius), repeat=2):
        for coordinate in range(2):
            point = add(shift[coordinate], add(scale(matrix[coordinate][0], corner[0]),
                                              scale(matrix[coordinate][1], corner[1])))
            require(contains_algebraic(rect[2*coordinate], rect[2*coordinate+1], point),
                    "outer rectangle omits an algebraic affine corner")


def hull(rects):
    require(bool(rects), "empty hull input")
    return (min(r[0] for r in rects), max(r[1] for r in rects),
            min(r[2] for r in rects), max(r[3] for r in rects))


def intersection_area(a, b):
    rectangle_valid(a)
    rectangle_valid(b)
    return max(Q(0), min(a[1], b[1])-max(a[0], b[0])) * max(
        Q(0), min(a[3], b[3])-max(a[2], b[2]))


def parse_packet(text):
    require(len(text.encode()) <= 2000000, "certificate byte budget")
    packet = {"fixtures": {}, "charts": {}, "occurrences": {}, "slices": {},
              "uppers": {}, "sc": {}, "status": {}}
    schema_seen = False
    for line in text.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        require(all(len(field) <= 256 for field in fields), "record token budget")
        kind, items = fields[0], fields[1:]
        if kind == "schema":
            require(not schema_seen and items == ["c4-finite-cylinder-v1"], "schema mismatch")
            schema_seen = True
            continue
        if kind == "fixture":
            require(len(items) == 3, "fixture record shape")
            key = int(items[0])
            value = (tuple(items[1].split("/")), int(items[2]))
            target = "fixtures"
        elif kind == "chart":
            require(len(items) == 7, "chart record shape")
            key = int(items[0])
            value = (parse_rational(items[1]), parse_rational(items[2]), int(items[3]), int(items[4]),
                     parse_rational(items[5]), parse_rational(items[6]))
            target = "charts"
        elif kind == "occurrence":
            require(len(items) == 18, "occurrence record shape")
            numbers = tuple(map(int, items[:14]))
            key = numbers[:4]
            value = numbers[4:5] + (numbers[5:8], numbers[8:11], numbers[11:14],
                                   tuple(map(parse_rational, items[14:])))
            target = "occurrences"
        elif kind == "slice":
            require(len(items) == 10, "slice record shape")
            key = tuple(map(int, items[:6]))
            value = tuple(map(parse_rational, items[6:]))
            target = "slices"
        elif kind == "upper":
            require(len(items) == 6, "upper record shape")
            key = tuple(map(int, items[:4]))
            value = tuple(map(parse_rational, items[4:]))
            target = "uppers"
        elif kind == "sc":
            require(len(items) == 9, "coincidence record shape")
            values = tuple(map(int, items))
            key, value = values[:3], values[3:]
            target = "sc"
        elif kind == "status":
            require(len(items) == 2, "status record shape")
            key, value, target = int(items[0]), items[1], "status"
        else:
            raise InvalidCertificate("unknown record: " + kind)
        require(key not in packet[target], "duplicate " + kind + " record")
        packet[target][key] = value
    require(schema_seen, "missing certificate schema")
    return packet


def parse_rational(token):
    require(bool(re.fullmatch(r"-?[0-9]+(?:/[0-9]+)?", token)), "non-rational token")
    try:
        value = Q(token)
    except (ValueError, ZeroDivisionError) as error:
        raise InvalidCertificate("invalid rational token") from error
    require(value.numerator.bit_length() <= 1024 and value.denominator.bit_length() <= 1024,
            "rational arithmetic budget")
    return value


def reference_packet():
    """Independent calibration producer, not the canonical research executable.

    Builds affine corners in Q[beta], whereas native builds rational interval
    images of boxes. This also permits standalone oracle regressions without a
    local Mojo installation. Native parity is a separate mandatory CI check.
    """
    packet = {"fixtures": {}, "charts": {}, "occurrences": {}, "slices": {},
              "uppers": {}, "sc": {}, "status": {}}
    beta_lo, beta_hi = root_bracket(64)
    kappa_lo, kappa_hi = interval_at(KAPPA)
    for fixture, sigma in enumerate(CONTROLS):
        radius = 40
        packet["fixtures"][fixture] = sigma, 2
        packet["charts"][fixture] = beta_lo, beta_hi, radius, 12, kappa_lo, kappa_hi
        packet["status"][fixture] = "upper_only_no_strict_density"
        for first, second in combinations(range(3), 2):
            witness = None
            for depth in range(1, 13):
                ww = words(sigma, depth)
                prefix_a = [0, 0, 0]
                prefix_b = [0, 0, 0]
                for position, (a, b) in enumerate(zip(ww[first], ww[second])):
                    if a == b and prefix_a == prefix_b:
                        witness = (depth, position, *prefix_a, int(a))
                        break
                    prefix_a[int(a)] += 1
                    prefix_b[int(b)] += 1
                if witness is not None:
                    break
            require(witness is not None, "control witness budget exhausted")
            packet["sc"][fixture, first, second] = witness
        for q in DEPTHS:
            groups = defaultdict(list)
            bq = stable_power(q)
            for source, position, letter, prefix in occurrences(sigma, q):
                coords = [[], []]
                shift = project(prefix)
                for corner in product((-radius, radius), repeat=2):
                    for coordinate in range(2):
                        point = add(shift[coordinate], add(scale(bq[coordinate][0], corner[0]),
                                                          scale(bq[coordinate][1], corner[1])))
                        coords[coordinate].append(interval_at(point))
                rect = tuple(value for coordinate in range(2) for value in (
                    Q(math.floor(16*min(x[0] for x in coords[coordinate])), 16),
                    Q(math.ceil(16*max(x[1] for x in coords[coordinate])), 16)))
                residue, parent = residue_key(q, prefix), residue_key(q-2, prefix)
                packet["occurrences"][fixture,q,source,position] = letter,prefix,residue,parent,rect
                groups[letter, residue].append(rect)
            for (letter, residue), rects in groups.items():
                packet["slices"][(fixture,q,letter)+residue] = hull(rects)
            for first, second in combinations(range(3), 2):
                raw = sum((intersection_area(hull(rects), hull(groups[second,residue]))
                           for (letter,residue),rects in groups.items()
                           if letter == first and (second,residue) in groups), Q(0))
                packet["uppers"][fixture,q,first,second] = raw, raw/(2**q)
    return packet


def serialize_packet(packet):
    lines = ["schema c4-finite-cylinder-v1"]
    for fixture in sorted(packet["fixtures"]):
        sigma, period = packet["fixtures"][fixture]
        lines.append(f"fixture {fixture} {'/'.join(sigma)} {period}")
        lines.append("chart " + " ".join(map(str, (fixture,)+packet["charts"][fixture])))
    for key, (letter,prefix,residue,parent,rect) in sorted(packet["occurrences"].items()):
        lines.append("occurrence " + " ".join(map(str, key+(letter,)+prefix+residue+parent+rect)))
    for key, rect in sorted(packet["slices"].items()):
        lines.append("slice " + " ".join(map(str, key+rect)))
    for key, bounds in sorted(packet["uppers"].items()):
        lines.append("upper " + " ".join(map(str, key+bounds)))
    for key, witness in sorted(packet["sc"].items()):
        lines.append("sc " + " ".join(map(str, key+witness)))
    for fixture, status in sorted(packet["status"].items()):
        lines.append(f"status {fixture} {status}")
    return "\n".join(lines)+"\n"


def literal_strict_system(sigma, supplied_states):
    """Complete normalized word factorization; never accepts a graph alone."""
    require(len(sigma) == 3 and all(0 < len(w) <= 64 and set(w) <= set("012") for w in sigma),
            "strict substitution domain")
    require(0 < len(supplied_states) <= 128, "strict state count cap")
    states = []
    for state in supplied_states:
        require(len(state) == 2, "strict state shape")
        u, v = state
        require(isinstance(u, str) and isinstance(v, str), "literal words required")
        require(0 < len(u) == len(v) <= 256 and set(u+v) <= set("012"), "strict word domain")
        require(u != v, "coincident state")
        delta = [0,0,0]
        for position, (a,b) in enumerate(zip(u,v)):
            delta[int(a)] += 1
            delta[int(b)] -= 1
            require(delta != [0,0,0] or position == len(u)-1, "reducible state")
        require(delta == [0,0,0], "unbalanced state")
        normalized = min((u,v),(v,u))
        require(normalized not in states, "duplicate normalized state")
        states.append(normalized)
    lookup = {state:i for i,state in enumerate(states)}
    children = []
    for u,v in states:
        top = "".join(sigma[int(c)] for c in u)
        bottom = "".join(sigma[int(c)] for c in v)
        require(len(top) == len(bottom) <= 16384, "inflated word cap or balance")
        delta, start, row = [0,0,0], 0, []
        for position, (a,b) in enumerate(zip(top,bottom), 1):
            delta[int(a)] += 1
            delta[int(b)] -= 1
            if delta == [0,0,0]:
                child = top[start:position],bottom[start:position]
                require(child[0] != child[1], "coincident child refutes strictness")
                normalized = min(child,child[::-1])
                require(normalized in lookup, "omitted literal child refutes closure")
                row.append(lookup[normalized])
                start = position
        require(start == len(top) and row, "incomplete factorization")
        children.append(tuple(row))
    return tuple(states), tuple(children)


def all_column_pair_cover(states, children, pair, steps):
    """Every source has a literal target after exactly steps; no SCC fiction."""
    require(pair in tuple(combinations(range(3),2)), "pair domain")
    require(type(steps) is int and 0 <= steps <= 32, "density depth budget")
    reached = [tuple(sorted((int(u[0]),int(v[0])))) == pair for u,v in states]
    for _ in range(steps):
        reached = [any(reached[child] for child in row) for row in children]
    require(all(reached), "pair has no verified common-depth cover of every source")


def verify_normalized_density(packet, fixture, pair, supplied_states, steps,
                              proposed_lower, normalization=CHART):
    """Bind a conservative density to actual complete words and the fixed chart.

    If every state has an e-descendant at depth t, b_e(n,j) >=
    beta^(n-t) L_j/Lmax. Thus 1/(beta_hi^t Lmax_hi) is a lower
    physical cut density. No PF vector, numeric frequency, or missing bounded
    strong-coincidence witness is accepted as this word premise.
    """
    require(normalization == CHART, "incompatible density normalization")
    require(fixture in range(2), "unsupported density substitution")
    require(isinstance(proposed_lower,(int,Q)) and not isinstance(proposed_lower,bool),
            "density input must be exact rational")
    require(proposed_lower > 0, "nonpositive density claim")
    sigma = CONTROLS[fixture]
    require(packet["fixtures"].get(fixture) == (sigma,2), "density substitution mismatch")
    chart = packet["charts"][fixture]
    validate_chart(sigma,chart)
    states,children = literal_strict_system(sigma,supplied_states)
    all_column_pair_cover(states,children,pair,steps)
    length_hi = max(interval_at(add(add(scale(ONE,u.count("0")),
                                          scale(BETA,u.count("1"))),
                                      scale(C,u.count("2"))))[1] for u,_ in states)
    certified_lower = 1/(chart[1]**steps * length_hi)
    require(proposed_lower <= certified_lower, "unsupported density magnitude")
    return certified_lower


def compare_equation_11(packet, fixture, depth, pair, supplied_states,
                        steps, proposed_lower, normalization=CHART):
    """A scalar comparison earns no certificate without the word/density layer."""
    require(type(fixture) is int and fixture in range(2), "density fixture domain")
    require(type(depth) is int and depth in DEPTHS, "density cylinder depth domain")
    require(pair in tuple(combinations(range(3),2)), "density pair domain")
    verify_packet(packet)
    verify_normalized_density(packet,fixture,pair,supplied_states,steps,
                              proposed_lower,normalization)
    upper = packet["uppers"][(fixture,depth)+pair][1]
    lower = packet["charts"][fixture][4] * proposed_lower
    gap = strict_arithmetic_gap(upper,packet["charts"][fixture][4],proposed_lower)
    return {"upper":str(upper), "forced_lower":str(lower),
            "gap":str(gap),
            "scope":"conditional incompatibility of the supplied hypotheses",
            "measure_proof":"separate written dependency"}


def strict_arithmetic_gap(upper, covolume_lower, density_lower):
    """Scalar arithmetic only: callers must establish all theorem premises."""
    require(all(isinstance(value,(int,Q)) and not isinstance(value,bool)
                for value in (upper,covolume_lower,density_lower)),
            "scalar inputs must be exact rational")
    require(upper >= 0 and covolume_lower > 0 and density_lower > 0,
            "invalid nonnegative area or positive lower input")
    gap = covolume_lower*density_lower - upper
    require(gap > 0, "equation (11) needs a strict inequality")
    return gap


def verify_packet(packet):
    require(set(packet) == {"fixtures","charts","occurrences","slices","uppers","sc","status"},
            "unsupported certificate fields")
    fixture_ids = set(range(len(CONTROLS)))
    for name in ("fixtures", "charts", "status"):
        require(set(packet[name]) == fixture_ids, "missing/extra " + name)
    expected_occurrences, expected_slices, expected_uppers, expected_sc = set(), set(), set(), set()
    result = {"schema": "c4-finite-cylinder-independent-replay-v1",
              "scope": "two productive controls; finite upper bounds only",
              "measure_proof": "written, not machine verified",
              "equation_11_certificate": False, "controls": []}
    for fixture, sigma in enumerate(CONTROLS):
        require(packet["fixtures"][fixture] == (sigma, 2), "substitution/period mismatch")
        require(words(sigma, 2)[0].startswith("0"), "fixed-point period lacks a witness")
        require(packet["status"][fixture] == "upper_only_no_strict_density", "unsupported density claim")
        chart = packet["charts"][fixture]
        chart_result = validate_chart(sigma, chart)
        radius = chart[2]
        control = {"images": list(sigma), "chart": CHART, "outer_certificate": chart_result,
                   "strong_coincidences": [], "depths": [], "strict_component_supplied": False}
        best_bounds = {}
        for first, second in combinations(range(3), 2):
            key = fixture, first, second
            expected_sc.add(key)
            require(key in packet["sc"], "missing productive-control witness")
            depth, position, p0, p1, p2, letter = packet["sc"][key]
            require(1 <= depth <= 12 and position >= 0 and 0 <= letter <= 2, "witness domain")
            ww = words(sigma, depth)
            require(position < min(len(ww[first]), len(ww[second])), "witness position")
            for source in (first, second):
                require(ww[source][position] == str(letter), "false coincidence letter")
                require(tuple(ww[source][:position].count(str(c)) for c in range(3)) == (p0,p1,p2),
                        "false coincidence prefix")
            control["strong_coincidences"].append({"pair": [first, second], "depth": depth,
                                                   "position": position, "prefix": [p0,p1,p2], "letter": letter})
        for q in DEPTHS:
            groups = defaultdict(list)
            parent_of = {}
            for source, position, letter, prefix in occurrences(sigma, q):
                key = fixture, q, source, position
                expected_occurrences.add(key)
                require(key in packet["occurrences"], "missing literal occurrence")
                recorded_letter, recorded_prefix, residue, parent, rect = packet["occurrences"][key]
                require((recorded_letter, recorded_prefix) == (letter, prefix), "relabeled literal occurrence")
                require(residue == residue_key(q, prefix), "incorrect residue class")
                require(parent == residue_key(q-2, prefix), "incorrect residue refinement")
                if q > 2:
                    require((fixture,q-2,letter)+parent in packet["slices"],
                            "fine occurrence refines an absent coarse letter slice")
                require(residue not in parent_of or parent_of[residue] == parent, "inconsistent bonding map")
                parent_of[residue] = parent
                validate_occurrence_rectangle(q, prefix, radius, rect)
                groups[letter, residue].append(rect)
            for (letter, residue), rects in groups.items():
                key = (fixture, q, letter) + residue
                expected_slices.add(key)
                require(packet["slices"].get(key) == hull(rects), "slice hull lacks complete occurrence coverage")
            representatives = quotient_representatives(q)
            fibers = defaultdict(int)
            for representative in representatives.values():
                fibers[residue_key(q-2, representative)] += 1
            require(len(fibers) == 2**(q-2) and set(fibers.values()) == {4}, "false quotient refinement degree")
            depth_result = {"depth": q, "quotient_index": 2**q,
                            "occurrences": sum(map(len, groups.values())),
                            "nonempty_slices": len(groups), "pairs": []}
            for first, second in combinations(range(3), 2):
                raw = Q(0)
                common = 0
                for residue in representatives:
                    left, right = groups.get((first, residue)), groups.get((second, residue))
                    if left and right:
                        common += 1
                        raw += intersection_area(hull(left), hull(right))
                upper = raw / (2**q)
                key = fixture, q, first, second
                expected_uppers.add(key)
                require(packet["uppers"].get(key) == (raw, upper), "incorrect Haar-weighted overlap upper bound")
                pair = first,second
                best_bounds[pair] = min(best_bounds.get(pair,upper),upper)
                depth_result["pairs"].append({"pair": [first, second], "common_residues": common,
                                               "summed_area": str(raw), "upper": str(upper),
                                               "best_upper_through_depth": str(best_bounds[pair]),
                                               "passes_necessary_upper_screen_U_lt_2": upper < 2,
                                               "residue_separation": common == 0})
            control["depths"].append(depth_result)
        result["controls"].append(control)
    for name, keys in (("occurrences", expected_occurrences), ("slices", expected_slices),
                       ("uppers", expected_uppers), ("sc", expected_sc)):
        require(set(packet[name]) == keys, "missing/extra " + name)
    result["verified_occurrences"] = len(expected_occurrences)
    result["verified_slices"] = len(expected_slices)
    result["verified_pair_bounds"] = len(expected_uppers)
    result["necessary_density_screen"] = {
        "physical_minimum_letter_length":"1",
        "minimum_noncoincident_balanced_state_length":"2",
        "pair_cut_density_upper":"1/2",
        "covolume_strict_upper":"4",
        "required_upper_bound":"U < 2 (necessary only)",
    }
    result["obstruction"] = [
        "No genuine fully strict component or positive strict-cut density is supplied.",
        "All pairs in both supported controls have literal strong-coincidence witnesses.",
        "The zero prefix of letters 0 and 1 occupies the same residue at every even depth.",
        "Fixed-depth slice hulls are outer bounds; M3 does not assert their convergence or an effective rate.",
    ]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native_output", type=Path)
    parser.add_argument("--density-input", type=Path,
                        help="optional literal strict-component input; invalid premises refuse a result")
    args = parser.parse_args()
    packet = parse_packet(args.native_output.read_text())
    if args.density_input is None:
        result = verify_packet(packet)
    else:
        density = parse_density_input(args.density_input.read_text())
        result = compare_equation_11(packet,**density)
    print(json.dumps(result, indent=2))


def parse_density_input(text):
    require(len(text.encode()) <= 65536, "density input byte budget")
    try:
        data = json.loads(text)
    except ValueError as error:
        raise InvalidCertificate("invalid density JSON") from error
    required = {"schema","fixture","depth","pair","supplied_states","steps",
                "proposed_lower","normalization"}
    require(isinstance(data,dict) and set(data) == required, "unsupported density fields")
    require(data.pop("schema") == "c4-strict-cut-density-v1", "density schema mismatch")
    require(type(data["fixture"]) is int and type(data["depth"]) is int and type(data["steps"]) is int,
            "density integer metadata")
    require(isinstance(data["pair"],list) and len(data["pair"]) == 2
            and all(type(x) is int for x in data["pair"]), "density pair shape")
    require(isinstance(data["supplied_states"],list)
            and all(isinstance(state,list) and len(state) == 2
                    and all(isinstance(word,str) for word in state) for state in data["supplied_states"]),
            "literal density state words required")
    require(isinstance(data["normalization"],str), "density normalization type")
    require(isinstance(data["proposed_lower"],str) and len(data["proposed_lower"]) <= 256,
            "exact rational density token required")
    data["pair"] = tuple(data["pair"])
    data["supplied_states"] = tuple(tuple(state) for state in data["supplied_states"])
    data["proposed_lower"] = parse_rational(data["proposed_lower"])
    return data


if __name__ == "__main__":
    main()
