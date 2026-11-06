"""All 18 literal source orders for the fixed non-unit incidence of #496.

No strong-coincidence witness is an input. Reuse the exact field/interval
arithmetic from the two-control oracle, but admit this complete finite class
only after all literal digits, graph occurrences and integer weights verify.
A cap failure is inconclusive; the written compact-set proof is separate.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations
from math import lcm
from pathlib import Path
import argparse
import hashlib
import json
import c4_pair_overlap_graph as core

SOURCES = tuple(("1", "".join(p), tail) for p in permutations("012")
                for tail in ("001", "010", "100"))
RADII = (24, 12)
DIGIT_BOUNDS = (Q(13, 2), Q(4))
RATE = 102
STATE_CAP = 16000
COORD_CAP = 40
ITERATION_CAP = 4000
SCHEMA = "c4-pair-overlap-class-v1"
require = core.require


def source(index):
    require(type(index) is int and 0 <= index < 18, "unsupported source-order index")
    return SOURCES[index]


def occurrences(index, depth):
    sigma = source(index)
    require(type(depth) is int and 0 <= depth <= 12, "literal depth budget")
    words = ("0", "1", "2")
    for _ in range(depth):
        words = tuple("".join(sigma[int(c)] for c in w) for w in words)
        require(all(len(w) <= 100000 for w in words), "literal word budget exhausted")
    for parent, word in enumerate(words):
        p = [0, 0, 0]
        for position, c in enumerate(word):
            yield parent, position, int(c), tuple(p)
            p[int(c)] += 1


def prefix_periods(index):
    """Actual first-letter cycles; this is NOT a coincidence test."""
    mapping = tuple(int(w[0]) for w in source(index))
    cycles = set()
    for letter in range(3):
        walk = []
        while letter not in walk:
            walk.append(letter)
            letter = mapping[letter]
        cycle = walk[walk.index(letter):]
        cycles.add(min(tuple(cycle[i:]+cycle[:i]) for i in range(len(cycle))))
    return sorted({len(c) for c in cycles})


@lru_cache(maxsize=18)
def certify_box(index):
    sigma = source(index)
    require(tuple(tuple(w.count(str(i)) for w in sigma) for i in range(3)) == core.M,
            "source incidence mismatch")
    require(core.root_bracket()[0]**2 > Q(103, 20), "Perron lower bound")
    a = core.interval((Q(0), Q(3, 2), Q(-1, 2)))
    b = core.interval((Q(-1), Q(-1, 2), Q(1, 2)))
    for coarse, fine in zip(core.COEFFICIENTS, (a, b)):
        require(Q(coarse[0], core.GRID) <= fine[0] <= fine[1] <= Q(coarse[1], core.GRID),
                "coarse stable-chart interval")
    bound = ((Q(473, 1000), Q(390, 1000)), (Q(147, 1000), Q(344, 1000)))
    block = core.stable_block()
    for i in range(2):
        for j in range(2):
            require(max(map(abs, core.interval(block[i][j]))) <= bound[i][j], "block contraction entry")
    # Exact common-denominator arithmetic avoids millions of Fraction objects.
    denominator = lcm(*(v.denominator for v in (*a, *b)))
    aa, bb = tuple(int(v*denominator) for v in a), tuple(int(v*denominator) for v in b)
    maxima, count = [0, 0], 0
    for _, _, _, (x, y, z) in occurrences(index, 12):
        maxima[0] = max(maxima[0], *(abs(denominator*x-v*y) for v in aa))
        maxima[1] = max(maxima[1], *(abs(denominator*z-v*y) for v in bb))
        count += 1
    for i in range(2):
        require(Q(maxima[i], denominator) <= DIGIT_BOUNDS[i], "underestimated complete digit bound")
        linear = sum(bound[i][j]*RADII[j] for j in range(2))
        require(linear < RADII[i] and linear+DIGIT_BOUNDS[i] <= RADII[i], "box invariance")
    require(count == 55583, "incomplete depth-twelve occurrence inventory")
    return {"block": 12, "literal_digits": count, "radii": list(RADII),
            "digit_bounds": list(map(str, DIGIT_BOUNDS)),
            "maximum_projected_digit_bounds": [str(Q(v, denominator)) for v in maxima],
            "beta_squared_lower": "103/20", "prefix_cycle_lengths": prefix_periods(index)}


def outside(z):
    for coordinate, (lo, hi), radius in zip((0, 2), core.COEFFICIENTS, RADII):
        ends = (core.GRID*z[coordinate]-lo*z[1], core.GRID*z[coordinate]-hi*z[1])
        if min(ends) > 2*radius*core.GRID or max(ends) < -2*radius*core.GRID:
            return True
    return False


def build_graph(index, state_cap=STATE_CAP):
    source(index)
    require(type(state_cap) is int and 3 <= state_cap <= STATE_CAP, "state cap domain")
    certify_box(index)
    digits = [[] for _ in range(3)]
    for parent, position, c, p in occurrences(index, 2):
        digits[c].append((parent, position, p))
    inv = core.inverse(core.power(core.M, 2))
    denominator = lcm(*(v.denominator for row in inv for v in row))
    numerator = tuple(tuple(int(v*denominator) for v in row) for row in inv)
    states = [core.canonical(c, d, (0, 0, 0)) for c, d in combinations(range(3), 2)]
    ids, rows = {s: i for i, s in enumerate(states)}, []
    residues = boxes = 0
    for c, d, x, y, z in states:
        targets = []
        for a, pos, p in digits[c]:
            for b, pos2, q in digits[d]:
                delta = (x+q[0]-p[0], y+q[1]-p[1], z+q[2]-p[2])
                candidate = tuple(sum(a*b for a, b in zip(row, delta)) for row in numerator)
                if any(v % denominator for v in candidate):
                    residues += 1
                    continue
                translated = tuple(v//denominator for v in candidate)
                if outside(translated):
                    boxes += 1
                    continue
                require(max(map(abs, translated)) <= COORD_CAP, "coordinate budget exhausted; inconclusive")
                child = core.canonical(a, b, translated)
                if child not in ids:
                    require(len(states) < state_cap, "state budget exhausted; inconclusive")
                    ids[child] = len(states)
                    states.append(child)
                targets.append(ids[child])  # Every occurrence, including repeated targets.
        rows.append(targets)
    return core.Graph(index, states, rows, residues, boxes)


def construct_weights(graph, iteration_cap=ITERATION_CAP):
    source(graph.fixture)
    require(type(iteration_cap) is int and 1 <= iteration_cap <= ITERATION_CAP, "iteration budget")
    w = [1]*len(graph.states)
    # Ordered monotone sweeps accelerate discovery. Acceptance checks every
    # final inequality independently; convergence is never presumed.
    for sweep in range(1, iteration_cap+1):
        unchanged = True
        for i, row in enumerate(graph.rows):
            value = 1+(20*sum(w[j] for j in row)+RATE-1)//RATE
            require(value <= core.WEIGHT_CAP, "weight budget exhausted; inconclusive")
            require(value >= w[i], "nonmonotone weight construction")
            if value != w[i]:
                unchanged = False
                w[i] = value
        if unchanged:
            return w, sweep, core.validate_weights(graph, w, RATE)
    raise core.InvalidCertificate("iteration budget exhausted; inconclusive")


def validate_supplied_graph(index, states, rows, weights):
    actual = build_graph(index)
    require(states == actual.states and rows == actual.rows, "incomplete occurrence graph")
    core.validate_weights(actual, weights, RATE)
    return actual


@lru_cache(maxsize=18)
def reference(index):
    graph = build_graph(index)
    return graph, *construct_weights(graph)


def packet_lines(graph, weights, sweeps):
    i = graph.fixture
    yield f"graph {i} {len(graph.states)} {sum(map(len, graph.rows))} {graph.residue_rejections} {graph.box_rejections} {sweeps} 102 20"
    for j, (s, row, w) in enumerate(zip(graph.states, graph.rows, weights)):
        yield "node "+" ".join(map(str, (i, j, *s, w)))
        yield "row "+" ".join(map(str, (i, j, len(row), *row)))


def summary(index):
    graph, w, sweeps, gap = reference(index)
    digest = hashlib.sha256()
    for line in packet_lines(graph, w, sweeps):
        digest.update((line+"\n").encode())
    upper = [Q(1152*v)*Q(102, 103)**2304 for v in w[:3]]
    require(all(u < Q(1, 10) for u in upper), "claimed rational upper bound failed")
    return {"source_index": index, "sigma": list(source(index)), "states": len(graph.states),
            "occurrence_edges": sum(map(len, graph.rows)), "residue_rejections": graph.residue_rejections,
            "box_rejections": graph.box_rejections, "weight_sweeps": sweeps,
            "minimum_integer_gap": gap, "maximum_weight": max(w), "root_weights": w[:3],
            "maximum_offset_coordinate": max(abs(v) for s in graph.states for v in s[2:]),
            "zero_offset_diagonal_states": sum(s[0] == s[1] and s[2:] == (0, 0, 0) for s in graph.states),
            "rate": "51/10", "ratio_upper": "102/103", "all_roots_below_one_tenth_at_2304_blocks": True,
            "canonical_graph_sha256": digest.hexdigest(), "chart": certify_box(index)}


def receipt():
    return {"schema": SCHEMA, "source_count": 18, "unshifted_pair_count": 54,
            "scope": "all source orders of one fixed non-unit M; no SC witness input; not general PSC",
            "base_head": "d5833e3ad2908cec847002b797d12c73d48045a4",
            "sources": [summary(i) for i in range(18)]}


def verify_source_stream(stream, index):
    """Compare every serialized field with the independently rebuilt source.

    Deliberately stronger than integer-weight validation: deleting an occurrence
    can preserve every row inequality while destroying canonical data parity.
    The caller owns schema, complete source-domain and end-of-file checks.
    """
    graph, w, sweeps, _ = reference(index)
    for line in packet_lines(graph, w, sweeps):
        require(stream.readline().rstrip("\n") == line, "native complete graph mismatch")


def verify_native_file(path):
    require(path.stat().st_size <= 40000000, "native packet byte budget")
    with path.open() as stream:
        require(stream.readline().rstrip("\n") == "schema "+SCHEMA, "wrong class schema")
        for index in range(18):
            verify_source_stream(stream, index)
        require(stream.read() == "", "trailing or duplicate native records")
    return receipt()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=int)
    parser.add_argument("--native", type=Path)
    parser.add_argument("--emit-packet", action="store_true")
    args = parser.parse_args()
    if args.native:
        result = verify_native_file(args.native)
    elif args.emit_packet:
        print("schema "+SCHEMA)
        for i in range(18):
            graph, w, sweeps, _ = reference(i)
            print("\n".join(packet_lines(graph, w, sweeps)))
        return
    else:
        result = summary(args.source) if args.source is not None else receipt()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
