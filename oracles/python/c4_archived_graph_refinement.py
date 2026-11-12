"""Independent full-address decoder for the archived named paired graphs.

Canonical implementation: kernel/psc/c4_archived_graph_refinement.mojo.
The original source and sharp box are authenticated before every finite row
is checked.  Prefixes are independently rescanned, rational elimination
solves the residue equation, and direct forward positions check the ordered
inverse lift.  Complete BFS births certify rooted finite inverse ancestry.

Passing this oracle supplies finite executable evidence.  It is not a Lean
deserializer, an all-strict-packet theorem, or evidence of positive overlap.
"""

from collections import Counter
from dataclasses import dataclass, replace
from fractions import Fraction
from functools import lru_cache
from itertools import zip_longest
from math import lcm
from pathlib import Path
import argparse
import hashlib
import json

import c4_pair_overlap_graph as archive


SCHEMA = "c4-archived-graph-refinement-v1"
ROOT = Path(__file__).resolve().parents[2]
ARCHIVE_REVISION = "765bb39c83035b5ccacbc8115ecc26acc4111865"
SOURCES = (((1,), (0, 2, 1), (0, 0, 1)), ((1,), (0, 1, 2), (0, 0, 1)))
ROOTS = ((0, 1, 0, 0, 0), (0, 2, 0, 0, 0), (1, 2, 0, 0, 0))
RADII = (16, 8)
STATE_CAP = 16000


class InvalidCertificate(ValueError):
    """Refuse an incomplete finite binding without making a theorem claim."""


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def integer(value, lo=None, hi=None):
    return type(value) is int and (lo is None or lo <= value) and (hi is None or value <= hi)


def source_images(fixture):
    require(integer(fixture, 0, 1), "original named fixture required")
    return SOURCES[fixture]


def square_words(images):
    return tuple(tuple(c for a in word for c in images[a]) for word in images)


def incidence(words):
    return tuple(tuple(word.count(c) for word in words) for c in range(3))


def mv(matrix, vector):
    return tuple(sum(x*y for x, y in zip(row, vector)) for row in matrix)


@lru_cache(maxsize=1)
def inverse_rows():
    square = incidence(square_words(SOURCES[0]))
    # Historical independent Gaussian elimination is generic matrix arithmetic;
    # it does not consume the native adjugate or any native graph decisions.
    inverse = archive.inverse(square)
    denominator = lcm(*(q.denominator for row in inverse for q in row))
    numerator = tuple(tuple(int(denominator*q) for q in row) for row in inverse)
    require(archive.mm(square, numerator)
            == tuple(tuple(denominator*int(i == j) for j in range(3)) for i in range(3)),
            "fractional inverse does not reconstruct the original square")
    return square, denominator, numerator


def integral_ancestor(delta):
    square, denominator, numerator = inverse_rows()
    values = mv(numerator, delta)
    if any(v % denominator for v in values):
        return None
    result = tuple(v // denominator for v in values)
    require(mv(square, result) == delta, "wrong direction in inverse equation")
    return result


def swap(state):
    return state[1], state[0], *(-x for x in state[2:])


def canonical(state):
    return min(state, swap(state))


def outside_box(offset):
    # Rational interval endpoints independently reproduce the integer native
    # predicate.  Equality and inconclusive separation are always retained.
    for coordinate, limits, radius in ((0, (828911, 828912), 16),
                                        (2, (440619, 440620), 8)):
        ends = [Fraction(offset[coordinate]) - Fraction(q, 1000000)*offset[1]
                for q in limits]
        if min(ends) > 2*radius or max(ends) < -2*radius:
            return True
    return False


@dataclass(frozen=True)
class Digit:
    selected: int
    parent: int
    position: int
    prefix: tuple
    outer: int
    local: int


@dataclass(frozen=True)
class Slot:
    target: int
    top: int
    bottom: int
    swapped: int


@dataclass(frozen=True)
class Binding:
    fixture: int
    images: tuple
    words: tuple
    digits: tuple
    states: tuple
    rows: tuple
    births: tuple
    depths: tuple
    residue: int
    box: int
    period: int = 2
    radii: tuple = RADII
    direction: int = 0


def literal_digits(images):
    words = square_words(images)
    digits = []
    for parent, word in enumerate(words):
        addresses = tuple((outer, local)
                          for outer, a in enumerate(images[parent])
                          for local in range(len(images[a])))
        require(len(addresses) == len(word), "nested address inventory")
        for position, selected in enumerate(word):
            outer, local = addresses[position]
            require(images[images[parent][outer]][local] == selected,
                    "nested address selects a different actual letter")
            # Full prefix rescan is independent of the native accumulator.
            prefix = tuple(word[:position].count(c) for c in range(3))
            digits.append(Digit(selected, parent, position, prefix, outer, local))
    require(len(digits) == 15, "incomplete original two-step occurrence inventory")
    return tuple(digits)


def _validate_domain(states):
    require(type(states) is tuple and 3 <= len(states) <= STATE_CAP,
            "finite archived domain dimensions")
    for state in states:
        require(type(state) is tuple and len(state) == 5
                and all(integer(x, 0, 2) for x in state[:2])
                and all(integer(x, -32, 32) for x in state[2:]),
                "malformed or resource-exhausted packet")
        require(state == canonical(state) and state != swap(state),
                "noncanonical packet or fixed track swap")
        require(not outside_box(state[2:]), "domain packet outside original sharp box")
    require(len(set(states)) == len(states) and states[:3] == ROOTS,
            "duplicate packet or graph/root domain mismatch")


@lru_cache(maxsize=4)
def _full_rows(states, digits):
    """All integral admitted candidates, including ones missing from domain."""
    lookup = {state: i for i, state in enumerate(states)}
    by_letter = tuple(tuple(i for i, d in enumerate(digits) if d.selected == c) for c in range(3))
    rows = []
    residue = box = 0
    for state in states:
        row = []
        for top in by_letter[state[0]]:
            p = digits[top]
            for bottom in by_letter[state[1]]:
                q = digits[bottom]
                delta = tuple(state[k+2] + q.prefix[k] - p.prefix[k] for k in range(3))
                offset = integral_ancestor(delta)
                if offset is None:
                    residue += 1
                    continue
                if outside_box(offset):
                    box += 1
                    continue
                require(max(map(abs, offset)) <= 32, "coordinate cap exhausted; no geometric verdict")
                raw = p.parent, q.parent, *offset
                representative = canonical(raw)
                require(representative in lookup, "admitted integral inverse ancestor missing from domain")
                row.append(Slot(lookup[representative], top, bottom, int(raw != representative)))
        rows.append(tuple(row))
    return tuple(rows), residue, box


def _births(rows):
    births = [None]*len(rows)
    depths = [0]*len(rows)
    for i in range(3):
        births[i] = (-1, -1)
    next_discovery = 3
    for source, row in enumerate(rows):
        for position, slot in enumerate(row):
            if births[slot.target] is None:
                require(source < slot.target == next_discovery,
                        "inverse ancestry is incomplete or not in first discovery order")
                births[slot.target] = source, position
                depths[slot.target] = depths[source]+1
                next_discovery += 1
    require(next_discovery == len(rows), "finite domain contains an unrooted inverse ancestor")
    return tuple(births), tuple(depths)


def check_ordered_lift(binding):
    """Actual forward positions independently check both sheets and transpose."""
    lift = tuple(packet for state in binding.states for packet in (state, swap(state)))
    require(len(set(lift)) == len(lift), "fixed swap or duplicate ordered representative")
    lookup = {packet: i for i, packet in enumerate(lift)}
    inverse_edges = set()
    transposed = Counter()
    for source, row in enumerate(binding.rows):
        for slot in row:
            p, q = binding.digits[slot.top], binding.digits[slot.bottom]
            key = 2*slot.target+slot.swapped, p.position, q.position, 2*source
            mate = 2*slot.target+1-slot.swapped, q.position, p.position, 2*source+1
            require(key != mate and key not in inverse_edges and mate not in inverse_edges,
                    "duplicate ordered positional occurrence")
            inverse_edges.update((key, mate))
            transposed[slot.target, source] += 1
    forward_edges = set()
    counts = Counter()
    matrix = incidence(binding.words)
    for source, parent in enumerate(lift):
        base = mv(matrix, parent[2:])
        for i, top in enumerate(binding.words[parent[0]]):
            p = tuple(binding.words[parent[0]][:i].count(c) for c in range(3))
            for j, bottom in enumerate(binding.words[parent[1]]):
                q = tuple(binding.words[parent[1]][:j].count(c) for c in range(3))
                child = top, bottom, *(base[k]+p[k]-q[k] for k in range(3))
                target = lookup.get(child)
                if target is not None:
                    forward_edges.add((source, i, j, target))
                    if source % 2 == 0:
                        counts[source//2, target//2] += 1
    require(forward_edges == inverse_edges,
            "ordered forward/inverse direction, address or multiplicity mismatch")
    require(counts == transposed, "incoming counts differ from the complete forward transpose")
    return len(forward_edges)


def bind_graph(graph):
    images = source_images(graph.fixture)
    words = square_words(images)
    digits = literal_digits(images)
    require(incidence(images) == archive.M and incidence(words) == inverse_rows()[0],
            "original source/power incidence mismatch")
    states = tuple(tuple(s) for s in graph.states)
    _validate_domain(states)
    require(len(graph.rows) == len(states)
            and all(len(row) <= 225 and all(integer(j, 0, len(states)-1) for j in row)
                    for row in graph.rows), "malformed historical target inventory")
    rows, residue, box = _full_rows(states, digits)
    require(tuple(tuple(row) for row in graph.rows)
            == tuple(tuple(slot.target for slot in row) for row in rows),
            "archived row omits, duplicates, reverses or reorders a literal occurrence")
    require(integer(graph.residue_rejections) and integer(graph.box_rejections)
            and (residue, box) == (graph.residue_rejections, graph.box_rejections),
            "exhaustive residue/box exclusion totals differ")
    births, depths = _births(rows)
    binding = Binding(graph.fixture, images, words, digits, states, rows, births, depths, residue, box)
    check_ordered_lift(binding)
    return binding


def validate_binding(binding):
    require(type(binding) is Binding, "binding record required")
    require(integer(binding.period) and binding.period == 2
            and binding.radii == RADII and all(integer(x) for x in binding.radii)
            and integer(binding.direction) and binding.direction == 0,
            "wrong block, sharp box or incoming direction")
    require(type(binding.images) is tuple
            and all(type(word) is tuple and all(integer(c, 0, 2) for c in word) for word in binding.images)
            and binding.images == source_images(binding.fixture)
            and type(binding.words) is tuple
            and all(type(word) is tuple and all(integer(c, 0, 2) for c in word) for word in binding.words)
            and binding.words == square_words(binding.images), "original substitution identity mismatch")
    require(type(binding.digits) is tuple and all(
        type(d) is Digit and all(integer(x) for x in (d.selected, d.parent, d.position, d.outer, d.local))
        and type(d.prefix) is tuple and len(d.prefix) == 3 and all(integer(x) for x in d.prefix)
        for d in binding.digits), "malformed literal address")
    require(binding.digits == literal_digits(binding.images), "complete literal parent/local addresses mismatch")
    _validate_domain(binding.states)
    require(type(binding.rows) is tuple and len(binding.rows) == len(binding.states), "row dimensions")
    for row in binding.rows:
        require(type(row) is tuple and len(row) <= 225, "literal row resource budget")
        for slot in row:
            require(type(slot) is Slot and integer(slot.target, 0, len(binding.states)-1)
                    and integer(slot.top, 0, 14) and integer(slot.bottom, 0, 14)
                    and integer(slot.swapped, 0, 1), "malformed positional edge")
    rows, residue, box = _full_rows(binding.states, binding.digits)
    require(binding.rows == rows, "missing or changed literal row refinement")
    require(integer(binding.residue) and integer(binding.box)
            and (binding.residue, binding.box) == (residue, box), "unjustified residue/box exclusions")
    births, depths = _births(rows)
    require(type(binding.births) is tuple and all(
        type(b) is tuple and len(b) == 2 and all(integer(x) for x in b) for b in binding.births)
        and type(binding.depths) is tuple and all(integer(x) for x in binding.depths)
        and binding.births == births and binding.depths == depths,
            "incomplete inverse ancestry or inconsistent discovery witness")
    check_ordered_lift(binding)
    return binding


def as_graph(binding):
    return archive.Graph(binding.fixture, list(binding.states),
                         [[s.target for s in row] for row in binding.rows], binding.residue, binding.box)


def validate_contraction(binding, weights):
    validate_binding(binding)
    return archive.validate_weights(as_graph(binding), weights, (99, 101)[binding.fixture])


def negative_controls(fixture):
    """Observe named structural rejections on a complete real finite graph."""
    binding, weights, _, _ = reference(fixture)
    observed = {}

    def reject(name, mutation, numeric=False, direct=False):
        if numeric:
            archive.validate_weights(as_graph(mutation), weights, (99, 101)[fixture])
        try:
            (check_ordered_lift if direct else validate_binding)(mutation)
        except InvalidCertificate as exc:
            observed[name] = {'rejected': True, 'reason': str(exc)}
            if numeric:
                observed[name]['numeric_subinvariance_still_valid'] = True
            return
        raise InvalidCertificate('negative control was admitted: '+name)

    victim = next(i for i, row in enumerate(binding.rows)
                  if len({s.target for s in row}) < len(row))
    row = binding.rows[victim]
    omitted = next(i for i, s in enumerate(row) if s.target in {x.target for x in row[:i]})
    rows = list(binding.rows)
    rows[victim] = row[:omitted]+row[omitted+1:]
    reject('omitted_repeated_positional_edge', replace(binding, rows=tuple(rows)), numeric=True)
    reject('swapped_graph_direction', replace(binding, direction=1), numeric=True)
    reject('wrong_24_12_box', replace(binding, radii=(24, 12)), numeric=True)
    reject('wrong_block_power', replace(binding, period=1), numeric=True)
    births = list(binding.births)
    births[3] = (-1, -1)
    reject('incomplete_inverse_ancestry', replace(binding, births=tuple(births)), numeric=True)
    states = list(binding.states)
    states[3] = states[4]
    reject('graph_domain_mismatch', replace(binding, states=tuple(states)), numeric=True)
    reject('different_original_substitution', replace(binding, images=SOURCES[1-fixture]), numeric=True)
    digits = list(binding.digits)
    digits[0] = replace(digits[0], local=digits[0].local+1)
    reject('wrong_nested_local_address', replace(binding, digits=tuple(digits)), numeric=True)
    digits = list(binding.digits)
    digits[0] = replace(digits[0], parent=(digits[0].parent+1) % 3)
    reject('wrong_parent_address', replace(binding, digits=tuple(digits)), numeric=True)
    reject('unjustified_residue_exclusion', replace(binding, residue=binding.residue+1), numeric=True)
    reject('unjustified_box_exclusion', replace(binding, box=binding.box+1), numeric=True)
    first = next(i for i, row in enumerate(binding.rows) if row)
    rows = list(binding.rows)
    slot = replace(rows[first][0], swapped=1-rows[first][0].swapped)
    rows[first] = (slot,)+rows[first][1:]
    flipped = replace(binding, rows=tuple(rows))
    reject('flipped_track_swap', flipped, numeric=True)
    reject('direct_forward_inverse_disagreement', flipped, numeric=True, direct=True)
    transposed = [[] for _ in binding.states]
    for i, row in enumerate(binding.rows):
        for slot in row:
            transposed[slot.target].append(replace(slot, target=i))
    reject('transposed_actual_rows', replace(binding, rows=tuple(tuple(r) for r in transposed)))
    digits = list(binding.digits)
    digits[0] = replace(digits[0], parent=False)
    reject('boolean_address_alias', replace(binding, digits=tuple(digits)), numeric=True)
    return observed


@lru_cache(maxsize=2)
def reference(fixture):
    source_images(fixture)
    graph, weights, iterations, gap = archive.reference(fixture)
    binding = bind_graph(graph)
    return binding, tuple(weights), iterations, gap


def graph_lines(binding, weights, iterations, gap):
    f = binding.fixture
    edges = sum(map(len, binding.rows))
    swapped = sum(s.swapped for row in binding.rows for s in row)
    repeated = sum(len(row)-len({s.target for s in row}) for row in binding.rows)
    yield "graph " + " ".join(map(str, (f, binding.period, *binding.radii, binding.direction,
                                        len(binding.states), edges, binding.residue, binding.box,
                                        swapped, repeated, max(binding.depths), iterations, gap)))
    for parent, word in enumerate(binding.images):
        yield "image " + " ".join(map(str, (f, parent, len(word), *word)))
    for i, d in enumerate(binding.digits):
        yield "digit " + " ".join(map(str, (f, i, d.selected, d.parent, d.position, *d.prefix, d.outer, d.local)))
    for i, (state, row, weight, birth, depth) in enumerate(zip(binding.states, binding.rows, weights, binding.births, binding.depths)):
        yield "node " + " ".join(map(str, (f, i, *state, weight, *birth, depth)))
        yield f"row {f} {i} {len(row)}"
        for ordinal, slot in enumerate(row):
            yield "slot " + " ".join(map(str, (f, i, ordinal, slot.target, slot.top, slot.bottom, slot.swapped)))


def receipt():
    historical = json.loads((ROOT/'evidence/c4-pair-overlap-graph-2026-11-05/receipt.json').read_text())
    require(historical == archive.receipt(), "archived complete graph digest or potential changed")
    fixtures = []
    for f in range(2):
        binding, weights, iterations, gap = reference(f)
        content = "\n".join(graph_lines(binding, weights, iterations, gap))+"\n"
        old = historical['fixtures'][f]
        require(hashlib.sha256(archive.graph_text(as_graph(binding), weights, iterations).encode()).hexdigest()
                == old['canonical_graph_sha256'], "addressed decoder changed historical graph bytes")
        fixtures.append({
            'fixture': f, 'sigma': old['sigma'], 'period': 2, 'radii': [16, 8],
            'states': len(binding.states), 'positional_edges': sum(map(len, binding.rows)),
            'literal_block_positions': len(binding.digits),
            'ordered_lift_positions': 2*sum(map(len, binding.rows)),
            'swapped_slots': sum(s.swapped for row in binding.rows for s in row),
            'repeated_endpoint_slots': sum(len(row)-len({s.target for s in row}) for row in binding.rows),
            'maximum_rooted_inverse_depth': max(binding.depths),
            'residue_rejections': binding.residue, 'strict_box_rejections': binding.box,
            'historical_graph_sha256': old['canonical_graph_sha256'],
            'addressed_packet_sha256': hashlib.sha256(content.encode()).hexdigest(),
            'rate': old['rate'], 'minimum_integer_gap': gap,
            'root_weights': list(weights[:3]), 'weight_iterations': iterations,
        })
    sources = [
        'kernel/psc/c4_archived_graph_refinement.mojo',
        'kernel/c4_archived_graph_refinement.mojo',
        'kernel/tests/test_c4_archived_graph_refinement.mojo',
        'oracles/python/c4_archived_graph_refinement.py',
        'tests/test_c4_archived_graph_refinement_oracle.py',
        'kernel/psc/c4_pair_overlap_graph.mojo',
        'kernel/psc/c4_literal_inverse_binding.mojo',
        'kernel/psc/c4_finite_cylinder_overlap.mojo',
        'kernel/psc/c4_nonunit_residue_occupancy.mojo',
        'oracles/python/c4_pair_overlap_graph.py',
        'evidence/c4-pair-overlap-graph-2026-11-05/receipt.json',
    ]
    return {'schema': SCHEMA, 'historical_snapshot_revision': ARCHIVE_REVISION,
            'scope': 'source-bound finite rooted inverse rows; sharp-box geometry and arbitrary strict-packet representation are separate obligations',
            'source_sha256': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
            'fixtures': fixtures}


def verify_native(text):
    require(len(text.encode()) <= 16000000, "native packet byte budget")
    lines = iter(text.splitlines())
    require(next(lines, None) == 'schema '+SCHEMA, "wrong addressed packet schema")
    def expected():
        for f in range(2):
            yield from graph_lines(*reference(f))
    for ordinal, (actual, wanted) in enumerate(zip_longest(lines, expected())):
        require(actual == wanted, f"native full address/domain/ancestry mismatch at line {ordinal+2}")
    return receipt()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native', type=Path)
    parser.add_argument('--emit-packet', action='store_true')
    parser.add_argument('--controls', action='store_true')
    args = parser.parse_args()
    if args.native:
        result = verify_native(args.native.read_text())
    elif args.emit_packet:
        print('schema '+SCHEMA)
        for f in range(2):
            print('\n'.join(graph_lines(*reference(f))))
        return
    else:
        result = receipt()
    if args.controls:
        result['observed_negative_controls'] = {str(f): negative_controls(f) for f in range(2)}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
