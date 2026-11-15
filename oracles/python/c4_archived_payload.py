"""Independent decode of the complete original archived Lean payload.

Canonical producer: kernel/c4_archived_lean_export.mojo.  This verifier reads
both the decoded source records and their packed rows/index.  It independently
checks bit fields, exact lookup shape, every literal occurrence, inverse
closure, root discovery, original graph digests and integer potentials.

This is executable boundary evidence.  The separate Lean compiler, typed
consumer audit and transitive axiom audit supply the formal acceptance.
"""

from dataclasses import dataclass, replace
from pathlib import Path
import argparse
import hashlib
import json
import re

import c4_archived_graph_refinement as refinement


SCHEMA = "c4-archived-payload-v1"
ROOT = Path(__file__).resolve().parents[2]
InvalidCertificate = refinement.InvalidCertificate
require = refinement.require
integer = refinement.integer
HEADER_WIDTHS = (20, 8, 25, 14, 8, 5)
SLOT_WIDTH = 23


@dataclass(frozen=True)
class Payload:
    binding: refinement.Binding
    weights: tuple
    sweeps: int
    minimum_gap: int
    summary: tuple
    packed: tuple
    lookup: tuple


def state_code(state):
    require(type(state) is tuple and len(state) == 5
            and all(integer(c, 0, 2) for c in state[:2])
            and all(integer(c, -32, 32) for c in state[2:]),
            "packed state outside original coordinate/letter budget")
    c, d, x, y, z = state
    return c + (d << 2) + ((x+64) << 4) + ((y+64) << 11) + ((z+64) << 18)


def orbit_key(state):
    return min(state_code(state), state_code(refinement.swap(state)))


def encode_row(state, weight, birth, depth, slots):
    """Independent integer-shift calibration, not a canonical producer."""
    fields = (weight, len(slots), state_code(state), birth[0]+1, birth[1]+1, depth)
    bits = shift = 0
    for field, width in zip(fields, HEADER_WIDTHS):
        require(integer(field, 0, (1 << width)-1), "row field overflow")
        bits |= field << shift
        shift += width
    for slot in slots:
        require(type(slot) is refinement.Slot and integer(slot.target, 0, 16383)
                and integer(slot.top, 0, 14) and integer(slot.bottom, 0, 14)
                and integer(slot.swapped, 0, 1), "slot field overflow")
        code = slot.target | (slot.top << 14) | (slot.bottom << 18) | (slot.swapped << 22)
        bits |= code << shift
        shift += SLOT_WIDTH
    return bits


def decode_row(bits):
    require(integer(bits, 0), "packed row must be a nonnegative exact integer")
    fields = []
    for width in HEADER_WIDTHS:
        fields.append(bits & ((1 << width)-1))
        bits >>= width
    weight, degree, code, parent, ordinal, depth = fields
    state = (code & 3, (code >> 2) & 3,
             ((code >> 4) & 127)-64, ((code >> 11) & 127)-64,
             ((code >> 18) & 127)-64)
    require(state_code(state) == code, "noncanonical packed state")
    require(1 <= weight <= 1000000 and degree <= 225,
            "packed positive potential or degree budget")
    slots = []
    for _ in range(degree):
        target = bits & 16383
        top = (bits >> 14) & 15
        bottom = (bits >> 18) & 15
        swapped = (bits >> 22) & 1
        require(top < 15 and bottom < 15, "packed literal address outside original source")
        slots.append(refinement.Slot(target, top, bottom, swapped))
        bits >>= SLOT_WIDTH
    require(bits == 0, "hidden payload after final positional edge")
    return state, weight, (parent-1, ordinal-1), depth, tuple(slots)


def lookup_records(states):
    """Independent midpoint tree, retaining original graph IDs exactly."""
    keyed = sorted((orbit_key(state), i) for i, state in enumerate(states))
    require(len({key for key, _ in keyed}) == len(states), "duplicate track-swap lookup key")
    out = []

    def walk(lo, hi, path):
        if lo == hi:
            return
        mid = (lo+hi)//2
        key, row = keyed[mid]
        out.append((path, key, row))
        walk(lo, mid, 2*path)
        walk(mid+1, hi, 2*path+1)

    walk(0, len(keyed), 1)
    return tuple(out)


class _Reader:
    def __init__(self, text):
        require(type(text) is str and len(text.encode()) <= 32000000,
                "archived payload byte budget")
        self.lines = text.splitlines()
        require(self.lines and self.lines[0] == "schema "+SCHEMA,
                "wrong archived payload schema")
        self.at = 1

    def take(self, tag, length=None):
        require(self.at < len(self.lines), "incomplete archived payload")
        line = self.lines[self.at]
        self.at += 1
        fields = line.split(" ")
        require(fields[0] == tag and all(re.fullmatch(r"0|[1-9][0-9]*|-[1-9][0-9]*", s)
                                       for s in fields[1:]),
                f"noncanonical {tag} record at line {self.at}")
        values = tuple(map(int, fields[1:]))
        require(length is None or len(values) == length,
                f"malformed {tag} record at line {self.at}")
        return values


def _read_fixture(reader, fixture):
    header = reader.take("graph", 14)
    f, power, rx, ry, direction, count, edges, residue, box, swapped, repeated, depth, sweeps, gap = header
    require(f == fixture and 3 <= count <= refinement.STATE_CAP, "wrong fixture or graph dimensions")
    images = []
    for parent in range(3):
        values = reader.take("image")
        require(len(values) >= 3 and values[:2] == (fixture, parent)
                and len(values[3:]) == values[2], "incomplete original source image")
        images.append(values[3:])
    images = tuple(images)
    require(images == refinement.source_images(fixture), "original substitution identity mismatch")
    digits = []
    for i in range(15):
        values = reader.take("digit", 10)
        require(values[:2] == (fixture, i), "missing or reordered literal digit")
        _, _, selected, parent, position, p0, p1, p2, outer, local = values
        digits.append(refinement.Digit(selected, parent, position, (p0, p1, p2), outer, local))
    states, weights, births, depths, rows = [], [], [], [], []
    for i in range(count):
        values = reader.take("node", 11)
        require(values[:2] == (fixture, i), "missing or reordered original graph state")
        states.append(values[2:7])
        weights.append(values[7])
        births.append(values[8:10])
        depths.append(values[10])
        rf, ri, degree = reader.take("row", 3)
        require((rf, ri) == (fixture, i) and 0 <= degree <= 225, "wrong literal row degree or identity")
        row = []
        for k in range(degree):
            values = reader.take("slot", 7)
            require(values[:3] == (fixture, i, k), "omitted, duplicated or reordered positional edge")
            row.append(refinement.Slot(*values[3:]))
        rows.append(tuple(row))
    packed = []
    for i in range(count):
        values = reader.take("packed", 3)
        require(values[:2] == (fixture, i), "missing or reordered raw packed row")
        packed.append(values[2])
    lookup = []
    for _ in range(count):
        values = reader.take("lookup", 4)
        require(values[0] == fixture, "lookup belongs to a different original fixture")
        lookup.append(values[1:])
    binding = refinement.Binding(fixture, images, refinement.square_words(images), tuple(digits),
                                 tuple(states), tuple(rows), tuple(births), tuple(depths), residue, box,
                                 power, (rx, ry), direction)
    return Payload(binding, tuple(weights), sweeps, gap,
                   (edges, swapped, repeated, depth), tuple(packed), tuple(lookup))


def parse_payload(text, fixture=None):
    require(fixture is None or integer(fixture, 0, 1), "unsupported payload fixture")
    reader = _Reader(text)
    payloads = tuple(_read_fixture(reader, f) for f in ((fixture,) if fixture is not None else range(2)))
    require(reader.at == len(reader.lines), "unexpected or duplicated trailing payload records")
    return payloads


def validate_payload(payload):
    require(type(payload) is Payload, "archived payload record required")
    binding = payload.binding
    # These independent checks exhaust actual source positions and solve the
    # residue equations by rational elimination, not by native packed fields.
    refinement.validate_binding(binding)
    count = len(binding.states)
    require(type(payload.weights) is tuple and len(payload.weights) == count,
            "incomplete original positive potential")
    gap = refinement.archive.validate_weights(refinement.as_graph(binding), payload.weights,
                                              (99, 101)[binding.fixture])
    require(integer(payload.minimum_gap) and payload.minimum_gap == gap
            and integer(payload.sweeps, 1, 4000), "potential gap or iteration metadata mismatch")
    expected_summary = (sum(map(len, binding.rows)),
                        sum(s.swapped for row in binding.rows for s in row),
                        sum(len(row)-len({s.target for s in row}) for row in binding.rows),
                        max(binding.depths))
    require(payload.summary == expected_summary, "decoded summary differs from full positional rows")
    require(type(payload.packed) is tuple and len(payload.packed) == count,
            "missing packed table leaf")
    for i, bits in enumerate(payload.packed):
        require(decode_row(bits) == (binding.states[i], payload.weights[i], binding.births[i],
                                    binding.depths[i], binding.rows[i]),
                f"raw packed fields disagree with original source row {i}")
    require(type(payload.lookup) is tuple and all(
        type(record) is tuple and len(record) == 3 and all(integer(x, 0) for x in record)
        for record in payload.lookup), "malformed orbit-key lookup")
    require(payload.lookup == lookup_records(binding.states),
            "lookup shape, orientation key or original state identity mismatch")
    # Authenticate the actual historical graph and its exact original weights;
    # a newly computed valid potential is not silently substituted for it.
    historical = json.loads((ROOT/'evidence/c4-pair-overlap-graph-2026-11-05/receipt.json').read_text())
    archived = historical['fixtures'][binding.fixture]
    graph_text = refinement.archive.graph_text(refinement.as_graph(binding), payload.weights, payload.sweeps)
    digest = hashlib.sha256(graph_text.encode()).hexdigest()
    require(digest == archived['canonical_graph_sha256'], "original archived graph/weight digest mismatch")
    addressed = "\n".join(refinement.graph_lines(binding, payload.weights, payload.sweeps, gap))+"\n"
    return {
        'fixture': binding.fixture, 'sigma': archived['sigma'], 'states': count,
        'positional_edges': expected_summary[0], 'ordered_lift_positions': 2*expected_summary[0],
        'rate': archived['rate'], 'radii': list(binding.radii),
        'maximum_rooted_inverse_depth': expected_summary[3],
        'historical_graph_sha256': digest,
        'addressed_packet_sha256': hashlib.sha256(addressed.encode()).hexdigest(),
        'packed_rows': len(payload.packed), 'lookup_nodes': len(payload.lookup),
    }


def payload_lines(payload):
    """Reference rendering for parser tests; never credited as native replay."""
    b = payload.binding
    yield from refinement.graph_lines(b, payload.weights, payload.sweeps, payload.minimum_gap)
    for i, bits in enumerate(payload.packed):
        yield f"packed {b.fixture} {i} {bits}"
    for path, key, row in payload.lookup:
        yield f"lookup {b.fixture} {path} {key} {row}"


def calibration_payload(binding, weights, sweeps, gap):
    """Test-only conversion from independently supplied complete records."""
    summary = (sum(map(len, binding.rows)), sum(s.swapped for r in binding.rows for s in r),
               sum(len(r)-len({s.target for s in r}) for r in binding.rows), max(binding.depths))
    packed = tuple(encode_row(state, weight, birth, depth, row)
                   for state, weight, birth, depth, row in
                   zip(binding.states, weights, binding.births, binding.depths, binding.rows))
    return Payload(binding, tuple(weights), sweeps, gap, summary, packed, lookup_records(binding.states))


def negative_controls(payload):
    """Mutate actual complete payloads; preserve each observed refusal."""
    observed = {}

    def reject(name, changed):
        try:
            validate_payload(changed)
        except (InvalidCertificate, refinement.archive.InvalidCertificate) as exc:
            observed[name] = {'rejected': True, 'reason': str(exc)}
            return
        raise InvalidCertificate('payload negative control admitted: '+name)

    b = payload.binding
    victim = next(i for i, row in enumerate(b.rows) if len({s.target for s in row}) < len(row))
    row = b.rows[victim]
    omitted = next(k for k, s in enumerate(row) if s.target in {t.target for t in row[:k]})
    rows = list(b.rows)
    rows[victim] = row[:omitted]+row[omitted+1:]
    reject('omitted_repeated_positional_edge', replace(payload, binding=replace(b, rows=tuple(rows))))
    reject('swapped_graph_direction', replace(payload, binding=replace(b, direction=1)))
    reject('wrong_24_12_box', replace(payload, binding=replace(b, radii=(24, 12))))
    births = list(b.births)
    births[3] = (-1, -1)
    reject('incomplete_inverse_ancestry', replace(payload, binding=replace(b, births=tuple(births))))
    states = list(b.states)
    states[3] = states[4]
    reject('graph_domain_mismatch', replace(payload, binding=replace(b, states=tuple(states))))
    size = len(b.states)-1
    rows = tuple(tuple(s for s in row if s.target < size) for row in b.rows[:size])
    reject('removed_ancestor_and_all_stored_edges', replace(payload, binding=replace(
        b, states=b.states[:size], rows=rows, births=b.births[:size], depths=b.depths[:size])))
    first = next(i for i, row in enumerate(b.rows) if row)
    rows = list(b.rows)
    rows[first] = (replace(rows[first][0], swapped=1-rows[first][0].swapped),)+rows[first][1:]
    reject('flipped_track_swap', replace(payload, binding=replace(b, rows=tuple(rows))))
    reject('different_original_substitution', replace(payload, binding=replace(b, images=refinement.SOURCES[1-b.fixture])))
    digits = list(b.digits)
    digits[0] = replace(digits[0], local=digits[0].local+1)
    reject('wrong_nested_local_address', replace(payload, binding=replace(b, digits=tuple(digits))))
    packed = list(payload.packed)
    packed[0] += 1 << (80+23*len(b.rows[0]))
    reject('hidden_high_payload', replace(payload, packed=tuple(packed)))
    packed = list(payload.packed)
    packed[first] ^= 1 << (80+22)
    reject('packed_orientation_mismatch', replace(payload, packed=tuple(packed)))
    packed = list(payload.packed)
    packed[0] ^= 1
    reject('packed_weight_mismatch', replace(payload, packed=tuple(packed)))
    reject('missing_packed_leaf', replace(payload, packed=payload.packed[:-1]))
    lookup = list(payload.lookup)
    path, key, row_id = lookup[0]
    lookup[0] = path, key, (row_id+1) % len(b.states)
    reject('wrong_lookup_identity', replace(payload, lookup=tuple(lookup)))
    lookup = list(payload.lookup)
    path, key, row_id = lookup[0]
    lookup[0] = path+1, key, row_id
    reject('wrong_lookup_shape', replace(payload, lookup=tuple(lookup)))
    reject('missing_lookup_node', replace(payload, lookup=payload.lookup[:-1]))
    return observed


def verify_native(text, fixture=None, controls=False):
    payloads = parse_payload(text, fixture)
    summaries = [validate_payload(p) for p in payloads]
    canonical = "schema "+SCHEMA+"\n"+"".join("\n".join(payload_lines(p))+"\n" for p in payloads)
    require(text == canonical, "noncanonical full payload serialization")
    result = {
        'schema': SCHEMA, 'fixtures': summaries,
        'all_two_original_fixtures_verified': fixture is None,
        'payload_sha256': hashlib.sha256(text.encode()).hexdigest(),
        'payload_bytes': len(text.encode()),
        'kernel_acceptance_supplied_by_this_oracle': False,
    }
    if controls:
        result['observed_negative_controls'] = {str(p.binding.fixture): negative_controls(p) for p in payloads}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native', type=Path, required=True)
    parser.add_argument('--fixture', type=int, choices=(0, 1),
                        help='Single-fixture development replay; no two-source verdict')
    parser.add_argument('--controls', action='store_true')
    args = parser.parse_args()
    print(json.dumps(verify_native(args.native.read_text(), args.fixture, args.controls), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
