"""Independent literal/Fraction replay of native finite S18 certificates.

Mojo is canonical. This checker independently reconstructs full literal
closures and shortest distances, and replays each selected quotient path
from every actual orientation. It makes no parameter-uniform assertion.
"""
from hashlib import sha256
import argparse
import gzip
import json
from pathlib import Path
import runpy

raw = runpy.run_path(str(Path(__file__).with_name('class_a_x_productivity.py')))
Geometry = raw['Geometry']
MEMBERS = raw['MEMBERS']
CONTRACT = ('contract-receipt: ClassACompleteS18LiteralOccurrencesAndExactQuotientDistances; '
            'finite specimens only; not universal BH')


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode() + b'\n'


def verify_member(k, t, vertices, edges, orbits, complete, pair_cap=20000000, state_cap=6000):
    """Inputs are untrusted native records; no counters replace full replay."""
    g = Geometry(-1, k, t)
    if state_cap < 1 or pair_cap < 1 or not vertices or len(vertices) > state_cap:
        raise ValueError('state verification cap exhausted; no verdict')
    preflight_pairs = 0
    for w, _, _, _ in vertices.values():
        if len(w) != 5 or not all(0 <= a < 3 for a in w[:2]):
            raise ValueError('invalid typed label')
        if not raw['coincidence'](w):
            preflight_pairs += len(g.words[w[0]]) * len(g.words[w[1]])
        if preflight_pairs > pair_cap:
            raise ValueError('literal verification pair cap exhausted; no verdict')
    _, seeds = raw['swap_sources'](g)
    states, ids, adj = raw['complete_graph'](g, seeds, state_cap)
    if set(vertices) != set(range(len(states))):
        raise ValueError('incomplete or noncontiguous native vertex domain')
    labels = {v: row[0] for v, row in vertices.items()}
    native_ids = {w: v for v, w in labels.items()}
    if len(native_ids) != len(vertices) or set(native_ids) != set(ids):
        raise ValueError('native labels differ from independently completed S18 closure')
    actual = [[] for _ in vertices]
    for v, dst, i, j in edges:
        if v not in labels or dst not in labels:
            raise ValueError('invalid source/target address')
        actual[v].append((dst, i, j))
    pairs = 0
    expected_reps = []
    expected_orbit = {}
    for v in range(len(vertices)):
        w = labels[v]
        rv = native_ids[raw['reverse'](w)]
        if v <= rv:
            orb = len(expected_reps)
            expected_reps.append(v)
            expected_orbit[v] = expected_orbit[rv] = orb
        required = [] if raw['coincidence'](w) else [
            (native_ids[child], i, j) for i, j, child in g.edges(w)]
        # List equality preserves multiplicity AND exact top-major addresses.
        if actual[v] != required:
            raise ValueError('outgoing row differs from full literal occurrences')
        budget = 0 if raw['coincidence'](w) else len(g.words[w[0]]) * len(g.words[w[1]])
        if vertices[v][3] != budget:
            raise ValueError('incorrect outgoing enumeration pair count')
        pairs += budget
    if pairs > pair_cap:
        raise ValueError('literal verification pair cap exhausted; no verdict')
    if set(orbits) != set(range(len(expected_reps))):
        raise ValueError('incomplete quotient orbit domain')
    if complete != (len(states), len(orbits), len(edges), pair_cap, state_cap):
        raise ValueError('completion/cap record mismatch')
    qadj = []
    for orb, rep in enumerate(expected_reps):
        if orbits[orb][0] != rep:
            raise ValueError('incorrect representative/orbit record')
        qadj.append([(expected_orbit[dst], i, j) for dst, i, j in actual[rep]])
    roots = [v for v in labels if raw['coincidence'](labels[v])]
    qroots = [orb for orb, rep in enumerate(expected_reps) if rep in roots]
    od, _ = raw['backwards'](actual, roots)
    qd, _ = raw['backwards'](qadj, qroots)
    if len(od) != len(states) or len(qd) != len(orbits):
        raise ValueError('unproductive finite specimen; no certificate')
    for v, (w, orb, distance, _) in vertices.items():
        if orb != expected_orbit[v] or distance != od[v] or distance != qd[orb]:
            raise ValueError('incorrect original/quotient shortest distance or orbit')
    for orb, (rep, distance, selected) in orbits.items():
        if distance != qd[orb]:
            raise ValueError('incorrect quotient shortest distance')
        if distance == 0:
            if selected != -1:
                raise ValueError('fabricated terminal path')
        elif not 0 <= selected < len(qadj[orb]):
            raise ValueError('invalid selected occurrence address')
        elif qd[qadj[orb][selected][0]] != distance - 1:
            raise ValueError('selected occurrence fails exact distance descent')
    edge_sets = [set(row) for row in actual]
    # All quotient edges, from BOTH actual orientations, then full terminal paths.
    lifts = 0
    path_steps = 0
    def lift(v, selected):
        orb = expected_orbit[v]
        rep = expected_reps[orb]
        if not 0 <= selected < len(qadj[orb]):
            raise ValueError('fabricated quotient path')
        target, i, j = qadj[orb][selected]
        if v != rep:
            i, j = j, i
        child = g.child(labels[v], i, j)
        dst = native_ids.get(child)
        if (dst, i, j) not in edge_sets[v] or not g.interior(child) or expected_orbit[dst] != target:
            raise ValueError('invalid actual occurrence lift')
        return dst
    for v in labels:
        for selected in range(len(qadj[expected_orbit[v]])):
            lift(v, selected)
            lifts += 1
        current = v
        for step in range(od[v]):
            current = lift(current, orbits[expected_orbit[current]][2])
            if od[current] != od[v] - step - 1:
                raise ValueError('lifted path has incorrect distance')
            path_steps += 1
        if current not in roots:
            raise ValueError('fabricated terminal path endpoint')
    certificate = dict(k=k, t=t, complete=list(complete),
        vertices=[[v, *vertices[v][0], *vertices[v][1:]] for v in sorted(vertices)],
        edges=edges, orbits=[[orb, *orbits[orb]] for orb in sorted(orbits)])
    summary = dict(k=k, t=t, vertices=len(states), quotient_orbits=len(orbits),
        indexed_edges=len(edges), literal_pairs=pairs, max_terminal_distance=max(od.values()),
        all_edge_orientation_lifts=lifts, selected_path_steps=path_steps,
        certificate_sha256=sha256(encoded(certificate)).hexdigest())
    return certificate, summary


def parse_native(data):
    records = {}
    negative = passed = receipt = False
    def record(key):
        return records.setdefault(key, dict(vertices={}, edges=[], orbits={}, complete=None))
    for line in data.decode().splitlines():
        if line.startswith('RC_'):
            tag, *values = line.split()
            values = list(map(int, values))
            if tag == 'RC_NEGATIVE_CONTROLS_PASS':
                if values != [16] or negative:
                    raise ValueError('invalid negative-control receipt')
                negative = True
                continue
            k, t, *row = values
            r = record((k, t))
            if tag == 'RC_VERTEX' and len(row) == 9:
                v, *w, orb, distance, pairs = row
                if v in r['vertices']:
                    raise ValueError('duplicate native vertex')
                r['vertices'][v] = (tuple(w), orb, distance, pairs)
            elif tag == 'RC_EDGE' and len(row) == 4:
                r['edges'].append(tuple(row))
            elif tag == 'RC_ORBIT' and len(row) == 4:
                orb, *value = row
                if orb in r['orbits']:
                    raise ValueError('duplicate native orbit')
                r['orbits'][orb] = tuple(value)
            elif tag == 'RC_COMPLETE' and len(row) == 5 and r['complete'] is None:
                r['complete'] = tuple(row)
            else:
                raise ValueError('malformed/duplicate native record')
        elif line == 'CLASS_A_NATIVE_REVERSAL_QUOTIENT_PASS 16088':
            if passed:
                raise ValueError('duplicate native pass')
            passed = True
        elif line == CONTRACT:
            if receipt:
                raise ValueError('duplicate contract receipt')
            receipt = True
        elif line.strip():
            raise ValueError('unexpected native certificate output')
    if set(records) != set(MEMBERS) or not (negative and passed and receipt):
        raise ValueError('incomplete native certificate emission/receipts')
    return records


def compare_native(data):
    records = parse_native(data)
    certificates, summaries = [], []
    for key in MEMBERS:
        cert, summary = verify_member(*key, **records[key])
        certificates.append(cert)
        summaries.append(summary)
    return dict(schema='psc-class-a-finite-v1', members=certificates), dict(
        scope='completed finite S18 specimens only', members=summaries,
        native_log_sha256=sha256(data).hexdigest(), all_literal_occurrences_equal=True,
        all_original_quotient_shortest_distances_equal=True, all_actual_lifts_verified=True,
        universal_x_carrier=False, nonunit_realization_bridge=False, general_psc=False)


def replay_certificate(packet):
    """Replay an archived, independently inspectable certificate without logs."""
    if set(packet) != {'schema', 'members'} or packet['schema'] != 'psc-class-a-finite-v1':
        raise ValueError('unknown finite certificate schema')
    keys = [(row['k'], row['t']) for row in packet['members']]
    if keys != list(MEMBERS):
        raise ValueError('missing, duplicate or reordered finite specimens')
    summaries = []
    for row in packet['members']:
        vertices = {}
        for v, top, bottom, x, c, y, orb, distance, pairs in row['vertices']:
            if v in vertices:
                raise ValueError('duplicate archived vertex')
            vertices[v] = ((top, bottom, x, c, y), orb, distance, pairs)
        orbits = {}
        for orb, rep, distance, selected in row['orbits']:
            if orb in orbits:
                raise ValueError('duplicate archived orbit')
            orbits[orb] = (rep, distance, selected)
        certificate, summary = verify_member(row['k'], row['t'], vertices,
            [tuple(e) for e in row['edges']], orbits, tuple(row['complete']))
        if encoded(certificate) != encoded(row):
            raise ValueError('noncanonical archived certificate')
        summaries.append(summary)
    return dict(scope='completed finite S18 specimens only', members=summaries,
                archived_certificate_replayed=True, universal_x_carrier=False,
                nonunit_realization_bridge=False, general_psc=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument('--native-log')
    inputs.add_argument('--certificate')
    parser.add_argument('--certificates')
    args = parser.parse_args()
    source = args.native_log or args.certificate
    data = Path(source).read_bytes()
    if source.endswith('.gz'):
        data = gzip.decompress(data)
    if args.certificate:
        if args.certificates:
            parser.error('--certificates requires --native-log')
        summary = replay_certificate(json.loads(data))
    else:
        certs, summary = compare_native(data)
        if args.certificates:
            target = Path(args.certificates)
            payload = encoded(certs)
            target.write_bytes(gzip.compress(payload, mtime=0) if target.suffix == '.gz' else payload)
            summary['certificates_sha256'] = sha256(payload).hexdigest()
    print(json.dumps(summary, indent=2, sort_keys=True))
