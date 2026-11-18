"""Independent literal-word oracle for the Class-A central entry theorem.

Canonical constructors live in kernel/psc/class_a_central_entry.mojo and
class_a_entry_search.mojo. This oracle uses the unchanged Fraction/Perron
geometry and literal prefix counts. Finite replay does not replace the
all-parameter density and periodic-orbit proofs in the accompanying note.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
import gzip
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = runpy.run_path(str(HERE / "class_a_zero_defect_escape.py"))
Geometry = BASE["Geometry"]
literal_child = BASE["literal_child"]
reverse = BASE["reverse"]
MEMBERS = ((0, 3), (1, 2), (2, 1), (3, 0), (0, 4),
           (0, 20), (0, 64), (32, 0), (8, 8))
P_VALUES = (-12, -3, 0, 3, 12)
Q_VALUES = (-30, -9, -1, 0, 1, 9, 30)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def scale(a, k):
    return tuple(k*x for x in a)


def central(g, w):
    """Half-width condition, in the independent common length scale."""
    if w[:2] != (2, 2):
        return False
    twice = scale(g.shift(w), 2)
    return (g.sign(add(twice, g.lengths[2])) >= 0
            and g.sign(add(twice, scale(g.lengths[2], -1))) <= 0)


def nearest_run(g, w):
    """Independent complete RUN-gap scan, not the native binary search."""
    if g.n < 6 or not central(g, w):
        raise ValueError("nearest RUN requires a central y/y source and n>=6")
    choices = []
    for gap in range(2-g.n, g.n-1):
        i, j = 1 + max(gap, 0), 1 + max(-gap, 0)
        child = literal_child(g, w, i, j)
        if central(g, child):
            choices.append((i, j, child))
    if len(choices) != 1:
        raise ValueError("nearest actual RUN child must exist uniquely")
    return choices[0]


def cycle_addresses(k, t, H, flip=False):
    n, _, _ = BASE["parameters"](k, t)
    K = k + 1
    if n < 6 or H < 1:
        raise ValueError("outside the central cycle parameter domain")
    kh = K*H
    if kh >= 4:
        if kh > n-2:
            raise ValueError("cycle exceeds the proved RUN bound")
        addresses = [(1, kh), (0, n+3-kh)]
        # Genuine reversal of the existing Q_H suffix, with its first
        # P_H -> Q_H edge removed. No unrelated path is spliced in.
        addresses.append((2*n+4-kh, 0))
        for r in range(H-1, 0, -1):
            addresses.extend([(0, n+4-K*r), (2*n+4-K*r, 0)])
        addresses.extend([(0, n+2), (1, 2)])
    elif K == 1 and H in (1, 2):
        addresses = [(0, 0), (1, 1+(n+2)*H), (2*H+1, 1)]
    elif (K, H) == (2, 1):
        addresses = [(0, 0), (0, 2*n+2), (2, 1)]
    elif (K, H) == (3, 1):
        addresses = [(0, 1), (1, 4)]
    elif (K, H) == (1, 3):
        addresses = [(0, 1), (0, 1), (2*n, 0), (1, 2*n+6), (5, 1)]
    else:
        raise ValueError("uncovered small product KH")
    return [(j, i) for i, j in addresses] if flip else addresses


def replay(g, source, addresses, *, require_zero=True):
    if not g.interior(source):
        raise ValueError("non-strict initial source")
    result, w = [], source
    for i, j in addresses:
        if w[2:] == (0, 0, 0):
            raise ValueError("production transcript continues after integral zero")
        child = literal_child(g, w, i, j)
        if not g.interior(child):
            raise ValueError("non-strict child in supplied transcript")
        result.append((i, j, child))
        w = child
    if require_zero and w[2:] != (0, 0, 0):
        raise ValueError("transcript does not reach full integral zero")
    return result


def cycle_escape(g, H, flip=False):
    source = (2, 2, H, 3*H, -6*H)
    if flip:
        source = reverse(source)
    if not central(g, source):
        raise ValueError("outside the actual central cycle interval")
    addresses = cycle_addresses(g.k, g.t, H, flip)
    return replay(g, source, addresses)


def central_escape(g, source, step_cap=10000):
    if g.n < 6 or not central(g, source) or step_cap < 0:
        raise ValueError("outside the central constructor domain")
    result, seen, w = [], set(), source
    while w[2:] != (0, 0, 0):
        if w in seen:
            raise AssertionError("unclassified nearest-RUN cycle")
        seen.add(w)
        p, q, r = w[2:]
        if p and q == 3*p and r == -6*p:
            tail = cycle_escape(g, abs(p), p < 0)
            if len(result)+len(tail) > step_cap:
                raise ValueError("central step cap exhausted; no verdict")
            return result + tail
        if len(result) >= step_cap:
            raise ValueError("central step cap exhausted; no verdict")
        edge = nearest_run(g, w)
        result.append(edge)
        w = edge[2]
    return result


def entry_escape(g, source, state_cap=10000, pair_cap=20000000, step_cap=10000, typed=False):
    """Bounded literal BFS oracle; exhausted budgets never mean no hit."""
    if (g.n < 6 or state_cap < 1 or pair_cap < 1 or step_cap < 0
            or not g.interior(source)):
        raise ValueError("outside entry constructor domain")
    states, parent, addresses = [source], [-1], [None]
    ids, queue, scanned = {source: 0}, deque([0]), 0
    found = None
    def terminal(w):
        return w[2:] == (0, 0, 0) and (not typed or w[0] == w[1])
    while queue:
        index = queue.popleft()
        w = states[index]
        if terminal(w) or central(g, w):
            found = index
            break
        scanned += len(g.words[w[0]])*len(g.words[w[1]])
        if scanned > pair_cap:
            raise ValueError("literal-pair cap exhausted; no verdict")
        for i, j, child in g.edges(w):
            if child in ids:
                continue
            if len(states) >= state_cap:
                raise ValueError("entry state cap exhausted; no verdict")
            ids[child] = len(states)
            queue.append(len(states))
            states.append(child)
            parent.append(index)
            addresses.append((i, j))
    if found is None:
        raise AssertionError("finite actual closure missed the proved central target")
    selected = []
    cursor = found
    while parent[cursor] != -1:
        selected.append((*addresses[cursor], states[cursor]))
        cursor = parent[cursor]
    selected.reverse()
    if len(selected) > step_cap:
        raise ValueError("entry path cap exhausted; no verdict")
    if not terminal(states[found]):
        selected += central_escape(g, states[found], step_cap-len(selected))
    return selected


def original_prefix_certificate(g, source, path, typed=False):
    """Inductive original marked-word prefixes and the exact BH identity."""
    if (len(source) != 5 or any(type(v) is not int for v in source)
            or source[0] not in range(3) or source[1] not in range(3)
            or not g.interior(source)):
        raise ValueError("prefix certificate requires a strict integral source")
    columns = [Counter(word) for word in g.words]

    def M(w):
        return tuple(sum(columns[c][r]*w[c] for c in range(3)) for r in range(3))

    P = Q = (0, 0, 0)
    scaled = source[2:]
    top_total = tuple(int(i == source[0]) for i in range(3))
    bottom_total = tuple(int(i == source[1]) for i in range(3))
    w = source
    for i, j, child in path:
        if w[2:] == (0, 0, 0) and (not typed or w[0] == w[1]):
            raise ValueError("prefix transcript passes an earlier zero hit")
        if literal_child(g, w, i, j) != child or not g.interior(child):
            raise ValueError("original occurrence or child offset altered")
        pc = Counter(g.words[w[0]][:i])
        qc = Counter(g.words[w[1]][:j])
        P = add(M(P), tuple(pc[r] for r in range(3)))
        Q = add(M(Q), tuple(qc[r] for r in range(3)))
        scaled, top_total, bottom_total = M(scaled), M(top_total), M(bottom_total)
        if not (0 <= sum(P) < sum(top_total) and 0 <= sum(Q) < sum(bottom_total)):
            raise ValueError("composed marked prefix is not proper")
        if add(scaled, add(Q, scale(P, -1))) != child[2:]:
            raise ValueError("original-prefix affine recurrence failed")
        w = child
    if w[2:] != (0, 0, 0) or scaled != add(P, scale(Q, -1)):
        raise ValueError("missing full integral BH prefix equality")
    if typed and w[0] != w[1]:
        raise ValueError("integral zero is not the requested typed coincidence")
    return dict(depth=len(path), top_prefix=list(P), bottom_prefix=list(Q),
                top_ordinal=sum(P), bottom_ordinal=sum(Q),
                top_image_length=sum(top_total), bottom_image_length=sum(bottom_total),
                scaled_source=list(scaled), terminal_letters=list(w[:2]),
                terminal_policy="typed coincidence" if typed else "full integral zero")


def two_level_density(g):
    """Nine strict density inequalities from actual expanded depth-two words."""
    if g.n < 6:
        raise ValueError("two-level density certificate is scoped to n>=6")
    rows = []
    for a, image in enumerate(g.words):
        word = tuple(c for b in image for c in g.words[b])
        counts = Counter(word)
        # N_y/(beta^2 L_a)>5/beta and N_x,N_c densities<1/beta.
        scaled_length = g.times_beta(g.lengths[a])
        y_margin = add(scale(g.lengths[2], counts[2]), scale(scaled_length, -5))
        x_margin = add(scaled_length, scale(g.lengths[2], -counts[0]))
        c_margin = add(scaled_length, scale(g.lengths[2], -counts[1]))
        if any(g.sign(m) <= 0 for m in (y_margin, x_margin, c_margin)):
            raise ValueError("literal two-level density inequality fails")
        rows.append(dict(parent=a, counts=[counts[i] for i in range(3)],
                         scaled_margin_polynomials=[list(m) for m in
                                                    (y_margin, x_margin, c_margin)]))
    return rows


SMALL_MEMBERS = ((0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0))


def verify_small_members(archive=None):
    """Replay only the six complementary COMPLETE S18 certificates."""
    path = Path(archive or ROOT / "evidence/class-a-finite-certificates-2026-11-02/certificates.json.gz")
    data = path.read_bytes()
    packet = json.loads(gzip.decompress(data))
    verifier = runpy.run_path(str(HERE / "class_a_finite_certificates.py"))
    if packet.get("schema") != "psc-class-a-finite-v1":
        raise ValueError("wrong archived finite certificate schema")
    selected = [row for row in packet["members"] if (row["k"], row["t"]) in SMALL_MEMBERS]
    if sorted((r["k"], r["t"]) for r in selected) != list(SMALL_MEMBERS):
        raise ValueError("missing or duplicate small-parameter certificate")
    summaries = []
    for row in selected:
        vertices = {}
        for v, top, bottom, x, c, y, orb, distance, pairs in row["vertices"]:
            if v in vertices:
                raise ValueError("duplicate small-member vertex")
            vertices[v] = ((top, bottom, x, c, y), orb, distance, pairs)
        orbits = {}
        for orb, rep, distance, edge in row["orbits"]:
            if orb in orbits:
                raise ValueError("duplicate small-member orbit")
            orbits[orb] = (rep, distance, edge)
        rebuilt, summary = verifier["verify_member"](
            row["k"], row["t"], vertices, [tuple(e) for e in row["edges"]],
            orbits, tuple(row["complete"]))
        if verifier["encoded"](rebuilt) != verifier["encoded"](row):
            raise ValueError("small-member archive record changed on replay")
        summaries.append(summary)
    return dict(scope="six complete terminalized S18 closures at n<6; not all formal strict sources",
                archive_sha256=sha256(data).hexdigest(), members=summaries,
                states=sum(r["vertices"] for r in summaries),
                indexed_edges=sum(r["indexed_edges"] for r in summaries),
                literal_pairs=sum(r["literal_pairs"] for r in summaries))


def central_sources(g):
    result = []
    for p in P_VALUES:
        for q in Q_VALUES:
            base = -2*p-q
            padding = abs(p) + abs(q)//(g.n+2) + 2
            choices = [(2, 2, p, q, r) for r in range(base-padding, base+padding+1)
                       if central(g, (2, 2, p, q, r))]
            if len(choices) != 1:
                raise AssertionError("specified central-source interval is incomplete")
            result += choices
    return result


def entry_sources(k, t):
    nine = ((0, 1, 0, 0, 0), (0, 0, 0, 1, 0), (1, 0, -1, 1, 0),
            (0, 2, 0, 0, 0), (0, 0, 0, 0, 1), (2, 0, -1, 0, 1),
            (1, 2, 0, 0, 0), (1, 1, 0, 0, 1), (2, 1, 0, -1, 1))
    sources = [v for w in nine for v in (w, reverse(w))]
    sources.append((0, 0, -1, -5, 6))
    if (k, t) == (0, 20):
        sources.append((2, 2, 10, -738, 738))
    return sources


def expected_native_keys(geometries):
    expected = set()
    for k, t in MEMBERS:
        g = geometries[(k, t)]
        expected.update(("CENTRAL_PATH", k, t, *w) for w in central_sources(g))
        for H in range(1, (g.n+4)//(2*(k+1))+2):
            w = (2, 2, H, 3*H, -6*H)
            if central(g, w):
                expected.update(("CYCLE_PATH", k, t, *v) for v in (w, reverse(w)))
        expected.update(("ENTRY_PATH", k, t, *w) for w in entry_sources(k, t))
        expected.update(("TYPED_ENTRY_PATH", k, t, a, b, 0, 0, 0)
                        for a in range(3) for b in range(3) if a != b)
    return expected


def check_native_log(path):
    """Every emitted original path is reconstructed independently."""
    geometries, seen, certificates = {}, set(), []
    paths = edge_count = 0
    summaries, contracts = {}, set()
    for line in Path(path).read_text().splitlines():
        if not line.startswith(("CENTRAL_PATH ", "CYCLE_PATH ", "ENTRY_PATH ", "TYPED_ENTRY_PATH ")):
            if line.startswith(("CLASS_A_CENTRAL_ENTRY_PASS ", "CLASS_A_ENTRY_SEARCH_PASS ",
                                "CLASS_A_TYPED_ENTRY_PASS ")):
                tag = line.split()[0]
                if tag in summaries:
                    raise ValueError("duplicate native completion receipt")
                fields_text = line[len(tag):].strip()
                if not re.fullmatch(r"\w+=\s*\d+(?:\s+\w+=\s*\d+)*", fields_text):
                    raise ValueError("malformed native completion fields")
                fields = re.findall(r"(\w+)=\s*(\d+)", fields_text)
                if len({k for k, _ in fields}) != len(fields):
                    raise ValueError("duplicate native completion field")
                summaries[tag] = {k: int(v) for k, v in fields}
            elif line == ("contract-receipt: exact nearest RUN occurrence selection from central y/y "
                          "minus-Class-A sources n>=6; original ordered indices, full integral offsets, "
                          "strict geometry and first-zero terminal policy; canonical cycle exits including "
                          "every small KH case and the n=6 LAST correction; finite replay is separate from "
                          "the written all-source entrance and termination proof"):
                if "central" in contracts:
                    raise ValueError("duplicate native central contract")
                contracts.add("central")
            elif line == ("contract-receipt: ClassAActualCentralEntryAndFullIntegralZeroWitnesses; "
                           "n>=6; bounded search refuses caps"):
                if "entry" in contracts:
                    raise ValueError("duplicate native entry contract")
                contracts.add("entry")
            elif line == ("contract-receipt: ClassAActualTypedCoincidenceEntry; "
                           "mixed-letter integral zero is nonterminal"):
                if "typed" in contracts:
                    raise ValueError("duplicate native typed-entry contract")
                contracts.add("typed")
            elif line.strip():
                raise ValueError("unexpected native path-log output")
            continue
        tag, *fields = line.split()
        values = list(map(int, fields))
        k, t, a, b, p, q, r, length, *tail = values
        if length < 0 or len(tail) != 7*length:
            raise ValueError("malformed native ordered-occurrence transcript")
        key = (tag, k, t, a, b, p, q, r)
        if key in seen:
            raise ValueError("duplicate native source row")
        seen.add(key)
        if (k, t) not in geometries:
            geometries[(k, t)] = Geometry(-1, k, t)
        g = geometries[(k, t)]
        source = (a, b, p, q, r)
        if tag == "CENTRAL_PATH":
            expected = central_escape(g, source)
        elif tag == "CYCLE_PATH":
            if source != (2, 2, p, 3*p, -6*p) or not p:
                raise ValueError("native cycle source is not an alternating full offset")
            expected = cycle_escape(g, abs(p), p < 0)
        else:
            expected = entry_escape(g, source, typed=tag == "TYPED_ENTRY_PATH")
        native = [(tail[i], tail[i+1], tuple(tail[i+2:i+7]))
                  for i in range(0, len(tail), 7)]
        if expected != native:
            raise ValueError("native/oracle original path mismatch")
        certificate = original_prefix_certificate(g, source, native, tag == "TYPED_ENTRY_PATH")
        certificates.append(dict(kind=tag, k=k, t=t, source=list(source), **certificate))
        paths += 1
        edge_count += length
    if set(geometries) != set(MEMBERS) or seen != expected_native_keys(geometries):
        raise ValueError("native path source set is incomplete or contains an extra source")
    if contracts != {"central", "entry", "typed"}:
        raise ValueError("missing native terminal contract receipt")
    central_records = [c for c in certificates if c["kind"] in ("CENTRAL_PATH", "CYCLE_PATH")]
    entry_records = [c for c in certificates if c["kind"] == "ENTRY_PATH"]
    typed_records = [c for c in certificates if c["kind"] == "TYPED_ENTRY_PATH"]
    required = {
        "CLASS_A_CENTRAL_ENTRY_PASS": dict(members=9, central_paths=315, cycle_paths=124,
            checked_edges=sum(c["depth"] for c in central_records),
            max_path=max(c["depth"] for c in central_records)),
        "CLASS_A_ENTRY_SEARCH_PASS": dict(members=9, paths=172,
            checked_edges=sum(c["depth"] for c in entry_records),
            max_path=max(c["depth"] for c in entry_records), density_inequalities=81, refusals=7),
        "CLASS_A_TYPED_ENTRY_PASS": dict(members=9, paths=54,
            checked_edges=sum(c["depth"] for c in typed_records),
            max_path=max(c["depth"] for c in typed_records)),
    }
    if summaries != required:
        raise ValueError("native success counters do not match complete original path records")
    return dict(paths=paths, checked_edges=edge_count, members=sorted(geometries),
                maximum_depth=max(c["depth"] for c in certificates),
                original_prefix_certificates=certificates,
                literal_two_level_density={f"{k},{t}": two_level_density(g)
                                          for (k, t), g in geometries.items()})


def check_small_native_log(path):
    """Bind fresh six-member native output to every original archived record."""
    records, passes = {}, {}
    final = contract = False
    for line in Path(path).read_text().splitlines():
        if line.startswith("SMALL_"):
            tag, *fields = line.split()
            k, t, *row = map(int, fields)
            record = records.setdefault((k, t), dict(vertices={}, edges=[], orbits={}, complete=None))
            if tag == "SMALL_VERTEX" and len(row) == 9:
                v, *w, orb, distance, pairs = row
                if v in record["vertices"]:
                    raise ValueError("duplicate native small-case vertex")
                record["vertices"][v] = (tuple(w), orb, distance, pairs)
            elif tag == "SMALL_EDGE" and len(row) == 4:
                record["edges"].append(tuple(row))
            elif tag == "SMALL_ORBIT" and len(row) == 4:
                orbit, *data = row
                if orbit in record["orbits"]:
                    raise ValueError("duplicate native small-case orbit")
                record["orbits"][orbit] = tuple(data)
            elif tag == "SMALL_COMPLETE" and len(row) == 5 and record["complete"] is None:
                record["complete"] = tuple(row)
            else:
                raise ValueError("malformed or duplicated small-case native record")
        elif line.startswith("CLASS_A_SMALL_MEMBER_PASS "):
            k, t, *counts = map(int, line.split()[1:])
            if (k, t) in passes:
                raise ValueError("duplicate small-case pass")
            passes[(k, t)] = counts
        elif line == "CLASS_A_SIX_SMALL_ENTRY_PASS 4470 35688 351816":
            if final:
                raise ValueError("duplicate six-member pass")
            final = True
        elif line == ("contract-receipt: ClassASixSmallCompleteS18EntryCertificates; "
                       "all actual children and every source zero hit; n<6"):
            if contract:
                raise ValueError("duplicate six-member contract")
            contract = True
        elif line.strip():
            raise ValueError("unexpected small-case native output")
    if set(records) != set(SMALL_MEMBERS) or set(passes) != set(SMALL_MEMBERS) or not (final and contract):
        raise ValueError("incomplete six-member native certificate packet")
    verifier = runpy.run_path(str(HERE / "class_a_finite_certificates.py"))
    archive_path = ROOT / "evidence/class-a-finite-certificates-2026-11-02/certificates.json.gz"
    archive_bytes = archive_path.read_bytes()
    archive = {(r["k"], r["t"]): r for r in json.loads(gzip.decompress(archive_bytes))["members"]}
    summaries = []
    for key in SMALL_MEMBERS:
        cert, summary = verifier["verify_member"](*key, **records[key])
        if verifier["encoded"](cert) != verifier["encoded"](archive[key]):
            raise ValueError("fresh native small-case record differs from the original archive")
        if passes[key] != [summary[x] for x in ("vertices", "indexed_edges", "literal_pairs", "max_terminal_distance")]:
            raise ValueError("small-case success counters disagree with complete records")
        summaries.append(summary)
    return dict(scope="six original complete S18 graphs, independently rebuilt from literal words",
                original_archive_sha256=sha256(archive_bytes).hexdigest(),
                native_log_sha256=sha256(Path(path).read_bytes()).hexdigest(),
                all_original_records_equal=True, members=summaries,
                states=sum(r["vertices"] for r in summaries),
                indexed_edges=sum(r["indexed_edges"] for r in summaries),
                literal_pairs=sum(r["literal_pairs"] for r in summaries))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--native-log")
    parser.add_argument("--small-native-log")
    parser.add_argument("--small-members", action="store_true")
    args = parser.parse_args()
    if args.native_log:
        answer = check_native_log(args.native_log)
    elif args.small_native_log:
        answer = check_small_native_log(args.small_native_log)
    elif args.small_members:
        answer = verify_small_members()
    else:
        parser.error("choose --native-log or --small-members")
    print(json.dumps(answer, sort_keys=True, indent=2))
