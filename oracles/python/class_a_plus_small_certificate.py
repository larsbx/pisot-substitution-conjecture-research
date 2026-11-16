"""Independent complete S18 replay for exactly five plus-Class-A members.

The canonical certificate is Mojo. This oracle rebuilds every child by
Cartesian enumeration over literal words, verifies every ordered occurrence,
then composes original proper prefixes from every vertex to typed zero.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
PLUS = runpy.run_path(str(HERE / "class_a_plus_constant_entry.py"))
GRAPH = runpy.run_path(str(HERE / "class_a_x_productivity.py"))
SmallGeometry = PLUS["SmallGeometry"]
original_prefix_certificate = PLUS["original_prefix_certificate"]
MEMBERS = tuple((n, n+4) for n in range(1, 6))
STATE_CAP, PAIR_CAP = 6000, 20_000_000
CONTRACT = ("ClassAPlusFiveSmallCompleteS18; every original ordered child and "
            "every full integral state has an actual typed-zero path; exactly "
            "n=1..5,d=n+4; caps refuse")


class BoundedGeometry(SmallGeometry):
    def __init__(self, n, d, pair_cap):
        if type(pair_cap) is not int or pair_cap < 1:
            raise ValueError("nonpositive occurrence-pair cap")
        super().__init__(n, d)
        self.pair_cap, self.pairs = pair_cap, 0

    def edges(self, w):
        self.pairs += len(self.words[w[0]])*len(self.words[w[1]])
        if self.pairs > self.pair_cap:
            raise GRAPH["IncompleteGraph"]("complete original-pair budget exhausted")
        yield from super().edges(w)


def make_member(n, d, state_cap=STATE_CAP, pair_cap=PAIR_CAP):
    if type(state_cap) is not int or state_cap < 18:
        raise ValueError("insufficient complete source-state cap")
    g = BoundedGeometry(n, d, pair_cap)
    nine, _ = GRAPH["swap_sources"](g)
    # The native discovery order alternates each literal intersection and
    # its actual track reversal. The sources themselves are derived anew.
    seeds = tuple(w for source in nine for w in (source, GRAPH["reverse"](source)))
    states, ids, adj = GRAPH["complete_graph"](g, seeds, state_cap)
    if tuple(states[:18]) != seeds:
        raise ValueError("original eighteen-source order was not retained")
    terminals = {v for v, w in enumerate(states) if GRAPH["coincidence"](w)}
    distance, _ = GRAPH["backwards"](adj, terminals)
    if set(distance) != set(range(len(states))):
        raise ValueError("complete small graph has a state without typed coincidence")
    selected = [next((z for z, (target, _, _) in enumerate(row)
                      if distance[target] == distance[v]-1), -1)
                for v, row in enumerate(adj)]
    if any((selected[v] < 0) != (v in terminals) for v in range(len(states))):
        raise ValueError("missing actual decreasing occurrence")
    pairs = [0 if v in terminals else len(g.words[w[0]])*len(g.words[w[1]])
             for v, w in enumerate(states)]
    vertices = [[v, *w, distance[v], selected[v], pairs[v]]
                for v, w in enumerate(states)]
    edges = [[v, z, target, i, j] for v, row in enumerate(adj)
             for z, (target, i, j) in enumerate(row)]
    paths, prefixes = [], []
    for source, w in enumerate(states):
        cursor, path, record = source, [], [source, distance[source]]
        while cursor not in terminals:
            target, i, j = adj[cursor][selected[cursor]]
            if distance[target] != distance[cursor]-1:
                raise ValueError("selected original edge does not decrease the distance")
            path.append((i, j, states[target]))
            record.extend((i, j, target))
            cursor = target
        if len(path) != distance[source]:
            raise ValueError("path omitted or passed the first typed zero")
        certificate = original_prefix_certificate(g, w, path, typed=True)
        prefixes.append(dict(vertex=source, source=list(w), **certificate))
        paths.append(record)
    if g.pairs != sum(pairs):
        raise ValueError("independent Cartesian pair accounting mismatch")
    counts = [len(states), len(edges), sum(pairs), max(distance.values()),
              sum(distance.values())]
    packet = dict(n=n, d=d, vertices=vertices, edges=edges, paths=paths,
                  complete=[*counts, state_cap, pair_cap])
    summary = dict(n=n, d=d, sources=18, vertices=counts[0], indexed_edges=counts[1],
                   occurrence_pairs=counts[2], max_distance=counts[3],
                   paths=len(paths), path_edges=counts[4],
                   terminal_labels=[list(states[v]) for v in sorted(terminals)],
                   target_policy="typed full integral zero", complete=True,
                   graph_sha256=sha256(json.dumps([states, adj], separators=(",", ":")).encode()).hexdigest(),
                   original_prefix_certificates=prefixes)
    return packet, summary


@lru_cache(maxsize=5)
def _canonical(n, d):
    return make_member(n, d)


def verify_member(packet):
    if set(packet) != {"n", "d", "vertices", "edges", "paths", "complete"}:
        raise ValueError("missing or unexpected complete-certificate field")
    n, d = packet["n"], packet["d"]
    if type(n) is not int or type(d) is not int or (n, d) not in MEMBERS:
        raise ValueError("unexpected small-member parameter")
    expected, summary = _canonical(n, d)
    # Exact lists retain vertex order, every ordered edge and multiplicity,
    # original selected path indices, and all distances and counters.
    for key in ("vertices", "edges", "paths", "complete"):
        if packet[key] != expected[key]:
            raise ValueError("small certificate differs from literal rebuild: " + key)
        flat = packet[key] if key == "complete" else [x for row in packet[key] for x in row]
        if any(type(x) is not int for x in flat):
            raise ValueError("small certificate requires integral fields")
    return summary


def verify_native_text(text):
    packets, completions, member_passes = {}, set(), {}
    total, contract = None, False
    for line in text.splitlines():
        if not line.strip():
            continue
        if line.startswith("contract-receipt:"):
            if contract or line != "contract-receipt: " + CONTRACT:
                raise ValueError("missing, altered or repeated complete-small contract")
            contract = True
            continue
        parts = line.split()
        try:
            values = list(map(int, parts[1:]))
        except ValueError as exc:
            raise ValueError("nonintegral small native record") from exc
        if parts[0] == "CLASS_A_PLUS_FIVE_SMALL_ENTRY_PASS":
            if total is not None or len(values) != 7:
                raise ValueError("malformed or duplicate small-total receipt")
            total = values
            continue
        if len(values) < 2 or tuple(values[:2]) not in MEMBERS:
            raise ValueError("unexpected small record/member")
        n, d = values[:2]
        key = (n, d)
        row = packets.setdefault(key, dict(n=n, d=d, vertices=[], edges=[], paths=[], complete=[]))
        data = values[2:]
        if parts[0] == "PLUS_SMALL_VERTEX":
            if len(data) != 9 or data[0] != len(row["vertices"]):
                raise ValueError("missing, duplicate, reordered or malformed vertex")
            row["vertices"].append(data)
        elif parts[0] == "PLUS_SMALL_EDGE":
            if len(data) != 5:
                raise ValueError("malformed original edge")
            row["edges"].append(data)
        elif parts[0] == "PLUS_SMALL_PATH":
            if len(data) < 2 or data[0] != len(row["paths"]) or data[1] < 0 or len(data) != 2+3*data[1]:
                raise ValueError("missing, duplicate, reordered or truncated original path")
            row["paths"].append(data)
        elif parts[0] == "PLUS_SMALL_COMPLETE":
            if key in completions or len(data) != 7:
                raise ValueError("missing or duplicate complete graph counters")
            completions.add(key)
            row["complete"] = data
        elif parts[0] == "CLASS_A_PLUS_SMALL_MEMBER_PASS":
            if key in member_passes or len(data) != 5:
                raise ValueError("missing or duplicate small-member pass receipt")
            member_passes[key] = data
        else:
            raise ValueError("unexpected line in complete-small transcript")
    if set(packets) != set(MEMBERS) or completions != set(MEMBERS) or set(member_passes) != set(MEMBERS):
        raise ValueError("the five complete small members are not all present")
    if not contract or total is None:
        raise ValueError("complete-small transcript has no final acceptance receipts")
    summaries = []
    for key in MEMBERS:
        summary = verify_member(packets[key])
        if member_passes[key] != packets[key]["complete"][:5]:
            raise ValueError("small-member printed pass differs from complete record")
        summaries.append(summary)
    expected_total = [sum(s["vertices"] for s in summaries),
                      sum(s["indexed_edges"] for s in summaries),
                      sum(s["occurrence_pairs"] for s in summaries),
                      sum(s["paths"] for s in summaries),
                      sum(s["path_edges"] for s in summaries),
                      max(s["max_distance"] for s in summaries), 12]
    if total != expected_total:
        raise ValueError("small-total counters or refusal count disagree")
    return dict(scope="exactly five complete literal S18 graphs; not arbitrary strict sources",
                native_log_sha256=sha256(text.encode()).hexdigest(),
                members=summaries, total=dict(zip(("vertices", "indexed_edges", "occurrence_pairs",
                "paths", "path_edges", "max_distance", "native_refusals"), expected_total)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-log", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(verify_native_text(args.native_log.read_text()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
