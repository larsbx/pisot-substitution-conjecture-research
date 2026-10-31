"""Independent exact finite audit and literal replay of the X ladder.

Graph verdicts require completed literal occurrence enumeration. The uniform
ladder argument is in docs/class-a-x-productivity-2026-10-31.md; no finite
census establishes universal productivity. Geometry is unchanged main code.
"""
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import runpy

Geometry = runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))["Geometry"]
X = (0, 0, 1, 0, -1)
E = (0, 0, 0, 1, 0)
C = (2, 2, 0, 0, 0)


class IncompleteGraph(RuntimeError):
    pass


def reverse(w):
    return (w[1], w[0], *(-z for z in w[2:]))


def coincidence(w):
    return w[0] == w[1] and w[2:] == (0, 0, 0)


def swap_sources(g):
    """Derive the nine sources from two-tile ab/ba, then genuinely reverse.

    Top/bottom tile starts have full Parikh prefixes, not physical scalars.
    All twelve candidates are tested with strict geometry.
    """
    nine = []
    for a, b in ((0, 1), (0, 2), (1, 2)):
        top, bottom = (a, b), (b, a)
        for i in range(2):
            for j in range(2):
                w = (top[i], bottom[j], *(int(j == 1 and q == b)
                     - int(i == 1 and q == a) for q in range(3)))
                if g.interior(w):
                    nine.append(w)
    eighteen = tuple(nine) + tuple(reverse(w) for w in nine)
    if len(nine) != 9 or len(set(eighteen)) != 18:
        raise AssertionError("swap construction or orientation changed")
    return tuple(nine), eighteen


def complete_graph(g, seeds, cap=6000):
    """Independent builder: preserve every (target,i,j), terminalize C only."""
    if cap < 1:
        raise ValueError("nonpositive cap")
    states, ids, adj = [], {}, []
    def intern(w):
        if w not in ids:
            if len(states) >= cap:
                raise IncompleteGraph("incomplete closure: cap reached")
            ids[w] = len(states)
            states.append(w)
        return ids[w]
    for w in seeds:
        if not g.interior(w):
            raise ValueError("non-strict source")
        intern(w)
    cursor = 0
    while cursor < len(states):
        w = states[cursor]
        row = [] if coincidence(w) else [
            (intern(child), i, j) for i, j, child in g.edges(w)]
        adj.append(row)
        cursor += 1
    return states, ids, adj


def reach(adj, starts):
    seen = set(starts)
    todo = deque(sorted(seen))
    while todo:
        for w, _, _ in adj[todo.popleft()]:
            if w not in seen:
                seen.add(w)
                todo.append(w)
    return seen


def backwards(adj, starts):
    rev = [[] for _ in adj]
    for v, row in enumerate(adj):
        for w, i, j in row:
            rev[w].append((v, i, j))
    distance = {v: 0 for v in starts}
    via = {}
    todo = deque(sorted(distance))
    while todo:
        w = todo.popleft()
        for v, i, j in rev[w]:
            if v not in distance:
                distance[v] = distance[w] + 1
                via[v] = (w, i, j)
                todo.append(v)
    return distance, via


def components(adj):
    """Iterative Kosaraju, independent of the existing four-seed audit."""
    seen, order = set(), []
    for root in range(len(adj)):
        if root in seen:
            continue
        seen.add(root)
        stack = [(root, iter(adj[root]))]
        while stack:
            v, it = stack[-1]
            edge = next(it, None)
            if edge is None:
                order.append(v)
                stack.pop()
            elif edge[0] not in seen:
                seen.add(edge[0])
                stack.append((edge[0], iter(adj[edge[0]])))
    rev = [[] for _ in adj]
    for v, row in enumerate(adj):
        for w, _, _ in row:
            rev[w].append(v)
    seen, out = set(), []
    for root in reversed(order):
        if root in seen:
            continue
        seen.add(root)
        todo, part = [root], []
        while todo:
            v = todo.pop()
            part.append(v)
            for w in rev[v]:
                if w not in seen:
                    seen.add(w)
                    todo.append(w)
        out.append(part)
    return out


def verify_forest(g, states, adj, distance, via, targets):
    """Each certificate edge is literal, strict and lowers an integer rank."""
    if set(distance) != set(via) | set(targets):
        raise ValueError("forest domain does not match ranks/targets")
    for v, rank in distance.items():
        if v in targets:
            if rank != 0 or v in via:
                raise ValueError("bad forest root")
            continue
        w, i, j = via[v]
        if (w, i, j) not in adj[v] or rank < 1 or distance.get(w) != rank - 1:
            raise ValueError("missing edge or rank does not descend")
        if (g.child(states[v], i, j) != states[w]
                or not g.interior(states[v]) or not g.interior(states[w])):
            raise ValueError("invalid occurrence/typed/strict witness")


def ladder_a(m):
    return (0, 2, 2*m, 6*m+1, 1-12*m)


def ladder_b(m):
    return (2, 0, 1-2*m, 2-6*m, 12*m-7)


def ladder_path(k, t, m, flip=False):
    """Uniform local path; reachability of the source from X is NOT assumed."""
    if min(k, t) < 0 or m < 1 or 2*k+t < 2 or (k+1)*m > k+t+6:
        raise ValueError("outside proved ladder domain")
    n, d = k+t+3, k+2*t+5
    A = n+d
    edges = []
    for r in range(m, 1, -1):
        edges.extend(((ladder_a(r), d+k+8-2*(k+1)*r, 0, ladder_b(r)),
                      (ladder_b(r), 0, d+2*k+9-2*(k+1)*r, ladder_a(r-1))))
    D, H, J, Q = ((2, 0, -1, -4, 6), (0, 2, 1, 2, -3),
                  (0, 2, 1, -1, 1), (2, 0, 0, -1, 1))
    edges.extend(((ladder_a(1), d+5-k, 0, D), (D, 0, t+6, H),
                  (H, A+1, n-1, J), (J, A+1, 0, X),
                  (X, d+1, 0, Q), (Q, 1, 2, C)))
    if flip:
        return [(reverse(a), j, i, reverse(b)) for a, i, j, b in edges]
    return edges


def verify_path(g, edges):
    for z, (a, i, j, b) in enumerate(edges):
        if z and edges[z-1][3] != a:
            raise ValueError("broken path")
        if (g.child(a, i, j) != b or not g.interior(a) or not g.interior(b)):
            raise ValueError("wrong index/type/offset/strict geometry")
    if not edges or not coincidence(edges[-1][3]):
        raise ValueError("not a typed terminal")


def audit(k, t, cap=6000, certificate=False):
    g = Geometry(-1, k, t)
    nine, seeds = swap_sources(g)
    states, ids, adj = complete_graph(g, seeds, cap)
    U = reach(adj, [ids[X]])
    terminals = {v for v, w in enumerate(states) if coincidence(w)}
    dc, vc = backwards(adj, terminals)
    dx, vx = backwards(adj, [ids[X]])
    # Delete only RUN/RUN edges. Endpoints mean FIRST or actual LAST.
    def endpoint(v, index, which):
        return index in (0, len(g.words[states[v][which]])-1)
    sparse = [[e for e in row if endpoint(v, e[1], 0) or endpoint(v, e[2], 1)]
              for v, row in enumerate(adj)]
    de, ve = backwards(sparse, terminals)
    corners = [[e for e in row if endpoint(v, e[1], 0) and endpoint(v, e[2], 1)]
               for v, row in enumerate(adj)]
    dcorners, _ = backwards(corners, terminals)
    verify_forest(g, states, adj, dc, vc, terminals)
    verify_forest(g, states, adj, dx, vx, {ids[X]})
    verify_forest(g, states, sparse, de, ve, terminals)
    parts = components(adj)
    owner = {v: z for z, part in enumerate(parts) for v in part}
    sinks, recurrent = [], []
    for z, part in enumerate(parts):
        if all(owner[w] == z for v in part for w, _, _ in adj[v]):
            sinks.append(z)
        if len(part) > 1 or any(w == v for v in part for w, _, _ in adj[v]):
            recurrent.append(z)
    xpart = set(parts[owner[ids[X]]])
    if xpart != U & set(dx):
        raise AssertionError("independent X-SCC identity failed")
    # Full indexed reversal covariance, including endpoint letter types.
    edge_sets = [set(row) for row in adj]
    for v, w in enumerate(states):
        rv = ids[reverse(w)]
        for u, i, j in adj[v]:
            if (ids[reverse(states[u])], j, i) not in edge_sets[rv]:
                raise AssertionError("indexed reversal edge missing")
    if {reverse(states[v]) for v in U} != {states[v] for v in U}:
        raise AssertionError("X closure not reversal invariant")
    extras = sorted(set(states)-{states[v] for v in U})
    graph_bytes = json.dumps([states, adj], separators=(",", ":")).encode()
    members, source_members = [], []
    if 2*k+t >= 2:
        members = list(range(1, (k+t+6)//(k+1)+1))
        for m in members:
            for flip in (False, True):
                path = ladder_path(k, t, m, flip)
                verify_path(g, path)
                if len(path) != 2*m+4:
                    raise AssertionError("wrong ladder length")
            if ladder_a(m) in ids and ids[ladder_a(m)] in U:
                source_members.append(m)
    row = dict(k=k, t=t, n=g.n, d=g.d, vertices=len(states),
        indexed_edges=sum(map(len, adj)), x_vertices=len(U),
        nine_vertices=len(reach(adj, [ids[w] for w in nine])),
        scc_sizes=sorted(map(len, parts), reverse=True),
        x_scc_vertices=len(xpart), terminal_labels=sorted(states[v] for v in terminals),
        recurrent_sccs=len(recurrent), sink_sccs=len(sinks),
        nonproductive_sink_sccs=[sorted(states[v] for v in parts[z]) for z in sinks
                                if not any(v in dc for v in parts[z])],
        unproductive_labels=sorted(states[v] for v in range(len(states)) if v not in dc),
        nonterminal_not_returning_x=sorted(states[v] for v in range(len(states))
                                          if v not in dx and v not in terminals),
        max_distance_coincidence=max(dc.values()), max_distance_x=max(dx.values()),
        no_run_run_unproductive=len(states)-len(de),
        no_run_run_max_distance=max(de.values()),
        corners_only_unproductive=len(states)-len(dcorners),
        corners_only_first_failure=next((w for v, w in enumerate(states)
                                        if v not in dcorners), None),
        exceptions=extras, graph_sha256=sha256(graph_bytes).hexdigest(),
        ladder_proved_indices=members, ladder_indices_in_x_closure=source_members,
        complete=True, universal_x_productivity=False)
    if certificate:
        # Ranks and one actual edge per vertex encode paths for EVERY vertex.
        def forest(d, via):
            return [[d.get(v, -1), *via.get(v, (-1, -1, -1))]
                    for v in range(len(states))]
        row["certificate"] = dict(states=states, coincidence=forest(dc, vc),
            return_x=forest(dx, vx), no_run_run=forest(de, ve))
    return row


MEMBERS = tuple((k, t) for k in range(4) for t in range(4)) + (
    (0, 4), (4, 0), (4, 4), (0, 8), (8, 0), (8, 8))


def compare_native(path):
    """Compare EVERY native full label and indexed edge, not just counts."""
    import ast
    native = {}
    summaries = {}
    total = False
    contract = False
    for line in Path(path).read_text().splitlines():
        if line.startswith("X_VERTEX "):
            k, t, v, *w = map(int, line.split()[1:])
            vs, es = native.setdefault((k, t), ({}, []))
            if len(w) != 5 or v in vs:
                raise ValueError("malformed or duplicate native vertex")
            vs[v] = tuple(w)
        elif line.startswith("X_EDGE "):
            k, t, v, w, i, j = map(int, line.split()[1:])
            native.setdefault((k, t), ({}, []))[1].append((v, w, i, j))
        elif line.startswith("X_GRAPH "):
            _, k, t, payload = line.split(" ", 3)
            key = (int(k), int(t))
            if key in summaries:
                raise ValueError("duplicate native summary")
            summaries[key] = ast.literal_eval(payload)
        elif line == "X_GRAPH_TOTAL 16132 190966":
            total = True
        elif line == "contract-receipt: ClassAXCompleteOrientedIndexedFiniteGraphs":
            contract = True
    if set(native) != set(MEMBERS) or set(summaries) != set(MEMBERS) or not total or not contract:
        raise ValueError("incomplete native emission or missing contract receipt")
    rows = []
    for k, t in MEMBERS:
        g = Geometry(-1, k, t)
        _, seeds = swap_sources(g)
        states, ids, adj = complete_graph(g, seeds)
        nv, ne = native[k, t]
        if set(nv) != set(range(len(nv))) or len(set(nv.values())) != len(nv):
            raise ValueError("noncanonical native vertex IDs/lifts")
        expected = {w: {(states[z], i, j) for z, i, j in adj[v]}
                    for v, w in enumerate(states)}
        actual = {w: set() for w in nv.values()}
        for v, w, i, j in ne:
            edge = (nv[w], i, j)
            if edge in actual[nv[v]]:
                raise ValueError("duplicate indexed native edge")
            actual[nv[v]].add(edge)
        if expected != actual:
            raise ValueError(("native/oracle indexed graph mismatch", k, t))
        row = audit_summary_from_record(k, t)
        keys = ("vertices", "indexed_edges", "x_vertices", None, "x_scc_vertices",
                None, "recurrent_sccs", "sink_sccs", None, None, None,
                "max_distance_coincidence", "max_distance_x", "no_run_run_unproductive",
                "no_run_run_max_distance", "corners_only_unproductive")
        expected_summary = [row[key] if key is not None else 0 for key in keys]
        expected_summary[3] = len(row["scc_sizes"])
        expected_summary[5] = len(row["terminal_labels"])
        if summaries[k, t] != expected_summary:
            raise ValueError("native/oracle SCC or reachability mismatch")
        canonical = [[w, sorted(actual[w])] for w in sorted(actual)]
        digest = sha256(json.dumps(canonical, separators=(",", ":")).encode()).hexdigest()
        rows.append(dict(k=k, t=t, vertices=len(nv), indexed_edges=len(ne),
                         canonical_indexed_sha256=digest))
    return dict(all_full_labels_and_indexed_edges_equal=True,
                native_scc_and_reachability_equal=True, members=rows,
                native_log_sha256=sha256(Path(path).read_bytes()).hexdigest(),
                universal_x_productivity=False)


def audit_summary_from_record(k, t):
    record = Path(__file__).resolve().parents[2] / "evidence/class-a-x-productivity-2026-10-31/finite-certificates.json"
    rows = json.loads(record.read_text())["members"]
    return next(row for row in rows if (row["k"], row["t"]) == (k, t))


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificates", action="store_true")
    parser.add_argument("--native-log")
    args = parser.parse_args()
    if args.native_log:
        print(json.dumps(compare_native(args.native_log), indent=2, sort_keys=True))
        raise SystemExit(0)
    rows = [audit(k, t, certificate=args.certificates) for k, t in MEMBERS]
    print(json.dumps(dict(scope="exact finite observations; not universal X productivity",
                         members=rows), separators=(",", ":"), sort_keys=True))
