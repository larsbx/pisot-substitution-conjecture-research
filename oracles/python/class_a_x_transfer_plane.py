"""Independent literal/Fraction replay of guarded odd-plane transfers.

Only the z=1,s=0, nonnegative-index slice has the proved unit descent.
Generic plane transport alone supplies neither strictness nor word bounds.
The finite coverage profile consumes #436's completed graph certificate;
it does not extrapolate a parameter-uniform reachable interval.
"""
from hashlib import sha256
import json
from pathlib import Path
import runpy

BASE = runpy.run_path(str(Path(__file__).with_name("class_a_x_productivity.py")))
Geometry, reverse = BASE["Geometry"], BASE["reverse"]
ROOT = Path(__file__).resolve().parents[2]
RECORD = ROOT / "evidence/class-a-x-productivity-2026-10-31/finite-certificates.json"
E, D, C = (0, 0, 0, 1, 0), (2, 0, 0, 1, -1), (2, 2, 0, 0, 0)


def source(z, s, p):
    return (0, 2, p, 3*p+2*s+1, z-6*p-3*s-1)


def middle(z, s, p):
    return (2, 0, z-p-s-1, z-3*p-s, 6*p+3*s+1-4*z)


def generic_packet(k, t, z, s, p):
    if min(k, t) < 0:
        raise ValueError("outside minus cone")
    n, d, K = k+t+3, k+2*t+5, k+1
    i = (z-s)*n-K*p+3*z+1
    j = (K+3)*z-K*p+(n-K)*s+d+1
    q = middle(z, s, p)
    return [(source(z, s, p), i, 0, q),
            (q, 0, j, source(z, s, p-z))]


def verify_edges(g, packet):
    for a, i, j, b in packet:
        if g.child(a, i, j) != b or not g.interior(a) or not g.interior(b):
            raise ValueError("generic algebra did not give an actual strict typed edge")


def unit_path(k, t, p, flip=False):
    n = k+t+3
    if min(k, t, p) < 0 or (k+1)*p > n+3:
        raise ValueError("outside proved unit-descent domain")
    edges = []
    for r in range(p, 0, -1):
        a, b = generic_packet(k, t, 1, 0, r)
        if (k, t, r) == (0, 0, 1):
            b = (b[0], b[1], b[2], E)
        edges.extend((a, b))
    last = E if (k, t) == (0, 0) and p > 0 else source(1, 0, 0)
    edges.extend(((last, n+2, 0, D), (D, 2, 1, C)))
    if flip:
        return [(reverse(a), j, i, reverse(b)) for a, i, j, b in edges]
    return edges


MEMBERS = tuple((k, t) for k in range(13) for t in range(9)) + ((0, 20), (0, 64), (32, 0))


def exception_base_path(k, t, flip=False):
    if min(k, t) < 0:
        raise ValueError("outside minus exception-base parameters")
    packet = [(E, k+t+5, 0, D), (D, 2, 1, C)]
    return [(reverse(a), j, i, reverse(b)) for a, i, j, b in packet] if flip else packet


def replay():
    rows = []
    for k, t in MEMBERS:
        g = Geometry(-1, k, t)
        paths = edges = 0
        for flip in (False, True):
            BASE["verify_path"](g, exception_base_path(k, t, flip))
        for p in range((g.n+3)//(k+1)+1):
            for flip in (False, True):
                packet = unit_path(k, t, p, flip)
                BASE["verify_path"](g, packet)
                if len(packet) != 2*p+2:
                    raise AssertionError("wrong selected path length")
                paths += 1
                edges += len(packet)
        rows.append(dict(k=k, t=t, largest_proved_p=(g.n+3)//(k+1),
                         oriented_paths=paths, selected_edges=edges))
    return dict(scope="finite exact path replay; uniform local proof separate",
                specimens=len(rows), oriented_paths=sum(r["oriented_paths"] for r in rows),
                selected_edges=sum(r["selected_edges"] for r in rows), members=rows,
                exceptional_base_oriented_paths=2*len(rows), exceptional_base_selected_edges=4*len(rows),
                universal_x_productivity=False)


def profile():
    data = json.loads(RECORD.read_text())
    rows = []
    for old in data["members"]:
        k, t, n = old["k"], old["t"], old["n"]
        states = set(map(tuple, old["certificate"]["states"]))
        x_closure = states-set(map(tuple, old["exceptions"]))
        # Existing proved ladder carrier, including its intermediate states,
        # fixed tail and real reversals; this is NOT all known main results.
        previous = {BASE["X"], BASE["C"], (2, 0, 0, -1, 1)}
        if 2*k+t >= 2:
            for m in range(1, (k+t+6)//(k+1)+1):
                for a, _, _, b in BASE["ladder_path"](k, t, m):
                    previous.update((a, b))
        previous |= {reverse(w) for w in previous}
        new = set()
        for p in range((n+3)//(k+1)+1):
            new.add(source(1, 0, p))
            if p:
                new.add(middle(1, 0, p))
        new |= {reverse(w) for w in new}
        reached = new & x_closure
        ps = sorted(w[2] for w in x_closure if w[:2] == (0, 2)
                    and w[2] >= 0 and w == source(1, 0, w[2]))
        candidate = list(range((n-1)//(k+1)+1))
        if ps != candidate:
            raise AssertionError("finite reachable-interval candidate failed")
        rows.append(dict(k=k, t=t, p_indices_in_x_closure=ps,
            candidate_interval_matches=True, largest_proved_p=(n+3)//(k+1),
            reached_oriented_source_labels=len(reached),
            reached_labels_outside_previous_ladder_carrier=len(reached-previous),
            labels_outside_previous_carrier=sorted(reached-previous),
            parameter_uniform_reachable_interval_proved=False))
    return dict(scope="finite coverage measurements on the 22 completed #436 graphs",
        certificate_sha256=sha256(RECORD.read_bytes()).hexdigest(), members=rows,
        universal_x_productivity=False)


def plane_counterexample():
    """A genuine X descendant; plane membership cannot waive word bounds."""
    g = Geometry(-1, 0, 0)
    _, seeds = BASE["swap_sources"](g)
    states, ids, adj = BASE["complete_graph"](g, seeds)
    w = source(1, 1, 1)
    start, end = ids[BASE["X"]], ids[w]
    from collections import deque
    todo, prev = deque([start]), {start: None}
    while todo:
        v = todo.popleft()
        for target, i, j in adj[v]:
            if target not in prev:
                prev[target] = (v, i, j)
                todo.append(target)
    if end not in prev:
        raise AssertionError("control source not an actual X descendant")
    path = []
    v = end
    while v != start:
        u, i, j = prev[v]
        path.append((states[u], i, j, states[v]))
        v = u
    path.reverse()
    verify_edges(g, path)
    packet = generic_packet(0, 0, 1, 1, 1)
    if not all(g.interior(w) for w in (packet[0][0], packet[0][3], packet[1][3])):
        raise AssertionError("formal control labels must all be strict")
    verify_edges(g, packet[:1])
    if packet[1][2] != g.n+g.d+3:
        raise AssertionError("counter-calibration changed")
    try:
        verify_edges(g, packet)
    except ValueError:
        pass
    else:
        raise AssertionError("accepted nonexistent second occurrence")
    return dict(k=0, t=0, source=w, x_to_source_path=path,
                first_edge=packet[0], refused_second_edge=packet[1],
                all_three_formal_labels_strict=True,
                top_run=g.n+g.d, second_index=packet[1][2],
                conclusion="odd-plane algebra does not imply occurrence-valid transfer")


if __name__ == "__main__":
    print(json.dumps(dict(paths=replay(), finite_profile=profile(),
                         plane_counterexample=plane_counterexample()), indent=2, sort_keys=True))
