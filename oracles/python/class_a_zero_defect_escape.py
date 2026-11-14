"""Independent literal-word oracle for the Class-A zero-defect escape table.

The canonical implementation is kernel/psc/class_a_zero_defect_escape.mojo.
This oracle counts prefixes in the actual words, constructs the incidence
matrix from those words, and uses Fraction Perron enclosures for strictness.
No forward graph, guessed source cover, floating root, or search cap is used.
The parameter-uniform argument is the accompanying written/symbolic proof;
the specimen replay and native differential check remain finite evidence.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import runpy

Geometry = runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))["Geometry"]

# Explicit boundary representatives; these are regression inputs, not a
# purported finite cover of the parameter quadrant or reachable overlaps.
FIXTURES = ((0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (3, 2),
            (2, 4), (3, 5), (4, 6), (0, 3), (0, 4), (1, 6),
            (0, 5), (0, 8))


def parameters(k, t):
    if not isinstance(k, int) or not isinstance(t, int) or min(k, t) < 0:
        raise ValueError("k and t must be nonnegative integers")
    n, d = k + t + 3, k + 2*t + 5
    return n, d, n + d


def xx5_strict_domain(k, t):
    parameters(k, t)
    return t >= k + 3 or (t == k + 2 and k >= 2)


def reverse(w):
    return (w[1], w[0], *(-q for q in w[2:]))


def endpoint_source(top, bottom, s):
    return (top, bottom, -int(bottom == 0), -int(bottom == 1), s)


def address_formula(k, t, top, bottom, s, select_k, select_t):
    """Written path table; symbolic inputs may use a fixed branch selector.

    The symbolic checker separately proves every ordinal inequality over
    each entire unbounded integer chamber. A sampled selector is never an
    inequality certificate or an occurrence check by itself.
    """
    n, d = k + t + 3, k + 2*t + 5
    A = n + d
    if (top, bottom) == (1, 0):
        if s == 1:
            return [(1, d+2)]
        if s == 2:
            return [(n+1, d+1), (d+2, 0), (1, 2)]
        if s == 3 and select_k >= 1:
            return [(k+3, 0), (t+3, 0), (1, t+5), (3, 1)]
        if s == 3:
            return [(3, 0), (n, 0), (0, n), (n+1, 0), (1, 4)]
    if (top, bottom) == (0, 1):
        if s == 1:
            return [(0, 1), (2, 1)]
        if s == 2:
            return [(n+1, 1), (3, 1)]
        if s == 3 and select_k >= 1:
            return [(2*n+2, 0), (t+3, 0), (0, t+4), (4, 1)]
        if s == 3:
            return [(2*n+2, 0), (n, 0), (0, n), (0, n-1),
                    (n+1, 0), (t+3, 1), (1, 3)]
    if (top, bottom) == (1, 1):
        if s == 1:
            return [(1, 2)]
        if s == 2:
            return [(n+1, 0), (d+1, n+1), (0, d+2), (2, 1)]
    if (top, bottom) == (0, 0):
        if s == 1:
            return [(0, d+1), (2, 1)]
        if s == 2:
            return [(1, t+3), (3, 1)]
        if s == 3:
            return [(k+3, 0), (0, n-2), (1, 2)]
        if s == 4:
            prefix = [(A+1, 2*t+1)]
            if select_k + select_t == 0:
                return prefix + [(7, 0), (1, 7), (3, 1)]
            prefix.append((2*t+9, 1))
            if select_k + select_t >= 2:
                return prefix + [(1, 5)]
            return prefix + [(0, 4), (A+1, 4)]
        if s == 5:
            difference = select_t - select_k
            if difference == 2 and select_k == 2:
                return [(25, 0), (25, 0), (19, 0), (0, 2), (1, 4)]
            if difference == 2 and select_k >= 3:
                return [(A+1, 0), (4*k+18, 0), (n-2, 0), (2, 1)]
            if difference == 3:
                return [(A+1, 0), (2*t+10, 1), (1, 5)]
            if difference == 4:
                return [(A+1, 0), (7, 0), (1, 2*t+10), (5, 1)]
            if difference >= 5:
                prefix = [(3*k+2*t+13, 0), (t-k+3, 0)]
                if select_k >= 1:
                    return prefix + [(1, 2*t+10), (5, 1)]
                return prefix + [(1, 2*t+9), (n, 0), (1, 0),
                                 (n, 0), (0, n), (n+1, 0), (1, 4)]
    raise ValueError("outside the proved strict endpoint table")


def endpoint_addresses(k, t, top, bottom, s):
    parameters(k, t)
    if (top, bottom) == (0, 0) and s == 5 and not xx5_strict_domain(k, t):
        raise ValueError("the fifth x/x endpoint is not strict")
    return address_formula(k, t, top, bottom, s, k, t)


def literal_child(g, w, i, j):
    """Construct M and both proper prefixes from actual finite words."""
    a, b, *offset = w
    if a not in range(3) or b not in range(3):
        raise ValueError("invalid parent letter")
    if not (0 <= i < len(g.words[a]) and 0 <= j < len(g.words[b])):
        raise ValueError("nonexistent literal occurrence")
    columns = [Counter(word) for word in g.words]
    top_prefix, bottom_prefix = Counter(g.words[a][:i]), Counter(g.words[b][:j])
    image = tuple(sum(columns[col][row]*offset[col] for col in range(3))
                  + bottom_prefix[row] - top_prefix[row] for row in range(3))
    child = (g.words[a][i], g.words[b][j], *image)
    if child != g.child(w, i, j):
        raise AssertionError("literal counts disagree with independent geometric transport")
    return child


def replay(g, source, addresses):
    if not g.interior(source):
        raise ValueError("non-strict source")
    w, edges = source, []
    for i, j in addresses:
        w = literal_child(g, w, i, j)
        if not g.interior(w):
            raise ValueError("non-strict intermediate child")
        edges.append((i, j, w))
    if w[2:] != (0, 0, 0):
        raise ValueError("path does not end at the full integral zero offset")
    return edges


def zero_defect_addresses(k, t, source):
    n, d, A = parameters(k, t)
    a, b, p, q, r = source
    if a not in range(3) or b not in range(3):
        raise ValueError("invalid source letter")
    if (p, q, r) == (0, 0, 0):
        return []
    delta = int(a != 1) - int(b != 1)
    if p != delta or p + q + r != 0:
        raise ValueError("outside the zero-defect slice")
    runs = (A, n, n-1)
    gap = q + (d+1)*delta
    if -runs[b] <= gap <= runs[a]:
        i = max(1, 1+gap)
        return [(i, i-gap)]
    if gap < -runs[b]:
        return [(j, i) for i, j in zero_defect_addresses(k, t, reverse(source))]
    s = gap - runs[a]
    end_top = 1 if a == 2 else 0
    end_bottom = 1 if b == 1 else 0
    return [(runs[a]+1, 0)] + endpoint_addresses(k, t, end_top, end_bottom, s)


def countercontrol():
    g = Geometry(-1, 0, 0)
    w = (2, 2, 0, -4, 4)

    def target(v):
        a, b, p, q, r = v
        delta = int(a != 1) - int(b != 1)
        gap = q + 6*delta
        return v[2:] == (0, 0, 0) or (
            p == delta and p+q+r == 0 and -(8, 3, 2)[b] <= gap <= (8, 3, 2)[a])

    assert not target(w)
    first = list(g.edges(w))
    assert len(first) == 2
    pairs, second_count = 16, 0
    for _, _, v in first:
        assert not target(v)
        pairs += len(g.words[v[0]])*len(g.words[v[1]])
        for _, _, child in g.edges(v):
            assert not target(child)
            second_count += 1
    assert (pairs, second_count) == (106, 13)
    edges = replay(g, w, [(0, 3), (6, 4), (0, 7), (2, 1)])
    assert target(edges[2][2]) and not target(edges[1][2])
    return {"literal_pairs": pairs, "first_occurrences": len(first),
            "second_occurrences": second_count, "first_target_depth": 3,
            "first_zero_depth": 4}


def certify_fixtures():
    paths = edges = max_length = 0
    rows = []
    for k, t in FIXTURES:
        g = Geometry(-1, k, t)
        n, d, A = parameters(k, t)
        runs = (A, n, n-1)
        count = 0
        for a in range(3):
            for b in range(3):
                delta = int(a != 1) - int(b != 1)
                # Complete overestimate of the proved strict m interval.
                for m in range(-runs[b]-6, runs[a]+7):
                    w = (a, b, delta, m-(d+1)*delta, -m+d*delta)
                    if not g.interior(w):
                        continue
                    path = replay(g, w, zero_defect_addresses(k, t, w))
                    assert len(path) <= 10
                    count += 1
                    paths += 1
                    edges += len(path)
                    max_length = max(max_length, len(path))
        epsilon = int(xx5_strict_domain(k, t))
        assert g.interior((0, 0, -1, 0, 5)) == bool(epsilon)
        assert count == 18*n + 6*d + 63 + 8*epsilon
        rows.append({"k": k, "t": t, "strict_zero_defect_states": count})
    return {"scope": "finite complete strict-slice replay at named specimens",
            "members": len(FIXTURES), "paths": paths, "checked_edges": edges,
            "maximum_path_length": max_length, "rows": rows,
            "countercontrol": countercontrol(), "universal_seed_entry": False}


def check_native_log(path):
    """Compare each original ordinal, intermediate type and all coordinates."""
    geometries = {}
    count = edges = 0
    kinds = Counter()
    seen = set()
    for line in Path(path).read_text().splitlines():
        fields = line.split()
        if not fields or fields[0] not in {"ENDPOINT_PATH", "ZERO_DEFECT_PATH"}:
            continue
        kind, values = fields[0], list(map(int, fields[1:]))
        if kind == "ENDPOINT_PATH":
            k, t, a, b, s, length, *payload = values
            source = endpoint_source(a, b, s)
            addresses = endpoint_addresses(k, t, a, b, s)
        else:
            k, t, a, b, p, q, r, length, *payload = values
            source = (a, b, p, q, r)
            addresses = zero_defect_addresses(k, t, source)
        key = (kind, k, t, source)
        if key in seen:
            raise ValueError("duplicate native source record")
        seen.add(key)
        if len(payload) != 7*length:
            raise ValueError("native path length/payload mismatch")
        actual = [(payload[z], payload[z+1], tuple(payload[z+2:z+7]))
                  for z in range(0, len(payload), 7)]
        g = geometries.setdefault((k, t), None)
        if g is None:
            g = geometries[k, t] = Geometry(-1, k, t)
        expected = replay(g, source, addresses)
        if actual != expected:
            raise ValueError(f"native path differs at {k,t,source}: {actual} != {expected}")
        count += 1
        edges += length
        kinds[kind] += 1
    if set(geometries) != set(FIXTURES):
        raise ValueError("missing or unexpected named native fixture")
    # Recover the promised emitted source set from the mathematical domains,
    # not just aggregate counts. One valid row per member is insufficient.
    expected_sources = set()
    for (k, t), g in geometries.items():
        n, d, A = parameters(k, t)
        runs = (A, n, n-1)
        for a in range(2):
            for b in range(2):
                for s in range(1, 6):
                    w = endpoint_source(a, b, s)
                    if g.interior(w):
                        expected_sources.add(("ENDPOINT_PATH", k, t, w))
        for a in range(3):
            for b in range(3):
                delta = int(a != 1) - int(b != 1)
                expected_sources.add(("ZERO_DEFECT_PATH", k, t, (a, b, 0, 0, 0)))
                expected_sources.add(("ZERO_DEFECT_PATH", k, t,
                    (a, b, delta, 1-(d+1)*delta, d*delta-1)))
                for m in range(-runs[b]-6, runs[a]+7):
                    if -runs[b] <= m <= runs[a]:
                        continue
                    w = (a, b, delta, m-(d+1)*delta, d*delta-m)
                    if g.interior(w):
                        expected_sources.add(("ZERO_DEFECT_PATH", k, t, w))
    if seen != expected_sources:
        raise ValueError(f"native source coverage mismatch: "
                         f"{len(expected_sources-seen)} missing, "
                         f"{len(seen-expected_sources)} unexpected")
    return {"native_paths_compared": count, "native_edges_compared": edges,
            "native_members": len(geometries), "row_kinds": dict(kinds),
            "complete_source_set_compared": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--native-log", type=Path)
    args = parser.parse_args()
    result = certify_fixtures()
    if args.native_log:
        result["native_differential"] = check_native_log(args.native_log)
    print(json.dumps(result, indent=2, sort_keys=True))
