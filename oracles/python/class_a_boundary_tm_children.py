"""Independent literal-word/field replay of all nine T_m child kinds."""
from pathlib import Path
import runpy

base = runpy.run_path(str(Path(__file__).with_name("class_a_boundary_next_run.py")))
Geometry, first_run = base["Geometry"], base["expected"]


def allowed(eps, k, t, m, n, i, j):
    N = n+eps
    last = N+1
    if i == 0:
        if j == 0:
            return (m == 1 and t <= 1) if eps == -1 else (m == 2 and k <= 6)
        if j == last:
            return eps == 1 and m == 1 and 4 <= k <= 7
        return j in first_run(eps, k, t, m, n)
    if i == last:
        if j == 0:
            return (eps == -1 and m == 2 and t <= 2) or (eps == 1 and k <= 3 and m == 3)
        if j == last:
            return (eps == -1 and m == 1 and t == 0) or (eps == 1 and m == 2 and k in (3, 4))
        if eps == -1 and m == 2:
            return t-2 <= j <= t-1
        return eps == 1 and k >= 4 and m == 2 and k+t+9 <= j <= k+t+10
    if j == 0:
        if eps == -1 and m == 2:
            return k+3 <= i <= k+5
        if eps == 1 and k <= 3 and m == 3:
            return n+k-1 <= i
        return eps == 1 and k >= 4 and m == 2 and k-6 <= i <= k-3
    if j == last:
        if eps == -1 and m == 1:
            return k+2 <= i <= k+3
        if eps == 1 and k <= 3 and m == 2:
            return n+k-2 <= i <= n+k-1
        return eps == 1 and k >= 4 and m == 1 and k-7 <= i <= k-6
    if eps == -1:
        deltas = (t, t+1) if m == 1 else (-k-5, -k-4)
    else:
        deltas = (k+t+12, k+t+13) if m == 1 else ((3-k, 4-k) if m == 2 else ())
    return j-i in deltas


def probe():
    pairs = edges = members = 0
    kinds = {f"{a}/{b}": 0 for a in ("first", "run", "last") for b in ("first", "run", "last")}
    witnesses = {}
    for eps in (-1, 1):
        for k in range(13):
            for t in range(7):
                members += 1
                g = Geometry(eps, k, t)
                r = 2 if eps == 1 and k <= 3 else 1
                N = g.n+eps
                names = lambda i: "first" if i == 0 else ("last" if i == N+1 else "run")
                for m in (r, r+1):
                    source = (2, 2, -1, 1, m)
                    for i in range(N+2):
                        for j in range(N+2):
                            pairs += 1
                            target = g.child(source, i, j)
                            actual = g.interior(target)
                            want = allowed(eps, k, t, m, g.n, i, j)
                            assert actual == want, (eps, k, t, m, i, j, target, actual, want)
                            if actual:
                                edges += 1
                                kinds[f"{names(i)}/{names(j)}"] += 1
                                witnesses.setdefault(target, dict(eps=eps, k=k, t=t, m=m, i=i, j=j))
    return dict(scope="finite independent all-kind replay; no global closure or BH",
                members=members, source_cells=2*members, pairs=pairs,
                accepted=edges, kind_counts=kinds, image_labels=len(witnesses),
                witnesses=[dict(target=label, **witnesses[label]) for label in sorted(witnesses)])


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), indent=2, sort_keys=True))
