"""Independent exact finite first/run replay; canonical implementation is Mojo."""
from pathlib import Path
import runpy

Geometry = runpy.run_path(str(Path(__file__).with_name("class_a_boundary_children.py")))["Geometry"]


def expected(eps, k, t, m, n):
    if eps == -1:
        return set(range(max(1, t-1), t+2)) if m == 1 else set()
    if k <= 3:
        return set(range(1, 5-k)) if m == 2 else set()
    return set(range(k+t+10, min(k+t+13, n+1)+1)) if m == 1 else set()


def probe():
    members = ordinals = accepted = cells = last_accepted = 0
    rows = []
    for eps in (-1, 1):
        for k in range(16):
            for t in range(16):
                members += 1
                g = Geometry(eps, k, t)
                r = 2 if eps == 1 and k <= 3 else 1
                for m in (r, r+1):
                    cells += 1
                    parent = (2, 2, -1, 1, m)
                    assert g.interior(parent)
                    actual = set()
                    for j in range(1, g.n+eps+1):
                        ordinals += 1
                        target = g.child(parent, 0, j)
                        assert target == (0, 2, m, m+1, m*(g.n+eps)-g.d+j-1)
                        if g.interior(target):
                            actual.add(j)
                            accepted += 1
                    want = expected(eps, k, t, m, g.n)
                    assert actual == want, (eps, k, t, m, actual, want)
                    last = g.child(parent, 0, g.n+eps+1)
                    last_overlap = g.interior(last)
                    assert last_overlap == (eps == 1 and m == 1 and 4 <= k <= 7)
                    if last_overlap:
                        assert last == (0, 1, 1, 2, k-9)
                        last_accepted += 1
                    if t in (0, 1, 2, 15) and k in (0, 3, 4, 5, 6, 7, 8, 15):
                        rows.append(dict(eps=eps, k=k, t=t, m=m, indices=sorted(actual)))
    return dict(scope="finite independent exact oracle; not closed carrier or BH",
                members=members, source_cells=cells, run_ordinals=ordinals,
                accepted=accepted, first_last_accepted=last_accepted, rows=rows)


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), indent=2, sort_keys=True))
