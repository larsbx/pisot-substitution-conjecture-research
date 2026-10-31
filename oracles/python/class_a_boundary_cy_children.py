"""Independent exact literal-word oracle for C_y=(c,y,0,-2,2).

The symbolic nine-kind derivation is in docs/class-a-boundary-cy-carrier-2026-10-31.md.
The 117-member replay here is finite validation, not the universal proof.
"""
from pathlib import Path
import runpy

Geometry = runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))["Geometry"]
TX = runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_tx_children.py")))
CY = (1, 2, 0, -2, 2)
Y0 = (2, 2, 1, -1, -1)
C = (2, 2, 0, 0, 0)
BASE_IMAGE = {
    (1, 0, 0, 0, -2),  # FF c/x
    (1, 2, 1, 0, -2),  # FR c/y
    (2, 2, 1, -1, -2), # RR diagonal zero
    Y0,                # RR diagonal one
    (2, 1, 1, -1, -1), # RL (n-1,n)
    (2, 1, 1, -1, -2), # RL (n,n)
}


def reverse(w):
    return (w[1], w[0], *(-x for x in w[2:]))


def source(flip):
    if flip not in (0, 1):
        raise ValueError("bad orientation")
    return reverse(CY) if flip else CY


def envelope():
    return BASE_IMAGE | {reverse(w) for w in BASE_IMAGE}


def predicted(flip, g, i, j):
    w = source(flip)
    if not (0 <= i < len(g.words[w[0]]) and
            0 <= j < len(g.words[w[1]])):
        raise ValueError("nonexistent ordered occurrence")
    a, b = (j, i) if flip else (i, j)
    n, N = g.n, g.n - 1
    if a == 0:
        return b in (0, 1)
    if a == n + 1:
        return False
    if b == 0:
        return False
    if 1 <= b <= N:
        return b - a in (0, 1)
    return b == n and a in (n-1, n)


def selected_path(flip, g):
    # CY(1,2)->Y0 followed by the existing Y0 three-edge suffix.
    # For reverse CY swap actual ordered indices and true oriented labels.
    base = [(1, 2, Y0)] + TX["path"](4, g)
    if flip:
        return [(j, i, reverse(w)) for i, j, w in base]
    return base


def verify_selected(flip, g, path):
    if path != selected_path(flip, g):
        raise ValueError("selected CY exit packet changed")
    state = source(flip)
    for i, j, target in path:
        if not (g.interior(state) and
                g.child(state, i, j) == target and
                g.interior(target)):
            raise ValueError("actual CY exit occurrence or geometry invalid")
        state = target
    if state != C:
        raise ValueError("not typed coincidence")


def probe():
    rows = []
    witness = {}
    pairs = accepted = path_edges = 0
    assert len(BASE_IMAGE) == 6 and len(envelope()) == 12
    for k in range(13):
        for t in range(9):
            g = Geometry(-1, k, t)
            assert g.interior(CY)
            counts = []
            for flip in (0, 1):
                w = source(flip)
                actual = set(g.edges(w))
                selected = {(i, j, g.child(w, i, j))
                            for i in range(len(g.words[w[0]]))
                            for j in range(len(g.words[w[1]]))
                            if predicted(flip, g, i, j)}
                assert actual == selected
                assert len(actual) == 2*g.n + 1
                for i, j, target in sorted(actual):
                    assert target in envelope()
                    assert g.child(reverse(w), j, i) == reverse(target)
                    assert g.interior(reverse(target))
                    witness.setdefault(target, dict(k=k, t=t, flip=flip, i=i, j=j))
                path = selected_path(flip, g)
                verify_selected(flip, g, path)
                assert len(path) == 4
                counts.append(len(actual))
                pairs += len(g.words[w[0]])*len(g.words[w[1]])
                accepted += len(actual)
                path_edges += len(path)

            assert g.child(Y0, g.n, k+2) == CY
            assert g.child(CY, 1, 2) == Y0
            assert g.interior(g.child(Y0, g.n, g.n)) == (t == 0)
            assert not g.interior(g.child(CY, 0, 2))
            assert not g.interior(g.child(CY, g.n+1, g.n))
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert set(witness) == envelope()
    return dict(scope="finite exact independent CY complete-star and selected-exit replay, not BH",
                members=len(rows), source_cells=2*len(rows),
                pairs=pairs, accepted=accepted, path_edges=path_edges,
                image_labels=len(witness), selected_exit_depth=4,
                cycle_Y0_CY_with_exit=True, all_child_productivity=False,
                forward_closed=False, universal_BH=False,
                witnesses=[dict(target=list(w), **rec) for w,rec in sorted(witness.items())],
                rows=rows)


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), indent=2, sort_keys=True))
