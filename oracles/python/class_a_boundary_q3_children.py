"""Independent literal-word/integer-polynomial/Fraction Q3 oracle.

Uses no Mojo output, guard evaluator or floating-point root approximation.
Finite replay checks implementation; the universal nine-kind proof is separate.
"""
from pathlib import Path
import runpy

Geometry = runpy.run_path(str(Path(__file__).with_name('class_a_boundary_children.py')))['Geometry']
Q3 = (0, 2, 1, -1, 1)
X = (0, 0, 1, 0, -1)
V = (2, 0, 0, -1, 2)
W = (1, 0, 0, 1, -1)
Q = (2, 0, 0, -1, 1)
C = (2, 2, 0, 0, 0)
P3 = (0, 2, 1, 3, -4)


def reverse(w):
    return (w[1], w[0], *(-x for x in w[2:]))


def source(kind):
    if kind not in (0, 1):
        raise ValueError('unknown Q3 orientation')
    return reverse(Q3) if kind else Q3


def predicted(kind, g, i, j):
    w = source(kind)
    if not (0 <= i < len(g.words[w[0]]) and 0 <= j < len(g.words[w[1]])):
        raise ValueError('unavailable occurrence')
    return (j, i) == (g.n+g.d+1, 0) if kind else (i, j) == (g.n+g.d+1, 0)


def path(kind, g):
    source(kind)
    out = [(g.n+g.d+1, 0, X), (g.d, 0, V), (g.n, 0, W), (1, 0, Q), (1, 2, C)]
    return [(j, i, reverse(w)) for i, j, w in out] if kind else out


def typed_coincidence(w):
    return w[0] == w[1] and w[2:] == (0, 0, 0)


def verify_path(w, g, packet, want):
    if packet != want:
        raise ValueError('different intended occurrences/intermediates')
    for i, j, target in packet:
        if not (g.interior(w) and g.child(w, i, j) == target and g.interior(target)):
            raise ValueError('literal types, full transport or strict geometry failed')
        w = target
    if w != C or not typed_coincidence(w):
        raise ValueError('wrong typed terminal')


def verify_star(kind, g, edges):
    w = source(kind)
    if len(edges) != 1:
        raise ValueError('not a singleton indexed star')
    i, j, target = edges[0]
    expected = reverse(X) if kind else X
    if not predicted(kind, g, i, j) or target != expected:
        raise ValueError('wrong singleton packet')
    if g.child(w, i, j) != target or not g.interior(target):
        raise ValueError('actual singleton edge failed')


def probe():
    rows = []
    witnesses = {}
    pairs = accepted = path_edges = cycle_edges = 0
    for k in range(13):
        for t in range(9):
            g = Geometry(-1, k, t)
            A, n = g.n+g.d, g.n
            assert g.child(P3, A+1, n-2) == Q3 and g.interior(Q3)
            assert g.child(reverse(P3), n-2, A+1) == reverse(Q3)
            counts = []
            for kind in (0, 1):
                w = source(kind)
                assert g.interior(w)
                actual = set(g.edges(w))
                chosen = {(i, j, g.child(w, i, j))
                          for i in range(len(g.words[w[0]]))
                          for j in range(len(g.words[w[1]])) if predicted(kind, g, i, j)}
                assert actual == chosen and len(actual) == 1
                verify_star(kind, g, list(actual))
                for i, j, target in actual:
                    witnesses.setdefault(target, dict(k=k, t=t, kind=kind, i=i, j=j))
                    assert g.child(reverse(w), j, i) == reverse(target)
                    assert g.interior(reverse(target))
                selected = path(kind, g)
                verify_path(w, g, selected, selected)
                # Independently check the four-edge tail from every actual
                # direct child, rather than extrapolating a selected subset.
                verify_path(next(iter(actual))[2], g, selected[1:], selected[1:])
                xs = reverse(X) if kind else X
                i, j = (n+1, A+1) if kind else (A+1, n+1)
                assert g.words[xs[0]][i] == w[0] and g.words[xs[1]][j] == w[1]
                assert g.child(xs, i, j) == w and g.interior(w)
                cycle_edges += 2
                path_edges += len(selected)
                pairs += len(g.words[w[0]])*len(g.words[w[1]])
                accepted += len(actual)
                counts.append(len(actual))
            assert not g.interior(g.child(Q3, A+1, 1))
            assert g.child(Q, 0, 2) == (0, 2, 1, 0, 0)  # exact endpoint contact
            assert not g.interior(g.child(Q, 0, 2))
            assert g.child(Q, n, n+1) == (1, 2, 0, 0, 0)
            assert not typed_coincidence((1, 2, 0, 0, 0))
            rows.append(dict(k=k, t=t, n=n, d=g.d, counts=counts))
    assert set(witnesses) == {X, reverse(X)}
    return dict(scope='finite independent replay; universal inequalities separate; two Q3 orientations, not global BH',
                members=len(rows), source_cells=2*len(rows), pairs=pairs, accepted=accepted,
                image_labels=2, path_edges=path_edges, cycle_edges=cycle_edges,
                Q3_typed_exit_at_most_five=True, every_direct_child_typed_tail_at_most_four=True,
                unresolved_direct_Q3_children=0, all_edge_descent=False, forward_closure=False,
                witnesses=[dict(target=list(w), **v) for w, v in sorted(witnesses.items())], rows=rows)


if __name__ == '__main__':
    import json
    print(json.dumps(probe(), indent=2, sort_keys=True))
