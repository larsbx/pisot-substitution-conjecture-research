"""Independent literal-word/Fraction R3/D3 replay and explicit source registry.

Finite implementation validation, separate from the universal guard derivation.
"""
from pathlib import Path
import runpy

ROOT = Path(__file__).parent
Geometry = runpy.run_path(str(ROOT/'class_a_boundary_children.py'))['Geometry']
p3 = runpy.run_path(str(ROOT/'class_a_boundary_p3_children.py'))
pp = runpy.run_path(str(ROOT/'class_a_boundary_p_children.py'))
eh = runpy.run_path(str(ROOT/'class_a_boundary_e_children.py'))
h3 = runpy.run_path(str(ROOT/'class_a_boundary_h3_children.py'))
R3 = (0, 2, 1, -1, 0)
D3 = (0, 1, 1, -1, -1)
X = (0, 0, 1, 0, -1)
C = (2, 2, 0, 0, 0)


def reverse(w):
    return (w[1], w[0], *(-z for z in w[2:]))


def source(kind):
    if kind not in range(4):
        raise ValueError('unknown R3/D3 orientation')
    w = (R3, D3)[kind//2]
    return reverse(w) if kind % 2 else w


def candidate(include_d3=False):
    out = p3['envelope']() | {X, reverse(X)}
    if include_d3:
        out |= {D3, reverse(D3)}
    assert len(out) == (41 if include_d3 else 39)
    return out


def interface(w, include_new=False):
    if w == C:
        return 'terminal'
    bases = [(p3['BASE'][1], 'T'), (p3['BASE'][2], 'U'),
             ((2, 0, 0, -1, 2), 'V'), (eh['BASE'][0], 'E'),
             ((2, 2, -1, 1, 1), 'T1'), ((2, 2, -1, 1, 2), 'T2'),
             ((0, 2, 1, -1, 1), 'Q3'), (X, 'X'),
             (pp['BASE'][0], 'P0'), (pp['BASE'][1], 'P1'), (h3['BASE'][0], 'H3')]
    if include_new:
        bases += [(R3, 'R3'), (D3, 'D3')]
    found = [name for label, name in bases if w in (label, reverse(label))]
    assert len(found) <= 1
    return found[0] if found else None


def registered_exit(w, include_new=False):
    return interface(w, include_new) not in (None, 'T2')


def reconciliation():
    rows = [dict(label=list(w), before=interface(w), after=interface(w, True),
                 before_exit=registered_exit(w), after_exit=registered_exit(w, True))
            for w in sorted(candidate())]
    assert sum(r['before'] is not None for r in rows) == 17
    assert sum(r['after'] is not None for r in rows) == 19
    assert sum(r['before_exit'] for r in rows) == 15
    assert sum(r['after_exit'] for r in rows) == 17
    after41 = sum(interface(w, True) is not None for w in candidate(True))
    assert after41 == 21
    return dict(scope='explicit named complete-star and exit interfaces; not an impossibility claim for unregistered labels',
                labels=39, terminal_labels=1, before_registered_including_terminal=17,
                before_unregistered=22, before_registered_exits_including_terminal=15,
                after_registered_including_terminal=19, after_unregistered=20,
                after_registered_exits_including_terminal=17,
                labels_after_D3=41, after41_registered_including_terminal=21,
                after41_unregistered=20, rows=rows)


def verify_native_registry(output):
    ids = {None: 0, 'terminal': 1, 'T': 2, 'U': 3, 'V': 4, 'E': 5,
           'T1': 6, 'T2': 7, 'Q3': 8, 'X': 9, 'R3': 10, 'D3': 11,
           'P0': 12, 'P1': 13, 'H3': 14}
    got = {}
    for line in output.splitlines():
        if not line.startswith('CLASS_A_R3_REGISTRY '):
            continue
        values = tuple(map(int, line.split()[1:]))
        if len(values) != 9 or values[:5] in got:
            raise ValueError('malformed or duplicate native registry row')
        got[values[:5]] = values[5:]
    want = {tuple(r['label']): (ids[r['before']], ids[r['after']],
                              int(r['before_exit']), int(r['after_exit']))
            for r in reconciliation()['rows']}
    if got != want:
        raise ValueError('native/source-oracle registry disagreement')


def predicted(kind, g, i, j):
    w = source(kind)
    if g.eps != -1:
        raise ValueError('R3/D3 packet requires the minus chamber')
    if not (0 <= i < len(g.words[w[0]]) and 0 <= j < len(g.words[w[1]])):
        raise ValueError('unavailable occurrence')
    a, b = (j, i) if kind % 2 else (i, j)
    n, d, t, A = g.n, g.d, g.t, g.n+g.d
    if kind//2 == 0:
        if 1 <= a <= A:
            return d-1 <= a <= d+2 if b == 0 else 1 <= b <= n-1 and a-b in (d+1, d+2)
        return a == A+1 and b in (n-1, n)
    if a == 0:
        return t <= 1 if b == 0 else t == 0 and b == 1
    if 1 <= a <= A:
        if b == 0:
            return t-1 <= a <= t
        if b <= n:
            return a-b in (t-1, t)
        return n+t <= a <= n+t+2
    return False


def envelope():
    base = ({(2, 0, 0, -1, r) for r in range(-1, 3)} |
            {(2, 2, 1, -1, r) for r in (-2, -1)} |
            {(0, 2, 1, -1, -2), D3} |
            {(0, 1, 0, -2, r) for r in (3, 4)} |
            {(2, 2, -1, -1, r) for r in (3, 4)} |
            {(0, 2, 0, -1, 3)} |
            {(2, 1, -1, -2, r) for r in (4, 5)} |
            {(2, 0, -1, -1, r) for r in (2, 3, 4)})
    assert len(base) == 18
    out = base | {reverse(w) for w in base}
    assert len(out) == 36
    return out


def path(kind, g):
    source(kind)
    if g.eps != -1:
        raise ValueError('R3/D3 packet requires the minus chamber')
    if kind//2 == 0:
        out = [(g.d, 0, p3['BASE'][1]), (1, 2, C)]
    else:
        out = [(g.t+1, 1, pp['BASE'][0])] + pp['path'](0, g)
    return [(j, i, reverse(w)) for i, j, w in out] if kind % 2 else out


def verify_star(kind, g, edges):
    w = source(kind)
    expected = 2*g.n+3 if kind//2 == 0 else 2*g.n+4+(g.t > 0)
    if len(edges) != expected or len(set(edges)) != len(edges):
        raise ValueError('incomplete or duplicate indexed star')
    for i, j, target in edges:
        if not (predicted(kind, g, i, j) and g.child(w, i, j) == target and g.interior(target)):
            raise ValueError('star has wrong indices, types, full offset or geometry')


def verify_path(w, g, packet, want):
    if g.eps != -1:
        raise ValueError('R3/D3 packet requires the minus chamber')
    if packet != want:
        raise ValueError('different intended occurrences/intermediates')
    for i, j, target in packet:
        if not (g.interior(w) and g.child(w, i, j) == target and g.interior(target)):
            raise ValueError('actual words, full transport or strict geometry failed')
        w = target
    if w != C:
        raise ValueError('wrong typed terminal')


def probe():
    rows, witnesses = [], {}
    pairs = accepted = path_edges = 0
    for k in range(13):
        for t in range(9):
            g = Geometry(-1, k, t)
            n, d, A = g.n, g.d, g.n+g.d
            counts = []
            for kind in range(4):
                w = source(kind)
                assert g.interior(w)
                actual = set(g.edges(w))
                chosen = {(i, j, g.child(w, i, j)) for i in range(len(g.words[w[0]]))
                          for j in range(len(g.words[w[1]])) if predicted(kind, g, i, j)}
                assert actual == chosen, (k, t, kind, actual ^ chosen)
                assert len(actual) == (2*n+3 if kind//2 == 0 else 2*n+4+(t > 0))
                verify_star(kind, g, list(actual))
                for i, j, target in sorted(actual):
                    assert target in envelope() and target[3] != 0
                    witnesses.setdefault(target, dict(k=k, t=t, kind=kind, i=i, j=j))
                    assert g.child(reverse(w), j, i) == reverse(target) and g.interior(reverse(target))
                p = path(kind, g)
                verify_path(w, g, p, p)
                assert len(p) == (2 if kind//2 == 0 else 6 if k == 0 else 4)
                pairs += len(g.words[w[0]])*len(g.words[w[1]])
                accepted += len(actual)
                path_edges += len(p)
                counts.append(len(actual))
            assert g.child(X, A+1, n) == R3 and R3 in candidate()
            assert g.child(reverse(X), n, A+1) == reverse(R3)
            if n >= 4:
                assert g.child(p3['BASE'][0], A+1, n-3) == R3
            else:
                assert n-3 == 0 and g.child(p3['BASE'][0], A+1, 0) == p3['BASE'][2] != R3
            assert g.child(R3, A+1, n) == D3 and D3 not in candidate()
            assert g.child(R3, d+1, 0) == (2, 0, 0, -1, 0)
            assert g.child(D3, t+1, 1) == pp['BASE'][0] and pp['BASE'][0] not in candidate(True)
            assert not g.interior(g.child(R3, d-2, 0))
            assert predicted(2, g, 0, 0) == (t <= 1)
            assert predicted(2, g, 0, 1) == (t == 0)
            rows.append(dict(k=k, t=t, n=n, d=d, counts=counts))
    assert set(witnesses) == envelope()
    return dict(scope='finite exact literal replay; universal guard proof separate; no all-child/global BH claim',
                members=len(rows), source_cells=4*len(rows), pairs=pairs, accepted=accepted,
                path_edges=path_edges, image_labels=36, R3_exit_at_most_two=True,
                D3_exit_at_most_six=True, candidate39_not_forward_closed=True,
                candidate41_not_forward_closed=True, all_direct_children_productivity_proved=False,
                reconciliation=reconciliation(),
                witnesses=[dict(target=list(w), **v) for w, v in sorted(witnesses.items())], rows=rows)


if __name__ == '__main__':
    import json
    print(json.dumps(probe(), indent=2, sort_keys=True))
