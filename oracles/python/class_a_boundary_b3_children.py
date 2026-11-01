"""Independent literal-word/integer-polynomial/Fraction B3 replay.

Finite implementation validation; the universal nine-kind guard proof is separate.
"""
from pathlib import Path
import runpy

ROOT = Path(__file__).parent
r3 = runpy.run_path(str(ROOT/'class_a_boundary_r3_children.py'))
eh = runpy.run_path(str(ROOT/'class_a_boundary_e_children.py'))
Geometry = r3['Geometry']
reverse = r3['reverse']
B3 = (2, 0, 0, -1, 0)
C = (2, 2, 0, 0, 0)


def source(kind):
    if kind not in (0, 1):
        raise ValueError('unknown B3 orientation')
    return reverse(B3) if kind else B3


def interface(w, include_b3=False):
    old = r3['interface'](w, True)
    if old is not None:
        return old
    if w in (eh['BASE'][1], reverse(eh['BASE'][1])):
        return 'H1'
    if w in (eh['BASE'][2], reverse(eh['BASE'][2])):
        return 'H2'
    if include_b3 and w in (B3, reverse(B3)):
        return 'B3'
    return None


def registered_exit(w, include_b3=False):
    return interface(w, include_b3) not in (None, 'T2')


def reconciliation():
    rows = [dict(label=list(w), before=interface(w), after=interface(w, True),
                 before_exit=registered_exit(w), after_exit=registered_exit(w, True))
            for w in sorted(r3['candidate'](True))]
    assert sum(r['before'] is not None for r in rows) == 21
    assert sum(r['after'] is not None for r in rows) == 23
    assert sum(r['before_exit'] for r in rows) == 19
    assert sum(r['after_exit'] for r in rows) == 21
    return dict(scope='explicit named complete-star and exit interfaces, not applicability of every repository mechanism',
                labels=41, terminal_labels=1, before_registered_including_terminal=21,
                before_unregistered=20, before_exits_including_terminal=19,
                after_registered_including_terminal=23, after_unregistered=18,
                after_exits_including_terminal=21, rows=rows)


def verify_native_registry(output):
    ids = {None: 0, 'terminal': 1, 'T': 2, 'U': 3, 'V': 4, 'E': 5,
           'T1': 6, 'T2': 7, 'Q3': 8, 'X': 9, 'R3': 10, 'D3': 11,
           'P0': 12, 'P1': 13, 'H3': 14, 'H1': 15, 'H2': 16, 'B3': 17}
    got = {}
    for line in output.splitlines():
        if not line.startswith('CLASS_A_B3_REGISTRY '):
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
        raise ValueError('B3 requires the minus chamber')
    if not (0 <= i < len(g.words[w[0]]) and 0 <= j < len(g.words[w[1]])):
        raise ValueError('unavailable occurrence')
    a, b = (j, i) if kind else (i, j)
    n, t, A = g.n, g.t, g.n+g.d
    if a == 0:
        return n+2 <= b <= n+4
    if a < n:
        if 1 <= b <= A:
            return b-a in (n+3, n+4)
        return t == 0 and a == n-1 and b == A+1
    return (b == A+1 and t <= 1) or (2*n+3 <= b <= min(2*n+4, A))


def envelope():
    base = ({(0, 2, 0, -1, r) for r in (1, 2, 3)} |
            {(2, 2, -1, -1, r) for r in (3, 4)} |
            {(1, 2, -1, -1, r) for r in (3, 4)} |
            {(1, 0, -1, -1, r) for r in (3, 4)} |
            {(2, 0, -1, -1, 4)})
    out = base | {reverse(w) for w in base}
    assert len(out) == 20
    return out


def path(kind, g):
    source(kind)
    if g.eps != -1:
        raise ValueError('B3 requires the minus chamber')
    out = [(0, g.n+2, eh['BASE'][1]), (1, 2, C)]
    return [(j, i, reverse(w)) for i, j, w in out] if kind else out


def verify_star(kind, g, edges):
    w = source(kind)
    if len(edges) != 2*g.n+2+(g.t > 0) or len(set(edges)) != len(edges):
        raise ValueError('incomplete or duplicate indexed star')
    for i, j, target in edges:
        if not (predicted(kind, g, i, j) and g.child(w, i, j) == target and g.interior(target)):
            raise ValueError('wrong indices, types, full offset or strict geometry')


def verify_path(w, g, packet, want):
    if g.eps != -1 or packet != want:
        raise ValueError('different chamber or intended occurrences/intermediates')
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
            for kind in range(2):
                w = source(kind)
                assert g.interior(w)
                actual = set(g.edges(w))
                chosen = {(i, j, g.child(w, i, j)) for i in range(len(g.words[w[0]]))
                          for j in range(len(g.words[w[1]])) if predicted(kind, g, i, j)}
                assert actual == chosen, (k, t, kind, actual ^ chosen)
                verify_star(kind, g, list(actual))
                for i, j, target in sorted(actual):
                    assert target in envelope() and target[3] != 0
                    witnesses.setdefault(target, dict(k=k, t=t, kind=kind, i=i, j=j))
                    assert g.child(reverse(w), j, i) == reverse(target) and g.interior(reverse(target))
                p = path(kind, g)
                verify_path(w, g, p, p)
                assert len(p) == 2
                assert g.child(r3['source'](kind), 0 if kind else d+1, d+1 if kind else 0) == w
                pairs += len(g.words[w[0]])*len(g.words[w[1]])
                accepted += len(actual)
                path_edges += len(p)
                counts.append(len(actual))
            # Conditional endpoints and false uniform RUNs remain explicit.
            assert predicted(0, g, n-1, A+1) == (t == 0)
            assert predicted(0, g, n, A+1) == (t <= 1)
            assert (2*n+3 <= A) == (t >= 1)
            if t == 0:
                assert 2*n+3 == A+1
                assert g.child(B3, n, 2*n+3) == (1, 0, -1, -1, 3)
            assert g.child(B3, 0, n+2) == eh['BASE'][1] not in r3['candidate'](True)
            assert g.child(B3, 1, n+4) == r3['pp']['BASE'][0]
            # Off-by-one is a different *interior* label, not the intended H1.
            assert g.child(B3, 0, n+3) == eh['BASE'][2] != eh['BASE'][1]
            rows.append(dict(k=k, t=t, n=n, d=d, counts=counts))
    assert set(witnesses) == envelope()
    old_image = r3['envelope']()
    assert sum(interface(w, True) is not None for w in old_image) == 18
    assert sum(registered_exit(w, True) for w in old_image) == 16
    assert sum(interface(w, True) is not None for w in envelope()) == 10
    assert sum(registered_exit(w, True) for w in envelope()) == 10
    return dict(scope='finite exact literal replay; universal guard proof separate; no all-child/global BH claim',
                members=len(rows), source_cells=2*len(rows), pairs=pairs, accepted=accepted,
                path_edges=path_edges, image_labels=20, typed_exit_two_edges=True,
                candidate41_escape_via_H1=True, all_direct_children_productivity_proved=False,
                outgoing_registered_stars=10, outgoing_registered_exits=10,
                old_R3_D3_outgoing_registered_stars=18, old_R3_D3_outgoing_registered_exits=16,
                reconciliation=reconciliation(),
                witnesses=[dict(target=list(w), **v) for w, v in sorted(witnesses.items())], rows=rows)


if __name__ == '__main__':
    import json
    print(json.dumps(probe(), sort_keys=True, indent=2))
