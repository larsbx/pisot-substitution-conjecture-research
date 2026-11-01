"""Independent B4 literal-word/Fraction replay and separate star/exit registry.

Finite implementation validation; universal guard and path arguments are separate.
"""
from pathlib import Path
import runpy

ROOT = Path(__file__).parent
b3 = runpy.run_path(str(ROOT/'class_a_boundary_b3_children.py'))
e2 = runpy.run_path(str(ROOT/'class_a_boundary_e2_children.py'))
h3 = runpy.run_path(str(ROOT/'class_a_boundary_h3_children.py'))
Geometry, reverse = b3['Geometry'], b3['reverse']
BASE = ((2, 0, 0, -1, -1), (0, 0, -1, -2, 3), (0, 2, -1, -2, 4))
C = (2, 2, 0, 0, 0)


def high(k, t):
    if min(k, t) < 0:
        raise ValueError('negative half-chamber parameter')
    return t > k or (t == k and k >= 2)


def source(kind):
    if kind not in range(6):
        raise ValueError('unknown B4/companion orientation')
    return reverse(BASE[kind//2]) if kind % 2 else BASE[kind//2]


def interface(w, include_new=False):
    old = b3['interface'](w, True)
    if old is not None:
        return old
    if w in (e2['BASE'][1], reverse(e2['BASE'][1])):
        return 'Dxx'
    if include_new and w in (BASE[0], reverse(BASE[0])):
        return 'B4'
    return None


def exit_interface(w, include_new=False):
    star = interface(w, include_new)
    if star not in (None, 'T2'):
        return star
    if include_new:
        for label, name in zip(BASE[1:], ('D0', 'F4')):
            if w in (label, reverse(label)):
                return name
    return None


def envelope():
    base = ({(0, 2, -1, -2, r) for r in range(4, 8)} |
            {(0, 0, -1, -2, r) for r in range(3, 8)} |
            {(2, 2, -2, -2, r) for r in range(6, 9)} |
            {(2, 0, -2, -2, r) for r in range(5, 9)})
    out = base | {reverse(w) for w in base}
    assert len(out) == 32
    return out


def registry_rows(labels):
    return [dict(label=list(w), before=interface(w), after=interface(w, True),
                 before_exit=exit_interface(w), after_exit=exit_interface(w, True))
            for w in sorted(labels)]


def reconciliation():
    rows = registry_rows(b3['r3']['candidate'](True))
    assert sum(r['before'] is not None for r in rows) == 23
    assert sum(r['after'] is not None for r in rows) == 25
    assert sum(r['before_exit'] is not None for r in rows) == 21
    assert sum(r['after_exit'] is not None for r in rows) == 23
    return dict(scope='named interfaces; selected companion exits do not imply complete stars',
                labels=41, terminal_labels=1, before_registered_including_terminal=23,
                before_unregistered=18, before_exits_including_terminal=21,
                after_registered_including_terminal=25, after_unregistered=16,
                after_exits_including_terminal=23, rows=rows,
                image_rows=registry_rows(envelope()))


def verify_native_registry(output):
    ids = {None: 0, 'terminal': 1, 'T': 2, 'U': 3, 'V': 4, 'E': 5,
           'T1': 6, 'T2': 7, 'Q3': 8, 'X': 9, 'R3': 10, 'D3': 11,
           'P0': 12, 'P1': 13, 'H3': 14, 'H1': 15, 'H2': 16, 'B3': 17,
           'Dxx': 18, 'B4': 19, 'D0': 20, 'F4': 21}
    rec = reconciliation()
    for prefix, rows in [('CLASS_A_B4_CANDIDATE_REGISTRY ', rec['rows']),
                         ('CLASS_A_B4_IMAGE_REGISTRY ', rec['image_rows'])]:
        got = {}
        for line in output.splitlines():
            if not line.startswith(prefix):
                continue
            values = tuple(map(int, line.split()[1:]))
            if len(values) != 9 or values[:5] in got:
                raise ValueError('malformed or duplicate native registry row')
            got[values[:5]] = values[5:]
        want = {tuple(r['label']): tuple(ids[r[key]] for key in
                ('before', 'after', 'before_exit', 'after_exit')) for r in rows}
        if got != want:
            raise ValueError('native/source-oracle registry disagreement')


def predicted(kind, g, i, j):
    if kind not in (0, 1):
        raise ValueError('companions have no complete-star interface')
    w = source(kind)
    if g.eps != -1:
        raise ValueError('B4 requires the minus chamber')
    if not (0 <= i < len(g.words[w[0]]) and 0 <= j < len(g.words[w[1]])):
        raise ValueError('unavailable occurrence')
    a, b = (j, i) if kind else (i, j)
    n, t, A = g.n, g.t, g.n+g.d
    H = int(high(g.k, t))
    if a == 0:
        return t <= 3+H if b == A+1 else 2*n+4 <= b <= 2*n+6+H
    if a <= n-1:
        if b == A+1:
            return max(1, t-3-H) <= a <= t-1
        return 1 <= b <= A and b-a in (2*n+5+H, 2*n+6+H)
    return False


def path(kind, g):
    source(kind)
    if g.eps != -1:
        raise ValueError('B4 requires the minus chamber')
    if kind//2 == 0:
        if g.t == 0:
            out = [(0, g.n+g.d+1, BASE[1])] + path(2, g)
        elif g.t == 1:
            out = [(0, g.n+g.d+1, reverse(e2['BASE'][1]))] + e2['path'](3, g)
        else:
            out = [(0, 2*g.n+4, BASE[2])] + path(4, g)
    elif kind//2 == 1:
        out = [(0, g.d+3, reverse(b3['r3']['p3']['BASE'][1])), (2, 1, C)]
    else:
        out = [(0, g.t+2, reverse(h3['BASE'][2]))] + h3['path'](5, g)
    return [(j, i, reverse(w)) for i, j, w in out] if kind % 2 else out


def verify_star(kind, g, edges):
    if kind not in (0, 1):
        raise ValueError('companions have no complete-star interface')
    w = source(kind)
    if len(edges) != max(1, 2*g.t-1) or len(set(edges)) != len(edges):
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
    pairs = accepted = b4_edges = companion_edges = 0
    S = b3['r3']['candidate'](True)
    assert envelope().isdisjoint(S)
    for k in range(13):
        for t in range(9):
            g = Geometry(-1, k, t)
            n, d, A = g.n, g.d, g.n+g.d
            assert g.sign((-2*n-5, 2, 0)) == (1 if high(k, t) else -1)
            counts = []
            for kind in range(6):
                w = source(kind)
                assert g.interior(w)
                packet = path(kind, g)
                verify_path(w, g, packet, packet)
                assert len(packet) == ((3 if t == 0 else 5) if kind//2 == 0 else 2 if kind//2 == 1 else 4)
                if kind >= 2:
                    companion_edges += len(packet)
                    continue
                b4_edges += len(packet)
                actual = set(g.edges(w))
                chosen = {(i, j, g.child(w, i, j)) for i in range(len(g.words[w[0]]))
                          for j in range(len(g.words[w[1]])) if predicted(kind, g, i, j)}
                assert actual == chosen, (k, t, kind, actual ^ chosen)
                verify_star(kind, g, list(actual))
                for i, j, target in sorted(actual):
                    assert target in envelope() and target[3] != 0 and target not in S
                    witnesses.setdefault(target, dict(k=k, t=t, kind=kind, i=i, j=j))
                    assert g.child(reverse(w), j, i) == reverse(target) and g.interior(reverse(target))
                if t <= 1:
                    assert len(actual) == 1 and packet[0] in actual
                assert g.child(b3['r3']['source'](kind), 0 if kind else d+2, d+2 if kind else 0) == w
                pairs += len(g.words[w[0]])*len(g.words[w[1]])
                accepted += len(actual)
                counts.append(len(actual))
            if t == 0:
                assert 2*n+4 == A+2  # proposed uniform FR is not an occurrence
            elif t == 1:
                assert 2*n+4 == A+1
                assert g.child(BASE[0], 0, 2*n+4) == reverse(e2['BASE'][1]) != BASE[2]
            else:
                assert g.child(BASE[0], 0, 2*n+4) == BASE[2]
            rows.append(dict(k=k, t=t, n=n, d=d, high=high(k, t), counts=counts))
    assert set(witnesses) == envelope()
    assert sum(interface(w, True) is not None for w in envelope()) == 2
    assert sum(exit_interface(w, True) is not None for w in envelope()) == 6
    old = b3['r3']['envelope']()
    assert sum(interface(w, True) is not None for w in old) == 20
    assert sum(exit_interface(w, True) is not None for w in old) == 18
    return dict(scope='finite exact implementation replay; universal guards and paths separate; no global BH claim',
                members=len(rows), source_cells=2*len(rows), path_source_cells=6*len(rows),
                pairs=pairs, accepted=accepted, b4_path_edges=b4_edges,
                companion_path_edges=companion_edges, path_edges=b4_edges+companion_edges,
                image_labels=32, B4_typed_exit_at_most_five=True,
                D0_uniform_exit_two=True, F4_uniform_exit_four=True,
                companion_complete_stars_proved=False,
                all_direct_children_productive_on_t_le_1=True,
                all_direct_children_productive_for_all_t_proved=False,
                outgoing_registered_stars=2, outgoing_registered_exits=6,
                image_disjoint_from_candidate41=True,
                old_R3_D3_outgoing_registered_stars=20, old_R3_D3_outgoing_registered_exits=18,
                reconciliation=reconciliation(),
                witnesses=[dict(target=list(w), **v) for w, v in sorted(witnesses.items())], rows=rows)


if __name__ == '__main__':
    import json
    print(json.dumps(probe(), sort_keys=True, indent=2))
