"""Independent exact R4 literal-word replay with separate star/exit registries.

Finite implementation validation, not the universal guard or path proof.
"""
from pathlib import Path
import runpy

ROOT = Path(__file__).parent
b4 = runpy.run_path(str(ROOT/'class_a_boundary_b4_children.py'))
h3 = b4['h3']
pp = b4['b3']['r3']['pp']
Geometry, reverse = b4['Geometry'], b4['reverse']
BASE = ((0, 2, 1, -1, -2), (0, 1, 0, -3, 3), (0, 2, 0, -3, 3),
        (0, 2, 1, 0, -1), (0, 1, 0, -3, 4), (0, 2, 0, -3, 5))
T = b4['b3']['r3']['p3']['BASE'][1]
C = (2, 2, 0, 0, 0)


def source(kind):
    if kind not in range(12):
        raise ValueError('unknown R4/companion orientation')
    return reverse(BASE[kind//2]) if kind % 2 else BASE[kind//2]


def interface(w, include_new=False):
    old = b4['interface'](w, True)
    if old is not None:
        return old
    if w in (h3['BASE'][3], reverse(h3['BASE'][3])):
        return 'L'
    if include_new and w in (BASE[0], reverse(BASE[0])):
        return 'R4'
    return None


def exit_interface(w, include_new=False):
    old = b4['exit_interface'](w, True)
    if old is not None:
        return old
    star = interface(w, include_new)
    if star not in (None, 'T2'):
        return star
    if include_new:
        for label, name in zip(BASE[1:], ('E4', 'D4', 'Y4', 'E5', 'G5')):
            if w in (label, reverse(label)):
                return name
    return None


def envelope():
    base = ({(0, 2, 0, -3, r) for r in (3, 4, 5)} |
            {(0, 1, 0, -3, r) for r in (3, 4, 5)} |
            {(2, 2, -1, -3, r) for r in (5, 6)} |
            {(2, 1, -1, -3, r) for r in (5, 6)})
    out = base | {reverse(w) for w in base}
    assert len(out) == 20
    return out


def registry_rows(labels):
    return [dict(label=list(w), before=interface(w), after=interface(w, True),
                 before_exit=exit_interface(w), after_exit=exit_interface(w, True))
            for w in sorted(labels)]


def reconciliation():
    rows = registry_rows(b4['b3']['r3']['candidate'](True))
    assert sum(r['before'] is not None for r in rows) == 25
    assert sum(r['after'] is not None for r in rows) == 27
    assert sum(r['before_exit'] is not None for r in rows) == 23
    assert sum(r['after_exit'] is not None for r in rows) == 27
    return dict(scope='named interfaces, with new Y4 exits but no complete Y4 star',
                labels=41, terminal_labels=1, before_registered_including_terminal=25,
                before_unregistered=16, before_exits_including_terminal=23,
                after_registered_including_terminal=27, after_unregistered=14,
                after_exits_including_terminal=27, rows=rows,
                image_rows=registry_rows(envelope()))


def verify_native_registry(output):
    ids = {None: 0, 'terminal': 1, 'T': 2, 'U': 3, 'V': 4, 'E': 5,
           'T1': 6, 'T2': 7, 'Q3': 8, 'X': 9, 'R3': 10, 'D3': 11,
           'P0': 12, 'P1': 13, 'H3': 14, 'H1': 15, 'H2': 16, 'B3': 17,
           'Dxx': 18, 'B4': 19, 'D0': 20, 'F4': 21, 'L': 22, 'R4': 23,
           'E4': 24, 'D4': 25, 'Y4': 26, 'E5': 27, 'G5': 28}
    rec = reconciliation()
    for prefix, rows in [('CLASS_A_R4_CANDIDATE_REGISTRY ', rec['rows']),
                         ('CLASS_A_R4_IMAGE_REGISTRY ', rec['image_rows'])]:
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
        raise ValueError('R4 requires the minus chamber')
    if not (0 <= i < len(g.words[w[0]]) and 0 <= j < len(g.words[w[1]])):
        raise ValueError('unavailable occurrence')
    a, b = (j, i) if kind else (i, j)
    n, t, k, A = g.n, g.t, g.k, g.n+g.d
    if a == 0:
        return t <= 2 if b == n else k+3 <= b <= k+5
    if a <= A:
        if b == n:
            return max(1, t-2) <= a <= t-1
        return 1 <= b <= n-1 and b-a in (k+4, k+5)
    return False


def path(kind, g):
    source(kind)
    if g.eps != -1:
        raise ValueError('R4 requires the minus chamber')
    group = kind//2
    if group == 0:
        if g.t == 0:
            out = [(0, g.n, BASE[1])] + path(2, g)
        elif g.t == 1:
            out = [(0, g.k+3, BASE[2])] + path(4, g)
        else:
            out = [(0, g.k+4, reverse(h3['BASE'][3]))] + h3['path'](7, g)
    elif group == 1:
        out = [(0, 3, reverse(T)), (2, 1, C)]
    elif group == 2:
        if g.n == 3:
            out = [(0, 2, (0, 2, 1, 0, -2)), (0, 0, (0, 0, 0, -2, 4)),
                   (2*g.n+1, 0, h3['BASE'][1])] + h3['path'](2, g)
        else:
            out = [(0, 3, BASE[3])] + path(6, g)
    elif group == 3:
        out = [(g.d+1, 0, T), (1, 2, C)]
    elif group == 4:
        out = [(g.n, 1, pp['BASE'][3])] + pp['path'](6, g)
    else:
        out = [(2*g.n, 0, h3['BASE'][1])] + h3['path'](2, g)
    return [(j, i, reverse(w)) for i, j, w in out] if kind % 2 else out


def verify_star(kind, g, edges):
    if kind not in (0, 1):
        raise ValueError('companions have no complete-star interface')
    w = source(kind)
    if len(edges) != max(1, 2*g.t) or len(set(edges)) != len(edges):
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


def path_length(kind, g):
    return ((4 if g.t == 1 else 3), 2, (7 if g.n == 3 else 3), 2, 3, 5)[kind//2]


def probe():
    rows, witnesses = [], {}
    pairs = accepted = r4_edges = companion_edges = 0
    S = b4['b3']['r3']['candidate'](True)
    assert envelope().isdisjoint(S)
    for k in range(13):
        for t in range(9):
            g = Geometry(-1, k, t)
            n, d, A = g.n, g.d, g.n+g.d
            counts = []
            for kind in range(12):
                w = source(kind)
                assert g.interior(w)
                packet = path(kind, g)
                verify_path(w, g, packet, packet)
                assert len(packet) == path_length(kind, g)
                if kind >= 2:
                    companion_edges += len(packet)
                    continue
                r4_edges += len(packet)
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
                        target_kind = next(z for z in range(2, 12) if source(z) == target)
                        suffix = path(target_kind, g)
                        verify_path(target, g, suffix, suffix)
                assert g.child(b4['b3']['r3']['source'](kind), n-1 if kind else A+1, A+1 if kind else n-1) == w
                pairs += len(g.words[w[0]])*len(g.words[w[1]])
                accepted += len(actual)
                counts.append(len(actual))
            if n == 3:
                assert g.child(BASE[2], 0, 3) == (0, 1, 1, 0, -1) != BASE[3]
                assert g.interior(g.child(BASE[2], 0, 3))  # real LAST c, not RUN y
            else:
                assert g.child(BASE[2], 0, 3) == BASE[3]
            assert predicted(0, g, 0, n) == (t <= 2)
            rows.append(dict(k=k, t=t, n=n, d=d, counts=counts))
    assert set(witnesses) == envelope()
    assert sum(interface(w, True) is not None for w in envelope()) == 2
    assert sum(exit_interface(w, True) is not None for w in envelope()) == 10
    old = b4['b3']['r3']['envelope']()
    assert sum(interface(w, True) is not None for w in old) == 22
    assert sum(exit_interface(w, True) is not None for w in old) == 20
    return dict(scope='finite exact implementation replay; universal guards and paths separate; no global BH claim',
                members=len(rows), source_cells=2*len(rows), path_source_cells=12*len(rows),
                pairs=pairs, accepted=accepted, r4_path_edges=r4_edges,
                companion_path_edges=companion_edges, path_edges=r4_edges+companion_edges,
                image_labels=20, R4_typed_exit_at_most_four=True,
                companion_exit_bounds=dict(E4=2, D4=7, Y4=2, E5=3, G5=5),
                companion_complete_stars_proved=False,
                all_direct_children_productive_on_t_le_1=True,
                all_direct_children_productive_for_all_t_proved=False,
                outgoing_registered_stars=2, outgoing_registered_exits=10,
                image_disjoint_from_candidate41=True,
                old_R3_D3_outgoing_registered_stars=22, old_R3_D3_outgoing_registered_exits=20,
                reconciliation=reconciliation(),
                witnesses=[dict(target=list(w), **v) for w, v in sorted(witnesses.items())], rows=rows)


if __name__ == '__main__':
    import json
    print(json.dumps(probe(), sort_keys=True, indent=2))
