"""Independent literal-word/Fraction Y4 stars and every-first-choice replay.

Finite implementation validation; universal guards and tail proofs are separate.
"""
from pathlib import Path
import runpy

ROOT = Path(__file__).parent
r4 = runpy.run_path(str(ROOT/'class_a_boundary_r4_children.py'))
ww = runpy.run_path(str(ROOT/'class_a_boundary_w_children.py'))
b4, b3 = r4['b4'], r4['b4']['b3']
pp, p3 = r4['pp'], b3['r3']['p3']
Geometry, reverse = r4['Geometry'], r4['reverse']
BASE = ((0, 2, 1, 0, -1), (0, 2, 1, -1, -1), (0, 1, 1, -1, 0),
        (2, 2, -1, 1, 2), (2, 0, 0, 3, -3), (1, 0, 0, 3, -3), (2, 0, -1, 0, 2))
V, T1, C = (2, 0, 0, -1, 2), (2, 2, -1, 1, 1), (2, 2, 0, 0, 0)


def source(kind):
    if kind not in range(14):
        raise ValueError('unknown Y4/companion orientation')
    return reverse(BASE[kind//2]) if kind % 2 else BASE[kind//2]


def interface(w, include_new=False):
    old = r4['interface'](w, True)
    if old is not None:
        return old
    if include_new and w in (BASE[0], reverse(BASE[0])):
        return 'Y4'
    return None


def exit_interface(w, include_new=False):
    old = r4['exit_interface'](w, True)
    if old is not None:
        return old
    if include_new:
        for label, name in zip(BASE[1:], ('R5', 'D5', 'T2', 'M5', 'CM', 'F0')):
            if w in (label, reverse(label)):
                return name
    return None


def envelope():
    base = ({(2, 0, 0, -1, r) for r in range(-1, 3)} |
            {(2, 2, 1, -1, r) for r in (-2, -1)} |
            {(0, 2, 1, -1, r) for r in (-2, -1)} | {BASE[2]})
    out = base | {reverse(w) for w in base}
    assert len(out) == 18
    return out


def registry_rows(labels):
    return [dict(label=list(w), before=interface(w), after=interface(w, True),
                 before_exit=exit_interface(w), after_exit=exit_interface(w, True))
            for w in sorted(labels)]


def reconciliation():
    rows = registry_rows(b3['r3']['candidate'](True))
    assert sum(r['before'] is not None for r in rows) == 27
    assert sum(r['after'] is not None for r in rows) == 29
    assert sum(r['before_exit'] is not None for r in rows) == 27
    assert sum(r['after_exit'] is not None for r in rows) == 31
    return dict(scope='named complete-star and uniform-exit interfaces, not a closed/global carrier',
                labels=41, terminal_labels=1, before_registered_including_terminal=27,
                before_unregistered=14, before_exits_including_terminal=27,
                after_registered_including_terminal=29, after_unregistered=12,
                after_exits_including_terminal=31, rows=rows,
                image_rows=registry_rows(envelope()))


def verify_native_registry(output):
    ids = {None: 0, 'terminal': 1, 'T': 2, 'U': 3, 'V': 4, 'E': 5,
           'T1': 6, 'T2': 7, 'Q3': 8, 'X': 9, 'R3': 10, 'D3': 11,
           'P0': 12, 'P1': 13, 'H3': 14, 'H1': 15, 'H2': 16, 'B3': 17,
           'Dxx': 18, 'B4': 19, 'D0': 20, 'F4': 21, 'L': 22, 'R4': 23,
           'E4': 24, 'D4': 25, 'Y4': 26, 'E5': 27, 'G5': 28,
           'R5': 29, 'D5': 30, 'M5': 31, 'CM': 32, 'F0': 33}
    rec = reconciliation()
    for prefix, rows in [('CLASS_A_Y4_CANDIDATE_REGISTRY ', rec['rows']),
                         ('CLASS_A_Y4_IMAGE_REGISTRY ', rec['image_rows'])]:
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
        raise ValueError('new complete-star interface only covers Y4')
    w = source(kind)
    if g.eps != -1:
        raise ValueError('Y4 requires the minus chamber')
    if not (0 <= i < len(g.words[w[0]]) and 0 <= j < len(g.words[w[1]])):
        raise ValueError('unavailable occurrence')
    a, b = (j, i) if kind else (i, j)
    n, d, A = g.n, g.d, g.n+g.d
    if 1 <= a <= A:
        return d <= a <= d+3 if b == 0 else 1 <= b <= n-1 and a-b in (d+2, d+3)
    return a == A+1 and b in (n-2, n-1, n)


def seed_suffix(start, flip, g):
    if g.eps != -1 or start not in (1, 3) or flip not in (0, 1):
        raise ValueError('unknown inherited seed suffix')
    out = [(i, j, target) for w, i, j, target in ww['path'](g)[start:]]
    return [(j, i, reverse(w)) for i, j, w in out] if flip else out


def path(kind, g):
    source(kind)
    if g.eps != -1:
        raise ValueError('Y4 requires the minus chamber')
    group = kind//2
    if group == 0:
        return r4['path'](6+kind%2, g)
    if group == 1:
        out = [(g.t+1, 1, reverse(pp['BASE'][3]))] + pp['path'](7, g)
    elif group == 2:
        out = [(g.d+1, 1, C)]
    elif group == 3:
        out = [(g.n, 0, BASE[5])] + path(10, g) if g.t == 0 else [(g.k+3, 0, BASE[4])] + path(8, g)
    elif group == 4:
        out = [(2, 0, BASE[6])] + path(12, g)
    elif group == 5:
        out = [(2, 0, V)] + seed_suffix(3, 0, g)
    else:
        out = [(0, g.t+1, pp['BASE'][4])] + pp['path'](8, g)
    return [(j, i, reverse(w)) for i, j, w in out] if kind % 2 else out


def tail(w, g):
    if g.eps != -1 or w not in envelope():
        raise ValueError('no Y4-image tail interface')
    for flip in range(2):
        rv = reverse if flip else lambda v: v
        if w == rv(V):
            return seed_suffix(3, flip, g)
        if w == rv(p3['BASE'][1]):
            return [(2, 1, C)] if flip else [(1, 2, C)]
        if w == rv(b3['B3']):
            return b3['path'](flip, g)
        if w == rv(b4['BASE'][0]):
            return b4['path'](flip, g)
        if w == rv(T1):
            return seed_suffix(1, flip, g)
        if w == source(6+flip):
            return path(6+flip, g)
        if w == r4['source'](flip):
            return r4['path'](flip, g)
        if w == source(2+flip):
            return path(2+flip, g)
        if w == source(4+flip):
            return path(4+flip, g)
    raise ValueError('complete tail dispatch missed an image label')


def walk(kind, g, edge):
    i, j, target = edge
    if not (predicted(kind, g, i, j) and g.child(source(kind), i, j) == target):
        raise ValueError('wrong first-choice packet')
    return [edge] + tail(target, g)


def verify_path(w, g, packet, want):
    if g.eps != -1 or packet != want:
        raise ValueError('different chamber or intended occurrences/intermediates')
    for i, j, target in packet:
        if not (g.interior(w) and g.child(w, i, j) == target and g.interior(target)):
            raise ValueError('actual words, full transport or strict geometry failed')
        w = target
    if w != C:
        raise ValueError('wrong typed terminal')


def verify_walk(kind, g, edge, packet):
    if len(packet) > 8:
        raise ValueError('first-choice walk exceeds its bound')
    verify_path(source(kind), g, packet, walk(kind, g, edge))


def verify_star(kind, g, edges):
    if kind not in (0, 1):
        raise ValueError('no new companion complete-star interface')
    w = source(kind)
    if len(edges) != 2*g.n+2 or len(set(edges)) != len(edges):
        raise ValueError('incomplete or duplicate indexed star')
    for i, j, target in edges:
        if not (predicted(kind, g, i, j) and g.child(w, i, j) == target and g.interior(target)):
            raise ValueError('wrong indices, types, full offset or strict geometry')


def path_length(kind, g):
    return (2, 3, 1, 5 if g.t == 0 else 7, 6, 4, 5)[kind//2]


def probe():
    rows, witnesses = [], {}
    pairs = accepted = source_edges = walk_edges = max_walk = 0
    S = b3['r3']['candidate'](True)
    for k in range(13):
        for t in range(9):
            g = Geometry(-1, k, t)
            n, d, A = g.n, g.d, g.n+g.d
            counts = []
            for kind in range(14):
                w = source(kind)
                assert g.interior(w)
                packet = path(kind, g)
                verify_path(w, g, packet, packet)
                assert len(packet) == path_length(kind, g)
                source_edges += len(packet)
                if kind >= 2:
                    continue
                actual = set(g.edges(w))
                chosen = {(i, j, g.child(w, i, j)) for i in range(len(g.words[w[0]]))
                          for j in range(len(g.words[w[1]])) if predicted(kind, g, i, j)}
                assert actual == chosen, (k, t, kind, actual ^ chosen)
                verify_star(kind, g, list(actual))
                for edge in sorted(actual):
                    i, j, target = edge
                    assert target in envelope() and exit_interface(target, True) is not None
                    witnesses.setdefault(target, dict(k=k, t=t, kind=kind, i=i, j=j))
                    assert g.child(reverse(w), j, i) == reverse(target) and g.interior(reverse(target))
                    packet = walk(kind, g, edge)
                    verify_walk(kind, g, edge, packet)
                    assert 2 <= len(packet) <= 8
                    walk_edges += len(packet)
                    max_walk = max(max_walk, len(packet))
                assert g.child(p3['source'](2+kind), 1 if kind else 0, 0 if kind else 1) == w
                assert g.child(w, 0 if kind else d+1, d+1 if kind else 0) == p3['source'](2+kind)
                assert g.child(w, n if kind else A+1, A+1 if kind else n) == source(4+kind) not in S
                pairs += len(g.words[w[0]])*len(g.words[w[1]])
                accepted += len(actual)
                counts.append(len(actual))
            # Exact endpoint: t=0 T2(k+3,0) is LAST c, not RUN y.
            assert g.child(BASE[3], k+3, 0) == (BASE[5] if t == 0 else BASE[4])
            assert g.child(BASE[1], t+1, 1) == reverse(pp['BASE'][3])
            assert g.child(BASE[2], d+1, 1) == C
            rows.append(dict(k=k, t=t, n=n, d=d, counts=counts))
    assert set(witnesses) == envelope()
    assert sum(interface(w, True) is not None for w in envelope()) == 14
    assert sum(exit_interface(w, True) is not None for w in envelope()) == 18
    old = b3['r3']['envelope']()
    assert sum(interface(w, True) is not None for w in old) == 22
    assert sum(exit_interface(w, True) is not None for w in old) == 22
    return dict(scope='finite exact implementation replay; universal guards and all-child tails separate; no global BH claim',
                members=len(rows), source_cells=2*len(rows), path_source_cells=14*len(rows),
                pairs=pairs, accepted=accepted, source_path_edges=source_edges,
                all_child_walk_edges=walk_edges, max_walk=max_walk, image_labels=18,
                all_direct_children_productive=True, direct_child_tail_bound=7, first_choice_walk_bound=8,
                T2_uniform_exit_bound=7, Y4_source_exit_bound=2,
                Y4_T_cycle=True, candidate41_escape_via_D5=True,
                outgoing_registered_stars=14, outgoing_registered_exits=18,
                old_R3_D3_outgoing_registered_stars=22, old_R3_D3_outgoing_registered_exits=22,
                new_companion_complete_stars_proved=False, closed_carrier_proved=False,
                reconciliation=reconciliation(),
                witnesses=[dict(target=list(w), **v) for w, v in sorted(witnesses.items())], rows=rows)


if __name__ == '__main__':
    import json
    print(json.dumps(probe(), sort_keys=True, indent=2))
