"""Independent literal-word/integer-polynomial/Fraction R5 replay.

Finite implementation validation; the quantified strict guards are documented separately.
"""
from pathlib import Path
import runpy

ROOT = Path(__file__).parent
y4 = runpy.run_path(str(ROOT/'class_a_boundary_y4_children.py'))
pp = y4['pp']
h3 = runpy.run_path(str(ROOT/'class_a_boundary_h3_children.py'))
Geometry, reverse = y4['Geometry'], y4['reverse']
R5 = (0, 2, 1, -1, -1)


def source(kind):
    if kind not in (0, 1):
        raise ValueError('unknown R5 orientation')
    return reverse(R5) if kind else R5


def interface(w, include_new=False):
    old = y4['interface'](w, True)
    if old is not None:
        return old
    for label, name in [(pp['BASE'][2], 'B2'), (pp['BASE'][3], 'B2h'),
                        (h3['BASE'][2], 'K')]:
        if w in (label, reverse(label)):
            return name
    return 'R5' if include_new and w in (R5, reverse(R5)) else None


def exit_interface(w):
    old = y4['exit_interface'](w, True)
    if old is not None:
        return old
    for label, name in [(pp['BASE'][2], 'B2'), (pp['BASE'][3], 'B2h'),
                        (h3['BASE'][2], 'K')]:
        if w in (label, reverse(label)):
            return name
    return None


def envelope():
    base = ({(0, 0, 0, -2, r) for r in (3, 4)} |
            {(2, 0, -1, -2, r) for r in (3, 4, 5)} |
            {(2, b, 0, -2, r) for b in (1, 2) for r in (2, 3)})
    out = base | {reverse(w) for w in base}
    assert len(out) == 18
    return out


def registry_rows(labels):
    return [dict(label=list(w), before=interface(w), after=interface(w, True),
                 exit=exit_interface(w)) for w in sorted(labels)]


def reconciliation():
    rows = registry_rows(y4['b3']['r3']['candidate'](True))
    return dict(labels=41, terminal_labels=1,
                before_registered_including_terminal=sum(r['before'] is not None for r in rows),
                after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                exits_including_terminal=sum(r['exit'] is not None for r in rows),
                rows=rows, image_rows=registry_rows(envelope()),
                reused_complete_families=['K', 'B2', 'B2h'])


def verify_native_registry(output):
    ids = {None: 0, 'terminal': 1, 'T': 2, 'U': 3, 'V': 4, 'E': 5,
           'T1': 6, 'T2': 7, 'Q3': 8, 'X': 9, 'R3': 10, 'D3': 11,
           'P0': 12, 'P1': 13, 'H3': 14, 'H1': 15, 'H2': 16, 'B3': 17,
           'Dxx': 18, 'B4': 19, 'D0': 20, 'F4': 21, 'L': 22, 'R4': 23,
           'E4': 24, 'D4': 25, 'Y4': 26, 'E5': 27, 'G5': 28,
           'R5': 29, 'D5': 30, 'M5': 31, 'CM': 32, 'F0': 33,
           'B2': 34, 'B2h': 35, 'K': 36}
    rec = reconciliation()
    for prefix, rows in [('CLASS_A_R5_CANDIDATE_REGISTRY ', rec['rows']),
                         ('CLASS_A_R5_IMAGE_REGISTRY ', rec['image_rows'])]:
        got = {}
        for line in output.splitlines():
            if line.startswith(prefix):
                values = tuple(map(int, line.split()[1:]))
                if len(values) != 8 or values[:5] in got:
                    raise ValueError('malformed or duplicate native registry row')
                got[values[:5]] = values[5:]
        want = {tuple(r['label']): tuple(ids[r[key]] for key in ('before', 'after', 'exit')) for r in rows}
        if got != want:
            raise ValueError('native/source registry disagreement')


def predicted(kind, g, i, j):
    w = source(kind)
    if g.eps != -1:
        raise ValueError('R5 requires the minus chamber')
    if not (0 <= i < len(g.words[w[0]]) and 0 <= j < len(g.words[w[1]])):
        raise ValueError('unavailable R5 occurrence')
    a, b = (j, i) if kind else (i, j)
    n, t, A = g.n, g.t, g.n+g.d
    if a == 0:
        return b == 0 and t <= 1
    if a <= A:
        if b == 0:
            return max(1, t-1) <= a <= t+1
        if b < n:
            return a-b in (t, t+1)
        return a in (n+t, n+t+1)
    return False


def path(kind, g):
    source(kind)
    return y4['path'](2+kind, g)


def verify_path(kind, g, packet):
    if len(packet) != 3:
        raise ValueError('R5 selected path has three edges')
    y4['verify_path'](source(kind), g, packet, path(kind, g))


def verify_star(kind, g, edges):
    w = source(kind)
    if g.eps != -1 or len(edges) != 2*g.n+(2 if g.t == 0 else 3):
        raise ValueError('wrong chamber or incomplete R5 star')
    seen = set()
    for i, j, target in edges:
        if ((i, j) in seen or not predicted(kind, g, i, j) or
                g.child(w, i, j) != target or not g.interior(target)):
            raise ValueError('duplicate occurrence or incorrect full packet')
        seen.add((i, j))


def probe():
    rows, witnesses = [], {}
    pairs = accepted = path_edges = reused_edges = 0
    for k in range(13):
        for t in range(9):
            g = Geometry(-1, k, t)
            counts = []
            for kind in (0, 1):
                w = source(kind)
                assert g.interior(w)
                packet = path(kind, g)
                verify_path(kind, g, packet)
                path_edges += len(packet)
                actual = set(g.edges(w))
                chosen = {(i, j, g.child(w, i, j)) for i in range(len(g.words[w[0]]))
                          for j in range(len(g.words[w[1]])) if predicted(kind, g, i, j)}
                assert actual == chosen, (k, t, kind, actual ^ chosen)
                verify_star(kind, g, list(actual))
                for i, j, target in sorted(actual):
                    assert target in envelope()
                    witnesses.setdefault(target, dict(k=k, t=t, kind=kind, i=i, j=j))
                    assert g.child(reverse(w), j, i) == reverse(target) and g.interior(reverse(target))
                parent = y4['source'](kind)
                i, j = (g.n-1, g.n+g.d+1) if kind else (g.n+g.d+1, g.n-1)
                assert g.child(parent, i, j) == w
                pairs += len(g.words[w[0]])*len(g.words[w[1]])
                accepted += len(actual)
                counts.append(len(actual))
                for group in (2, 3):
                    suffix = pp['path'](2*group+kind, g)
                    pp['verify_path'](2*group+kind, g, suffix)
                    reused_edges += len(suffix)
                suffix = h3['path'](4+kind, g)
                h3['verify_path'](4+kind, g, suffix)
                reused_edges += len(suffix)
            assert g.child(R5, t+1, 1) == reverse(pp['BASE'][3]) not in y4['b3']['r3']['candidate'](True)
            # K lies in this outgoing image but its already-proved exit leaves it.
            assert h3['BASE'][2] in envelope()
            edge = h3['path'](4, g)[0]
            assert g.child(h3['BASE'][2], edge[0], edge[1]) == edge[2] not in envelope()
            rows.append(dict(k=k, t=t, n=g.n, d=g.d, counts=counts))
    assert set(witnesses) == envelope()
    rec = reconciliation()
    assert (rec['before_registered_including_terminal'], rec['after_registered_including_terminal'], rec['exits_including_terminal']) == (29, 31, 31)
    assert sum(interface(w, True) is not None for w in envelope()) == 6
    assert sum(exit_interface(w) is not None for w in envelope()) == 6
    Y = y4['envelope']()
    assert sum(interface(w, True) is not None for w in Y) == 16
    return dict(scope='finite exact implementation replay; universal nine-kind guard proof separate; no global BH',
                members=len(rows), source_cells=2*len(rows), pairs=pairs, accepted=accepted,
                source_path_edges=path_edges, reused_exit_edges=reused_edges, image_labels=18, source_exit_bound=3,
                image_registered_stars=6, image_registered_exits=6, image_exit_gaps=12,
                Y4_image_registered_stars=16, Y4_image_registered_exits=18,
                old_R3_D3_image_registered_stars=22, old_R3_D3_image_registered_exits=22,
                all_direct_children_productive_proved=False, closed_carrier_proved=False,
                S41_escape=True, image_escape_via_K=True, reconciliation=rec,
                witnesses=[dict(target=list(w), **v) for w, v in sorted(witnesses.items())], rows=rows)


if __name__ == '__main__':
    import json
    print(json.dumps(probe(), sort_keys=True, indent=2))
