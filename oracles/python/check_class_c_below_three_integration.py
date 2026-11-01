"""Independent bounded assembly oracle; graph replay is checked separately.

Reads actual packet inventory instead of assuming every proposed line worked.
The native arithmetic regression is canonical; this oracle cross-checks its
finite category counts and detects missing line / finite-record mutations.
"""
import csv
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'evidence/class-c-below-three-2026-10-29'


def check(plans=None, records=None):
    if plans is None:
        plans = json.loads((PACKET / 'plan.json').read_text())
    if records is None:
        records = list(csv.DictReader((PACKET / 'finite-members.csv').open()))
    ends = {(r['sign'], int(r['d']), int(r['n'])) for r in records}
    assert len(ends) == len(records), 'duplicate finite record'
    results = []
    for eps, name, a, b in [(1, 'plus', 8, 16), (-1, 'minus', 16, 8)]:
        p = plans[name]
        assert (p['a'], p['b'], p['finite_a']) == (a, b, 8)
        lines = {r['c']: r for r in p['lines']}
        assert len(lines) == len(p['lines'])
        for c in range(1-b, 0):
            r = lines[c]
            assert r['floor'] == 32, 'required bridge is not certified from d=32'
            header = (PACKET / r['file']).read_text().splitlines()[0]
            assert f'eps={eps} ' in header and f'n-3d={c} ' in header and 'd>=32 ' in header
            assert r['args'] == ['line', str(eps), str(c)]
        counts = [0]*6
        for d in range(6, 65):
            for n in range(401):
                if n+n < 5*d+a:
                    kind = 0
                elif n >= 3*d:
                    kind = 4 if n < 4*d+(0 if eps == 1 else 4) else 5
                elif d < 32:
                    assert (name, d, n) in ends, ('missing finite member', name, d, n)
                    kind = 1
                elif n <= 3*d-b:
                    u, v = n+n-5*d-a, 3*d-n-b
                    assert u >= 0 and v >= 0
                    assert (d, n) == (a+2*b+u+2*v, 3*a+5*b+3*u+5*v)
                    kind = 2
                else:
                    r = lines[n-3*d]
                    assert d >= r['floor'] and d >= a-2*r['c']
                    kind = 3
                counts[kind] += 1
        results.append(f'MAINLINE_COVER eps={eps} d=6..64 n=0..400'+''.join(f' kind{i}={v}' for i,v in enumerate(counts)))
    return results


if __name__ == '__main__':
    output = check()
    if len(sys.argv) == 2:
        native = Path(sys.argv[1]).read_text().splitlines()
        assert native[:2] == output, 'native/oracle assembly category mismatch'
    print(json.dumps({'bounded_counts': output, 'actual_packet_inventory_checked': True,
                      'scope': 'bounded assembly cross-check, not a universal graph proof'}, indent=2))
