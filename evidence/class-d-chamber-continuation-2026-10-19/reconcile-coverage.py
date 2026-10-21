"""Reconcile execution-log identities; this does not certify mathematics."""
import json
from pathlib import Path

root = Path(__file__).resolve().parent
r = json.loads((root/'component-results.json').read_text())
assert (r['completed_strip_obligations'], r['distinct_completed_lines'], len(r['interfaces'])) == (73,69,6)
for name,w in r['wedges'].items():
    assert w['component_receipt'] and w['exit'] == 0, name
    assert w['core']['vertices'] == 164
    assert len(w['boundaries']) == w['core']['u0'] + w['core']['v0']
for j in range(1,7):
    assert (root/f'pinned-component-line{j}.exit').read_text().strip() == '0'
plan = json.loads((root.parent/'class-d-chamber-execution-2026-10-19/low-boundary-plan.json').read_text())
expected = {(tuple(p['coefficients']),c['low_wedge'],c['fixed_axis'],c['value']) for p in plan for c in p['covers']}
actual = set()
for k in range(5):
    w = r['wedges'][f'low{k}']
    a0 = w['core']['u0']
    for b in w['boundaries']:
        i = b['index']
        actual.add((tuple(b['coefficients']),k,'u' if i<a0 else 'v',i if i<a0 else i-a0))
assert expected == actual
for b in r['wedges']['high']['boundaries']:
    i = b['index']
    assert b['coefficients'] == [1,11+8*i,1,10+8*i,1,8+7*i]
print('Execution-log mapping agrees: 66 low + 7 high obligations; 69 distinct lines; six interfaces.')
