"""Reconcile native serial log receipts with the earlier component campaign.

This is provenance validation, not a mathematical certificate or a generator
of the native certificate marker. Every conclusion is attributed to source logs.
"""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
prior = json.loads((ROOT.parent / 'class-d-chamber-continuation-2026-10-19/component-results.json').read_text())
assert (ROOT / 'aggregate.exit').read_text().strip() == '0'
lines = (ROOT / 'aggregate.log').read_text().splitlines()
core_re = re.compile(r'WEDGE_CORE_CERTIFIED u0= (\d+) v0= (\d+) vertices= (\d+)')
begin_re = re.compile(r'BEGIN_BOUNDARY_LINE (\d+) class D line \(norm mode\) p = (-?\d+)n \+ (-?\d+) q = (-?\d+)n \+ (-?\d+) r = (-?\d+)n \+ (-?\d+)')
done_re = re.compile(r'BOUNDARY_LINE_CERTIFIED (\d+) q0= (\d+) finite_pip= (\d+)')
interface_re = re.compile(r'BEGIN_INTERFACE_LINE (\d+)')
tail_re = re.compile(r'LINE_SYMBOLIC_CERTIFIED q0= (\d+) vertices= (\d+)')
receipt_re = re.compile(r'CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= (\d+) explicit_lines= (\d+) boundary_lines= (\d+) finite_prefix_pip= (\d+) max_symbolic_vertices= (\d+)')
wedges, interfaces, receipts = [], [], []
line_vertex_counts = []
pending = None
interface = None
for line in lines:
    if tail := tail_re.fullmatch(line):
        line_vertex_counts.append(int(tail[2]))
    if m := core_re.fullmatch(line):
        assert pending is None and interface is None
        wedges.append({'core':dict(zip(('u0','v0','vertices'),map(int,m.groups()))),'boundaries':[]})
    elif m := begin_re.fullmatch(line):
        assert wedges and pending is None and interface is None
        fields = list(map(int,m.groups()))
        pending = {'index':fields[0],'coefficients':fields[1:]}
    elif m := done_re.fullmatch(line):
        i,q0,finite = map(int,m.groups())
        assert pending is not None and pending['index'] == i
        pending.update(q0=q0,finite_pip=finite)
        wedges[-1]['boundaries'].append(pending)
        pending = None
    elif m := interface_re.fullmatch(line):
        assert pending is None
        interface = {'line':int(m[1])}
        interfaces.append(interface)
    elif interface is not None and (m := tail_re.fullmatch(line)):
        interface.update(q0=int(m[1]), vertices=int(m[2]))
    elif m := receipt_re.fullmatch(line):
        receipts.append(list(map(int,m.groups())))
assert pending is None
assert len(line_vertex_counts) == 79  # 73 strip calls and six interfaces
assert len(wedges) == 6 and len(interfaces) == 6
for name,wedge in zip(('low0','low1','low2','low3','low4','high'),wedges):
    assert wedge['core'] == prior['wedges'][name]['core'], name
    assert wedge['boundaries'] == prior['wedges'][name]['boundaries'], name
for actual,expected in zip(interfaces,prior['interfaces']):
    assert actual == {k:expected[k] for k in ('line','q0','vertices')}
strips = [b for w in wedges for b in w['boundaries']]
finite = sum(b['finite_pip'] for b in strips) + sum(x['finite_pip'] for x in prior['interfaces'])
assert receipts == [[6,6,73,finite,164]] and finite == 952
assert len({tuple(b['coefficients']) for b in strips}) == 69
result = {'native_receipt_count':1,'aggregate_exit':0,'wedges':6,'strip_obligations':73,'distinct_boundary_lines':69,'explicit_lines':6,'finite_prefix_pip_obligations':finite,'native_max_symbolic_vertices':164,'observed_max_line_symbolic_vertices':max(line_vertex_counts),'native_max_field_scope':'wedge cores and explicit interfaces; boundary-line graph sizes are not accumulated by the driver','matches_previous_complete_component_campaign':True,'mathematical_source':'aggregate.log (native Mojo driver), not this script'}
(ROOT/'aggregate-reconciliation.json').write_text(json.dumps(result,indent=2)+'\n')
print('Native serial log reconciles with all six cores, 73 strips, six interfaces and 952 finite-prefix PIP obligations.')
