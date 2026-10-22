"""Index completed canonical call receipts; never emit a certificate marker."""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
CORE = re.compile(r'^WEDGE_CORE_CERTIFIED u0= (\d+) v0= (\d+) vertices= (\d+)$')
BEGIN = re.compile(r'^BEGIN_BOUNDARY_LINE (\d+) class D line \(norm mode\) p = (-?\d+)n \+ (-?\d+) q = (-?\d+)n \+ (-?\d+) r = (-?\d+)n \+ (-?\d+)$')
DONE = re.compile(r'^BOUNDARY_LINE_CERTIFIED (\d+) q0= (\d+) finite_pip= (\d+)$')
INTERFACE = re.compile(r'^PLUS_CHAMBER_COMPONENT_CERTIFIED line (\d+) q0= (\d+) vertices= (\d+) finite_pip= (\d+)$')


def scan(name, low0=False):
    path = ROOT/name
    if not path.exists():
        return {'log': name, 'state': 'not-started', 'boundaries': []}
    text = path.read_text()
    if low0:
        text = text.split('BEGIN_LOW_WEDGE 1\n')[0]
    result = {'log': name, 'core': None, 'boundaries': []}
    pending = None
    for line in text.splitlines():
        if m := CORE.fullmatch(line):
            result['core'] = dict(zip(['u0','v0','vertices'], map(int,m.groups())))
        if m := BEGIN.fullmatch(line):
            pending = [int(x) for x in m.groups()]
        if m := DONE.fullmatch(line):
            index, threshold, finite = map(int,m.groups())
            if pending is None or pending[0] != index:
                raise RuntimeError(f'unmatched boundary receipt in {name}')
            result['boundaries'].append({'index':index,'coefficients':pending[1:], 'q0':threshold,'finite_pip':finite})
            pending = None
    exit_path = path.with_suffix('.exit')
    result['exit'] = int(exit_path.read_text()) if exit_path.exists() else None
    result['component_receipt'] = any(x.startswith('PLUS_CHAMBER_COMPONENT_CERTIFIED') for x in text.splitlines())
    if low0:
        result['component_receipt'] = 'BEGIN_LOW_WEDGE 1\n' in path.read_text()
        result['exit'] = None  # enclosing aggregate may still be running
    return result


def main():
    low0 = scan('pinned-component-low0.log')
    if not low0.get('component_receipt'):
        low0 = scan('pinned-complete-chambers.log', True)
    wedges = {'low0': low0}
    for name in ['low1','low2','low3','low4','high']:
        wedges[name] = scan(f'pinned-component-{name}.log')
    interfaces = []
    for j in range(1,7):
        path = ROOT/f'pinned-component-line{j}.log'
        if path.exists():
            for line in path.read_text().splitlines():
                if m := INTERFACE.fullmatch(line):
                    interfaces.append(dict(zip(['line','q0','vertices','finite_pip'],map(int,m.groups()))))
    completed = [b for w in wedges.values() for b in w['boundaries']]
    aggregate = ROOT/'pinned-complete-chambers.log'
    receipt = [s for s in aggregate.read_text().splitlines() if s.startswith('CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED')] if aggregate.exists() else []
    result = {'wedges':wedges, 'interfaces':interfaces,
              'completed_strip_obligations':len(completed),
              'distinct_completed_lines':len({tuple(b['coefficients']) for b in completed}),
              'aggregate_receipt':receipt,
              'source_context':'run-context.json',
              'note':'Progress index only. Source log calls and their exit status are authoritative; this index certifies nothing.'}
    (ROOT/'component-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('strip obligations',len(completed),'distinct lines',result['distinct_completed_lines'],
          'interfaces',len(interfaces),'aggregate receipt',bool(receipt))

if __name__ == '__main__':
    main()
