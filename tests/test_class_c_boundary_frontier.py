"""Reject damaged frontier exports, including plausible summaries/counts."""
import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'frontier_oracle',ROOT / 'oracles/python/check_class_c_boundary_frontier.py')
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


@pytest.fixture(scope='module')
def export_lines():
    lines = []
    for d in range(7,65):
        o = oracle.ExactClassC(d,1,2*d-5)
        for index,parent in enumerate(oracle.source_parents(o)):
            children = sorted(set(o.children(parent)))
            for prefix,states in [('P',[parent]),('C',children)]:
                for A,B,w in states:
                    lines.append(' '.join(map(str,(prefix,d,index,A,B,*w))))
            lines.append(f'COUNTS {d} {index} {len(children)}')
    lines.append('BOUNDARY_TEN_FRONTIER_PASS 58 580 4439')
    return tuple(lines)


@pytest.mark.parametrize('damage', ['missing_parent','missing_child','duplicate_parent',
                                    'duplicate_child','corrupt_child','false_summary'])
def test_damaged_frontier_refused(tmp_path,export_lines,damage):
    lines = list(export_lines)
    parent = next(i for i,s in enumerate(lines) if s.startswith('P '))
    child = next(i for i,s in enumerate(lines) if s.startswith('C '))
    if damage == 'missing_parent':
        lines.pop(parent)
    elif damage == 'missing_child':
        lines.pop(child)
    elif damage == 'duplicate_parent':
        lines.append(lines[parent])
    elif damage == 'duplicate_child':
        lines.append(lines[child])
    elif damage == 'corrupt_child':
        row = lines[child].split()
        row[-1] = str(int(row[-1])+1)
        lines[child] = ' '.join(row)
    else:
        lines[-1] = 'BOUNDARY_TEN_FRONTIER_PASS 58 580 4438'
    dump = tmp_path / 'damaged.txt'
    dump.write_text('\n'.join(lines)+'\n')
    with pytest.raises(AssertionError):
        oracle.check(dump)
