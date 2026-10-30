"""Full-set corruption and omitted sharp-boundary records must refuse."""
import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'indexed_oracle',ROOT / 'oracles/python/check_class_c_indexed_transfer.py')
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


@pytest.fixture(scope='module')
def export_lines():
    lines = []
    for d in range(7,65):
        o = oracle.ExactClassC(d,1,2*d-5)
        for K in oracle.representatives(d):
            for prefix,states in [('P',[oracle.parent(o,K)]),('C',sorted(oracle.formulas(o,K)))]:
                for A,B,w in states:
                    lines.append(' '.join(map(str,(prefix,d,K,A,B,*w))))
    lines.append('INDEXED_TRANSFER_INTERFACES_PASS 58 357 3686')
    return tuple(lines)


@pytest.mark.parametrize('damage',['missing_parent','missing_child','duplicate_child',
                                 'corrupt_child','missing_wall','false_summary'])
def test_damaged_indexed_export_refused(tmp_path,export_lines,damage):
    lines = list(export_lines)
    parent = next(i for i,s in enumerate(lines) if s.startswith('P '))
    child = next(i for i,s in enumerate(lines) if s.startswith('C '))
    if damage == 'missing_parent':
        lines.pop(parent)
    elif damage == 'missing_child':
        lines.pop(child)
    elif damage == 'duplicate_child':
        lines.append(lines[child])
    elif damage == 'corrupt_child':
        row = lines[child].split()
        row[-1] = str(int(row[-1])+1)
        lines[child] = ' '.join(row)
    elif damage == 'missing_wall':
        lines = [s for s in lines if not s.startswith(('P 7 7 ','C 7 7 '))]
    else:
        lines[-1] = 'INDEXED_TRANSFER_INTERFACES_PASS 58 357 3685'
    dump = tmp_path / 'damaged.txt'
    dump.write_text('\n'.join(lines)+'\n')
    with pytest.raises(AssertionError):
        oracle.check(dump)
