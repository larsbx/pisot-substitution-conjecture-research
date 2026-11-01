"""Reject corrupt full sets and erased/changed translation counterexamples."""
import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'r_oracle',ROOT / 'oracles/python/check_class_c_r_transfer.py')
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


@pytest.fixture(scope='module')
def export_lines():
    lines = []
    for d in range(7,65):
        o = oracle.ExactClassC(d,1,2*d-5)
        parents,children = oracle.formulas(o)
        for index in range(3):
            for prefix,states in [('P',[parents[index]]),('C',sorted(children[index]))]:
                for A,B,w in states:
                    lines.append(' '.join(map(str,(prefix,d,index,A,B,*w))))
    lines.extend(['R_TRANSFER_INTERFACES_PASS 58 174 870','N 0 2 -30 -9 4',
                  'R_TRANSLATION_NONCOMMUTATION_PASS 6 4'])
    return tuple(lines)


@pytest.mark.parametrize('damage',['missing_parent','missing_child','duplicate_parent',
    'duplicate_child','corrupt_child','false_summary','missing_negative','corrupt_negative'])
def test_damaged_r_export_refused(tmp_path,export_lines,damage):
    lines = list(export_lines)
    parent = next(i for i,s in enumerate(lines) if s.startswith('P '))
    child = next(i for i,s in enumerate(lines) if s.startswith('C '))
    negative = next(i for i,s in enumerate(lines) if s.startswith('N '))
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
    elif damage == 'false_summary':
        lines[-3] = 'R_TRANSFER_INTERFACES_PASS 58 174 869'
    elif damage == 'missing_negative':
        lines.pop(negative)
    else:
        lines[negative] = 'N 0 2 -30 -9 5'
    dump = tmp_path / 'damaged.txt'
    dump.write_text('\n'.join(lines)+'\n')
    with pytest.raises(AssertionError):
        oracle.check(dump)
