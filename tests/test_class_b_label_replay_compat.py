"""Historical pins stay strict; independent occurrence checks refuse mutations."""
import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('b_label_compat', ROOT/'oracles/python/class_b_label_replay_compat.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


@pytest.mark.parametrize('q', [9, 10])
def test_all_historical_occurrences_are_legal(q):
    data = (m.PACKET/f'witnesses/plus-g1-q{q}.labels').read_bytes()
    count = m.validate_witnesses(data, data, 'plus', 1, q)
    assert count == sum(line.startswith(b'W ') for line in data.splitlines())
    assert count > 2000


def test_historical_exporter_pin_is_original(tmp_path):
    assert m.check_source() == '7b42520141e1c68de19f86880ebef1b2b61b3d521f5878798ba2207b2de33747'
    wrong = tmp_path/'wrong.mojo'
    wrong.write_bytes(m.SOURCE.read_bytes()+b'\n')
    with pytest.raises(ValueError, match='original packet source pin'):
        m.check_source(source=wrong)


@pytest.mark.parametrize('mutation', ['ordinal', 'letters', 'shift', 'depth', 'missing', 'duplicate', 'extra', 'labels'])
def test_occurrence_and_coverage_mutations_refuse(mutation):
    original = (m.PACKET/'witnesses/plus-g1-q10.labels').read_bytes()
    lines = original.decode().splitlines()
    w = next(i for i,line in enumerate(lines) if line.startswith('W '))
    if mutation in ('ordinal', 'letters', 'shift'):
        fields = lines[w].split()
        column = {'ordinal': 11, 'letters': 6, 'shift': 8}[mutation]
        fields[column] = '999999'
        lines[w] = ' '.join(fields)
    elif mutation in ('depth', 'labels'):
        v = next(i for i,line in enumerate(lines) if line.startswith('V '))
        fields = lines[v].split()
        column = 6 if mutation == 'depth' else 3
        fields[column] = str(int(fields[column])+1)
        lines[v] = ' '.join(fields)
    elif mutation == 'missing':
        lines.pop(w)
    elif mutation == 'duplicate':
        lines.append(lines[w])
    else:
        lines.append('UNKNOWN')
    with pytest.raises(ValueError):
        m.validate_witnesses(('\n'.join(lines)+'\n').encode(), original, 'plus', 1, 10)
