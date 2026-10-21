"""Independent exact graph comparison and damaged-evidence controls."""
import importlib.util
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('class_a_oracle', ROOT/'oracles/python/class_a_run_index.py')
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)
PACKET = ROOT/'evidence/class-a-run-index-2026-10-21'


def test_independent_complete_graph():
    result = oracle.calibrate(PACKET/'graph-n4.log')
    assert result['vertices'] == 275
    assert result['max_first_hit'] == 5
    assert result['all_labels_depths_seeds_and_edges_equal']


@pytest.mark.parametrize('damage', ['edge', 'duplicate', 'index', 'depth', 'seed', 'completion'])
def test_damaged_graph_refuses(tmp_path, damage):
    lines = (PACKET/'graph-n4.log').read_text().splitlines()
    pos = next(i for i,l in enumerate(lines) if l.startswith('E '))
    if damage=='edge':
        lines.pop(pos)
    elif damage=='duplicate':
        lines.append(lines[pos])
    elif damage=='index':
        fields=lines[pos].split(); fields[-1]='999'; lines[pos]=' '.join(fields)
    elif damage=='depth':
        i=next(i for i,l in enumerate(lines) if l.startswith('V '))
        fields=lines[i].split(); fields[-1]='999'; lines[i]=' '.join(fields)
    elif damage=='seed':
        lines.pop(next(i for i,l in enumerate(lines) if l.startswith('SEED ')))
    else:
        lines=[l for l in lines if not l.startswith('SUMMARY ')]
    damaged=tmp_path/'damaged.log'
    damaged.write_text('\n'.join(lines)+'\n')
    with pytest.raises(ValueError):
        oracle.calibrate(damaged)
