"""Replay provenance guards must refuse mismatches even under python -O."""
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize('mode,message', [('ast', 'unrelated semantic change'),
                                         ('corpus', 'ordered warm-up corpus mismatch')])
def test_optimized_replay_refuses_corruption(mode, message):
    code = '''
import runpy
import subprocess
ns = runpy.run_path('oracles/python/pip_mul_benchmark.py')
original = subprocess.check_output
mode = MODE

def corrupt(*args, **kwargs):
    source = original(*args, **kwargs)
    if mode == 'ast':
        return source + '\\ndef unrelated(): return 0\\n'
    return source.replace('def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]',
                          'def mul(A,B): return [[0]*3 for _ in range(3)]')
subprocess.check_output = corrupt
ns['main']()
'''.replace('MODE', repr(mode))
    result = subprocess.run([sys.executable, '-O', '-c', code], cwd=ROOT,
                            text=True, capture_output=True)
    assert result.returncode != 0
    assert message in result.stderr
    assert not result.stdout
